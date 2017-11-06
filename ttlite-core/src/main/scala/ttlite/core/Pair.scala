package ttlite.core

import ttlite.common._

trait PairAST extends AST {
  case class Product(A: Term, B: Term) extends Term
  case class Pair(et: Term, a: Term, b: Term) extends Term
  case class ProductElim(et: Term, m: Term, f: Term, pair: Term) extends Term

  case class VProduct(A: Value, B: Value) extends Value
  case class VPair(et: Value, a: Value, b: Value) extends Value
  case class NProductElim(et: Value, m: Value, f: Value, pair: Neutral) extends Neutral
}

trait PairMetaSyntax extends MetaSyntax with PairAST {
  abstract override def translate(m: MTerm): Term = m match {
    case MVar(Global("Product")) @@ a @@ b =>
      Product(translate(a), translate(b))
    case MVar(Global("Pair")) @@ et @@ x @@ y =>
      Pair(translate(et), translate(x), translate(y))
    case MVar(Global("elim")) @@ (MVar(Global("Product")) @@ a @@ b) @@ m @@ f @@ p =>
      ProductElim(Product(translate(a), translate(b)), translate(m), translate(f), translate(p))
    case _ => super.translate(m)
  }
}

trait PairPrinter extends Printer with PairAST {
  abstract override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Product(a, b) =>
      printL(p, ii, 'Product, a, b)
    case Pair(et, x, y) =>
      printL(p, ii, 'Pair, et, x, y)
    case ProductElim(et, m, f, pair) =>
      printL(p, ii, 'elim, et, m, f, pair)
    case _ =>
      super.print(p, ii, t)
  }
}

trait PairPrinterAgda extends PrinterAgda with PairAST {
  abstract override def printA(p: Int, ii: Int, t: Term): Doc = t match {
    case Product(a, b) =>
      printAL(p, ii, 'Pair, a, b)
    case Pair(Product(a, b), x, y) =>
      printAL(p, ii, 'pair, a, b, x, y)
    case ProductElim(Product(a, b), m, f, pair) =>
      printAL(p, ii, 'elimPair, a, b, m, f, pair)
    case _ =>
      super.printA(p, ii, t)
  }
}

trait PairPrinterCoq extends PrinterCoq with PairAST {
  abstract override def printC(p: Int, ii: Int, t: Term): Doc = t match {
    case Product(a, b) =>
      printCL(p, ii, 'Pair, a, b)
    case Pair(Product(a, b), x, y) =>
      printCL(p, ii, 'pair, a, b, x, y)
    case ProductElim(Product(a, b), m, f, pair) =>
      printCL(p, ii, 'elimPair, a, b, m, f, pair)
    case _ =>
      super.printC(p, ii, t)
  }
}

trait PairPrinterIdris extends PrinterIdris with PairAST {
  abstract override def printI(p: Int, ii: Int, t: Term): Doc = t match {
    case Product(a, b) =>
      printIL(p, ii, 'TTPair, a, b)
    case Pair(Product(a, b), x, y) =>
      printIL(p, ii, 'Pair, a, b, x, y)
    case ProductElim(Product(a, b), m, f, pair) =>
      printIL(p, ii, 'elimPair, a, b, m, f, pair)
    case _ =>
      super.printI(p, ii, t)
  }
}

trait PairEval extends Eval with PairAST { self: FunAST =>
  abstract override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Product(a, b) =>
      VProduct(eval(a, ctx, bound), eval(b, ctx, bound))
    case Pair(et, x, y) =>
      VPair(eval(et, ctx, bound), eval(x, ctx, bound), eval(y, ctx, bound))
    case ProductElim(et, m, f, pair) =>
      val etVal = eval(et, ctx, bound)
      val mVal = eval(m, ctx, bound)
      val fVal = eval(f, ctx, bound)
      val pVal = eval(pair, ctx, bound)
      productElim(etVal, mVal, fVal, pVal)
    case _ =>
      super.eval(t, ctx, bound)
  }

  def productElim(etVal: Value, mVal: Value, fVal: Value, pVal: Value): Value =
    pVal match {
      case VPair(_, x, y) =>
        fVal @@ x @@ y
      case VNeutral(n) =>
        VNeutral(NProductElim(etVal, mVal, fVal, n))
    }
}

trait PairCheck extends Check with PairAST { self: FunAST =>
  abstract override def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value = t match {
    case Product(a, b) =>
      val aType = iType(i, path/(2, 3), ctx, a)
      val j = checkUniverse(i, aType, path/(2, 3))

      val bType = iType(i, path/(3, 3), ctx, b)
      val k = checkUniverse(i, bType, path/(3, 3))

      VUniverse(math.max(j, k))
    case Pair(et, x, y) =>
      val eType = iType(i, path/(2, 4), ctx, et)
      checkUniverse(i, eType, path/(2, 4))
      val etVal = eval(et, ctx, List())
      require(etVal.isInstanceOf[VProduct], path/(2, 4), "Product _ _", et)
      val VProduct(aVal, bVal) = etVal

      val xType = iType(i, path/(3, 4), ctx, x)
      checkEqual(i, xType, aVal, path/(3, 4))

      val yType = iType(i, path/(4, 4), ctx, y)
      checkEqual(i, yType, bVal, path/(4, 4))

      VProduct(aVal, bVal)
    case ProductElim(et, m, f, p) =>
      val eType = iType(i, path/(2, 5), ctx, et)
      checkUniverse(i, eType, path/(2, 5))
      val etVal = eval(et, ctx, List())
      require(etVal.isInstanceOf[VProduct], path/(2, 5), "Product _ _", et)
      val VProduct(aVal, bVal) = etVal

      val mType = iType(i, path/(3, 5), ctx, m)
      checkEqual(i, mType, VPi(VProduct(aVal, bVal), {_ => VUniverse(-1)}), path/(3, 5))
      val mVal = eval(m, ctx, List())

      val fType = iType(i, path/(4, 5), ctx, f)
      checkEqual(i, fType, VPi(aVal, a => VPi(bVal, b => mVal @@ VPair(VProduct(aVal, bVal), a, b))), path/(4, 5))

      val pType = iType(i, path/(5, 5), ctx, p)
      checkEqual(i, pType, VProduct(aVal, bVal), path/(5, 5))
      val pVal = eval(p, ctx, List())

      mVal @@ pVal
    case _ =>
      super.iType(i, path, ctx, t)
  }

  abstract override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Product(a, b) =>
      Product(iSubst(i, r, a), iSubst(i, r, b))
    case Pair(et, x, y) =>
      Pair(iSubst(i, r, et), iSubst(i, r, x), iSubst(i, r, y))
    case ProductElim(et, m, f, p) =>
      ProductElim(iSubst(i, r, et), iSubst(i, r, m), iSubst(i, r, f), iSubst(i, r, p))
    case _ => super.iSubst(i, r, it)
  }
}

trait PairQuoting extends Quoting with PairAST {
  abstract override def quote(ii: Int, v: Value): Term = v match {
    case VProduct(a, b) =>
      Product(quote(ii, a), quote(ii, b))
    case VPair(et, x, y) =>
      Pair(quote(ii, et), quote(ii, x), quote(ii, y))
    case _ => super.quote(ii, v)
  }

  abstract override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NProductElim(et, m, f, p) =>
      ProductElim(quote(ii, et), quote(ii, m), quote(ii, f), neutralQuote(ii, p))
    case _ => super.neutralQuote(ii, n)
  }
}

trait PairREPL
  extends CoreREPL
  with PairAST
  with PairMetaSyntax
  with PairPrinter
  with PairPrinterAgda
  with PairPrinterCoq
  with PairPrinterIdris
  with PairCheck
  with PairEval
  with PairQuoting {
  self: FunAST =>
}
