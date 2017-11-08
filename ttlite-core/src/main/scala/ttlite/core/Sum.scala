package ttlite.core

import ttlite.common._

// Chapter 12. Disjoint union of two sets
trait SumAST extends AST {
  case class Sum(A: Term, B: Term) extends Term
  case class InL(et: Term, l: Term) extends Term
  case class InR(et: Term, r: Term) extends Term
  case class SumElim(et: Term, m: Term, lCase: Term, rCase: Term, sum: Term) extends Term

  case class VSum(L: Value, R: Value) extends Value
  case class VInL(et: Value, l: Value) extends Value
  case class VInR(et: Value, r: Value) extends Value
  case class NSumElim(et: Value, m: Value, lCase: Value, rCase: Value, sum: Neutral) extends Neutral
}

trait SumMetaSyntax extends MetaSyntax with SumAST {
  abstract override def translate(m: MTerm): Term = m match {
    case MVar(Global("Sum")) @@ l @@ r =>
      Sum(translate(l), translate(r))
    case MVar(Global("InL")) @@ et @@ inj =>
      InL(translate(et), translate(inj))
    case MVar(Global("InR")) @@ et @@ inj =>
      InR(translate(et), translate(inj))
    case MVar(Global("elim")) @@ (MVar(Global("Sum")) @@ l @@ r) @@ m @@ lc @@ rc @@ inj =>
      SumElim(Sum(translate(l), translate(r)), translate(m), translate(lc), translate(rc), translate(inj))
    case _ => super.translate(m)
  }
}

trait SumPrinter extends Printer with SumAST {
  abstract override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Sum(a, b) =>
      printL(p, ii, 'Sum, a, b)
    case InL(et, l) =>
      printL(p, ii, 'InL, et, l)
    case InR(et, r) =>
      printL(p, ii, 'InR, et, r)
    case SumElim(et, m, lc, rc, sum) =>
      printL(p, ii, 'elim, et, m, lc, rc, sum)
    case _ =>
      super.print(p, ii, t)
  }
}

trait SumPrinterAgda extends PrinterAgda with SumAST {
  abstract override def printA(p: Int, ii: Int, t: Term): Doc = t match {
    case Sum(a, b) =>
      printAL(p, ii, 'Sum, a, b)
    case InL(Sum(a, b), l) =>
      printAL(p, ii, 'inl, a, b, l)
    case InR(Sum(a, b), r) =>
      printAL(p, ii, 'inr, a, b, r)
    case SumElim(Sum(a, b), m, lc, rc, sum) =>
      printAL(p, ii, 'elimSum, a, b, m, lc, rc, sum)
    case _ =>
      super.printA(p, ii, t)
  }
}

trait SumPrinterCoq extends PrinterCoq with SumAST {
  abstract override def printC(p: Int, ii: Int, t: Term): Doc = t match {
    case Sum(a, b) =>
      printCL(p, ii, 'Sum, a, b)
    case InL(Sum(a, b), l) =>
      printCL(p, ii, 'inl, a, b, l)
    case InR(Sum(a, b), r) =>
      printCL(p, ii, 'inr, a, b, r)
    case SumElim(Sum(a, b), m, lc, rc, sum) =>
      printCL(p, ii, 'elimSum, a, b, m, lc, rc, sum)
    case _ =>
      super.printC(p, ii, t)
  }
}

trait SumPrinterIdris extends PrinterIdris with SumAST {
  abstract override def printI(p: Int, ii: Int, t: Term): Doc = t match {
    case Sum(a, b) =>
      printIL(p, ii, 'Sum, a, b)
    case InL(Sum(a, b), l) =>
      printIL(p, ii, 'Inl, a, b, l)
    case InR(Sum(a, b), r) =>
      printIL(p, ii, 'Inr, a, b, r)
    case SumElim(Sum(a, b), m, lc, rc, sum) =>
      printIL(p, ii, 'elimSum, a, b, m, lc, rc, sum)
    case _ =>
      super.printI(p, ii, t)
  }
}

trait SumEval extends Eval with SumAST { self: FunAST =>
  abstract override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Sum(lt, rt) =>
      VSum(eval(lt, ctx, bound), eval(rt, ctx, bound))
    case InL(et, l) =>
      VInL(eval(et, ctx, bound), eval(l, ctx, bound))
    case InR(et, r) =>
      VInR(eval(et, ctx, bound), eval(r, ctx, bound))
    case SumElim(et@Sum(lt, rt), m, lc, rc, sum) =>
      val etVal = eval(et, ctx, bound)
      val mVal = eval(m, ctx, bound)
      val lcVal = eval(lc, ctx, bound)
      val rcVal = eval(rc, ctx, bound)
      val sumVal = eval(sum, ctx, bound)
      sumElim(etVal, mVal, lcVal, rcVal, sumVal)
    case _ =>
      super.eval(t, ctx, bound)
  }

  def sumElim(etVal: Value, mVal: Value, lcVal: Value, rcVal: Value, sumVal: Value): Value =
    sumVal match {
      case VInL(_, lVal) =>
        lcVal @@ lVal
      case VInR(_, rVal) =>
        rcVal @@ rVal
      case VNeutral(n) =>
        VNeutral(NSumElim(etVal, mVal, lcVal, rcVal, n))
    }
}

trait SumCheck extends Check with SumAST { self: FunAST =>
  abstract override def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value = t match {
    case Sum(a, b) =>
      val aType = iType(i, path/(2, 3), ctx, a)
      val j = checkUniverse(i, aType, path/(2, 3))

      val bType = iType(i, path/(3, 3), ctx, b)
      val k = checkUniverse(i, bType, path/(3, 3))

      VUniverse(math.max(j, k))
    case InL(et, l) =>
      val eType = iType(i, path/(2, 3), ctx, et)
      checkUniverse(i, eType, path/(2, 3))
      val etVal = eval(et, ctx, List())
      require(etVal.isInstanceOf[VSum], path/(2, 3), "Sum _ _", et)
      val VSum(aVal, bVal) = etVal

      val lType = iType(i, path/(3, 3), ctx, l)
      checkEqual(i, lType, aVal, path/(3, 3))

      VSum(aVal, bVal)
    case InR(et, r) =>
      val eType = iType(i, path/(2, 3), ctx, et)
      checkUniverse(i, eType, path/(2, 3))
      val etVal = eval(et, ctx, List())
      require(etVal.isInstanceOf[VSum], path/(2, 3), "Sum _ _", et)
      val VSum(aVal, bVal) = etVal

      val rType = iType(i, path/(3, 3), ctx, r)
      checkEqual(i, rType, bVal, path/(3, 3))

      VSum(aVal, bVal)
    case SumElim(et, m, lc, rc, sum) =>
      val eType = iType(i, path/(2, 6), ctx, et)
      checkUniverse(i, eType, path/(2, 6))
      val etVal = eval(et, ctx, List())
      require(etVal.isInstanceOf[VSum], path/(2, 6), "Sum _ _", et)
      val VSum(ltVal, rtVal) = etVal

      val mType = iType(i, path/(3, 6), ctx, m)
      checkEqual(i, mType, VPi(VSum(ltVal, rtVal), {_ => VUniverse(-1)}), path/(3, 6))
      val mVal = eval(m, ctx, List())

      val lcType = iType(i, path/(4, 6), ctx, lc)
      checkEqual(i, lcType, VPi(ltVal, {lVal => mVal @@ VInL(etVal, lVal)}), path/(4, 6))

      val rcType = iType(i, path/(5, 6), ctx, rc)
      checkEqual(i, rcType, VPi(rtVal, {rVal => mVal @@ VInR(etVal, rVal)}), path/(5, 6))

      val sumType = iType(i, path/(6, 6), ctx, sum)
      checkEqual(i, sumType, VSum(ltVal, rtVal), path/(6, 6))
      val sumVal = eval(sum, ctx, List())

      mVal @@ sumVal
    case _ =>
      super.iType(i, path, ctx, t)
  }

  abstract override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Sum(a, b) =>
      Sum(iSubst(i, r, a), iSubst(i, r, b))
    case InL(et, x) =>
      InL(iSubst(i, r, et), iSubst(i, r, x))
    case InR(et, x) =>
      InR(iSubst(i, r, et), iSubst(i, r, x))
    case SumElim(et, m, lc, rc, sum) =>
      SumElim(iSubst(i, r, et), iSubst(i, r, m), iSubst(i, r, lc), iSubst(i, r, rc), iSubst(i, r, sum))
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait SumQuoting extends Quoting with SumAST { self: FunAST =>
  abstract override def quote(ii: Int, v: Value): Term = v match {
    case VSum(a, b) =>
      Sum(quote(ii, a), quote(ii, b))
    case VInL(et, x) =>
      InL(quote(ii, et), quote(ii, x))
    case VInR(et, x) =>
      InR(quote(ii, et), quote(ii, x))
    case _ =>
      super.quote(ii, v)
  }

  abstract override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NSumElim(et, m, lc, rc, sum) =>
      SumElim(quote(ii, et), quote(ii, m), quote(ii, lc), quote(ii, rc), neutralQuote(ii, sum))
    case _ => super.neutralQuote(ii, n)
  }
}

trait SumREPL
  extends CoreREPL
  with SumAST
  with SumMetaSyntax
  with SumPrinter
  with SumPrinterAgda
  with SumPrinterCoq
  with SumPrinterIdris
  with SumCheck
  with SumEval
  with SumQuoting {
  self: FunAST =>
}
