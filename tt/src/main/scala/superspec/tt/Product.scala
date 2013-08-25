package superspec.tt

trait ProductAST extends CoreAST {
  case class Product(A: Term, B: Term) extends Term
  case class Pair(et: Term, a: Term, b: Term) extends Term
  case class ProductElim(et: Term, m: Term, f: Term, pair: Term) extends Term

  case class VProduct(A: Value, B: Value) extends Value
  case class VPair(et: Value, a: Value, b: Value) extends Value
  case class NProductElim(et: Value, m: Value, f: Value, pair: Neutral) extends Neutral
}

trait ProductMetaSyntax extends CoreMetaSyntax with ProductAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Product")) @@ a @@ b =>
      Product(fromM(a), fromM(b))
    case MVar(Global("Pair")) @@ et @@ x @@ y =>
      Pair(fromM(et), fromM(x), fromM(y))
    case MVar(Global("elim")) @@ (MVar(Global("Product")) @@ a @@ b) @@ m @@ f @@ p =>
      ProductElim(Product(fromM(a), fromM(b)), fromM(m), fromM(f), fromM(p))
    case _ => super.fromM(m)
  }
}

trait ProductPrinter extends FunPrinter with ProductAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Product(a, b) =>
      print(p, ii, 'Product @@ a @@ b)
    case Pair(et, x, y) =>
      print(p, ii, 'Pair @@ et @@ x @@ y)
    case ProductElim(et, m, f, pair) =>
      print(p, ii, 'elim @@ et @@ m @@ f @@ pair)
    case _ =>
      super.print(p, ii, t)
  }
}

trait ProductEval extends FunEval with ProductAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Product(a, b) =>
      VProduct(eval(a, named, bound), eval(b, named, bound))
    case Pair(et, x, y) =>
      VPair(eval(et, named, bound), eval(x, named, bound), eval(y, named, bound))
    case ProductElim(et, m, f, pair) =>
      val etVal = eval(et, named, bound)
      val mVal = eval(m, named, bound)
      val fVal = eval(f, named, bound)
      val pVal = eval(pair, named, bound)
      productElim(etVal, mVal, fVal, pVal)
    case _ =>
      super.eval(t, named, bound)
  }

  def productElim(etVal: Value, mVal: Value, fVal: Value, pVal: Value) =
    pVal match {
      case VPair(_, x, y) =>
        fVal @@ x @@ y
      case VNeutral(n) =>
        VNeutral(NProductElim(etVal, mVal, fVal, n))
    }
}

trait ProductCheck extends FunCheck with ProductAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Product(a, b) =>
      val aType = iType(i, named, bound, a)
      val j = checkUniverse(i, aType)

      val bType = iType(i, named, bound, b)
      val k = checkUniverse(i, bType)

      VUniverse(math.max(j, k))
    case Pair(et, x, y) =>
      val eType = iType(i, named, bound, et)
      checkUniverse(i, eType)

      val VProduct(aVal, bVal) = eval(et, named, List())

      val xType = iType(i, named, bound, x)
      checkEqual(i, xType, aVal)

      val yType = iType(i, named, bound, y)
      checkEqual(i, yType, bVal)

      VProduct(aVal, bVal)
    case ProductElim(et, m, f, p) =>
      val eType = iType(i, named, bound, et)
      checkUniverse(i, eType)

      val VProduct(aVal, bVal) = eval(et, named, List())

      val mVal = eval(m, named, List())
      val pVal = eval(p, named, List())

      val pType = iType(i, named, bound, p)
      checkEqual(i, pType, VProduct(aVal, bVal))

      val mType = iType(i, named, bound, m)
      checkEqual(i, mType, VPi(VProduct(aVal, bVal), {_ => VUniverse(-1)}))

      val fType = iType(i, named, bound, f)
      checkEqual(i, fType, VPi(aVal, a => VPi(bVal, b => mVal @@ VPair(VProduct(aVal, bVal), a, b))))

      mVal @@ pVal
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Product(a, b) =>
      Product(iSubst(i, r, a), iSubst(i, r, b))
    case Pair(et, x, y) =>
      Pair(iSubst(i, r, et), iSubst(i, r, x), iSubst(i, r, y))
    case ProductElim(et, m, f, p) =>
      ProductElim(iSubst(i, r, et), iSubst(i, r, m), iSubst(i, r, f), iSubst(i, r, p))
    case _ => super.iSubst(i, r, it)
  }
}

trait ProductQuote extends CoreQuote with ProductAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VProduct(a, b) =>
      Product(quote(ii, a), quote(ii, b))
    case VPair(et, x, y) =>
      Pair(quote(ii, et), quote(ii, x), quote(ii, y))
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NProductElim(et, m, f, p) =>
      ProductElim(quote(ii, et), quote(ii, m), quote(ii, f), neutralQuote(ii, p))
    case _ => super.neutralQuote(ii, n)
  }
}

trait ProductREPL extends CoreREPL with ProductAST with ProductMetaSyntax with ProductPrinter with ProductCheck with ProductEval with ProductQuote
