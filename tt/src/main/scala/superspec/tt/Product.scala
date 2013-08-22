package superspec.tt

trait ProductAST extends CoreAST {
  case class Product(A: Term, B: Term) extends Term
  case class Pair(A: Term, B: Term, a: Term, b: Term) extends Term
  case class ProductElim(A: Term, B: Term, m: Term, f: Term, pair: Term) extends Term

  case class VProduct(A: Value, B: Value) extends Value
  case class VPair(A: Value, B: Value, a: Value, b: Value) extends Value
  case class NProductElim(A: Value, B: Value, m: Value, f: Value, pair: Neutral) extends Neutral
}

trait MProduct extends MCore with ProductAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Product")) @@ a @@ b =>
      Product(fromM(a), fromM(b))
    case MVar(Global("Pair")) @@ a @@ b @@ x @@ y =>
      Pair(fromM(a), fromM(b), fromM(x), fromM(y))
    case MVar(Global("productElim")) @@ a @@ b @@ m @@ f @@ p =>
      ProductElim(fromM(a), fromM(b), fromM(m), fromM(f), fromM(p))
    case _ => super.fromM(m)
  }
}

trait ProductPrinter extends FunPrinter with ProductAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Product(a, b) =>
      print(p, ii, 'Product @@ a @@ b)
    case Pair(a, b, x, y) =>
      print(p, ii, 'Pair @@ a @@ b @@ x @@ y)
    case ProductElim(a, b, m, f, pair) =>
      print(p, ii, 'productElim @@ a @@ b @@ m @@ f @@ pair)
    case _ =>
      super.print(p, ii, t)
  }
}

trait ProductEval extends FunEval with ProductAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Product(a, b) =>
      VProduct(eval(a, named, bound), eval(b, named, bound))
    case Pair(a, b, x, y) =>
      VPair(eval(a, named, bound), eval(b, named, bound), eval(x, named, bound), eval(y, named, bound))
    case ProductElim(a, b, m, f, pair) =>
      val aVal = eval(a, named, bound)
      val bVal = eval(b, named, bound)
      val mVal = eval(m, named, bound)
      val fVal = eval(f, named, bound)
      val pVal = eval(pair, named, bound)
      productElim(aVal, bVal, mVal, fVal, pVal)
    case _ =>
      super.eval(t, named, bound)
  }

  def productElim(aVal: Value, bVal: Value, mVal: Value, fVal: Value, pVal: Value) =
    pVal match {
      case VPair(_, _, x, y) =>
        fVal @@ x @@ y
      case VNeutral(n) =>
        VNeutral(NProductElim(aVal, bVal, mVal, fVal, n))
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
    case Pair(a, b, x, y) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())

      val aType = iType(i, named, bound, a)
      checkUniverse(i, aType)

      val bType = iType(i, named, bound, b)
      checkUniverse(i, bType)

      val xType = iType(i, named, bound, x)
      checkEqual(i, xType, aVal)

      val yType = iType(i, named, bound, y)
      checkEqual(i, yType, bVal)

      VProduct(aVal, bVal)
    case ProductElim(a, b, m, f, p) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())
      val mVal = eval(m, named, List())
      val pVal = eval(p, named, List())

      val aType = iType(i, named, bound, a)
      checkUniverse(i, aType)

      val bType = iType(i, named, bound, b)
      checkUniverse(i, bType)

      val pType = iType(i, named, bound, p)
      checkEqual(i, pType, VProduct(aVal, bVal))

      val mType = iType(i, named, bound, m)
      checkEqual(i, mType, VPi(VProduct(aVal, bVal), {_ => VUniverse(-1)}))

      val fType = iType(i, named, bound, f)
      checkEqual(i, fType, VPi(aVal, a => VPi(bVal, b => mVal @@ VPair(aVal, bVal, a, b))))

      mVal @@ pVal
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Product(a, b) =>
      Product(iSubst(i, r, a), iSubst(i, r, b))
    case Pair(a, b, x, y) =>
      Pair(iSubst(i, r, a), iSubst(i, r, b), iSubst(i, r, x), iSubst(i, r, y))
    case ProductElim(a, b, m, f, p) =>
      ProductElim(iSubst(i, r, a), iSubst(i, r, b), iSubst(i, r, m), iSubst(i, r, f), iSubst(i, r, p))
    case _ => super.iSubst(i, r, it)
  }
}

trait ProductQuote extends CoreQuote with ProductAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VProduct(a, b) =>
      Product(quote(ii, a), quote(ii, b))
    case VPair(a, b, x, y) =>
      Pair(quote(ii, a), quote(ii, b), quote(ii, x), quote(ii, y))
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NProductElim(a, b, m, f, p) =>
      ProductElim(quote(ii, a), quote(ii, b), quote(ii, m), quote(ii, f), neutralQuote(ii, p))
    case _ => super.neutralQuote(ii, n)
  }
}

trait ProductREPL2 extends CoreREPL2 with ProductAST with MProduct with ProductPrinter with ProductCheck with ProductEval with ProductQuote
