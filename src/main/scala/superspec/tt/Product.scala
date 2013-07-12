package superspec.tt

trait ProductAST extends CoreAST {
  case class Product(A: Term, B: Term) extends Term
  case class Pair(A: Term, B: Term, a: Term, b: Term) extends Term
  case class ProductElim(A: Term, B: Term, m: Term, f: Term, pair: Term) extends Term

  case class VProduct(A: Value, B: Value) extends Value
  case class VPair(A: Value, B: Value, a: Value, b: Value) extends Value
  case class NProductElim(A: Value, B: Value, m: Value, f: Value, pair: Neutral) extends Neutral
}

trait ProductPrinter extends CorePrinter with ProductAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Product(a, b) =>
      print(p, ii, Free(Global("Product")) @@ a @@ b)
    case Pair(a, b, x, y) =>
      print(p, ii, Free(Global("Pair")) @@ a @@ b @@ x @@ y)
    case ProductElim(a, b, m, f, pair) =>
      print(p, ii, Free(Global("productElim")) @@ a @@ b @@ a @@ f @@ pair)
    case _ =>
      super.print(p, ii, t)
  }
}

trait ProductEval extends CoreEval with ProductAST {
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
      eval(pair, named, bound) match {
        case VPair(_, _, x, y) =>
          fVal @@ x @@ y
        case VNeutral(n) =>
          VNeutral(NProductElim(aVal, bVal, mVal, fVal, n))
      }
    case _ =>
      super.eval(t, named, bound)
  }
}

trait ProductCheck extends CoreCheck with ProductAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Product(a, b) =>
      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val bType = iType(i, named, bound, b)
      checkEqual(bType, Star)

      VStar
    case Pair(a, b, x, y) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val bType = iType(i, named, bound, b)
      checkEqual(bType, Star)

      val xType = iType(i, named, bound, x)
      checkEqual(xType, aVal)

      val yType = iType(i, named, bound, y)
      checkEqual(yType, bVal)

      VProduct(aVal, bVal)
    case ProductElim(a, b, m, f, p) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())
      val mVal = eval(m, named, List())
      val pVal = eval(f, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val bType = iType(i, named, bound, b)
      checkEqual(bType, Star)

      val pType = iType(i, named, bound, p)
      checkEqual(pType, VProduct(aVal, bVal))

      val mType = iType(i, named, bound, m)
      checkEqual(mType, VPi(VProduct(aVal, bVal), {_ => VStar}))

      val fType = iType(i, named, bound, f)
      checkEqual(fType, VPi(aVal, a => VPi(bVal, b => mVal @@ VPair(aVal, bVal, a, b))))

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

trait ProductREPL extends CoreREPL with ProductAST with ProductPrinter with ProductCheck with ProductEval with ProductQuote {
  lazy val productTE: NameEnv[Value] =
    Map(
      Global("Product") ->
        VPi(VStar, _ => VPi(VStar, _ => VStar)),
      Global("Pair") ->
        VPi(VStar, a => VPi(VStar, b => VPi(a, _ => VPi(b, _ => VProduct(a, b))))),
      Global("productElim") ->
        productElimType
    )

  val productElimTypeIn =
    """
      |forall (A :: *) .
      |forall (B :: *) .
      |forall (m :: forall (_ :: Product A B) . *) .
      |forall (f :: forall (a :: A) (b :: B) . m (Pair A B a b)) .
      |forall (p :: Product A B) .
      |  m p
    """.stripMargin

  lazy val productElimType = int.ieval(productVE, int.parseIO(int.iParse, productElimTypeIn).get)

  val productVE: NameEnv[Value] =
    Map(
      Global("Product") ->
        VLam(VStar, a => VLam(VStar, b => VProduct(a, b))),
      Global("Pair") ->
        VLam(VStar, a => VLam(VStar, b => VLam(a, x => VLam(b, y => VPair(a, b, x, y))))),
      Global("productElim") ->
        VLam(VStar, a => VLam(VStar, b =>
          VLam(VPi(VProduct(a, b), _ => VStar), m =>
            VLam(a, x => VLam(b, y =>
              VLam(VProduct(a, b), p =>
                eval(ProductElim(Bound(4), Bound(3), Bound(2), Bound(1), Bound(0)), productVE, List(p, y, x, m, b, a))
              ))))))

    )
}
