package superspec.tt

trait ProductAST extends CoreAST {
  case class Product(A: Term, B: Term) extends Term
  case class Pair(A: Term, B: Term, a: Term, b: Term) extends Term
  case class Fst(A: Term, B: Term, p: Term) extends Term
  case class Snd(A: Term, B: Term, p: Term) extends Term

  case class VProduct(A: Value, B: Value) extends Value
  case class VPair(A: Value, B: Value, a: Value, b: Value) extends Value
  case class NFst(A: Value, B: Value, p: Neutral) extends Neutral
  case class NSnd(A: Value, B: Value, p: Neutral) extends Neutral
}

trait ProductPrinter extends CorePrinter with ProductAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Product(a, b) =>
      print(p, ii, Free(Global("Product")) @@ a @@ b)
    case Pair(a, b, x, y) =>
      print(p, ii, Free(Global("Pair")) @@ a @@ b @@ x @@ y)
    case Fst(a, b, pr) =>
      print(p, ii, Free(Global("fst")) @@ a @@ b @@ pr)
    case Snd(a, b, pr) =>
      print(p, ii, Free(Global("snd")) @@ a @@ b @@ pr)
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
    case Fst(a, b, p) =>
      eval(p, named, bound) match {
        case VPair(_, _, x, _) => x
        case VNeutral(n) => VNeutral(NFst(eval(a, named, bound), eval(b, named, bound), n))
      }
    case Snd(a, b, p) =>
      eval(p, named, bound) match {
        case VPair(_, _, _, y) => y
        case VNeutral(n) => VNeutral(NSnd(eval(a, named, bound), eval(b, named, bound), n))
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
    case Fst(a, b, p) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val bType = iType(i, named, bound, b)
      checkEqual(bType, Star)

      val pType = iType(i, named, bound, p)
      checkEqual(pType, VProduct(aVal, bVal))

      aVal
    case Snd(a, b, p) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val bType = iType(i, named, bound, b)
      checkEqual(bType, Star)

      val pType = iType(i, named, bound, p)
      checkEqual(pType, VProduct(aVal, bVal))

      bVal
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Product(a, b) =>
      Product(iSubst(i, r, a), iSubst(i, r, b))
    case Pair(a, b, x, y) =>
      Pair(iSubst(i, r, a), iSubst(i, r, b), iSubst(i, r, x), iSubst(i, r, y))
    case Fst(a, b, p) =>
      Fst(iSubst(i, r, a), iSubst(i, r, b), iSubst(i, r, p))
    case Snd(a, b, p) =>
      Snd(iSubst(i, r, a), iSubst(i, r, b), iSubst(i, r, p))
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
    case NFst(a, b, p) =>
      Fst(quote(ii, a), quote(ii, b), neutralQuote(ii, p))
    case NSnd(a, b, p) =>
      Snd(quote(ii, a), quote(ii, b), neutralQuote(ii, p))
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
      Global("fst") ->
        VPi(VStar, a => VPi(VStar, b => VPi(VProduct(a, b), _ => a))),
      Global("snd") ->
        VPi(VStar, a => VPi(VStar, b => VPi(VProduct(a, b), _ => b)))
    )

  val productVE: NameEnv[Value] =
    Map(
      Global("Product") ->
        VLam(VStar, a => VLam(VStar, b => VProduct(a, b))),
      Global("Pair") ->
        VLam(VStar, a => VLam(VStar, b => VLam(a, x => VLam(b, y => VPair(a, b, x, y))))),
      Global("fst") ->
        VLam(VStar, a => VLam(VStar, b => VLam(VProduct(a, b), {n =>
          eval(Fst(Bound(2), Bound(1), Bound(0)), productVE, List(n, b, a))
        }))),
      Global("snd") ->
        VLam(VStar, a => VLam(VStar, b => VLam(VProduct(a, b), {n =>
          eval(Snd(Bound(2), Bound(1), Bound(0)), productVE, List(n, b, a))
        })))
    )
}
