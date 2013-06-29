package superspec.tt

trait ProductAST extends CoreAST {
  // pair data
  case class Pair(A: CTerm, B: CTerm, a: CTerm, b: CTerm) extends CTerm
  // type of pair
  case class Product(A: CTerm, B: CTerm) extends ITerm
  case class Fst(A: CTerm, B: CTerm, p: CTerm) extends ITerm
  case class Snd(A: CTerm, B: CTerm, p: CTerm) extends ITerm

  case class VPair(A: Value, B: Value, a: Value, b: Value) extends Value
  case class VProduct(A: Value, B: Value) extends Value

  case class NFst(A: Value, B: Value, p: Neutral) extends Neutral
  case class NSnd(A: Value, B: Value, p: Neutral) extends Neutral
}

trait ProductPrinter extends CorePrinter with ProductAST {
  override def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Product(a, b) =>
      iPrint(p, ii, Free(Global("Product")) @@ a @@ b)
    case Fst(a, b, pr) =>
      iPrint(p, ii, Free(Global("fst")) @@ a @@ b @@ pr)
    case Snd(a, b, pr) =>
      iPrint(p, ii, Free(Global("snd")) @@ a @@ b @@ pr)
    case _ =>
      super.iPrint(p, ii, t)
  }

  override def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case Pair(a, b, x, y) =>
      iPrint(p, ii, Free(Global("Pair")) @@ a @@ b @@ x @@ y)
    case _ =>
      super.cPrint(p, ii, t)
  }
}

trait ProductEval extends CoreEval with ProductAST {
  override def eval(t: CTerm, named: NameEnv[Value], bound: Env): Value = t match {
    case Pair(a, b, x, y) =>
      VPair(eval(a, named, bound), eval(b, named, bound), eval(x, named, bound), eval(y, named, bound))
    case _ =>
      super.eval(t, named, bound)
  }

  override def eval(t: ITerm, named: NameEnv[Value], bound: Env): Value = t match {
    case Product(a, b) =>
      VProduct(eval(a, named, bound), eval(b, named, bound))
    case Fst(a, b, p) =>
      eval(p, named, bound) match {
        case VPair(_, _, x, _) =>
          x
        case VNeutral(n) =>
          VNeutral(NFst(eval(a, named, bound), eval(b, named, bound), n))
      }
    case Snd(a, b, p) =>
      eval(p, named, bound) match {
        case VPair(_, _, _, y) =>
          y
        case VNeutral(n) =>
          VNeutral(NSnd(eval(a, named, bound), eval(b, named, bound), n))
      }
    case _ =>
      super.eval(t, named, bound)
  }
}

trait ProductCheck extends CoreCheck with ProductAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: ITerm): Value = t match {
    case Product(a, b) =>
      cType(i, named, bound, a, VStar)
      cType(i, named, bound, b, VStar)
      VStar
    case Fst(a, b, p) =>
      cType(i, named, bound, a, VStar)
      val aVal = eval(a, named, List())
      cType(i, named, bound, b, VStar)
      val bVal = eval(b, named, List())
      cType(i, named, bound, p, VProduct(aVal, bVal))
      aVal
    case Snd(a, b, p) =>
      cType(i, named, bound, a, VStar)
      val aVal = eval(a, named, List())
      cType(i, named, bound, b, VStar)
      val bVal = eval(b, named, List())
      cType(i, named, bound, p, VProduct(aVal, bVal))
      bVal
    case _ =>
      super.iType(i, named, bound, t)
  }


  override def cType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], ct: CTerm, t: Value): Unit = (ct, t) match {
    case (Pair(a, b, x, y), VProduct(aVal, bVal)) =>
      cType(i, named, bound, a, VStar)
      assert(quote0(eval(a, named, List())) == quote0(aVal), "type mismatch")
      cType(i, named, bound, b, VStar)
      assert (quote0(eval(b, named, List())) == quote0(bVal), "type mismatch")
      cType(i, named, bound, x, aVal)
      cType(i, named, bound, y, bVal)
    case _ =>
      super.cType(i, named, bound, ct, t)
  }

  override def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Product(a, b) =>
      Product(cSubst(i, r, a), cSubst(i, r, b))
    case Fst(a, b, p) =>
      Fst(cSubst(i, r, a), cSubst(i, r, b), cSubst(i, r, p))
    case Snd(a, b, p) =>
      Snd(cSubst(i, r, a), cSubst(i, r, b), cSubst(i, r, p))
    case _ => super.iSubst(i, r, it)
  }

  override def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case Pair(a, b, x, y) =>
      Pair(cSubst(ii, r, a), cSubst(ii, r, b), cSubst(ii, r, x), cSubst(ii, r, y))
    case _ =>
      super.cSubst(ii, r, ct)
  }

}

trait ProductQuote extends CoreQuote with ProductAST {
  override def quote(ii: Int, v: Value): CTerm = v match {
    case VProduct(a, b) => Inf(Product(quote(ii, a), quote(ii, b)))
    case VPair(a, b, x, y) => Pair(quote(ii, a), quote(ii, b), quote(ii, x), quote(ii, y))
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): ITerm = n match {
    case NFst(a, b, p) =>
      Fst(quote(ii, a), quote(ii, b), Inf(neutralQuote(ii, p)))
    case NSnd(a, b, p) =>
      Snd(quote(ii, a), quote(ii, b), Inf(neutralQuote(ii, p)))
    case _ => super.neutralQuote(ii, n)
  }
}

trait ProductREPL extends CoreREPL with ProductAST with ProductPrinter with ProductCheck with ProductEval with ProductQuote {
  lazy val productTE: NameEnv[Value] =
    Map(
      Global("Product") -> VPi(VStar, _ => VPi(VStar, _ => VStar)),
      Global("Pair") -> VPi(VStar, a => VPi(VStar, b => VPi(a, _ => VPi(b, _ => VProduct(a, b))))),
      Global("fst") -> VPi(VStar, a => VPi(VStar, b => VPi(VProduct(a, b), _ => a))),
      Global("snd") -> VPi(VStar, a => VPi(VStar, b => VPi(VProduct(a, b), _ => b)))
    )

  val productVE: NameEnv[Value] =
    Map(
      Global("Product") -> VLam(a => VLam(b => VProduct(a, b))),
      Global("Pair") -> VLam(a => VLam(b => VLam(x => VLam(y => VPair(a, b, x, y))) )),
      Global("fst") -> eval0(Lam(Lam(Lam( Inf(Fst(Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)))) )))),
      Global("snd") -> eval0(Lam(Lam(Lam( Inf(Snd(Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)))) ))))
    )
}
