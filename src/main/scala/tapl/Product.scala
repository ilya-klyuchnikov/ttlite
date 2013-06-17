package tapl

trait PairAST extends LambdaPiAST {
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

trait PairPrinter extends LambdaPiPrinter with PairAST {
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

trait PairEval extends LambdaPiEval with PairAST {
  override def cEval(c: CTerm, d: (NameEnv[Value], Env)): Value = c match {
    case Pair(a, b, x, y) =>
      VPair(cEval(a, d), cEval(b, d), cEval(x, d), cEval(y, d))
    case _ =>
      super.cEval(c, d)
  }

  override def iEval(i: ITerm, d: (NameEnv[Value], Env)): Value = i match {
    case Product(a, b) =>
      VProduct(cEval(a, d), cEval(b, d))
    case Fst(a, b, p) =>
      cEval(p, d) match {
        case VPair(_, _, x, _) =>
          x
        case VNeutral(n) =>
          VNeutral(NFst(cEval(a, d), cEval(b, d), n))
      }
    case Snd(a, b, p) =>
      cEval(p, d) match {
        case VPair(_, _, _, y) =>
          y
        case VNeutral(n) =>
          VNeutral(NSnd(cEval(a, d), cEval(b, d), n))
      }
    case _ =>
      super.iEval(i, d)
  }
}

trait PairCheck extends LambdaPiCheck with PairAST {
  override def iType(i: Int, g: (NameEnv[Value], Context), t: ITerm): Result[Type] = t match {
    case Product(a, b) =>
      assert(cType(i, g, a, VStar).isRight)
      assert(cType(i, g, b, VStar).isRight)
      Right(VStar)
    case Fst(a, b, p) =>
      assert(cType(i, g, a, VStar).isRight)
      val aVal = cEval(a, (g._1, List()))

      assert(cType(i, g, b, VStar).isRight)
      val bVal = cEval(b, (g._1, List()))

      assert(cType(i, g, p, VProduct(aVal, bVal)).isRight)
      Right((aVal))
    case Snd(a, b, p) =>
      assert(cType(i, g, a, VStar).isRight)
      val aVal = cEval(a, (g._1, List()))

      assert(cType(i, g, b, VStar).isRight)
      val bVal = cEval(b, (g._1, List()))

      assert(cType(i, g, p, VProduct(aVal, bVal)).isRight)
      Right((bVal))
    case _ =>
      super.iType(i, g, t)
  }


  override def cType(ii: Int, g: (NameEnv[Value], Context), ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (Pair(a, b, x, y), VProduct(aVal, bVal)) =>
      assert(cType(ii, g, a, VStar).isRight)
      if (quote0(cEval(a, (g._1, List()))) != quote0(aVal))
        return Left("type mismatch")
      assert(cType(ii, g, b, VStar).isRight)
      if (quote0(cEval(b, (g._1, List()))) != quote0(bVal))
        return Left("type mismatch")
      assert(cType(ii, g, x, aVal).isRight)
      assert(cType(ii, g, y, bVal).isRight)
      Right(())
    case _ =>
      super.cType(ii, g, ct, t)
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

trait PairQuote extends LambdaPiQuote with PairAST {
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

trait PairREPL extends LambdaPiREPL with PairAST with PairPrinter with PairCheck with PairEval with PairQuote {
  lazy val productTE: Ctx[Value] =
    List(
      Global("Product") -> VPi(VStar, _ => VPi(VStar, _ => VStar)),
      Global("Pair") -> VPi(VStar, a => VPi(VStar, b => VPi(a, _ => VPi(b, _ => VProduct(a, b))))),
      Global("fst") -> VPi(VStar, a => VPi(VStar, b => VPi(VProduct(a, b), _ => a))),
      Global("snd") -> VPi(VStar, a => VPi(VStar, b => VPi(VProduct(a, b), _ => b)))
    )

  val productVE: Ctx[Value] =
    List(
      Global("Product") -> VLam(a => VLam(b => VProduct(a, b))),
      Global("Pair") -> VLam(a => VLam(b => VLam(x => VLam(y => VPair(a, b, x, y))) )),
      Global("fst") -> cEval(Lam(Lam(Lam( Inf(Fst(Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)))) ))), (Nil, Nil)),
      Global("snd") -> cEval(Lam(Lam(Lam( Inf(Snd(Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)))) ))), (Nil, Nil))
    )
}
