package superspec.lambdapi

trait VectorAST extends CoreAST {
  case class VecNil(A: CTerm) extends CTerm
  case class VecCons(A: CTerm, n: CTerm, head: CTerm, tail: CTerm) extends CTerm

  case class Vec(A: CTerm, n: CTerm) extends ITerm
  case class VecElim(A: CTerm, motive: CTerm, nilCase: CTerm, consCase: CTerm, n: CTerm, vec: CTerm) extends ITerm

  case class VVec(A: Value, n: Value) extends Value
  case class VVecNil(A: Value) extends Value
  case class VVecCons(A: Value, n: Value, head: Value, tail: Value) extends Value

  case class NVecElim(A: Value, motive: Value, nilCase: Value, consCase: Value, n: Value, vec: Neutral) extends Neutral
}

trait VectorPrinter extends NatPrinter with VectorAST {
  override def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Vec(a, n) =>
      iPrint(p, ii, Free(Global("Vec")) @@ a @@ n)
    case VecElim(a, m, mn, mc, n, xs) =>
      iPrint(p, ii, Free(Global("veqElim")) @@ a @@ m @@ mn @@ mc @@ n @@ xs)
    case _ =>
      super.iPrint(p, ii, t)
  }

  override def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case VecNil(a) =>
      iPrint(p, ii, Free(Global("VNil")) @@ a)
    case VecCons(a, n, x, xs) =>
      iPrint(p, ii, Free(Global("VCons")) @@ a @@ n @@ x @@ xs)
    case _ =>
      super.cPrint(p, ii, t)
  }
}

trait VectorEval extends CoreEval with VectorAST {
  override def cEval(c: CTerm, nEnv: NameEnv[Value], bEnv: Env): Value = c match {
    case VecNil(a) =>
      VVecNil(cEval(a, nEnv, bEnv))
    case VecCons(a, n, head, tail) =>
      VVecCons(cEval(a, nEnv, bEnv), cEval(n, nEnv, bEnv), cEval(head, nEnv, bEnv), cEval(tail, nEnv, bEnv))
    case _ =>
      super.cEval(c, nEnv, bEnv)
  }

  override def iEval(i: ITerm, nEnv: NameEnv[Value], bEnv: Env): Value = i match {
    case Vec(a, n) =>
      VVec(cEval(a, nEnv, bEnv), cEval(n, nEnv, bEnv))
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      val nilCaseVal = cEval(nilCase, nEnv, bEnv)
      val consCaseVal = cEval(consCase, nEnv, bEnv)
      def rec(nVal: Value, vecVal: Value): Value = vecVal match {
        case VVecNil(_) =>
          nilCaseVal
        case VVecCons(_, n, head, tail) =>
          consCaseVal @@ n @@ head @@ tail @@ rec(n, tail)
        case VNeutral(n) =>
          VNeutral(NVecElim(cEval(a, nEnv, bEnv), cEval(m, nEnv, bEnv), nilCaseVal, consCaseVal, nVal, n))
      }
      rec(cEval(n, nEnv, bEnv), cEval(vec, nEnv, bEnv))
    case _ =>
      super.iEval(i, nEnv, bEnv)
  }
}

trait VectorCheck extends CoreCheck with VectorAST with NatAST with VectorEval {
  override def iType(i: Int, nEnv: NameEnv[Value], ctx: NameEnv[Value], t: ITerm): Result[Type] = t match {
    case Vec(a, n) =>
      assert(cType(i, nEnv, ctx, a, VStar).isRight)
      assert(cType(i, nEnv, ctx, n, VNat).isRight)
      Right(VStar)
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      assert(cType(i, nEnv, ctx, a, VStar).isRight)
      val aVal = cEval(a, nEnv, List())
      assert(cType(i, nEnv, ctx, m, VPi(VNat, {n => VPi(VVec(aVal, n), {_ => VStar})})).isRight)

      val mVal = cEval(m, nEnv, List())
      assert(cType(i, nEnv, ctx, nilCase, mVal @@ VZero @@ VVecNil(aVal)).isRight)

      assert(cType(i, nEnv, ctx, consCase, VPi(VNat, {n =>
        VPi(aVal, {y =>
          VPi(VVec(aVal, n), {ys =>
            VPi(mVal @@ n @@ ys, {_ =>
              mVal @@ VSucc(n) @@ VVecCons(aVal, n, y, ys)
            })
          })
        })
      })
      ).isRight)

      assert(cType(i, nEnv, ctx, n, VNat).isRight)
      val nVal = cEval(n, nEnv, List())
      assert(cType(i, nEnv, ctx, vec, VVec(aVal, nVal)).isRight)
      val vecVal = cEval(vec, nEnv, List())
      Right(mVal @@ nVal @@ vecVal)
    case _ =>
      super.iType(i, nEnv, ctx, t)
  }

  override def cType(ii: Int, nEnv: NameEnv[Value], ctx: NameEnv[Value], ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (VecNil(a), VVec(bVal, VZero)) =>
      assert(cType(ii, nEnv, ctx, a, VStar).isRight)
      val aVal = cEval(a, nEnv, List())
      if (quote0(aVal) != quote0(bVal)) return Left("type mismatch")
      Right()
    case (VecCons(a, n, head, tail), VVec(bVal, VSucc(k))) =>
      assert(cType(ii, nEnv, ctx, a, VStar).isRight)
      val aVal = cEval(a, nEnv, List())
      if (quote0(aVal) != quote0(bVal)) return Left("type mismatch")
      assert(cType(ii, nEnv, ctx, n, VNat).isRight)
      val nVal = cEval(n, nEnv, List())
      if (quote0(nVal) != quote0(k)) return Left("type mismatch")
      assert(cType(ii, nEnv, ctx, head, aVal).isRight)
      assert(cType(ii, nEnv, ctx, tail, VVec(bVal, k)).isRight)
      Right()
    case _ =>
      super.cType(ii, nEnv, ctx, ct, t)
  }

  override def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Vec(a, n) =>
      Vec(cSubst(i, r, a), cSubst(i, r, n))
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      VecElim(cSubst(i, r, a), cSubst(i, r, m), cSubst(i, r, nilCase), cSubst(i, r, consCase), cSubst(i, r, n), cSubst(i, r, vec))
    case _ => super.iSubst(i, r, it)
  }

  override def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case VecNil(a) =>
      VecNil(cSubst(ii, r, a))
    case VecCons(a, n, head, tail) =>
      VecCons(cSubst(ii, r, a), cSubst(ii, r, n), cSubst(ii, r, head), cSubst(ii, r, tail))
    case _ =>
      super.cSubst(ii, r, ct)
  }

}

trait VectorQuote extends CoreQuote with VectorAST {
  override def quote(ii: Int, v: Value): CTerm = v match {
    case VVec(a, n) => Inf(Vec(quote(ii, a), quote(ii, n)))
    case VVecNil(a) => VecNil(quote(ii, a))
    case VVecCons(a, n, head, tail) => VecCons(quote(ii, a), quote(ii, n), quote(ii, head), quote(ii, tail))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): ITerm = n match {
    case NVecElim(a, m, nilCase, consCase, n, vec) =>
      VecElim(quote(ii, a), quote(ii, m), quote(ii, nilCase), quote(ii, consCase),
        quote(ii, n), Inf(neutralQuote(ii, vec)))
    case _ => super.neutralQuote(ii, n)
  }
}

trait VectorREPL extends NatREPL with VectorAST with VectorPrinter with VectorCheck with VectorEval with VectorQuote {
  lazy val vectorTE: Ctx[Value] =
    List(
      Global("Vec") -> VecType,
      Global("vecElim") -> vecElimType,
      Global("VNil") -> VNilType,
      Global("VCons") -> VConsType
    )

  val VecTypeIn =
    "forall (a :: *) . forall (n :: Nat) . *"
  val vecElimTypeIn =
    """
      |forall (x :: *) .
      |forall (y :: forall (y :: Nat) . forall (z :: Vec x y) . *) .
      |forall (z :: y Zero (VNil x)) .
      |forall (a :: forall (a :: Nat) . forall (b :: x) . forall (c :: Vec x a) . forall (d :: y a c) . y (Succ a) (VCons x a b c)) .
      |forall (b :: Nat) .
      |forall (c :: Vec x b) .
      |  y b c
    """.stripMargin
  val VNilTypeIn =
    "forall x :: * . Vec x Zero"
  val VConsTypeIn =
    "forall (x :: *) . forall (y :: Nat) . forall (z :: x) . forall (a :: Vec x y) . Vec x (Succ y)"

  lazy val VecType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iiparse, VecTypeIn).get)
  lazy val vecElimType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iiparse, vecElimTypeIn).get)
  lazy val VNilType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iiparse, VNilTypeIn).get)
  lazy val VConsType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iiparse, VConsTypeIn).get)

  val vectorVE: Ctx[Value] =
    List(
      Global("Vec") -> VLam(a => VLam(n =>  VVec (a, n))),
      Global("vecElim") ->
        cEval(
          Lam(Lam(Lam(Lam(Lam(Lam(
            Inf(VecElim(Inf(Bound(5)), Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0))))
          )))))), List(),List()),
      Global("VNil") -> VLam(a => VVecNil(a)),
      Global("VCons") -> VLam(a => VLam(n => VLam(x => VLam(y => VVecCons(a, n, x, y)))))
    )
}