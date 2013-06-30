package superspec.tt
/*
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
  override def eval(t: CTerm, named: NameEnv[Value], bound: Env): Value = t match {
    case VecNil(a) =>
      VVecNil(eval(a, named, bound))
    case VecCons(a, n, head, tail) =>
      VVecCons(eval(a, named, bound), eval(n, named, bound), eval(head, named, bound), eval(tail, named, bound))
    case _ =>
      super.eval(t, named, bound)
  }

  override def eval(t: ITerm, named: NameEnv[Value], bound: Env): Value = t match {
    case Vec(a, n) =>
      VVec(eval(a, named, bound), eval(n, named, bound))
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      val nilCaseVal = eval(nilCase, named, bound)
      val consCaseVal = eval(consCase, named, bound)
      def rec(nVal: Value, vecVal: Value): Value = vecVal match {
        case VVecNil(_) =>
          nilCaseVal
        case VVecCons(_, n, head, tail) =>
          consCaseVal @@ n @@ head @@ tail @@ rec(n, tail)
        case VNeutral(n) =>
          VNeutral(NVecElim(eval(a, named, bound), eval(m, named, bound), nilCaseVal, consCaseVal, nVal, n))
      }
      rec(eval(n, named, bound), eval(vec, named, bound))
    case _ =>
      super.eval(t, named, bound)
  }
}

trait VectorCheck extends CoreCheck with VectorAST with NatAST with VectorEval {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: ITerm): Value = t match {
    case Vec(a, n) =>
      cType(i, named, bound, a, VStar)
      cType(i, named, bound, n, VNat)
      VStar
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      cType(i, named, bound, a, VStar)
      val aVal = eval(a, named, List())
      cType(i, named, bound, m, VPi(VNat, {n => VPi(VVec(aVal, n), {_ => VStar})}))

      val mVal = eval(m, named, List())
      cType(i, named, bound, nilCase, mVal @@ VZero @@ VVecNil(aVal))

      cType(i, named, bound, consCase, VPi(VNat, {n =>
        VPi(aVal, {y =>
          VPi(VVec(aVal, n), {ys =>
            VPi(mVal @@ n @@ ys, {_ =>
              mVal @@ VSucc(n) @@ VVecCons(aVal, n, y, ys)
            })})})}))

      cType(i, named, bound, n, VNat)
      val nVal = eval(n, named, List())
      cType(i, named, bound, vec, VVec(aVal, nVal))
      val vecVal = eval(vec, named, List())
      mVal @@ nVal @@ vecVal
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def cType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], ct: CTerm, t: Value): Unit = (ct, t) match {
    case (VecNil(a), VVec(bVal, VZero)) =>
      cType(i, named, bound, a, VStar)
      val aVal = eval(a, named, List())
      assert(quote0(aVal) == quote0(bVal), "type mismatch")
    case (VecCons(a, n, head, tail), VVec(bVal, VSucc(k))) =>
      cType(i, named, bound, a, VStar)
      val aVal = eval(a, named, List())
      assert(quote0(aVal) == quote0(bVal), "type mismatch")
      cType(i, named, bound, n, VNat)
      val nVal = eval(n, named, List())
      assert(quote0(nVal) == quote0(k), "type mismatch")
      cType(i, named, bound, head, aVal)
      cType(i, named, bound, tail, VVec(bVal, k))
    case _ =>
      super.cType(i, named, bound, ct, t)
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
  lazy val vectorTE: NameEnv[Value] =
    Map(
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

  lazy val VecType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iParse, VecTypeIn).get)
  lazy val vecElimType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iParse, vecElimTypeIn).get)
  lazy val VNilType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iParse, VNilTypeIn).get)
  lazy val VConsType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iParse, VConsTypeIn).get)

  val vectorVE: NameEnv[Value] =
    Map(
      Global("Vec") -> VLam(a => VLam(n =>  VVec (a, n))),
      Global("vecElim") ->
        eval0(
          Lam(Lam(Lam(Lam(Lam(Lam(
            Inf(VecElim(Inf(Bound(5)), Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0))))
          ))))))),
      Global("VNil") -> VLam(a => VVecNil(a)),
      Global("VCons") -> VLam(a => VLam(n => VLam(x => VLam(y => VVecCons(a, n, x, y)))))
    )
}*/
