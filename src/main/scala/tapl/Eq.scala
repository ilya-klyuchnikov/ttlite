package tapl

trait EqAST extends LambdaPiAST {
  // Refl t e -> Eq t e e
  case class Refl(t: CTerm, e: CTerm) extends CTerm
  case class Eq(t: CTerm, e1: CTerm, e2: CTerm) extends ITerm
  case class EqElim(c1: CTerm, c2: CTerm, c3: CTerm, c4: CTerm, c5: CTerm, c6: CTerm) extends ITerm
  case class VEq(t: Value, e1: Value, e2: Value) extends Value
  case class VRefl(t: Value, e: Value) extends Value
  case class NEqElim(v1: Value, v2: Value, v3: Value, v4: Value, v5: Value, n: Neutral) extends Neutral
}

trait EqEval extends LambdaPiEval with EqAST {
  override def cEval(c: CTerm, d: (NameEnv[Value], Env)): Value = c match {
    case Refl(a, x) => VRefl(cEval(a, d), cEval(x, d))
    case _ => super.cEval(c, d)
  }
  override def iEval(i: ITerm, d: (NameEnv[Value], Env)): Value = i match {
    case Eq(a, x, y) =>
      VEq(cEval(a, d), cEval(x, d), cEval(y, d))
    case EqElim(a, m, mr, x, y, eq) =>
      cEval(eq, d) match {
        case VRefl(_, z) => vapp(cEval(mr, d), z)
        case VNeutral(n) =>
          VNeutral(NEqElim(cEval(a, d), cEval(m, d), cEval(mr, d), cEval(x, d), cEval(y, d), n))
      }
    case _ =>
      super.iEval(i, d)
  }
}

trait EqCheck extends LambdaPiCheck with EqAST {
  override def iType(i: Int, g: (NameEnv[Value], Context), t: ITerm): Result[Type] = t match {
    case Eq(a, x, y) =>
      assert(cType(i, g, a, VStar).isRight)
      val aVal = cEval(a, (g._1, Nil))
      assert(cType(i, g, x, aVal).isRight)
      assert(cType(i, g, x, aVal).isRight)
      Right(VStar)
    case EqElim(a, m, mr, x, y, eq) =>
      val aVal = cEval(a, (g._1, Nil))
      assert(cType(i, g, m, VPi(aVal, {x => VPi(aVal, {y => VPi(VEq(aVal, x, y), {_ => VStar})})})).isRight)
      val mVal = cEval(m, (g._1, Nil))
      assert(cType(i, g, mr, VPi(aVal, {x => vapp(vapp(mVal, x), x)})).isRight)
      assert(cType(i, g, x, aVal).isRight)
      val xVal = cEval(x, (g._1, Nil))
      assert(cType(i, g, y, aVal).isRight)
      val yVal = cEval(y, (g._1, Nil))
      assert(cType(i, g, eq, VEq(aVal, xVal, yVal)).isRight)
      // why??
      val eqVal = cEval(eq, (g._1, Nil))
      Right(vapp(vapp(mVal, xVal), yVal))
    case _ =>
      super.iType(i, g, t)
  }

  override def cType(ii: Int, g: (NameEnv[Value], Context), ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (Refl(a, z), VEq(bVal, xVal, yVal)) =>
      assert(cType(ii, g, a, VStar).isRight)
      val aVal = cEval(a, (g._1, Nil))
      assert(quote0(aVal) == quote0(bVal), "type mismatch")
      assert(cType(ii, g, z, aVal).isRight)
      val zVal = cEval(z, (g._1, Nil))
      assert(quote0(zVal) == quote0(xVal) && quote0(zVal) == quote0(yVal))
      Right()
    case _ =>
      super.cType(ii, g, ct, t)
  }

  override def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Eq(a, x, y) =>
      Eq(cSubst(i, r, a), cSubst(i, r, x), cSubst(i, r, y))
    case EqElim(a, m, mr, x, y, eq) =>
      EqElim(cSubst(i, r, a), cSubst(i, r, m), cSubst(i, r, mr), cSubst(i, r, x), cSubst(i, r, y), cSubst(i, r, eq))
    case _ =>
      super.iSubst(i, r, it)
  }

  override def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case Refl(a, x) =>
      Refl(cSubst(ii, r, a), cSubst(ii, r, x))
    case _ =>
      super.cSubst(ii, r, ct)
  }
}

trait EqQuote extends LambdaPiQuote with EqAST {
  override def quote(ii: Int, v: Value): CTerm = v match {
    case VEq(a, x, y) =>
      Inf(Eq(quote(ii, a), quote(ii, x), quote(ii, y)))
    case VRefl(a, x) =>
      Refl(quote(ii, a), quote(ii, x))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): ITerm = n match {
    case NEqElim(a, m, mr, x, y, eq) =>
      EqElim(quote(ii, a), quote(ii, m), quote(ii, mr), quote(ii, x), quote(ii, y), Inf(neutralQuote(ii, eq)))
    case _ => super.neutralQuote(ii, n)
  }
}

trait EqREPL extends LambdaPiREPL with EqAST with EqCheck with EqEval with EqQuote {
  val eqTE: Ctx[Value] =
    List(
      Global("Refl") -> VPi(VStar, {a => VPi(a, {x => VEq(a, x, x)})}),
      Global("Eq") -> VPi(VStar, {a => VPi(a, {x => VPi(a, {y => VStar})})}),
      Global("eqElim") ->
        VPi(VStar, {a =>
        VPi(VPi(a, {x => VPi(a, {y => VPi(VEq(a, x, y), {_ => VStar})})}), {m =>
        VPi(VPi(a, {x => vapp(vapp(vapp(m, x), x), VRefl(a, x))}), {_ =>
        VPi(a, {x => VPi(a, {y =>
        VPi(VEq(a, x, y), {eq =>
        vapp(vapp(vapp(m, x), y), eq)}) })})})})})
    )
  val eqVE: Ctx[Value] =
    List(
      Global("Refl") -> VLam({a => VLam({x => VRefl(a, x)})}),
      Global("Eq") -> VLam(a => VLam(x => VLam(y =>VEq(a, x, y)))),
      Global("eqElim") ->
        cEval(Lam(Lam(Lam(Lam(Lam(Lam(Inf(EqElim(Inf(Bound(5)), Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)) ) ))))))), (Nil,Nil))
    )
}
