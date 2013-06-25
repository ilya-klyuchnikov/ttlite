package superspec.lambdapi

trait EqAST extends CoreAST {
  // Refl A x :: Eq A x x
  case class Refl(A: CTerm, x: CTerm) extends CTerm
  case class Eq(A: CTerm, x: CTerm, y: CTerm) extends ITerm
  // EqElim(A, prop, propR, x, y, eq)
  // A - type of x and y (that is, x :: A, y :: A)
  // prop(x, y, eq) - proposition we would like to infer (which involves both x and y and Eq A x y)
  // propR(a, refl) - "reflexive" proposition ( prop(x, y, eq)[x -> a, y -> a, eq -> refl]
  // x, y - elems
  // eq - proof that x = y
  // See Simon Thompson. "Type Theory & Functional Programming", pp 110,111 for a good explanation.
  case class EqElim(A: CTerm, prop: CTerm, propR: CTerm, x: CTerm, y: CTerm, eq: CTerm) extends ITerm
  case class VEq(A: Value, x: Value, y: Value) extends Value
  case class VRefl(A: Value, x: Value) extends Value
  case class NEqElim(A: Value, prop: Value, propR: Value, x: Value, y: Value, eq: Neutral) extends Neutral
}

trait EqSubst extends CoreSubst with EqAST {
  override def findSubst0(from: CTerm, to: CTerm): Option[Subst] = (from, to) match {
    case (Refl(a1, x1), Refl(a2, x2)) =>
      val s1 = findSubst0(a1, a2)
      val s2 = findSubst0(x1, x2)
      mergeOptSubst(s1, s2)
    case _ =>
      super.findSubst0(from, to)
  }

  override def findSubst0(from: ITerm, to: ITerm): Option[Subst] = (from, to) match {
    case (Eq(a1, x1, y1), Eq(a2, x2, y2)) =>
      mergeOptSubst(
        findSubst0(a1, a2),
        findSubst0(x1, x2),
        findSubst0(y1, y2)
      )
    case (EqElim(a1, m1, mr1, x1, y1, eq1), EqElim(a2, m2, mr2, x2, y2, eq2)) =>
      mergeOptSubst(
        findSubst0(a1, a2),
        findSubst0(m1, m2),
        findSubst0(mr1, mr2),
        findSubst0(x1, x2),
        findSubst0(y1, y2),
        findSubst0(eq1, eq2)
      )
    case _ =>
      super.findSubst0(from, to)
  }
}

trait EqPrinter extends CorePrinter with EqAST {
  override def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Eq(a, x, y) =>
      iPrint(p, ii, Free(Global("Eq")) @@ a @@ x @@ y)
    case EqElim(a, m, mr, x, y, eq) =>
      iPrint(p, ii, Free(Global("eqElim")) @@ a @@ m @@ mr @@ x @@ y @@ eq)
    case _ =>
      super.iPrint(p, ii, t)
  }

  override def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case Refl(a, x) =>
      iPrint(p, ii, Free(Global("Refl")) @@ a @@ x)
    case _ =>
      super.cPrint(p, ii, t)
  }
}

trait EqEval extends CoreEval with EqAST {
  override def cEval(c: CTerm, nEnv: NameEnv[Value], bEnv: Env): Value = c match {
    case Refl(a, x) => VRefl(cEval(a, nEnv, bEnv), cEval(x, nEnv, bEnv))
    case _ => super.cEval(c, nEnv, bEnv)
  }
  override def iEval(i: ITerm, nEnv: NameEnv[Value], bEnv: Env): Value = i match {
    case Eq(a, x, y) =>
      VEq(cEval(a, nEnv, bEnv), cEval(x, nEnv, bEnv), cEval(y, nEnv, bEnv))
    case EqElim(a, prop, propR, x, y, eq) =>
      cEval(eq, nEnv, bEnv) match {
        case VRefl(_, z) =>
          vapp(cEval(propR, nEnv, bEnv), z)
        case VNeutral(n) =>
          VNeutral(NEqElim(
            cEval(a, nEnv, bEnv),
            cEval(prop, nEnv, bEnv),
            cEval(propR, nEnv, bEnv),
            cEval(x, nEnv, bEnv),
            cEval(y, nEnv, bEnv), n))
      }
    case _ =>
      super.iEval(i, nEnv, bEnv)
  }
}

trait EqDriver extends CoreDriver with EqAST {
  override def driveNeutral(n: Neutral): DriveStep = n match {
    case eqElim: NEqElim =>
      driveNeutral(eqElim.eq)
    case _ =>
      super.driveNeutral(n)
  }
}

trait EqCheck extends CoreCheck with EqAST {
  override def iType(i: Int, nEnv: NameEnv[Value], ctx: NameEnv[Value], t: ITerm): Result[Type] = t match {
    case Eq(a, x, y) =>
      assert(cType(i, nEnv, ctx, a, VStar).isRight)
      val aVal = cEval(a, nEnv, Nil)
      assert(cType(i, nEnv, ctx, x, aVal).isRight)
      assert(cType(i, nEnv, ctx, x, aVal).isRight)
      Right(VStar)
    case EqElim(a, prop, propR, x, y, eq) =>
      assert(cType(i, nEnv, ctx, a, VStar).isRight)

      val aVal = cEval(a, nEnv, Nil)
      assert(cType(i, nEnv, ctx, x, aVal).isRight)

      assert(cType(i, nEnv, ctx, prop, VPi(aVal, {x => VPi(aVal, {y => VPi(VEq(aVal, x, y), {_ => VStar})})})).isRight)
      val propVal = cEval(prop, nEnv, Nil)

      // the main point is here: we check that prop x x (Refl A x) is well-typed
      // propR :: {a => x => prop x x (Refl a x)}
      assert(cType(i, nEnv, ctx, propR, VPi(aVal, {x => propVal @@ x @@ x @@ VRefl(aVal, x)})).isRight)

      val xVal = cEval(x, nEnv, Nil)
      assert(cType(i, nEnv, ctx, y, aVal).isRight)
      val yVal = cEval(y, nEnv, Nil)
      assert(cType(i, nEnv, ctx, eq, VEq(aVal, xVal, yVal)).isRight)

      Right(vapp(vapp(propVal, xVal), yVal))
    case _ =>
      super.iType(i, nEnv, ctx, t)
  }

  override def cType(ii: Int, nEnv: NameEnv[Value], ctx: NameEnv[Value], ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (Refl(a, z), VEq(bVal, xVal, yVal)) =>
      assert(cType(ii, nEnv, ctx, a, VStar).isRight)
      val aVal = cEval(a, nEnv, Nil)
      assert(quote0(aVal) == quote0(bVal), "type mismatch")
      assert(cType(ii, nEnv, ctx, z, aVal).isRight)
      val zVal = cEval(z, nEnv, Nil)
      assert(quote0(zVal) == quote0(xVal) && quote0(zVal) == quote0(yVal))
      Right()
    case _ =>
      super.cType(ii, nEnv, ctx, ct, t)
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

trait EqQuote extends CoreQuote with EqAST {
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

trait EqREPL extends CoreREPL with EqAST with EqPrinter with EqCheck with EqEval with EqQuote {
  lazy val eqTE: Ctx[Value] =
    List(
      Global("Refl") -> ReflType,
      Global("Eq") -> EqType,
      Global("eqElim") -> eqElimType
    )

  val EqTypeIn =
    "forall (A :: *) . forall (x :: A) . forall (y :: A) . *"
  val ReflTypeIn =
    "forall (A :: *) . forall (a :: A) . Eq A a a"
  val eqElimTypeIn =
    """
      |forall (A :: *) .
      |forall (prop :: forall (x :: A) . forall (y :: A) . forall (_ :: Eq A x y) . * ) .
      |forall (propR :: forall a :: A . prop a a (Refl A a)) .
      |forall (x :: A) .
      |forall (y :: A) .
      |forall (eq :: Eq A x y) .
      |prop x y eq
    """.stripMargin

  lazy val EqType = int.ieval(eqVE, int.parseIO(int.iiparse, EqTypeIn).get)
  lazy val ReflType = int.ieval(eqVE, int.parseIO(int.iiparse, ReflTypeIn).get)
  lazy val eqElimType = int.ieval(eqVE, int.parseIO(int.iiparse, eqElimTypeIn).get)

  val eqVE: Ctx[Value] =
    List(
      Global("Refl") -> VLam({a => VLam({x => VRefl(a, x)})}),
      Global("Eq") -> VLam(a => VLam(x => VLam(y =>VEq(a, x, y)))),
      Global("eqElim") ->
        cEval(
          Lam(Lam(Lam(Lam(Lam(Lam(
            Inf(EqElim(Inf(Bound(5)), Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0))))
          )))))),
          Nil,Nil)
    )
}
