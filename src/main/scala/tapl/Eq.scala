package tapl

trait EqAST extends LambdaPiAST {
  // Refl A x :: Eq A x x
  case class Refl(A: CTerm, x: CTerm) extends CTerm
  case class Eq(A: CTerm, x: CTerm, y: CTerm) extends ITerm
  // EqElim(A, prop, propR, x, y, eq)
  // A - type of x and y (that is, x :: A, y :: A)
  // prop(x, y, eq) - proposition we would like to infer (which involves both x and y and Eq A x y)
  // propR(a, refl) - "reflexive" proposition ( prop(x, y, eq)[x -> a, y -> a, eq -> refl]
  // x, y - elems
  // eq - proof that x = y
  // This is also called Leibniz principle.
  // See Simon Thompson. "Type Theory & Functional Programming", pp 110,111 for a good explanation.
  case class EqElim(A: CTerm, prop: CTerm, propR: CTerm, x: CTerm, y: CTerm, eq: CTerm) extends ITerm
  case class VEq(A: Value, x: Value, y: Value) extends Value
  case class VRefl(A: Value, x: Value) extends Value
  case class NEqElim(A: Value, prop: Value, propR: Value, x: Value, y: Value, eq: Neutral) extends Neutral
}

trait EqPrinter extends LambdaPiPrinter with EqAST {
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

trait EqEval extends LambdaPiEval with EqAST {
  override def cEval(c: CTerm, d: (NameEnv[Value], Env)): Value = c match {
    case Refl(a, x) => VRefl(cEval(a, d), cEval(x, d))
    case _ => super.cEval(c, d)
  }
  override def iEval(i: ITerm, d: (NameEnv[Value], Env)): Value = i match {
    case Eq(a, x, y) =>
      VEq(cEval(a, d), cEval(x, d), cEval(y, d))
    case EqElim(a, prop, propR, x, y, eq) =>
      cEval(eq, d) match {
        case VRefl(_, z) => vapp(cEval(propR, d), z)
        case VNeutral(n) =>
          VNeutral(NEqElim(cEval(a, d), cEval(prop, d), cEval(propR, d), cEval(x, d), cEval(y, d), n))
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
    case EqElim(a, prop, propR, x, y, eq) =>
      val aVal = cEval(a, (g._1, Nil))
      assert(cType(i, g, prop, VPi(aVal, {x => VPi(aVal, {y => VPi(VEq(aVal, x, y), {_ => VStar})})})).isRight)
      val propVal = cEval(prop, (g._1, Nil))
      // TODO: insert Refl
      assert(cType(i, g, propR, VPi(aVal, {x => vapp(vapp(propVal, x), x)})).isRight)
      assert(cType(i, g, x, aVal).isRight)
      val xVal = cEval(x, (g._1, Nil))
      assert(cType(i, g, y, aVal).isRight)
      val yVal = cEval(y, (g._1, Nil))
      assert(cType(i, g, eq, VEq(aVal, xVal, yVal)).isRight)
      // why??
      val eqVal = cEval(eq, (g._1, Nil))
      Right(vapp(vapp(propVal, xVal), yVal))
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
        cEval(Lam(Lam(Lam(Lam(Lam(Lam(Inf(EqElim(Inf(Bound(5)), Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)) ) ))))))), (Nil,Nil))
    )
}
