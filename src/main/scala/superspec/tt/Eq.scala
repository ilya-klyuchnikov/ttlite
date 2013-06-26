package superspec.tt

trait EqAST extends CoreAST {
  // Refl A x :: Eq A x x
  case class Refl(A: CTerm, x: CTerm) extends CTerm
  case class Eq(A: CTerm, x: CTerm, y: CTerm) extends ITerm
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
  override def eval(t: CTerm, named: NameEnv[Value], bound: Env): Value = t match {
    case Refl(a, x) => VRefl(eval(a, named, bound), eval(x, named, bound))
    case _ => super.eval(t, named, bound)
  }
  override def eval(t: ITerm, named: NameEnv[Value], bound: Env): Value = t match {
    case Eq(a, x, y) =>
      VEq(eval(a, named, bound), eval(x, named, bound), eval(y, named, bound))
    case EqElim(a, prop, propR, x, y, eq) =>
      eval(eq, named, bound) match {
        case VRefl(_, z) =>
          vapp(eval(propR, named, bound), z)
        case VNeutral(n) =>
          VNeutral(NEqElim(
            eval(a, named, bound),
            eval(prop, named, bound),
            eval(propR, named, bound),
            eval(x, named, bound),
            eval(y, named, bound), n))
      }
    case _ =>
      super.eval(t, named, bound)
  }
}

trait EqCheck extends CoreCheck with EqAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: ITerm): Result[Value] = t match {
    case Eq(a, x, y) =>
      assert(cType(i, named, bound, a, VStar).isRight)
      val aVal = eval(a, named, Nil)
      assert(cType(i, named, bound, x, aVal).isRight)
      assert(cType(i, named, bound, x, aVal).isRight)
      Right(VStar)
    case EqElim(a, prop, propR, x, y, eq) =>
      assert(cType(i, named, bound, a, VStar).isRight)

      val aVal = eval(a, named, Nil)
      assert(cType(i, named, bound, x, aVal).isRight)

      assert(cType(i, named, bound, prop, VPi(aVal, {x => VPi(aVal, {y => VPi(VEq(aVal, x, y), {_ => VStar})})})).isRight)
      val propVal = eval(prop, named, Nil)

      // the main point is here: we check that prop x x (Refl A x) is well-typed
      // propR :: {a => x => prop x x (Refl a x)}
      assert(cType(i, named, bound, propR, VPi(aVal, {x => propVal @@ x @@ x @@ VRefl(aVal, x)})).isRight)

      val xVal = eval(x, named, Nil)
      assert(cType(i, named, bound, y, aVal).isRight)
      val yVal = eval(y, named, Nil)
      assert(cType(i, named, bound, eq, VEq(aVal, xVal, yVal)).isRight)

      Right(vapp(vapp(propVal, xVal), yVal))
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def cType(ii: Int, named: NameEnv[Value], bound: NameEnv[Value], ct: CTerm, t: Value): Result[Unit] = (ct, t) match {
    case (Refl(a, z), VEq(bVal, xVal, yVal)) =>
      assert(cType(ii, named, bound, a, VStar).isRight)
      val aVal = eval(a, named, Nil)
      assert(quote0(aVal) == quote0(bVal), "type mismatch")
      assert(cType(ii, named, bound, z, aVal).isRight)
      val zVal = eval(z, named, Nil)
      assert(quote0(zVal) == quote0(xVal) && quote0(zVal) == quote0(yVal))
      Right()
    case _ =>
      super.cType(ii, named, bound, ct, t)
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
  lazy val eqTE: NameEnv[Value] =
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

  lazy val EqType = int.ieval(eqVE, int.parseIO(int.iParse, EqTypeIn).get)
  lazy val ReflType = int.ieval(eqVE, int.parseIO(int.iParse, ReflTypeIn).get)
  lazy val eqElimType = int.ieval(eqVE, int.parseIO(int.iParse, eqElimTypeIn).get)

  val eqVE: NameEnv[Value] =
    List(
      Global("Refl") -> VLam({a => VLam({x => VRefl(a, x)})}),
      Global("Eq") -> VLam(a => VLam(x => VLam(y =>VEq(a, x, y)))),
      Global("eqElim") ->
        eval(
          Lam(Lam(Lam(Lam(Lam(Lam(
            Inf(EqElim(Inf(Bound(5)), Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0))))
          )))))),
          Nil,Nil)
    )
}
