package superspec.tt

trait EqAST extends CoreAST {
  // Refl A x :: Eq A x x
  case class Eq(A: Term, x: Term, y: Term) extends Term
  case class Refl(A: Term, x: Term) extends Term
  // See Simon Thompson. "Type Theory & Functional Programming", pp 110,111 for a good explanation.
  case class EqElim(A: Term, prop: Term, propR: Term, x: Term, y: Term, eq: Term) extends Term
  case class VEq(A: Value, x: Value, y: Value) extends Value
  case class VRefl(A: Value, x: Value) extends Value
  case class NEqElim(A: Value, prop: Value, propR: Value, x: Value, y: Value, eq: Neutral) extends Neutral
}

trait EqPrinter extends CorePrinter with EqAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Eq(a, x, y) =>
      print(p, ii, Free(Global("Eq")) @@ a @@ x @@ y)
    case Refl(a, x) =>
      print(p, ii, Free(Global("Refl")) @@ a @@ x)
    case EqElim(a, m, mr, x, y, eq) =>
      print(p, ii, Free(Global("eqElim")) @@ a @@ m @@ mr @@ x @@ y @@ eq)
    case _ =>
      super.print(p, ii, t)
  }
}

trait EqEval extends CoreEval with EqAST with CoreQuote {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Eq(a, x, y) =>
      VEq(eval(a, named, bound), eval(x, named, bound), eval(y, named, bound))
    case Refl(a, x) =>
      VRefl(eval(a, named, bound), eval(x, named, bound))
    case EqElim(a, prop, propR, x, y, eq) =>
      eval(eq, named, bound) match {
        case r@VRefl(a, z) =>
          eval(propR, named, bound) @@ z
        case VNeutral(n) =>
          VNeutral(NEqElim(
            eval(a, named, bound),
            eval(prop, named, bound),
            eval(propR, named, bound),
            eval(x, named, bound),
            eval(y, named, bound),
            n))
      }
    case _ => super.eval(t, named, bound)
  }
}

trait EqCheck extends CoreCheck with EqAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Eq(a, x, y) =>
      val aVal = eval(a, named, Nil)

      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, Star)

      val xType = iType(i, named, bound, x)
      checkEqual(i, xType, aVal)

      val yType = iType(i, named, bound, y)
      checkEqual(i, yType, aVal)

      VStar
    case Refl(a, z) =>
      val aVal = eval(a, named, Nil)
      val zVal = eval(z, named, Nil)

      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, Star)

      val zType = iType(i, named, bound, z)
      checkEqual(i, zType, aVal)

      VEq(aVal, zVal, zVal)

    case EqElim(a, prop, propR, x, y, eq) =>
      val aVal = eval(a, named, Nil)
      val propVal = eval(prop, named, Nil)
      val xVal = eval(x, named, Nil)
      val yVal = eval(y, named, Nil)
      val eqVal = eval(y, named, Nil)

      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, Star)

      val xType = iType(i, named, bound, x)
      checkEqual(i, xType, aVal)

      val yType = iType(i, named, bound, y)
      checkEqual(i, yType, aVal)

      val propType = iType(i, named, bound, prop)
      checkEqual(i, propType, VPi(aVal, {x => VPi(aVal, {y => VPi(VEq(aVal, x, y), {_ => VStar})})}))

      // the main point is here: we check that prop x x (Refl A x) is well-typed
      // propR :: {a => x => prop x x (Refl a x)}
      val propRType = iType(i, named, bound, propR)
      checkEqual(i, propRType, VPi(aVal, {x => propVal @@ x @@ x @@ VRefl(aVal, x)}))

      val eqType = iType(i, named, bound, eq)
      checkEqual(i, eqType, VEq(aVal, xVal, yVal))

      propVal @@ xVal @@ yVal @@ eqVal
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Eq(a, x, y) =>
      Eq(iSubst(i, r, a), iSubst(i, r, x), iSubst(i, r, y))
    case Refl(a, x) =>
      Refl(iSubst(i, r, a), iSubst(i, r, x))
    case EqElim(a, m, mr, x, y, eq) =>
      EqElim(iSubst(i, r, a), iSubst(i, r, m), iSubst(i, r, mr), iSubst(i, r, x), iSubst(i, r, y), iSubst(i, r, eq))
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait EqQuote extends CoreQuote with EqAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VEq(a, x, y) =>
      Eq(quote(ii, a), quote(ii, x), quote(ii, y))
    case VRefl(a, x) =>
      Refl(quote(ii, a), quote(ii, x))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NEqElim(a, m, mr, x, y, eq) =>
      EqElim(quote(ii, a), quote(ii, m), quote(ii, mr), quote(ii, x), quote(ii, y), neutralQuote(ii, eq))
    case _ => super.neutralQuote(ii, n)
  }
}

trait EqREPL extends CoreREPL with EqAST with EqPrinter with EqCheck with EqEval with EqQuote {
  lazy val eqTE: NameEnv[Value] =
    Map(
      Global("Refl") -> ReflType,
      Global("Eq") -> EqType,
      Global("eqElim") -> eqElimType
    )

  val EqTypeIn =
    "forall (A :: *) (x :: A) (y :: A) . *"
  val ReflTypeIn =
    "forall (A :: *) (a :: A) . Eq A a a"
  val eqElimTypeIn =
    """
      |forall (A :: *) .
      |forall (prop :: forall (x :: A) . forall (y :: A) . forall (_ :: Eq A x y) . * ) .
      |forall (propR :: forall (a :: A) . prop a a (Refl A a)) .
      |forall (x :: A) .
      |forall (y :: A) .
      |forall (eq :: Eq A x y) .
      |prop x y eq
    """.stripMargin

  lazy val EqType = int.ieval(eqVE, int.parseIO(int.iParse, EqTypeIn).get)
  lazy val ReflType = int.ieval(eqVE, int.parseIO(int.iParse, ReflTypeIn).get)
  lazy val eqElimType = int.ieval(eqVE, int.parseIO(int.iParse, eqElimTypeIn).get)

  val eqVE: NameEnv[Value] =
    Map(
      Global("Refl") ->
        VLam(VStar, {a => VLam(a, {x => VRefl(a, x)})}),
      Global("Eq") ->
        VLam(VStar, a => VLam(a, x => VLam(a, y => VEq(a, x, y)))),
      Global("eqElim") ->
        VLam(VStar, a =>
          VLam( VPi(a, x => VPi(a, y => VPi(VEq(a, x, y), _ => VStar))), prop =>
            VLam(VPi(a, x => prop @@ x @@ x @@ VRefl(a, x)), propR =>
              VLam(a, x =>
                VLam(a, y =>
                  VLam(VEq(a, x, y), {eq =>
                    eval(EqElim(Bound(5), Bound(4), Bound(3), Bound(2), Bound(1), Bound(0)), eqVE,
                      List(eq, y, x, propR, prop, a))}))))))
    )
}
