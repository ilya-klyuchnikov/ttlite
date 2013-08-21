package superspec.tt

trait EqAST extends CoreAST {
  case class Eq(A: Term, x: Term, y: Term) extends Term
  case class Refl(A: Term, x: Term) extends Term
  // See Simon Thompson. "Type Theory & Functional Programming", pp 110,111 for a good explanation.
  case class EqElim(A: Term, prop: Term, propR: Term, x: Term, y: Term, eq: Term) extends Term

  case class VEq(A: Value, x: Value, y: Value) extends Value
  case class VRefl(A: Value, x: Value) extends Value
  case class NEqElim(A: Value, prop: Value, propR: Value, x: Value, y: Value, eq: Neutral) extends Neutral
}

trait MEq extends MCore with EqAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Eq")) @@ a @@ x @@ y =>
      Eq(fromM(a), fromM(x), fromM(y))
    case MVar(Global("Refl")) @@ a @@ x =>
      Refl(fromM(a), fromM(x))
    case MVar(Global("eqElim")) @@ a @@ p @@ pr @@ x @@ y @@ eq =>
      EqElim(fromM(a), fromM(p), fromM(pr), fromM(x), fromM(y), fromM(eq))
    case _ => super.fromM(m)
  }
}

trait EqPrinter extends FunPrinter with EqAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Eq(a, x, y) =>
      print(p, ii, 'Eq @@ a @@ x @@ y)
    case Refl(a, x) =>
      print(p, ii, 'Refl @@ a @@ x)
    case EqElim(a, m, mr, x, y, eq) =>
      print(p, ii, 'eqElim @@ a @@ m @@ mr @@ x @@ y @@ eq)
    case _ =>
      super.print(p, ii, t)
  }
}

trait EqEval extends FunEval with EqAST with CoreQuote {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Eq(a, x, y) =>
      VEq(eval(a, named, bound), eval(x, named, bound), eval(y, named, bound))
    case Refl(a, x) =>
      VRefl(eval(a, named, bound), eval(x, named, bound))
    case EqElim(a, prop, propR, x, y, eq) =>
      val aVal = eval(a, named, bound)
      val propVal = eval(prop, named, bound)
      val propRVal = eval(propR, named, bound)
      val xVal = eval(x, named, bound)
      val yVal = eval(y, named, bound)
      val eqVal = eval(eq, named, bound)
      eqElim(aVal, propVal, propRVal, xVal, yVal, eqVal)
    case _ => super.eval(t, named, bound)
  }

  def eqElim(aVal: Value, propVal: Value, propRVal: Value, xVal: Value, yVal: Value, eqVal: Value) = eqVal match {
    case r@VRefl(a, z) =>
      propRVal @@ z
    case VNeutral(n) =>
      VNeutral(NEqElim(aVal, propVal, propRVal, xVal, yVal, n))
  }
}

trait EqCheck extends FunCheck with EqAST {
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

trait EqREPL2 extends CoreREPL2 with EqAST with MEq with EqPrinter with EqCheck with EqEval with EqQuote
