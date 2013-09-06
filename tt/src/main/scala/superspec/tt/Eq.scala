package superspec.tt

trait EqAST extends CoreAST {
  case class Eq(A: Term, x: Term, y: Term) extends Term
  case class Refl(A: Term, x: Term) extends Term
  case class EqElim(et: Term, prop: Term, propR: Term, eq: Term) extends Term

  case class VEq(A: Value, x: Value, y: Value) extends Value
  case class VRefl(A: Value, x: Value) extends Value
  case class NEqElim(et: Value, prop: Value, propR: Value, eq: Neutral) extends Neutral
}

trait EqMetaSyntax extends CoreMetaSyntax with EqAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Eq")) @@ a @@ x @@ y =>
      Eq(fromM(a), fromM(x), fromM(y))
    case MVar(Global("Refl")) @@ a @@ x =>
      Refl(fromM(a), fromM(x))
    case MVar(Global("elim")) @@ (MVar(Global("Eq")) @@ a @@ x @@ y) @@ p @@ pr @@ eq =>
      EqElim(Eq(fromM(a), fromM(x), fromM(y)), fromM(p), fromM(pr), fromM(eq))
    case _ => super.fromM(m)
  }
}

trait EqPrinter extends FunPrinter with EqAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Eq(a, x, y) =>
      print(p, ii, 'Eq @@ a @@ x @@ y)
    case Refl(a, x) =>
      print(p, ii, 'Refl @@ a @@ x)
    case EqElim(et, m, mr, eq) =>
      print(p, ii, 'elim @@ et @@ m @@ mr @@ eq)
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
    case EqElim(et, prop, propR, eq) =>
      val etVal = eval(et, named, bound)
      val propVal = eval(prop, named, bound)
      val propRVal = eval(propR, named, bound)
      val eqVal = eval(eq, named, bound)
      eqElim(etVal, propVal, propRVal, eqVal)
    case _ => super.eval(t, named, bound)
  }

  def eqElim(etVal: Value, propVal: Value, propRVal: Value, eqVal: Value) = eqVal match {
    case r@VRefl(a, z) =>
      propRVal @@ z
    case VNeutral(n) =>
      VNeutral(NEqElim(etVal, propVal, propRVal, n))
  }
}

trait EqCheck extends FunCheck with EqAST {
  override def iType(i: Int, ctx: Context[Value], t: Term): Value = t match {
    case Eq(a, x, y) =>
      val aVal = eval(a, ctx.vals, Nil)

      val aType = iType(i, ctx, a)
      val m = checkUniverse(i, aType)

      val xType = iType(i, ctx, x)
      checkEqual(i, xType, aVal)

      val yType = iType(i, ctx, y)
      checkEqual(i, yType, aVal)

      VUniverse(m)
    case Refl(a, z) =>
      val aVal = eval(a, ctx.vals, Nil)
      val zVal = eval(z, ctx.vals, Nil)

      val aType = iType(i, ctx, a)
      checkUniverse(i, aType)

      val zType = iType(i, ctx, z)
      checkEqual(i, zType, aVal)

      VEq(aVal, zVal, zVal)

    case EqElim(et, prop, propR, eq) =>
      val eType = iType(i, ctx, et)
      checkUniverse(i, eType)

      val VEq(aVal, xVal, yVal) = eval(et, ctx.vals, Nil)

      val propVal = eval(prop, ctx.vals, Nil)
      val eqVal = eval(eq, ctx.vals, Nil)

      val propType = iType(i, ctx, prop)
      checkEqual(i, propType, VPi(aVal, {x => VPi(aVal, {y => VPi(VEq(aVal, x, y), {_ => VUniverse(-1)})})}))

      // the main point is here: we check that prop x x (Refl A x) is well-typed
      // propR :: {a => x => prop x x (Refl a x)}
      val propRType = iType(i, ctx, propR)
      checkEqual(i, propRType, VPi(aVal, {x => propVal @@ x @@ x @@ VRefl(aVal, x)}))

      val eqType = iType(i, ctx, eq)
      checkEqual(i, eqType, VEq(aVal, xVal, yVal))

      propVal @@ xVal @@ yVal @@ eqVal
    case _ =>
      super.iType(i, ctx, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Eq(a, x, y) =>
      Eq(iSubst(i, r, a), iSubst(i, r, x), iSubst(i, r, y))
    case Refl(a, x) =>
      Refl(iSubst(i, r, a), iSubst(i, r, x))
    case EqElim(et, m, mr, eq) =>
      EqElim(iSubst(i, r, et), iSubst(i, r, m), iSubst(i, r, mr), iSubst(i, r, eq))
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
    case NEqElim(et, m, mr, eq) =>
      EqElim(quote(ii, et), quote(ii, m), quote(ii, mr), neutralQuote(ii, eq))
    case _ => super.neutralQuote(ii, n)
  }
}

trait EqREPL extends CoreREPL with EqAST with EqMetaSyntax with EqPrinter with EqCheck with EqEval with EqQuote
