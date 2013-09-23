package ttlite.core

trait IdAST extends CoreAST {
  case class Id(A: Term, x: Term, y: Term) extends Term
  case class Refl(A: Term, x: Term) extends Term
  case class IdElim(et: Term, prop: Term, propR: Term, eq: Term) extends Term

  case class VId(A: Value, x: Value, y: Value) extends Value
  case class VRefl(A: Value, x: Value) extends Value
  case class NIdElim(et: Value, prop: Value, propR: Value, eq: Neutral) extends Neutral
}

trait IdMetaSyntax extends CoreMetaSyntax with IdAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Id")) @@ a @@ x @@ y =>
      Id(fromM(a), fromM(x), fromM(y))
    case MVar(Global("Refl")) @@ a @@ x =>
      Refl(fromM(a), fromM(x))
    case MVar(Global("elim")) @@ (MVar(Global("Id")) @@ a @@ x @@ y) @@ p @@ pr @@ eq =>
      IdElim(Id(fromM(a), fromM(x), fromM(y)), fromM(p), fromM(pr), fromM(eq))
    case _ => super.fromM(m)
  }
}

trait IdPrinter extends FunPrinter with IdAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Id(a, x, y) =>
      print(p, ii, 'Id @@ a @@ x @@ y)
    case Refl(a, x) =>
      print(p, ii, 'Refl @@ a @@ x)
    case IdElim(et, m, mr, eq) =>
      print(p, ii, 'elim @@ et @@ m @@ mr @@ eq)
    case _ =>
      super.print(p, ii, t)
  }
}

trait IdEval extends FunEval with IdAST with CoreQuote {
  override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Id(a, x, y) =>
      VId(eval(a, ctx, bound), eval(x, ctx, bound), eval(y, ctx, bound))
    case Refl(a, x) =>
      VRefl(eval(a, ctx, bound), eval(x, ctx, bound))
    case IdElim(et, prop, propR, eq) =>
      val etVal = eval(et, ctx, bound)
      val propVal = eval(prop, ctx, bound)
      val propRVal = eval(propR, ctx, bound)
      val eqVal = eval(eq, ctx, bound)
      idElim(etVal, propVal, propRVal, eqVal)
    case _ => super.eval(t, ctx, bound)
  }

  def idElim(etVal: Value, propVal: Value, propRVal: Value, eqVal: Value) = eqVal match {
    case r@VRefl(a, z) =>
      propRVal @@ z
    case VNeutral(n) =>
      VNeutral(NIdElim(etVal, propVal, propRVal, n))
  }
}

trait IdCheck extends FunCheck with IdAST {
  override def iType(i: Int, ctx: Context[Value], t: Term): Value = t match {
    case Id(a, x, y) =>
      val aVal = eval(a, ctx, Nil)

      val aType = iType(i, ctx, a)
      val m = checkUniverse(i, aType)

      val xType = iType(i, ctx, x)
      checkEqual(i, xType, aVal)

      val yType = iType(i, ctx, y)
      checkEqual(i, yType, aVal)

      VUniverse(m)
    case Refl(a, z) =>
      val aVal = eval(a, ctx, Nil)
      val zVal = eval(z, ctx, Nil)

      val aType = iType(i, ctx, a)
      checkUniverse(i, aType)

      val zType = iType(i, ctx, z)
      checkEqual(i, zType, aVal)

      VId(aVal, zVal, zVal)

    case IdElim(et, prop, propR, eq) =>
      val eType = iType(i, ctx, et)
      checkUniverse(i, eType)

      val VId(aVal, xVal, yVal) = eval(et, ctx, Nil)

      val propVal = eval(prop, ctx, Nil)
      val eqVal = eval(eq, ctx, Nil)

      val propType = iType(i, ctx, prop)
      checkEqual(i, propType, VPi(aVal, {x => VPi(aVal, {y => VPi(VId(aVal, x, y), {_ => VUniverse(-1)})})}))

      // the main point is here: we check that prop x x (Refl A x) is well-typed
      // propR :: {a => x => prop x x (Refl a x)}
      val propRType = iType(i, ctx, propR)
      checkEqual(i, propRType, VPi(aVal, {x => propVal @@ x @@ x @@ VRefl(aVal, x)}))

      val eqType = iType(i, ctx, eq)
      checkEqual(i, eqType, VId(aVal, xVal, yVal))

      propVal @@ xVal @@ yVal @@ eqVal
    case _ =>
      super.iType(i, ctx, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Id(a, x, y) =>
      Id(iSubst(i, r, a), iSubst(i, r, x), iSubst(i, r, y))
    case Refl(a, x) =>
      Refl(iSubst(i, r, a), iSubst(i, r, x))
    case IdElim(et, m, mr, eq) =>
      IdElim(iSubst(i, r, et), iSubst(i, r, m), iSubst(i, r, mr), iSubst(i, r, eq))
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait IdQuote extends CoreQuote with IdAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VId(a, x, y) =>
      Id(quote(ii, a), quote(ii, x), quote(ii, y))
    case VRefl(a, x) =>
      Refl(quote(ii, a), quote(ii, x))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NIdElim(et, m, mr, eq) =>
      IdElim(quote(ii, et), quote(ii, m), quote(ii, mr), neutralQuote(ii, eq))
    case _ => super.neutralQuote(ii, n)
  }
}

trait IdREPL extends CoreREPL with IdAST with IdMetaSyntax with IdPrinter with IdCheck with IdEval with IdQuote