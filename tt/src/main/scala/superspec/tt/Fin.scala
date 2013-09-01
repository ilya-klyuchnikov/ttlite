package superspec.tt

trait FinAST extends CoreAST {

  // Void, Empty Type
  case object Void extends Term
  case class VoidElim(m: Term, elem: Term) extends Term
  case object VVoid extends Value
  case class NVoidElim(m: Value, elem: Neutral) extends Neutral

  // Unit Type
  case object Unit extends Term
  case object U extends Term
  case class UnitElim(m: Term, f: Term, elem: Term) extends Term

  case object VUnit extends Value
  case object VU extends Value
  case class NUnitElim(m: Value, v: Value, elem: Neutral) extends Neutral

  // Bool type
  // this is just syntactic sugar - really it can be implemented via sum
  case object Bool extends Term
  case object False extends Term
  case object True extends Term
  case class BoolElim(m: Term, v1: Term, v2: Term, elem: Term) extends Term

  case object VBool extends Value
  case object VFalse extends Value
  case object VTrue extends Value
  case class NBoolElim(m: Value, v1: Value, v2: Value, elem: Neutral) extends Neutral
}

trait FinMetaSyntax extends CoreMetaSyntax with FinAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Void")) => Void
    case MVar(Global("Unit")) => Unit
    case MVar(Global("Bool")) => Bool
    case MVar(Global("U")) => U
    case MVar(Global("false")) => False
    case MVar(Global("true")) => True
    case MVar(Global("elim")) @@ MVar(Global("Void")) @@ m @@ el =>
      VoidElim(fromM(m), fromM(el))
    case MVar(Global("elim")) @@ MVar(Global("Unit")) @@ m @@ v @@ el =>
      UnitElim(fromM(m), fromM(v), fromM(el))
    case MVar(Global("elim")) @@ MVar(Global("Bool")) @@ m @@ c1 @@ c2 @@ el =>
      BoolElim(fromM(m), fromM(c1), fromM(c2), fromM(el))
    case _ => super.fromM(m)
  }
}

trait FinPrinter extends FunPrinter with FinAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Void =>
      print(p, ii, "Void")
    case Unit =>
      print(p, ii, "Unit")
    case Bool =>
      print(p, ii, "Bool")
    case U =>
      print(p, ii, "U")
    case False =>
      print(p, ii, "false")
    case True =>
      print(p, ii, "true")
    case VoidElim(m, elem) =>
      print(p, ii, 'elim @@ Void @@ elem)
    case UnitElim(m, v, elem) =>
      print(p, ii, 'elim @@ Unit @@ m @@ v @@ elem)
    case BoolElim(m, v1, v2, elem) =>
      print(p, ii, 'elim @@ Bool @@ m @@ v1 @@ v2 @@ elem)
    case _ =>
      super.print(p, ii, t)
  }
}

trait FinEval extends FunEval with FinAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Void =>
      VVoid
    case Unit =>
      VUnit
    case Bool =>
      VBool
    case U =>
      VU
    case False =>
      VFalse
    case True =>
      VTrue
    case VoidElim(m, elem) =>
      val mVal = eval(m, named, bound)
      val elemVal = eval(elem, named, bound)
      voidElim(mVal, elemVal)
    case UnitElim(m, f, elem) =>
      val mVal = eval(m, named, bound)
      val fVal = eval(f, named, bound)
      val elemVal = eval(elem, named, bound)
      unitElim(mVal, fVal, elemVal)
    case BoolElim(m, f1, f2, elem) =>
      val mVal = eval(m, named, bound)
      val f1Val = eval(f1, named, bound)
      val f2Val = eval(f2, named, bound)
      val elemVal = eval(elem, named, bound)
      boolElim(mVal, f1Val, f2Val, elemVal)
    case _ =>
      super.eval(t, named, bound)
  }

  def voidElim(m: Value, elem: Value) = elem match {
    case VNeutral(n) =>
      VNeutral(NVoidElim(m, n))
  }

  def unitElim(m: Value, f: Value, elem: Value) = elem match {
    case VU =>
      f
    case VNeutral(n) =>
      VNeutral(NUnitElim(m, f, n))
  }

  def boolElim(m: Value, f1: Value, f2: Value, elem: Value) = elem match {
    case VFalse =>
      f1
    case VTrue =>
      f2
    case VNeutral(n) =>
      VNeutral(NBoolElim(m, f1, f2, n))
  }
}

trait FinCheck extends FunCheck with FinAST {
  override def iType(i: Int, ctx: Context[Value], t: Term): Value = t match {
    case Void | Unit | Bool =>
      VUniverse(0)
    case U =>
      VUnit
    case False | True =>
      VBool
    case VoidElim(m, elem) =>
      val mType = iType(i, ctx, m)
      checkEqual(i, mType, VPi(VVoid, {_ => VUniverse(-1)}))

      val mVal = eval(m, ctx.vals, List())
      val elemVal = eval(elem, ctx.vals, List())

      mVal @@ elemVal
    case UnitElim(m, v, elem) =>
      val mType = iType(i, ctx, m)
      checkEqual(i, mType, VPi(VUnit, {_ => VUniverse(-1)}))

      val mVal = eval(m, ctx.vals, List())
      val elemVal = eval(elem, ctx.vals, List())

      val vType = iType(i, ctx, v)
      checkEqual(i, vType, mVal @@ VU)

      mVal @@ elemVal
    case BoolElim(m, v1, v2, elem) =>
      val mType = iType(i, ctx, m)
      checkEqual(i, mType, VPi(VBool, {_ => VUniverse(-1)}))

      val mVal = eval(m, ctx.vals, List())
      val elemVal = eval(elem, ctx.vals, List())

      val v1Type = iType(i, ctx, v1)
      checkEqual(i, v1Type, mVal @@ VFalse)

      val v2Type = iType(i, ctx, v2)
      checkEqual(i, v2Type, mVal @@ VTrue)

      mVal @@ elemVal
    case _ =>
      super.iType(i, ctx, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Void => Void
    case Unit => Unit
    case Bool => Bool
    case U => U
    case False => False
    case True => True
    case VoidElim(m, elem) =>
      VoidElim(iSubst(i, r, m), iSubst(i, r, elem))
    case UnitElim(m, v, elem) =>
      UnitElim(iSubst(i, r, m), iSubst(i, r, v), iSubst(i, r, elem))
    case BoolElim(m, v1, v2, elem) =>
      BoolElim(iSubst(i, r, m), iSubst(i, r, v1), iSubst(i, r, v2), iSubst(i, r, elem))
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait FinQuote extends CoreQuote with FinAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VVoid => Void
    case VUnit => Unit
    case VBool => Bool
    case VU => U
    case VFalse => False
    case VTrue => True
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NVoidElim(m, elem) =>
      VoidElim(quote(ii, m), neutralQuote(ii, elem))
    case NUnitElim(m, v, elem) =>
      UnitElim(quote(ii, m), quote(ii, v), neutralQuote(ii, elem))
    case NBoolElim(m, v1, v2, elem) =>
      BoolElim(quote(ii, m), quote(ii, v1), quote(ii, v2), neutralQuote(ii, elem))
    case _ => super.neutralQuote(ii, n)
  }
}

trait FinREPL extends CoreREPL with FinAST with FinMetaSyntax with FinPrinter with FinCheck with FinEval with FinQuote
