package ttlite.core

import ttlite.common._

trait FinAST extends CoreAST {

  // ⊥, Void, empty type
  case object Falsity extends Term
  case class FalsityElim(m: Term, elem: Term) extends Term
  case object VFalsity extends Value
  case class NFalsityElim(m: Value, elem: Neutral) extends Neutral

  // ⊤, Truth Type, unit type, single-element type
  case object Truth extends Term
  case object Triv extends Term
  case class TruthElim(m: Term, f: Term, elem: Term) extends Term

  case object VTruth extends Value
  case object VTriv extends Value
  case class NTruthElim(m: Value, v: Value, elem: Neutral) extends Neutral

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
  override def translate(m: MTerm): Term = m match {
    case MVar(Global("Falsity")) => Falsity
    case MVar(Global("Truth")) => Truth
    case MVar(Global("Bool")) => Bool
    case MVar(Global("Triv")) => Triv
    case MVar(Global("False")) => False
    case MVar(Global("True")) => True
    case MVar(Global("elim")) @@ MVar(Global("Falsity")) @@ m @@ el =>
      FalsityElim(translate(m), translate(el))
    case MVar(Global("elim")) @@ MVar(Global("Truth")) @@ m @@ v @@ el =>
      TruthElim(translate(m), translate(v), translate(el))
    case MVar(Global("elim")) @@ MVar(Global("Bool")) @@ m @@ c1 @@ c2 @@ el =>
      BoolElim(translate(m), translate(c1), translate(c2), translate(el))
    case _ => super.translate(m)
  }
}

trait FinPrinter extends FunPrinter with FinAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Falsity =>
      print(p, ii, "Falsity")
    case Truth =>
      print(p, ii, "Truth")
    case Bool =>
      print(p, ii, "Bool")
    case Triv =>
      print(p, ii, "Triv")
    case False =>
      print(p, ii, "False")
    case True =>
      print(p, ii, "True")
    case FalsityElim(m, elem) =>
      print(p, ii, 'elim @@ Falsity @@ m @@ elem)
    case TruthElim(m, v, elem) =>
      print(p, ii, 'elim @@ Truth @@ m @@ v @@ elem)
    case BoolElim(m, v1, v2, elem) =>
      print(p, ii, 'elim @@ Bool @@ m @@ v1 @@ v2 @@ elem)
    case _ =>
      super.print(p, ii, t)
  }
}

trait FinPrinterAgda extends FunPrinterAgda with FinAST {
  override def printA(p: Int, ii: Int, t: Term): Doc = t match {
    case Falsity =>
      printA(p, ii, "Falsity")
    case Truth =>
      printA(p, ii, "Truth")
    case Bool =>
      printA(p, ii, "Bool")
    case Triv =>
      printA(p, ii, "triv")
    case False =>
      printA(p, ii, "false")
    case True =>
      printA(p, ii, "true")
    case FalsityElim(m, elem) =>
      printA(p, ii, 'elimFalsity @@ m @@ elem)
    case TruthElim(m, v, elem) =>
      printA(p, ii, 'elimTruth @@ m @@ v @@ elem)
    case BoolElim(m, v1, v2, elem) =>
      printA(p, ii, 'elimBool @@ m @@ v1 @@ v2 @@ elem)
    case _ =>
      super.printA(p, ii, t)
  }
}

trait FinPrinterIdris extends FunPrinterIdris with FinAST {
  override def printI(p: Int, ii: Int, t: Term): Doc = t match {
    case Falsity =>
      printI(p, ii, "Falsity")
    case Truth =>
      printI(p, ii, "Truth")
    case Bool =>
      printI(p, ii, "Bool")
    case Triv =>
      printI(p, ii, "triv")
    case False =>
      printI(p, ii, "false")
    case True =>
      printI(p, ii, "true")
    case FalsityElim(m, elem) =>
      printI(p, ii, 'elimFalsity @@ m @@ elem)
    case TruthElim(m, v, elem) =>
      printI(p, ii, 'elimTruth @@ m @@ v @@ elem)
    case BoolElim(m, v1, v2, elem) =>
      printI(p, ii, 'elimBool @@ m @@ v1 @@ v2 @@ elem)
    case _ =>
      super.printI(p, ii, t)
  }
}

trait FinEval extends FunEval with FinAST {
  override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Falsity =>
      VFalsity
    case Truth =>
      VTruth
    case Bool =>
      VBool
    case Triv =>
      VTriv
    case False =>
      VFalse
    case True =>
      VTrue
    case FalsityElim(m, elem) =>
      val mVal = eval(m, ctx, bound)
      val elemVal = eval(elem, ctx, bound)
      voidElim(mVal, elemVal)
    case TruthElim(m, f, elem) =>
      val mVal = eval(m, ctx, bound)
      val fVal = eval(f, ctx, bound)
      val elemVal = eval(elem, ctx, bound)
      unitElim(mVal, fVal, elemVal)
    case BoolElim(m, f1, f2, elem) =>
      val mVal = eval(m, ctx, bound)
      val f1Val = eval(f1, ctx, bound)
      val f2Val = eval(f2, ctx, bound)
      val elemVal = eval(elem, ctx, bound)
      boolElim(mVal, f1Val, f2Val, elemVal)
    case _ =>
      super.eval(t, ctx, bound)
  }

  def voidElim(m: Value, elem: Value) = elem match {
    case VNeutral(n) =>
      VNeutral(NFalsityElim(m, n))
  }

  def unitElim(m: Value, f: Value, elem: Value) = elem match {
    case VTriv =>
      f
    case VNeutral(n) =>
      VNeutral(NTruthElim(m, f, n))
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
  override def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value = t match {
    case Falsity | Truth | Bool =>
      VUniverse(0)
    case Triv =>
      VTruth
    case False | True =>
      VBool
    case FalsityElim(m, elem) =>
      val mType = iType(i, path/(3, 4), ctx, m)
      checkEqual(i, mType, VPi(VFalsity, {_ => VUniverse(-1)}), path/(3, 4))

      val elemType = iType(i, path/(4, 4), ctx, elem)
      checkEqual(i, elemType, Falsity, path/(4, 4))

      val mVal = eval(m, ctx, List())
      val elemVal = eval(elem, ctx, List())

      mVal @@ elemVal
    case TruthElim(m, v, elem) =>
      val mType = iType(i, path/(3, 5), ctx, m)
      checkEqual(i, mType, VPi(VTruth, {_ => VUniverse(-1)}), path/(3, 5))
      val mVal = eval(m, ctx, List())

      val vType = iType(i, path/(4, 5), ctx, v)
      checkEqual(i, vType, mVal @@ VTriv, path/(4, 5))

      val elemType = iType(i, path/(5, 5), ctx, elem)
      checkEqual(i, elemType, Truth, path/(5, 5))
      val elemVal = eval(elem, ctx, List())

      mVal @@ elemVal
    case BoolElim(m, f1, f2, elem) =>
      val mType = iType(i, path/(3, 6), ctx, m)
      checkEqual(i, mType, VPi(VBool, {_ => VUniverse(-1)}), path/(3, 6))
      val mVal = eval(m, ctx, List())

      val f1Type = iType(i, path/(4, 6), ctx, f1)
      checkEqual(i, f1Type, mVal @@ VFalse, path/(4, 6))

      val f2Type = iType(i, path/(5, 6), ctx, f2)
      checkEqual(i, f2Type, mVal @@ VTrue, path/(5, 6))

      val elemType = iType(i, path/(6, 6), ctx, elem)
      checkEqual(i, elemType, Bool, path/(6, 6))
      val elemVal = eval(elem, ctx, List())

      mVal @@ elemVal
    case _ =>
      super.iType(i, path, ctx, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Falsity => Falsity
    case Truth => Truth
    case Bool => Bool
    case Triv => Triv
    case False => False
    case True => True
    case FalsityElim(m, elem) =>
      FalsityElim(iSubst(i, r, m), iSubst(i, r, elem))
    case TruthElim(m, v, elem) =>
      TruthElim(iSubst(i, r, m), iSubst(i, r, v), iSubst(i, r, elem))
    case BoolElim(m, v1, v2, elem) =>
      BoolElim(iSubst(i, r, m), iSubst(i, r, v1), iSubst(i, r, v2), iSubst(i, r, elem))
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait FinQuote extends CoreQuote with FinAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VFalsity => Falsity
    case VTruth => Truth
    case VBool => Bool
    case VTriv => Triv
    case VFalse => False
    case VTrue => True
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NFalsityElim(m, elem) =>
      FalsityElim(quote(ii, m), neutralQuote(ii, elem))
    case NTruthElim(m, v, elem) =>
      TruthElim(quote(ii, m), quote(ii, v), neutralQuote(ii, elem))
    case NBoolElim(m, v1, v2, elem) =>
      BoolElim(quote(ii, m), quote(ii, v1), quote(ii, v2), neutralQuote(ii, elem))
    case _ => super.neutralQuote(ii, n)
  }
}

trait FinREPL
  extends CoreREPL
  with FinAST
  with FinMetaSyntax
  with FinPrinter
  with FinPrinterAgda
  with FinPrinterIdris
  with FinCheck
  with FinEval
  with FinQuote
