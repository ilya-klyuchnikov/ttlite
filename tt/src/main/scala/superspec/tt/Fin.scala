package superspec.tt

trait FinAST extends CoreAST {
  case class Fin(n: Int) extends Term
  case class FinElem(i: Int, n: Int) extends Term
  case class FinElim(n: Int, motive: Term, cases: List[Term], elem: Term) extends Term

  case class VFin(n: Int) extends Value
  case class VFinElem(i: Int, n: Int) extends Value
  case class NFinElim(n: Int, motive: Value, cases: List[Value], elem: Neutral) extends Neutral
}

trait MFin extends MCore with FinAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Fin_0")) =>
      Fin(0)
    case MVar(Global("Fin_1")) =>
      Fin(1)
    case MVar(Global("Fin_2")) =>
      Fin(2)
    case MVar(Global("finElem_1_1")) =>
      FinElem(1, 1)
    case MVar(Global("finElem_1_2")) =>
      FinElem(1, 2)
    case MVar(Global("finElem_2_2")) =>
      FinElem(2, 2)
    case MVar(Global("finElim_0")) @@ m @@ el =>
      FinElim(0, fromM(m), List(), fromM(el))
    case MVar(Global("finElim_1")) @@ m @@ c1 @@ el =>
      FinElim(1, fromM(m), List(fromM(c1)), fromM(el))
    case MVar(Global("finElim_2")) @@ m @@ c1 @@ c2 @@ el =>
      FinElim(2, fromM(m), List(fromM(c1), fromM(c2)), fromM(el))
    case _ => super.fromM(m)
  }
}

trait FinPrinter extends CorePrinter with FinAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Fin(n) =>
      print(p, ii, s"Fin_$n")
    case FinElem(i, n) =>
      print(p, ii, s"finElem_${i}_${n}")
    case FinElim(n, m, cases, elem) =>
      val t = cases.foldLeft(s"finElim_${n}" @@ m)(_ @@ _) @@ elem
      print(p, ii, t)
    case _ =>
      super.print(p, ii, t)
  }
}

trait FinEval extends CoreEval with FinAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Fin(n) =>
      VFin(n)
    case FinElem(i, n) =>
      assert(i > 0 && i <= n)
      VFinElem(i, n)
    case FinElim(0, m, List(), elem) =>
      val mVal = eval(m, named, bound)
      val elemVal = eval(elem, named, bound)
      finElim0(mVal, elemVal)
    case FinElim(1, m, List(f), elem) =>
      val mVal = eval(m, named, bound)
      val fVal = eval(f, named, bound)
      val elemVal = eval(elem, named, bound)
      finElim1(mVal, fVal, elemVal)
    case FinElim(2, m, List(f1, f2), elem) =>
      val mVal = eval(m, named, bound)
      val f1Val = eval(f1, named, bound)
      val f2Val = eval(f2, named, bound)
      val elemVal = eval(elem, named, bound)
      finElim2(mVal, f1Val, f2Val, elemVal)
    case _ =>
      super.eval(t, named, bound)
  }

  def finElim0(m: Value, elem: Value) = elem match {
    case VNeutral(n) =>
      VNeutral(NFinElim(0, m, List(), n))
  }

  def finElim1(m: Value, f: Value, elem: Value) = elem match {
    case VFinElem(1, 1) =>
      f
    case VNeutral(n) =>
      VNeutral(NFinElim(1, m, List(f), n))
  }

  def finElim2(m: Value, f1: Value, f2: Value, elem: Value) = elem match {
    case VFinElem(1, 2) =>
      f1
    case VFinElem(2, 2) =>
      f2
    case VNeutral(n) =>
      VNeutral(NFinElim(2, m, List(f1, f2), n))
  }
}

trait FinCheck extends CoreCheck with FinAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Fin(n) =>
      VStar
    case FinElem(i, n) =>
      VFin(n)
    case FinElim(n, m, cases, elem) =>
      val mVal = eval(m, named, List())
      val elemVal = eval(elem, named, List())

      val mType = iType(i, named, bound, m)
      checkEqual(i, mType, VPi(VFin(n), {_ => VStar}))

      val casesTypes = cases.map(iType(i, named, bound, _))
      casesTypes.zipWithIndex.foreach { case (tp, in) =>
        checkEqual(i, tp, mVal @@ VFinElem(in + 1, n))
      }

      mVal @@ elemVal
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Fin(n) =>
      Fin(n)
    case FinElem(i, n) =>
      FinElem(i, n)
    case FinElim(n, m, cases, elem) =>
      FinElim(n, iSubst(i, r, m), cases.map(iSubst(i, r, _)), iSubst(i, r, elem))
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait FinQuote extends CoreQuote with FinAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VFin(a) => Fin(a)
    case VFinElem(i, n) => FinElem(i, n)
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NFinElim(n, m, cases, elem) =>
      FinElim(n, quote(ii, m), cases.map(quote(ii, _)), neutralQuote(ii, elem))
    case _ => super.neutralQuote(ii, n)
  }
}

trait FinREPL2 extends CoreREPL2 with FinAST with MFin with FinPrinter with FinCheck with FinEval with FinQuote
