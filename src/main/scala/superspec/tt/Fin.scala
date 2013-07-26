package superspec.tt

import mrsc.core._
import superspec._

trait FinAST extends CoreAST {
  case class Fin(n: Int) extends Term
  case class FinElem(i: Int, n: Int) extends Term
  case class FinElim(n: Int, motive: Term, cases: List[Term], elem: Term) extends Term

  case class VFin(n: Int) extends Value
  case class VFinElem(i: Int, n: Int) extends Value
  case class NFinElim(n: Int, motive: Value, cases: List[Value], elem: Neutral) extends Neutral
}

trait FinPrinter extends CorePrinter with FinAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Fin(n) =>
      print(p, ii, Free(Global(s"Fin_$n")))
    case FinElem(i, n) =>
      print(p, ii, Free(Global(s"finElem_${i}_${n}")))
    case FinElim(n, m, cases, elem) =>
      val t = cases.foldLeft(Free(Global(s"finElim_${n}")) @@ m)(_ @@ _) @@ elem
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
    case FinElim(n, m, cases, elem) =>
      val elemVal = eval(elem, named, bound)
      val casesVal = cases.map(eval(_, named, bound))
      elemVal match {
        case VFinElem(i, `n`) =>
          casesVal(i - 1)
        case VNeutral(ntr) =>
          VNeutral(NFinElim(n, eval(m, named, bound), casesVal, ntr))
      }
    case _ =>
      super.eval(t, named, bound)
  }
}

trait FinDriver extends CoreDriver with FinAST {

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NFinElim(n, m, cases, sel) =>
      sel match {
        case NFree(v) =>
          val cases1 = (1 to n).toList.map(i => ElimBranch(FinElem(i, n), Map()))
          ElimDStep(v, cases1)
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

}

trait FinResiduator extends BaseResiduator with FinDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, CaseBranchLabel(sel, ElimBranch(FinElem(_, n), _))) :: _ =>
        val motive =
          VLam(VFin(n), s => eval(node.conf.tp, env + (sel -> s), s :: bound))
        val cases = node.outs.map(_.node).map(fold(_, env, bound, recM))
        cases.foldLeft(VNeutral(NFree(Global(s"finElim_${n}"))) @@ motive)(_ @@ _) @@ env(sel)
      case _ =>
        super.fold(node, env, bound, recM)
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
      casesTypes.zipWithIndex.foreach { case (tp, i) =>
        checkEqual(i, tp, VPi(VFinElem(i + 1, n), {_ => VStar}))
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

trait FinREPL extends CoreREPL with FinAST with FinPrinter with FinCheck with FinEval with FinQuote {
  private lazy val finsTE: NameEnv[Value] =
    (0 to 10).toList.map(n => Global(s"Fin_${n}") -> VStar).toMap
  private lazy val finElemsTE: NameEnv[Value] =
    (for {n <- (0 to 10); i <- (1 to n)} yield (Global(s"finElem_${i}_${n}") -> VFin(n))).toMap
  private lazy val finElimsTE: NameEnv[Value] =
    (0 to 10).toList.map(n => Global(s"finElim_${n}") -> finElimType(n)).toMap

  lazy val finsVE: NameEnv[Value] =
    (0 to 10).toList.map(n => Global(s"Fin_${n}") -> VFin(n)).toMap
  private lazy val finElemsVE: NameEnv[Value] =
    (for {n <- (0 to 10); i <- (1 to n)} yield (Global(s"finElem_${i}_${n}") -> VFinElem(i, n))).toMap
  private lazy val finElimsVE: NameEnv[Value] =
    (0 to 10).toList.map(n => Global(s"finElim_${n}") -> finElim(n)).toMap

  def finElimType(n: Int): Value =
    VPi(VPi(VFin(n), _ => VStar), m =>
      (1 to n).foldRight(VPi(VFin(n), elem => m @@ elem))((i, pi) => VPi(m @@ VFinElem(i, n), e => pi)))

  def finElim(n: Int) =
    VLam(VPi(VFin(n), _ => VStar), m => {
      var args: List[Value] = List(m)
      var elem: Value = null
      lazy val body =
        eval(FinElim(n, Bound(n + 1), (1 to n).toList.reverse.map(Bound), Bound(0)), Map(), elem :: args)
      val lam0: Value = VLam(VFin(n), e => {elem = e; body})
      val tt: Value = (1 to n).foldRight(lam0)((i, lam) => VLam(m @@ VFinElem(i, n), arg => {args = arg :: args; lam}))
      tt
    }
    )

  lazy val finTE = finsTE ++ finElemsTE ++ finElimsTE
  lazy val finVE = finsVE ++ finElemsVE ++ finElimsVE

}