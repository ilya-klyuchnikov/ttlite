package superspec

import superspec.tt._
import mrsc.core._

trait FinDriver extends CoreDriver with FinAST with FinEval {

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NFinElim(n, m, cases, sel) =>
      sel match {
        case NFree(v) =>
          val cases1 = (1 to n).toList.map(i => ElimLabel(v, FinElem(i, n), Map()))
          ElimDStep(cases1:_*)
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
      case TEdge(nodeL, ElimLabel(sel, FinElem(1, 1), _)) :: _ =>
        val motive =
          VLam(VFin(1), s => eval(node.conf.tp, env + (sel -> s), s :: bound))
        val List(f) = node.outs.map(_.node).map(fold(_, env, bound, recM))
        finElim1(motive, f, env(sel))
      case TEdge(nodeL, ElimLabel(sel, FinElem(1, 2), _)) :: _ =>
        val motive =
          VLam(VFin(2), s => eval(node.conf.tp, env + (sel -> s), s :: bound))
        val List(f1, f2) = node.outs.map(_.node).map(fold(_, env, bound, recM))
        finElim2(motive, f1, f2, env(sel))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait FinProofResiduator extends FinResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, ElimLabel(sel, FinElem(1, 1), _)) :: _ =>
        val motive =
          VLam(VFin(1), n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))
        val List(f) =
          node.outs.map(_.node).map(proofFold(_, env, bound, recM, env2, bound2, recM2))
        finElim1(motive, f, env(sel))
      case TEdge(nodeL, ElimLabel(sel, FinElem(1, 2), _)) :: _ =>
        val motive =
          VLam(VFin(2), n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))
        val List(f1, f2) =
          node.outs.map(_.node).map(proofFold(_, env, bound, recM, env2, bound2, recM2))
        finElim2(motive, f1, f2, env(sel))
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
