package superspec

import superspec.tt._
import mrsc.core._

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
        cases.foldLeft(s"finElim_$n" @@ motive)(_ @@ _) @@ env(sel)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait FinProofResiduator extends FinResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, CaseBranchLabel(sel, ElimBranch(FinElem(_, n), _))) :: _ =>
        val motive =
          VLam(VFin(n), n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))
        val cases =
          node.outs.map(_.node).map(proofFold(_, env, bound, recM, env2, bound2, recM2))
        cases.foldLeft(s"finElim_$n" @@ motive)(_ @@ _) @@ env(sel)
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
