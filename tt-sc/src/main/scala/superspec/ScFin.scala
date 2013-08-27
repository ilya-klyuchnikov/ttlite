package superspec

import superspec.tt._
import mrsc.core._

trait FinDriver extends CoreDriver with FinAST with FinEval {

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NUnitElim(_, _, sel) =>
      sel match {
        case NFree(v) =>
          val c = ElimLabel(v, U, Map())
          ElimDStep(c)
        case n =>
          driveNeutral(n)
      }
    case NBoolElim(_, _, _, sel) =>
      sel match {
        case NFree(v) =>
          val c1 = ElimLabel(v, False, Map())
          val c2 = ElimLabel(v, True, Map())
          ElimDStep(c1, c2)
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
      case TEdge(n, ElimLabel(sel, U, _)) :: _ =>
        val m = VLam(VUnit, s => eval(node.conf.tp, env + (sel -> s), s :: bound))
        val f = fold(n, env, bound, recM)
        unitElim(m, f, env(sel))
      case TEdge(n1, ElimLabel(sel, False, _)) :: TEdge(n2, ElimLabel(_, True, _)) :: Nil =>
        val m = VLam(VBool, s => eval(node.conf.tp, env + (sel -> s), s :: bound))
        val f1 = fold(n1, env, bound, recM)
        val f2 = fold(n2, env, bound, recM)
        boolElim(m, f1, f2, env(sel))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait FinProofResiduator extends FinResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(n, ElimLabel(sel, U, _)) :: _ =>
        val m =
          VLam(VUnit, n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))
        val f = proofFold(n, env, bound, recM, env2, bound2, recM2)
        unitElim(m, f, env(sel))
      case TEdge(n1, ElimLabel(sel, False, _)) :: TEdge(n2, ElimLabel(_, True, _)) :: Nil =>
        val motive =
          VLam(VBool, n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))
        val f1 = proofFold(n1, env, bound, recM, env2, bound2, recM2)
        val f2 = proofFold(n2, env, bound, recM, env2, bound2, recM2)
        boolElim(motive, f1, f2, env(sel))
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
