package ttlite.sc

import mrsc.core._
import ttlite.common._
import ttlite.core._

trait FinDriver extends Driver with FinAST with FinEval {

  override def nv(t: Neutral): Option[Name] = t match {
    case NTruthElim(_, _, NFree(n)) => Some(n)
    case NTruthElim(_, _, n) => nv(n)
    case NBoolElim(_, _, _, NFree(n)) => Some(n)
    case NBoolElim(_, _, _, n) => nv(n)
    case _ => super.nv(t)
  }

  override def elimVar(n: Name, nt: Value): DriveStep = nt match {
    case VTruth =>
      val c = ElimLabel(n, Triv, Map(), Map())
      ElimDStep(c)
    case VBool =>
      val c1 = ElimLabel(n, False, Map(), Map())
      val c2 = ElimLabel(n, True, Map(), Map())
      ElimDStep(c1, c2)
    case _ =>
      super.elimVar(n, nt)
  }

}

trait FinResiduator extends Residuator with FinDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(n, ElimLabel(sel, Triv, _, _)) :: _ =>
        val m = VLam(VTruth, s => eval(node.conf.tp, env + (sel -> s), s :: bound))
        val f = fold(n, env, bound, recM)
        unitElim(m, f, env(sel))
      case TEdge(n1, ElimLabel(sel, False, _, _)) :: TEdge(n2, ElimLabel(_, True, _, _)) :: Nil =>
        val m = VLam(VBool, s => eval(node.conf.tp, env + (sel -> s), s :: bound))
        val f1 = fold(n1, env, bound, recM)
        val f2 = fold(n2, env, bound, recM)
        boolElim(m, f1, f2, env(sel))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait FinProofResiduator extends FinResiduator with ProofResiduator { self: FunAST with IdAST =>
  override def proofFold(node: N,
                         env1: NameEnv[Value], bound1: Env, recM1: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(n, ElimLabel(sel, Triv, _, _)) :: _ =>
        val m =
          VLam(VTruth, n =>
            VId(
              eval(node.conf.tp, env1 + (sel -> n), n :: bound1),
              eval(node.conf.term, env1 + (sel -> n), n :: bound1),
              fold(node, env1 + (sel -> n), n :: bound1, recM1)))
        val f = proofFold(n, env1, bound1, recM1, env2, bound2, recM2)
        unitElim(m, f, env1(sel))
      case TEdge(n1, ElimLabel(sel, False, _, _)) :: TEdge(n2, ElimLabel(_, True, _, _)) :: Nil =>
        val motive =
          VLam(VBool, n =>
            VId(
              eval(node.conf.tp, env1 + (sel -> n), n :: bound1),
              eval(node.conf.term, env1 + (sel -> n), n :: bound1),
              fold(node, env1 + (sel -> n), n :: bound1, recM1)))
        val f1 = proofFold(n1, env1, bound1, recM1, env2, bound2, recM2)
        val f2 = proofFold(n2, env1, bound1, recM1, env2, bound2, recM2)
        boolElim(motive, f1, f2, env1(sel))
      case _ =>
        super.proofFold(node, env1, bound1, recM1, env2, bound2, recM2)
    }
}
