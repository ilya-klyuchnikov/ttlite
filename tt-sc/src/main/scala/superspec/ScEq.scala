package superspec

import superspec.tt._
import mrsc.core._

trait EqDriver extends CoreDriver with EqEval {

  case object ReflLabel extends Label

  override def decompose(c: Conf): DriveStep = c.term match {
    case Refl(a, x) =>
      val Eq(_, _, _) = c.tp
      DecomposeDStep(ReflLabel, Conf(x, a))
    case _ =>
      super.decompose(c)
  }

}

trait EqResiduator extends BaseResiduator with EqDriver { self =>
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(x, ReflLabel) :: Nil =>
        val VEq(a, _, _) = eval(node.conf.tp, env, bound)
        VRefl(a, fold(x, env, bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait EqProofResiduator extends EqResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(x, ReflLabel) :: Nil =>
        val eq@VEq(a, _, _) = eval(node.conf.tp, env, bound)
        'cong1 @@
          a @@
          eq @@
          VLam(a, x => VRefl(a, x)) @@
          eval(x.conf.term, env, bound) @@
          fold(x, env, bound, recM) @@
          proofFold(x, env, bound, recM, env2, bound2, recM2)
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }

}