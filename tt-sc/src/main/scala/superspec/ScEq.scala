package superspec

import superspec.tt._
import mrsc.core._

trait EqDriver extends CoreDriver with EqEval {

  case object ReflLabel extends Label
  case object EqLabel extends Label

  override def decompose(c: Conf): DriveStep = c.term match {
    case Refl(a, x) =>
      DecomposeDStep(ReflLabel, Conf(x, c.ctx))
    case Eq(a, x, y) =>
      DecomposeDStep(EqLabel, Conf(x, c.ctx), Conf(y, c.ctx))
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
      case TEdge(x, EqLabel) :: TEdge(y, EqLabel) :: Nil =>
        val VEq(a, _, _) = eval(node.conf.term, env, bound)
        VEq(a, fold(x, env, bound, recM), fold(y, env, bound, recM))
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
          // This is an interesting difference due to dependent types!!
          // this is needed for typing purposes only!!
          // VLam(a, x => VRefl(a, x)) @@
          VLam(a, _ => VRefl(a, eval(x.conf.term, env, bound))) @@
          eval(x.conf.term, env, bound) @@
          fold(x, env, bound, recM) @@
          proofFold(x, env, bound, recM, env2, bound2, recM2)
      case TEdge(x, EqLabel) :: TEdge(y, EqLabel) :: Nil =>
        val tp = eval(node.conf.tp, env, bound)
        val VEq(a, _, _) = eval(node.conf.term, env, bound)

        val x1 = eval(x.conf.term, env, bound)
        val x2 = fold(x, env, bound, recM)
        val eq_x1_x2 = proofFold(x, env, bound, recM, env2, bound2, recM2)

        val y1 = eval(y.conf.term, env, bound)
        val y2 = fold(y, env, bound, recM)
        val eq_y1_y2 = proofFold(y, env, bound, recM, env2, bound2, recM2)

        'cong2 @@ a @@ a @@ tp @@
          VLam(a, x => VLam(a, y => VEq(a, x, y))) @@
          x1 @@ x2 @@ eq_x1_x2 @@
          y1 @@ y2 @@ eq_y1_y2
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }

}