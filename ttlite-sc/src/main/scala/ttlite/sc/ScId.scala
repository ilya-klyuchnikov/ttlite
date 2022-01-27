package ttlite.sc

import mrsc.core._
import ttlite.common._
import ttlite.core._

trait IdDriver extends Driver, IdEval { self: PiAST =>

  case object ReflLabel extends Label
  case object EqLabel extends Label

  override def nv(t: Neutral): Option[Name] =
    t match {
      case NIdElim(_, _, _, NFree(n)) => Some(n)
      case NIdElim(_, _, _, n)        => nv(n)
      case _                          => super.nv(t)
    }

  override def decompose(c: Conf): DriveStep =
    c.term match {
      case Refl(a, x) =>
        DecomposeDStep(ReflLabel, Conf(x, c.ctx))
      case Id(a, x, y) =>
        DecomposeDStep(EqLabel, Conf(x, c.ctx), Conf(y, c.ctx))
      case _ =>
        super.decompose(c)
    }

}

trait IdResiduator extends Residuator, IdDriver { self: PiAST =>
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(x, ReflLabel) :: Nil =>
        val VId(a, _, _) = eval(node.conf.tp, env, bound)
        VRefl(a, fold(x, env, bound, recM))
      case TEdge(x, EqLabel) :: TEdge(y, EqLabel) :: Nil =>
        val VId(a, _, _) = eval(node.conf.term, env, bound)
        VId(a, fold(x, env, bound, recM), fold(y, env, bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait IdProofResiduator extends IdResiduator, ProofResiduator { self: PiAST & IdAST =>
  override def proofFold(
      node: N,
      env1: NameEnv[Value],
      bound1: Env,
      recM1: Map[TPath, Value],
      env2: NameEnv[Value],
      bound2: Env,
      recM2: Map[TPath, Value],
  ): Value =
    node.outs match {
      case TEdge(x, ReflLabel) :: Nil =>
        val eq @ VId(a, _, _) = eval(node.conf.tp, env1, bound1)
        "cong1" @@
          a @@
          eq @@
          // This is an interesting difference due to dependent types!!
          // this is needed for typing purposes only!!
          // VLam(a, x => VRefl(a, x)) @@
          VLam(a, _ => VRefl(a, eval(x.conf.term, env1, bound1))) @@
          eval(x.conf.term, env1, bound1) @@
          fold(x, env1, bound1, recM1) @@
          proofFold(x, env1, bound1, recM1, env2, bound2, recM2)
      case TEdge(x, EqLabel) :: TEdge(y, EqLabel) :: Nil =>
        val tp = eval(node.conf.tp, env1, bound1)
        val VId(a, _, _) = eval(node.conf.term, env1, bound1)

        val x1 = eval(x.conf.term, env1, bound1)
        val x2 = fold(x, env1, bound1, recM1)
        val eq_x1_x2 = proofFold(x, env1, bound1, recM1, env2, bound2, recM2)

        val y1 = eval(y.conf.term, env1, bound1)
        val y2 = fold(y, env1, bound1, recM1)
        val eq_y1_y2 = proofFold(y, env1, bound1, recM1, env2, bound2, recM2)

        "cong2" @@ a @@ a @@ tp @@
          VLam(a, x => VLam(a, y => VId(a, x, y))) @@
          x1 @@ x2 @@ eq_x1_x2 @@
          y1 @@ y2 @@ eq_y1_y2
      case _ =>
        super.proofFold(node, env1, bound1, recM1, env2, bound2, recM2)
    }

}
