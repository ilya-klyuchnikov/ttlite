package superspec

import superspec.tt._
import mrsc.core._

trait DPairDriver extends CoreDriver with DPairAST with DPairEval {

  case object DPairLabel extends Label

  override def nv(t: Neutral): Option[Name] = t match {
    case NSigmaElim(_, _, _, NFree(n)) => Some(n)
    case NSigmaElim(_, _, _, n) => nv(n)
    case _ => super.nv(t)
  }

  override def elimVar(n: Name, nt: Value): DriveStep = nt match {
    case VSigma(a, b) =>
      val sigmaT = quote0(nt)
      val x = freshName()
      val y = freshName()
      val pairCase = ElimLabel(n, DPair(sigmaT, x, y), Map(), Map(x -> a, y -> b(vfree(x))))
      ElimDStep(pairCase)
    case _ =>
      super.elimVar(n, nt)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case DPair(sigma, x, y) =>
      DecomposeDStep(DPairLabel, Conf(x, c.ctx), Conf(y, c.ctx))
    case _ =>
      super.decompose(c)
  }

}

trait DPairResiduator extends CoreResiduator with DPairDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeS, ElimLabel(sel, DPair(sigma, Free(xN), Free(yN)), _, _)) :: Nil =>
        val sigmaVal@VSigma(x1, y1) = eval(sigma, env, bound)
        val motive =
          VLam(sigmaVal, p => eval(node.conf.tp, env + (sel -> p), p :: bound))
        val pairCase = VLam(x1, x => VLam(y1(x), y =>
          fold(nodeS, env + (xN -> x) + (yN -> y), y :: x :: bound, recM)))
        sigmaElim(sigmaVal, motive, pairCase, env(sel))
      case TEdge(x, DPairLabel) :: TEdge(y, DPairLabel) :: Nil =>
        val sigma = eval(node.conf.tp, env, bound)
        VDPair(sigma, fold(x, env, bound, recM), fold(y, env, bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait DPairProofResiduator extends DPairResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeS, ElimLabel(sel, DPair(sigma, Free(xN), Free(yN)), _, _)) :: Nil =>
        val sigmaVal@VSigma(x1, y1) = eval(sigma, env, bound)
        val motive =
          VLam(sigmaVal, n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))

        val pairCase = VLam(x1, x => VLam(y1(x), y =>
          proofFold(nodeS,
            env + (xN -> x) + (yN -> y), y :: x :: bound, recM,
            env2 + (xN -> x) + (yN -> y), y :: x :: bound2, recM2)))

        sigmaElim(sigmaVal, motive, pairCase, env(sel))

      case TEdge(x, DPairLabel) :: TEdge(y, DPairLabel) :: Nil =>
        val sigma = eval(node.conf.tp, env, bound)
        val x1 = eval(x.conf.term, env, bound)
        val x2 = fold(x, env, bound, recM)
        val eq_x1_x2 = proofFold(x, env, bound, recM, env2, bound2, recM2)

        val y1 = eval(y.conf.term, env, bound)
        val y2 = fold(y, env, bound, recM)
        val eq_y1_y2 = proofFold(y, env, bound, recM, env2, bound2, recM2)

        val a = eval(x.conf.tp, env, bound)
        val b = eval(y.conf.tp, env, bound)

        'cong2 @@ a @@ b @@ sigma @@
          //VLam(a, _ => VLam(b, _ => VDPair(sigma, x1, y1))) @@
          VLam(a, _ => VLam(b, y => VDPair(sigma, x1, y))) @@
          x1 @@ x2 @@ eq_x1_x2 @@
          y1 @@ y2 @@ eq_y1_y2

      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}


