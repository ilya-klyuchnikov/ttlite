package superspec

import mrsc.core._

trait DProductDriver extends CoreDriver {

  case object DPairLabel extends Label
  case class DPairStep(x: Conf, y: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(x -> DPairLabel, y -> DPairLabel))
  }
  case class DPairDStep(x: Conf, y: Conf) extends DriveStep {
    override def step(t: Conf) = DPairStep(x, y)
  }

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NSigmaElim(sigma@VSigma(a, b), m, f, p) =>
      p match {
        case NFree(n) =>

          val sigmaT@Sigma(aType, bType) = quote0(sigma)
          val xName = freshName(aType)
          val x = Free(xName)

          val bX = quote0(eval(bType @@ x, emptyNEnv, Nil))
          val yName = freshName(bX)
          val y = Free(yName)

          val pairCase = ElimBranch(DPair(sigmaT, x, y), Map())

          ElimDStep(n, List(pairCase))
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case DPair(sigma, x, y) =>
      val Sigma(a, b) = c.tp
      val bX = quote0(eval(b @@ x, emptyNEnv, Nil))
      DPairDStep(Conf(x, a), Conf(y, bX))
    case _ =>
      super.decompose(c)
  }

}

trait DProductResiduator extends CoreResiduator with DProductDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeS, CaseBranchLabel(sel, ElimBranch(DPair(sigma, Free(xN), Free(yN)), _))) :: Nil =>
        val sigmaVal@VSigma(x1, y1) = eval(sigma, env, bound)
        val motive =
          VLam(sigmaVal, p => eval(node.conf.tp, env + (sel -> p), p :: bound))
        val pairCase = VLam(x1, x => VLam(y1(x), y =>
          fold(nodeS, env + (xN -> x) + (yN -> y), y :: x :: bound, recM)))
        val VNeutral(n) = env(sel)
        VNeutral(NSigmaElim(sigmaVal, motive, pairCase, n))
      case TEdge(x, DPairLabel) :: TEdge(y, DPairLabel) :: Nil =>
        val sigma = eval(node.conf.tp, env, bound)
        VDPair(sigma, fold(x, env, bound, recM), fold(y, env, bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait DProductProofResiduator extends DProductResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeS, CaseBranchLabel(sel, ElimBranch(DPair(sigma, Free(xN), Free(yN)), _))) :: Nil =>
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

        val VNeutral(n) = env(sel)
        VNeutral(NSigmaElim(sigmaVal, motive, pairCase, n))

      case TEdge(x, DPairLabel) :: TEdge(y, DPairLabel) :: Nil =>
        val sigma = eval(node.conf.tp, env, bound)
        val x1 = eval(x.conf.term, env, bound)
        val x2 = fold(x, env, bound, recM)
        val eq_x1_x2 = proofFold(x, env, bound, recM, env2, bound2, recM2)

        val y1 = eval(y.conf.term, env, bound)
        val y2 = fold(y, env, bound, recM)
        val eq_y1_y2 = proofFold(y, env, bound, recM, env2, bound2, recM2)

        val a = eval(x.conf.tp, env, bound)
        println(a)
        val b = eval(y.conf.tp, env, bound)
        println(b)

        'cong2 @@ a @@ b @@ sigma @@
          VLam(a, x => VLam(b, y => VDPair(sigma, x, y))) @@
          x1 @@ x2 @@ eq_x1_x2 @@
          y1 @@ y2 @@ eq_y1_y2

      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}


