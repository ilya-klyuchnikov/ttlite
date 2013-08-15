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

