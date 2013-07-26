package superspec

import superspec.tt._
import mrsc.core._

trait ProductDriver extends CoreDriver with ProductAST {

  case object PairLabel extends Label

  case class PairStep(a: Conf, b: Conf, x: Conf, y: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(a -> PairLabel, b -> PairLabel, x -> PairLabel, y -> PairLabel))
  }
  case class PairDStep(a: Conf, b: Conf, x: Conf, y: Conf) extends DriveStep {
    override def step(t: Conf) = PairStep(a, b, x, y)
  }

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NProductElim(a, b, _, _, p) =>
      p match {
        case NFree(n) =>
          val aType = quote0(a)
          val bType = quote0(b)

          val xName = freshName(aType)
          val x = Free(xName)

          val yName = freshName(bType)
          val y = Free(yName)

          val pairCase = ElimBranch(Pair(aType, bType, x, y), Map())

          ElimDStep(n, List(pairCase))
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case Pair(a, b, x, y) =>
      val Product(a1, b1) = c.tp
      PairDStep(Conf(a, Star), Conf(b, Star), Conf(x, a), Conf(y, b))
    case _ =>
      super.decompose(c)
  }

}

trait ProductResiduator extends BaseResiduator with ProductDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeS, CaseBranchLabel(sel, ElimBranch(Pair(a, b, Free(xN), Free(yN)), _))) :: Nil =>
        val aVal = eval(a, env, bound)
        val bVal = eval(b, env, bound)
        val motive =
          VLam(VProduct(aVal, bVal), p => eval(node.conf.tp, env + (sel -> p), p :: bound))

        val pairCase = VLam(aVal, x => VLam(bVal, y =>
          fold(nodeS, env + (xN -> x) + (yN -> y), y :: x :: bound, recM)))

        VNeutral(NFree(Global("productElim"))) @@
          aVal @@
          bVal @@
          motive @@
          pairCase @@
          env(sel)
      case TEdge(a, PairLabel) :: TEdge(b, PairLabel) :: TEdge(x, PairLabel) :: TEdge(y, PairLabel) :: Nil =>
        val VProduct(aType, bType) = eval(node.conf.tp, env, bound)
        VNeutral(NFree(Global("Pair"))) @@
          fold(a, env, bound, recM) @@
          fold(b, env, bound, recM) @@
          fold(x, env, bound, recM) @@
          fold(y, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}
