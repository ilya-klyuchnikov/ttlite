package superspec

import superspec.tt._
import mrsc.core._

trait SumDriver extends CoreDriver with SumAST {

  case object InLLabel extends Label
  case object InRLabel extends Label
  case class InLStep(L: Conf, R: Conf, l: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(L -> InLLabel, R -> InLLabel, l -> InLLabel))
  }
  case class InRStep(L: Conf, R: Conf, r: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(L -> InRLabel, R -> InRLabel, r -> InRLabel))
  }
  case class InLDStep(L: Conf, R: Conf, l: Conf) extends DriveStep {
    override def step(t: Conf) = InLStep(L, R, l)
  }
  case class InRDStep(L: Conf, R: Conf, r: Conf) extends DriveStep {
    override def step(t: Conf) = InRStep(L, R, r)
  }

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NSumElim(l, r, _, _, _, s) =>
      s match {
        case NFree(n) =>
          val lType = quote0(l)
          val rType = quote0(r)

          val lCase = ElimBranch(InL(lType, rType, freshLocal(lType)), Map())
          val rCase = ElimBranch(InR(lType, rType, freshLocal(rType)), Map())

          ElimDStep(n, List(lCase, rCase))
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case InL(lType, rType, l) =>
      val Sum(_, _) = c.tp
      InLDStep(Conf(lType, Star), Conf(rType, Star), Conf(l, lType))
    case InR(lType, rType, r) =>
      val Sum(_, _) = c.tp
      InRDStep(Conf(lType, Star), Conf(rType, Star), Conf(r, rType))
    case _ =>
      super.decompose(c)
  }
}

trait SumResiduator extends BaseResiduator with SumDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, CaseBranchLabel(sel, ElimBranch(InL(a, b, Free(lN)), _))) ::
        TEdge(nodeR, CaseBranchLabel(_, ElimBranch(InR(_, _, Free(rN)), _))) ::
        Nil =>

        val aVal = eval(a, env, bound)
        val bVal = eval(b, env, bound)
        val motive =
          VLam(VSum(aVal, bVal), s => eval(node.conf.tp, env + (sel -> s), s :: bound))

        val lCase = VLam(aVal, l => fold(nodeL, env + (lN -> l), l :: bound, recM))
        val rCase = VLam(bVal, r => fold(nodeR, env + (rN -> r), r :: bound, recM))

        'sumElim @@
          aVal @@
          bVal @@
          motive @@
          lCase @@
          rCase @@
          env(sel)
      case TEdge(a, InLLabel) :: TEdge(b, InLLabel) :: TEdge(l, InLLabel) :: Nil =>
        val VSum(_, _) = eval(node.conf.tp, env, bound)
        'InL @@
          fold(a, env, bound, recM) @@
          fold(b, env, bound, recM) @@
          fold(l, env, bound, recM)
      case TEdge(a, InRLabel) :: TEdge(b, InRLabel) :: TEdge(r, InRLabel) :: Nil =>
        val VSum(_, _) = eval(node.conf.tp, env, bound)
        'InR @@
          fold(a, env, bound, recM) @@
          fold(b, env, bound, recM) @@
          fold(r, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}
