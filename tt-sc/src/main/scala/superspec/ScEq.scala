package superspec

import superspec.tt._
import mrsc.core._

trait EqDriver extends CoreDriver with EqAST {

  case object ReflLabel extends Label
  case class ReflStep(A: Conf, x: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(A -> ReflLabel, x -> ReflLabel))
  }
  case class ReflDStep(A: Conf, x: Conf) extends DriveStep {
    override def step(t: Conf) = ReflStep(A, x)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case Refl(a, x) =>
      val Eq(_, _, _) = c.tp
      ReflDStep(Conf(a, Star), Conf(x, a))
    case _ =>
      super.decompose(c)
  }

}

trait EqResiduator extends BaseResiduator with EqDriver { self =>
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(a, ReflLabel) :: TEdge(x, ReflLabel) :: Nil =>
        val VEq(_, _, _) = eval(node.conf.tp, env, bound)
        'Refl @@ fold(a, env, bound, recM) @@ fold(x, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}