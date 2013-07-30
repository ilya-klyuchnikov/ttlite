package superspec

import superspec.tt._
import mrsc.core._

trait EqDriver extends CoreDriver with EqAST {

  case object ReflLabel extends Label
  case class ReflStep(x: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(x -> ReflLabel))
  }
  case class ReflDStep(x: Conf) extends DriveStep {
    override def step(t: Conf) = ReflStep(x)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case Refl(a, x) =>
      val Eq(_, _, _) = c.tp
      ReflDStep(Conf(x, a))
    case _ =>
      super.decompose(c)
  }

}

trait EqResiduator extends BaseResiduator with EqDriver { self =>
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(x, ReflLabel) :: Nil =>
        val VEq(a, _, _) = eval(node.conf.tp, env, bound)
        'Refl @@ a @@ fold(x, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}