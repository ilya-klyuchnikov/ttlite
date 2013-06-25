package superspec.lambdapi

import mrsc.core._
import superspec._

trait CoreDriver extends PiSc {
  var v = 100
  def freshName(): Name = {v += 1; Local(v)}
  def freshLocal(): CTerm = Inf(Free(freshName()))

  // boilerplate/indirections
  case class LamLabel(f: Name) extends Label
  case class LamStep(f: Name, next: CTerm) extends Step {
    override val graphStep =
      AddChildNodesStep[CTerm, Label](List(next -> LamLabel(f)))
  }
  case class LamDStep(f: Name, next: CTerm) extends DriveStep {
    override def step(t: CTerm) =
      LamStep(f, next)
  }

  // logic
  override def driveTerm(c: CTerm): DriveStep = cEval0(c) match {
    case VNeutral(n) => driveNeutral(n)
    case _ => decompose(c)
  }

  def driveNeutral(n: Neutral): DriveStep = n match {
    case NFree(n) => StopDStep
    case NApp(n, _) => driveNeutral(n)
  }

  def decompose(c: CTerm): DriveStep = cEval0(c) match {
    case VLam(f) =>
      val fn = freshName()
      val nextTerm = quote0(f(vfree(fn)))
      LamDStep(fn, nextTerm)
    case _ =>
      StopDStep
  }

}

trait LamResiduator extends BaseResiduator with CoreDriver {
  override def fold(g: TGraph[CTerm, Label], node: TNode[CTerm, Label], nEnv: NameEnv[Value], bEnv: Env, dRed: Map[CTerm, Value]): Value =
    node.outs match {
      case TEdge(n1, LamLabel(fn)) :: Nil =>
        VLam(v => fold(g, n1, (fn, v) :: nEnv, bEnv, dRed))
      case _ =>
        super.fold(g, node, nEnv, bEnv, dRed)
    }
}
