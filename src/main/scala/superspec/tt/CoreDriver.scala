package superspec.tt

import mrsc.core._
import superspec._

trait CoreDriver extends TTSc {
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
  override def driveTerm(c: CTerm): DriveStep = eval0(c) match {
    case VNeutral(n) => driveNeutral(n)
    case _ => decompose(c)
  }

  def driveNeutral(n: Neutral): DriveStep = n match {
    case NFree(n) => StopDStep
    case NApp(n, _) => driveNeutral(n)
  }

  def decompose(c: CTerm): DriveStep = eval0(c) match {
    case VLam(f) =>
      val fn = freshName()
      val nextTerm = quote0(f(vfree(fn)))
      LamDStep(fn, nextTerm)
    case _ =>
      StopDStep
  }

}

trait CoreResiduator extends BaseResiduator with CoreDriver {
  override def fold(g: TGraph[CTerm, Label], node: TNode[CTerm, Label], nEnv: NameEnv[Value], bEnv: Env, dRed: Map[CTerm, Value], tps: NameEnv[Value], tp: Value): Value =
    node.outs match {
      case TEdge(n1, LamLabel(fn)) :: Nil =>
        val VPi(ty1, ty2) = tp
        VLam(v => fold(g, n1, (fn, v) :: nEnv, bEnv, dRed, tps, ty2(ty1)))
      case _ =>
        super.fold(g, node, nEnv, bEnv, dRed, tps, tp)
    }
}
