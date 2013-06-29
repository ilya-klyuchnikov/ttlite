package superspec.tt

import mrsc.core._
import superspec._

trait CoreDriver extends TTSc {

  var v = 100

  def freshName(tp: CTerm): Name = {
    v += 1;
    val res = Local(v)
    typeMap = typeMap + (res -> tp)
    res
  }

  def freshLocal(tp: CTerm): CTerm =
    Inf(Free(freshName(tp)))

  // current ad-hoc solution for mapping variables and types of new free variables

  // knowledge about which variable has which type
  var typeMap: Map[Name, CTerm] = Map()

  // boilerplate/indirections
  case class LamLabel(f: Name) extends Label
  case class LamStep(f: Name, next: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(next -> LamLabel(f)))
  }
  case class LamDStep(f: Name, next: Conf) extends DriveStep {
    override def step(t: Conf) =
      LamStep(f, next)
  }

  // logic
  override def driveTerm(c: Conf): DriveStep = eval0(c.ct) match {
    case VNeutral(n) => driveNeutral(n)
    case _ => decompose(c)
  }

  def driveNeutral(n: Neutral): DriveStep = n match {
    case NFree(n) => StopDStep
    case NApp(n, _) => driveNeutral(n)
  }

  def decompose(c: Conf): DriveStep = eval0(c.ct) match {
    case VLam(f) =>
      val Inf(Pi(t1, _)) = c.tp
      val fn: Name = freshName(t1)
      val nextTerm = quote0(f(vfree(fn)))
      val VPi(_, vt2) = eval0(c.tp)
      val nextType = quote0(vt2(vfree(fn)))
      LamDStep(fn, DConf(nextTerm, nextType))

    case _ =>
      StopDStep
  }

  override def elimFreeVar(c: Conf, fv: Local): List[ElimDStep] =
    Nil

}

trait CoreResiduator extends BaseResiduator with CoreDriver {
  override def fold(node: N, env: NameEnv[Value], recM: Map[TPath, Value], tp: Value): Value =
    node.outs match {
      case TEdge(n1, LamLabel(fn)) :: Nil =>
        val VPi(_, ty2) = tp
        VLam(v => fold(n1, env + (fn -> v), recM, ty2(vfree(fn))))
      case _ =>
        super.fold(node, env, recM, tp)
    }
}
