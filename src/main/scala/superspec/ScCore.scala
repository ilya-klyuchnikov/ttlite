package superspec

import superspec.tt._
import mrsc.core._

trait CoreDriver extends TTSc with CoreCheck {
  var v = 100
  def freshName(tp: Term): Name = {
    v += 1;
    val res = Local(v)
    typeMap = typeMap + (res -> tp)
    res
  }

  def freshLocal(tp: Term): Term =
    Free(freshName(tp))

  // current ad-hoc solution for mapping variables and types of new free variables

  // knowledge about which variable has which type
  // todo ; put bound here
  var typeMap: Map[Name, Term] = Map()

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
  override def driveTerm(c: Conf): DriveStep = eval0(c.term) match {
    case VNeutral(n) => driveNeutral(n)
    case _ => decompose(c)
  }

  // TODO: if override returns stop, then we can decompose
  def driveNeutral(n: Neutral): DriveStep = n match {
    case NApp(n, _) => driveNeutral(n)
    case _ => StopDStep
  }

  def decompose(c: Conf): DriveStep = c.term match {
    // TODO: into separate trait "WithLambda"
    /*
    case Lam(t, f) =>
      val Pi(t1, t2) = c.tp
      val fn = freshName(t1)
      val nextTerm = iSubst(0, Free(fn), f)
      val nextType = iSubst(0, Free(fn), t2)
      LamDStep(fn, Conf(nextTerm, nextType))
    */
    case _ => StopDStep
  }

  override def elimFreeVar(c: Conf, fv: Local): List[ElimDStep] =
    Nil

}

trait CoreResiduator extends BaseResiduator with CoreDriver {
  import mrsc.core._

  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(n1, LamLabel(fn)) :: Nil =>
        val Pi(t1, _) = node.conf.tp
        VLam(eval(t1, env, bound), v => fold(n1, env + (fn -> v), v :: bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait CoreProofResiduator extends ProofResiduator with CoreResiduator {
  import mrsc.core._

  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM)
    }
}
