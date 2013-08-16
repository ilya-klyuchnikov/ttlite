package superspec

import superspec.tt._
import mrsc.core._

trait CoreSubst extends CoreEval with CoreQuote {
  type Subst = Map[Name, Term]
  implicit class TermSubst(t: Term) {
    def /(subst: Subst) = {
      val env: NameEnv[Value] = subst.map {case (n, t) => (n, eval(t, emptyNEnv, Nil))}
      quote0(eval(t, env, Nil))
    }
  }
}

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
    // TODO: decomposition of application
    case _ => StopDStep
  }

}

trait CoreResiduator extends BaseResiduator with CoreDriver {
  import mrsc.core._

  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait CoreProofResiduator extends ProofResiduator with CoreResiduator {

  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case _ =>  super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
