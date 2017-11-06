package ttlite.sc

import mrsc.core._
import ttlite.common._
import ttlite.core._

trait CoreSubst extends CoreEval with CoreQuoting {
  type Subst = Map[Name, Term]

  implicit class TermSubst(t: Term) {
    def /(subst: Subst) = {
      val env: NameEnv[Value] = subst.map {case (n, t) => (n, eval(t, Map[Name, Value](), Nil))}
      quote0(eval(t, env, Nil))
    }
  }
}

trait CoreDriver extends TTSc with CoreCheck {
  import scala.language.implicitConversions

  var v = 100
  def freshName(): Name = {
    v += 1
    Local(v)
  }

  // logic
  override def singleDrive(c: Conf): DriveStep = eval0(c.term) match {
    case VNeutral(n) =>
      nv(n) match {
        case Some(n) =>
          elimVar(n, iType0(c.ctx, Free(n)))
        case None =>
          StopDStep
      }
    case _ => decompose(c)
  }

  override def multiDrive(c: Conf): List[DriveStep] =
    (decompose(c) +: freeVars(c.term).map(n => elimVar(n, iType0(c.ctx, Free(n))))).distinct

  // neutral variable of a value
  def nv(n: Neutral): Option[Name] =
    None

  def elimVar(n: Name, nt: Value): DriveStep = nt match {
    case _ => StopDStep
  }

  def decompose(c: Conf): DriveStep = StopDStep

  implicit def name2Term(n: Name) = Free(n)
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
