package ttlite.sc

import ttlite.common._
import ttlite.core._

trait FunDriver extends CoreDriver with FunEval {

  override def nv(t: Neutral): Option[Name] = t match {
    case NApp(NFree(n), _) => Some(n)
    case NApp(n, _) => nv(n)
    case _ => super.nv(t)
  }

  override def elimVar(n: Name, nt: Value): DriveStep = nt match {
    case VPi(_, _) => StopDStep
    case _ => super.elimVar(n, nt)
  }

  // TODO - it is possible to decompose application if the inner "operator" is neutral
  override def decompose(c: Conf): DriveStep = c.term match {
    case _ =>
      super.decompose(c)
  }
}

trait FunResiduator extends CoreResiduator with FunDriver
trait FunProofResiduator extends ProofResiduator with FunResiduator
