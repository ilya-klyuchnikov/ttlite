package superspec

import superspec.tt._

trait FunDriver extends CoreDriver with FunEval {

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NApp(n, _) =>
      driveNeutral(n)
    case _ =>
      super.driveNeutral(n)
  }

  // TODO - it is possible to decompose application if the inner "operator" is neutral
  override def decompose(c: Conf): DriveStep = c.term match {
    case _ =>
      super.decompose(c)
  }
}

trait FunResiduator extends CoreResiduator with FunDriver
trait FunProofResiduator extends ProofResiduator with FunResiduator
