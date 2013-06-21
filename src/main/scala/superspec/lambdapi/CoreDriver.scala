package superspec.lambdapi

import superspec.Driver

trait CoreDriver extends CoreSubst with Driver {
  var v = 100
  def freshName(): Name = {v += 1; Local(v)}
  def freshLocal(): CTerm = Inf(Free(freshName()))

  override def driveTerm(c: CTerm): DriveStep = cEval0(c) match {
    case VNeutral(n) => driveNeutral(n)
    case _ => driveLeibniz(c)
  }

  def driveNeutral(n: Neutral): DriveStep = n match {
    case NFree(n) => StopDStep
    case NApp(n, _) => driveNeutral(n)
  }

  def driveLeibniz(c: CTerm): DriveStep =
    StopDStep
}
