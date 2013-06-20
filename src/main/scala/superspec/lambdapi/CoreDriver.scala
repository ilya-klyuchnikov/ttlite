package superspec.lambdapi

import superspec.Driver

trait CoreDriver extends CoreSubst with Driver {
  var v = 100
  def freshName(): Name = {
    v += 1
    Local(v)
  }

  def freshLocal(): CTerm = {
    Inf(Free(freshName()))
  }

  override def driveTerm(c: CTerm): DriveStep = {
    val normedVal = cEval0(c)
    val normedTerm = quote0(normedVal)
    normedVal match {
      case VNeutral(n) =>
        driveNeutral(n)
      case _ =>
        normedTerm match {
          case `c` =>
            driveLeibniz(c)
          case _ =>
            NormDStep(normedTerm)

        }
    }
  }

  def driveNeutral(n: Neutral): DriveStep = n match {
    case NFree(n) =>
      StopDStep
    case NApp(n, _) =>
      driveNeutral(n)
  }

  def driveLeibniz(c: CTerm): DriveStep =
    StopDStep
}
