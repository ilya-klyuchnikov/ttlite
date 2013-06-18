package tapl.lambdapi

import tapl._

trait LambdaPiAST extends Common {
  trait CTerm
  case class Inf(inf: ITerm) extends CTerm
  case class Lam(t: CTerm) extends CTerm
  // ITerm
  trait ITerm {
    def @@(t1: CTerm) = :@:(this, t1)
  }
  case class Ann(c1: CTerm, ct2: CTerm) extends ITerm
  case object Star extends ITerm
  case class Pi(c1: CTerm, c2: CTerm) extends ITerm
  case class Bound(i: Int) extends ITerm
  case class Free(n: Name) extends ITerm
  case class :@:(it: ITerm, ct: CTerm) extends ITerm
  // Value
  trait Value {
    def @@(x: Value): Value = vapp(this, x)
  }
  case class VLam(l: Value => Value) extends Value
  case object VStar extends Value
  case class VPi(t: Value, e: Value => Value) extends Value
  case class VNeutral(n: Neutral) extends Value
  // Neutral
  trait Neutral
  case class NFree(n: Name) extends Neutral
  case class NApp(n: Neutral, v: Value) extends Neutral

  type Env = List[Value]
  type Context = List[(Name, Value)]
  type Type = Value

  def vfree(n: Name): Value = VNeutral(NFree(n))
  def vapp(x: Value, v: Value): Value = x match {
    case VLam(f) => f(v)
    case VNeutral(n) => VNeutral(NApp(n, v))
  }
}
