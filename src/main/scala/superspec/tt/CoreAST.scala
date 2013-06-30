package superspec.tt

import superspec._

trait CoreAST extends Common {
  trait Term {
    def @@(t1: Term) = :@:(this, t1)
  }
  case class Lam(t: Term, e: Term) extends Term
  case class Ann(c1: Term, ct2: Term) extends Term
  case object Star extends Term
  case class Pi(c1: Term, c2: Term) extends Term
  case class Bound(i: Int) extends Term
  case class Free(n: Name) extends Term
  case class :@:(h: Term, t: Term) extends Term
  // Value
  trait Value {
    def @@(x: Value): Value = vapp(this, x)
  }
  case class VLam(t: Value, e: Value => Value) extends Value
  case object VStar extends Value
  case class VPi(t: Value, e: Value => Value) extends Value
  case class VNeutral(n: Neutral) extends Value
  // Neutral
  trait Neutral
  case class NFree(n: Name) extends Neutral
  case class NApp(n: Neutral, v: Value) extends Neutral

  type Env = List[Value]
  val emptyNEnv = Map[Name, Value]()

  def vfree(n: Name): Value = VNeutral(NFree(n))
  @deprecated
  def vapp(x: Value, v: Value): Value = x match {
    case VLam(_, f) => f(v)
    case VNeutral(n) => VNeutral(NApp(n, v))
  }

  def freeLocals(c: Any): Set[Local] = c match {
    case Free(Local(n)) =>
      Set(Local(n))
    case p: scala.Product =>
      p.productIterator.flatMap(freeLocals).toSet
    case _ => Set()
  }

}
