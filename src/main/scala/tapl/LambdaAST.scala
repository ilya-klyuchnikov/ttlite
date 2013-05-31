package tapl

trait LambdaAST extends Common { self =>
  // inferable terms
  trait Term
  trait ITerm extends Term
  case class Ann(c1: CTerm, t: Type) extends ITerm
  case class Bound(i: Int) extends ITerm
  case class Free(n: Name) extends ITerm
  case class :@:(it: ITerm, ct: CTerm) extends ITerm

  // checkable terms
  trait CTerm extends Term {
    def :@:(it: ITerm) = self.:@:(it, this)
  }
  case class Inf(inf: ITerm) extends CTerm
  case class Lam(t: CTerm) extends CTerm

  trait Value
  case class VLam(l: Value => Value) extends Value
  case class VNeutral(n: Neutral) extends Value

  trait Neutral
  case class NFree(n: Name) extends Neutral
  case class NApp(n: Neutral, v: Value) extends Neutral

  type Env = List[Value]

  def vfree(n: Name): Value = VNeutral(NFree(n))
  def vapp(x: Value, v: Value): Value = x match {
    case VLam(f) => f(v)
    case VNeutral(n) => VNeutral(NApp(n, v))
  }

  trait Type
  case class TFree(n: Name) extends Type
  case class Fun(t1: Type, t2: Type) extends Type

  trait Kind
  case object Star extends Kind

  trait Info
  // Type n > 1
  case class HasKind(k: Kind) extends Info
  // Type 0
  case class HasType(t: Type) extends Info
  type Context = List[(Name, Info)]
}
