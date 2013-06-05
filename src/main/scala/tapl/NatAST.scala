package tapl

trait NatAST extends LambdaPiAST {

  case object Zero extends CTerm
  case class Succ(e: CTerm) extends CTerm

  case object Nat extends ITerm
  case class NatElim(a: CTerm, b: CTerm, c: CTerm, d: CTerm) extends ITerm

  case object VNat extends Value
  case object VZero extends Value
  case class VSucc(v: Value) extends Value

  case class NNatElim(v1: Value, v2: Value, v3: Value, n: Neutral) extends Neutral
}
