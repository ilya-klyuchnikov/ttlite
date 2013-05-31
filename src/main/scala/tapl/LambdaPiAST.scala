package tapl

trait LambdaPiAST extends LambdaAST {
  // CTerm
  case object Zero extends CTerm
  case class Succ(n: CTerm) extends CTerm
  case class Nil(c: CTerm) extends CTerm
  case class Cons(c1: CTerm, c2: CTerm, c3: CTerm, c4: CTerm) extends CTerm
  case class Refl(c1: CTerm, c2: CTerm) extends CTerm
  case class FZero(c: CTerm) extends CTerm
  case class FSucc(c1: CTerm, c2: CTerm) extends CTerm
  // ITerm
  case class Ann(c1: CTerm, c2: CTerm) extends ITerm
  case object Star_ extends ITerm
  case class Pi(c1: CTerm, c2: CTerm) extends ITerm
  // Bound, free, :@:
  case object Nat extends ITerm
  case class NatElim(c1: CTerm, c2: CTerm, c3: CTerm, c4: CTerm) extends ITerm
  case class Vec(c1: CTerm, c2: CTerm) extends ITerm
  case class VecElim(c1: CTerm, c2: CTerm, c3: CTerm, c4: CTerm, c5: CTerm, c6: CTerm) extends ITerm
  case class Eq(c1: CTerm, c2: CTerm, c3: CTerm) extends ITerm
  case class EqElim(c1: CTerm, c2: CTerm, c3: CTerm, c4: CTerm, c5: CTerm, c6: CTerm) extends ITerm
  case class Fin(c: CTerm) extends ITerm
  case class FinElim(c1: CTerm, c2: CTerm, c3: CTerm, c4: CTerm, c5: CTerm) extends ITerm
  // Value
  case object VStar extends Value
  case class VPi(t: Value, e: Value => Value) extends Value
  case object VNat extends Value
  case object VZero extends Value
  case class VSucc(n: Value) extends Value
  case class VNil(v: Value) extends Value
  case class VCons(v1: Value, v2: Value, v3: Value, v4: Value) extends Value
  case class VVec(v1: Value, v2: Value) extends Value
  case class VEq(v1: Value, v2: Value, v3: Value) extends Value
  case class VRefl(v1: Value, v2: Value) extends Value
  case class VFZero(v: Value) extends Value
  case class VFSucc(v1: Value, v2: Value) extends Value
  case class VFin(v: Value) extends Value
  // Neutral
  case class NNatElim(v1: Value, v2: Value, v3: Value, n: Neutral) extends Neutral
  case class NVecElim(v1: Value, v2: Value, v3: Value, v4: Value, v5: Value, n: Neutral) extends Neutral
  case class NEqElim(v1: Value, v2: Value, v3: Value, v4: Value, v5: Value, n: Neutral) extends Neutral
  case class NFinElim(v1: Value, v2: Value, v3: Value, v4: Value, n: Neutral) extends Neutral
}
