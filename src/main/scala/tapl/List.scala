package tapl

trait ListAST extends LambdaPiAST {
  case class LNil(A: CTerm) extends CTerm
  case class LCons(A: CTerm, head: CTerm, tail: CTerm) extends CTerm

  case class PiList(A: CTerm) extends ITerm
  case class PiListElim(A: CTerm, motive: CTerm, nilCase: CTerm, consCase: CTerm, l: CTerm) extends ITerm

  case class VPiList(A: Value) extends Value
  case class VPiNil(A: Value) extends Value
  case class VPiCons(A: Value, head: Value, tail: Value) extends Value

  case class NPiListElim(A: Value, motive: Value, nilCase: Value, consCase: Value, l: Neutral) extends Neutral
}
