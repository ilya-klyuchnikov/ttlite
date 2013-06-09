package tapl

object NatREPLMain extends NatREPL {
  override def initialState = State(true, natVE, natTE)
}

object AllREPLMain extends LambdaPiREPL with NatREPL with EqREPL {
  val te = natTE ++ eqTE
  val ve = natVE ++ eqVE
  override def initialState = State(true, ve, te)
}
