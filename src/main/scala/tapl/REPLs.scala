package tapl

object NatREPLMain extends NatREPL {
  override def initialState = State(true, natVE, natTE)
}

object AllREPLMain extends LambdaPiREPL with NatREPL with VectorREPL with EqREPL {
  val te = natTE ++ eqTE ++ vectorTE
  val ve = natVE ++ eqVE ++ vectorVE
  override def initialState = State(true, ve, te)
}
