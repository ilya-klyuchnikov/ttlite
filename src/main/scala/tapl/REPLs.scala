package tapl

object NatREPLMain extends NatREPL {
  override def initialState = State(true, natVE, natTE)
}

object AllREPLMain extends LambdaPiREPL with NatREPL with VectorREPL with EqREPL with FinREPL {
  val te = natTE ++ eqTE ++ vectorTE ++ finTE
  val ve = natVE ++ eqVE ++ vectorVE ++ finVE
  override def initialState = State(true, ve, te)
}
