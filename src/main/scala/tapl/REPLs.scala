package tapl

object NatREPLMain extends NatREPL {
  override def initialState = State(true, natVE, natTE)
}

object AllREPLMain extends LambdaPiREPL with NatREPL with VectorREPL with EqREPL with FinREPL with ListREPL {
  val te = natTE ++ eqTE ++ vectorTE ++ finTE ++ listTE
  val ve = natVE ++ eqVE ++ vectorVE ++ finVE ++ listVE
  override def initialState = State(true, ve, te)
}
