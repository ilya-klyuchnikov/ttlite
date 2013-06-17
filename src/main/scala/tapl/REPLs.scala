package tapl

object NatREPLMain extends NatREPL {
  override def initialState = State(true, natVE, natTE, Set())
}

object AllREPLMain extends LambdaPiREPL with NatREPL with VectorREPL with EqREPL with FinREPL with ListREPL with PairREPL {
  val te = natTE ++ eqTE ++ vectorTE ++ finTE ++ listTE ++ pairTE
  val ve = natVE ++ eqVE ++ vectorVE ++ finVE ++ listVE ++ pairVE
  override def initialState = State(true, ve, te, Set())
}
