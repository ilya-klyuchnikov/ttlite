package superspec.lambdapi

object NatREPLMain extends NatREPL {
  override def initialState = State(interactive = true, natVE, natTE, Set())
}

object AllREPLMain extends LambdaPiREPL with NatREPL with VectorREPL with EqREPL with FinREPL with ListREPL with PairREPL with SumREPL {
  val te = natTE ++ eqTE ++ vectorTE ++ finTE ++ listTE ++ productTE ++ sumTE
  val ve = natVE ++ eqVE ++ vectorVE ++ finVE ++ listVE ++ productVE ++ sumVE
  override def initialState = State(interactive = true, ve, te, Set())
}
