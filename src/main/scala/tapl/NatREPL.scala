package tapl

object NatREPLMain extends NatREPL {
  override def initialState = State(true, natVE, natTE)
}
