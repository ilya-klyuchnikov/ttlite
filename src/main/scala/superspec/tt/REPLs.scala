package superspec.tt

object CoreREPLMain extends CoreREPL {
  override def initialState =
    State(true, emptyNEnv, emptyNEnv, Set())
}

object NatREPLMain extends NatREPL {
  override def initialState =
    State(interactive = true, natVE, natTE, Set())
}

object ProductREPLMain extends ProductREPL {
  override def initialState =
    State(interactive = true, productVE, productTE, Set())
}

object SumREPLMain extends SumREPL {
  override def initialState =
    State(interactive = true, sumVE, sumTE, Set())
}

object ListREPLMain extends ListREPL {
  override def initialState =
    State(interactive = true, listVE, listTE, Set())
}

object EqREPLMain extends EqREPL {
  override def initialState =
    State(interactive = true, eqVE, eqTE, Set())
}

object VectorREPLMain extends VectorREPL {
  override def initialState =
    State(interactive = true, natVE ++ vectorVE, natTE ++ vectorTE, Set())
}

object FinNatREPLMain extends FinNatREPL {
  override def initialState =
    State(interactive = true, natVE ++ finVE, natTE ++ finTE, Set())
}

object FinREPLMain extends FinREPL {
  override def initialState =
    State(interactive = true, finVE, finTE, Set())
}

object TTREPLMain extends CoreREPL with NatREPL with VectorREPL with EqREPL with FinREPL with ListREPL with ProductREPL with SumREPL {
  val te = natTE ++ eqTE ++ vectorTE ++ finTE ++ listTE ++ productTE ++ sumTE
  val ve = natVE ++ eqVE ++ vectorVE ++ finVE ++ listVE ++ productVE ++ sumVE
  override def initialState = State(interactive = true, ve, te, Set())
}

