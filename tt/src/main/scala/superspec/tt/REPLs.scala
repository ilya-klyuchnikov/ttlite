package superspec.tt

object CoreREPLMain extends CoreREPL {
  override def initialState =
    State(true, emptyNEnv, emptyNEnv, Set())
}

object CoreREPLMain2 extends CoreREPL2
object ProductREPLMain2 extends ProductREPL2
object SumREPLMain2 extends SumREPL2
object NatREPLMain2 extends NatREPL2
object ListREPLMain2 extends ListREPL2
object EqREPLMain2 extends EqREPL2
object VectorREPLMain2 extends VectorREPL2
object FinREPLMain2 extends FinREPL2

object TTREPLMain2
  extends CoreREPL2
  with NatREPL2
  with VectorREPL2
  with EqREPL2
  with FinREPL2
  with ListREPL2
  with ProductREPL2
  with SumREPL2

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

object FinREPLMain extends FinREPL {
  override def initialState =
    State(interactive = true, finVE, finTE, Set())
}

object TTREPLMain extends CoreREPL with NatREPL with VectorREPL with EqREPL with FinREPL with ListREPL with ProductREPL with SumREPL {
  val te = natTE ++ eqTE ++ vectorTE ++ finTE ++ listTE ++ productTE ++ sumTE
  val ve = natVE ++ eqVE ++ vectorVE ++ finVE ++ listVE ++ productVE ++ sumVE
  override def initialState = State(interactive = true, ve, te, Set())
}
