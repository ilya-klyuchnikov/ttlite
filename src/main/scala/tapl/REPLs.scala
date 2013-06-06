package tapl

object AllREPLMain extends LambdaPiREPL with NatREPL with EqREPL {
  val te = natTE ++ eqTE
  val ve = natVE ++ eqVE
  def main(args: Array[String]) {
    loop(new LambdaPIInterpreter{}, State(true, ve, te))
  }
}
