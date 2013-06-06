package tapl

object NatREPLMain extends NatREPL {
  def main(args: Array[String]) {
    loop(new LambdaPIInterpreter{}, State(true, natVE, natTE))
  }
}
