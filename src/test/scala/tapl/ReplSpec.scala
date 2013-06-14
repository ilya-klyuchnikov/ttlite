package tapl

import org.scalatest.FunSpec

import tapl.lambda._

class ReplSpec extends FunSpec {
  describe("Lambda REPL should process prelude.st without errors") {
    LambdaREPL.main(Array("prelude.st"))
  }

  describe("Lambda Pi REPL should process prelude.lp without errors") {
    LambdaPiREPLMain.main(Array("prelude.lp"))
  }

  describe("Nat REPL should process prelude.nat without errors") {
    NatREPLMain.main(Array("prelude.nat"))
  }

  describe("All REPL should process prelude.all and lists.pi without errors") {
    AllREPLMain.main(Array("prelude.all", "lists.pi"))
  }
}
