package superspec

import org.scalatest.FunSpec

import superspec.tt._

class ReplSpec extends FunSpec {

  describe("Lambda Pi REPL should process prelude.lp without errors") {
    CoreREPLMain.main(Array("prelude.lp"))
  }

  describe("Nat REPL should process prelude.nat without errors") {
    NatREPLMain.main(Array("prelude.nat"))
  }

  describe("All REPL should process prelude.all and lists.pi without errors") {
    REPLMain.main(Array("prelude.all"))
  }

  describe("ScREPL should supercompile all tasks in tt/sc01.pi") {
    TTScREPL.main(Array("tt/sc01.pi"))
  }
}
