package superspec

import org.scalatest.FunSpec

import superspec.tt._

class ReplSpec extends FunSpec {

  describe("Lambda Pi REPL should process `tt/ex01_core.pi` without errors") {
    CoreREPLMain.main(Array("tt/ex01_core.pi"))
  }

  describe("Nat REPL should process prelude.nat without errors") {
    NatREPLMain.main(Array("tt/ex02_nat.pi"))
  }
  /*
  describe("All REPL should process prelude.all and lists.pi without errors") {
    REPLMain.main(Array("prelude.all"))
  }

  describe("ScREPL should supercompile all tasks in tt/sc01.pi") {
    TTScREPL.main(Array("tt/sc01.pi"))
  }
  */
}
