package superspec

import superspec.tt._

class ReplSpec extends org.scalatest.FunSpec {

  describe("Core REPL should process `tt/ex01_core.pi` without errors") {
    CoreREPLMain.main(Array("tt/ex01_core.pi"))
  }

  describe("Nat REPL should process `tt/ex02_nat.pi` without errors") {
    NatREPLMain.main(Array("tt/ex02_nat.pi"))
  }

  describe("Product REPL should process `tt/ex03_product.pi` without errors") {
    ProductREPLMain.main(Array("tt/ex03_product.pi"))
  }

  describe("Sum REPL should process `tt/ex04_sum.pi` without errors") {
    SumREPLMain.main(Array("tt/ex04_sum.pi"))
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
