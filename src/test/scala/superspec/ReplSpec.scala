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

  describe("List REPL should process `tt/ex05_list.pi` without errors") {
    ListREPLMain.main(Array("tt/ex05_list.pi"))
  }

  describe("Eq REPL should process `tt/ex06_eq.pi` without errors") {
    EqREPLMain.main(Array("tt/ex06_eq.pi"))
  }

  describe("Vector REPL should process `tt/ex07_vec.pi` without errors") {
    VectorREPLMain.main(Array("tt/ex07_vec.pi"))
  }

  describe("Fin REPL should process `tt/ex08_finn.pi` without errors") {
    FinREPLMain.main(Array("tt/ex08_finn.pi"))
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
