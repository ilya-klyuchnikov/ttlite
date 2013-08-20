package superspec.tt.test

import superspec.tt._

class ReplSpec extends org.scalatest.FunSpec {

  describe("Core REPL should process `examples/ex01_core.pi` without errors") {
    CoreREPLMain.main(Array("examples/ex01_core.pi"))
  }

  describe("Nat REPL should process `examples/ex02_nat.pi` without errors") {
    NatREPLMain.main(Array("examples/ex02_nat.pi"))
  }

  describe("Product REPL should process `examples/ex03_product.pi` without errors") {
    ProductREPLMain.main(Array("examples/ex03_product.pi"))
  }

  describe("Sum REPL should process `examples/ex04_sum.pi` without errors") {
    SumREPLMain.main(Array("examples/ex04_sum.pi"))
  }

  describe("List REPL should process `examples/ex05_list.pi` without errors") {
    ListREPLMain.main(Array("examples/ex05_list.pi"))
  }

  describe("Eq REPL should process `examples/ex06_eq.pi` without errors") {
    EqREPLMain.main(Array("examples/ex06_eq.pi"))
  }

  describe("Vector REPL should process `examples/ex07_vec.pi` without errors") {
    VectorREPLMain.main(Array("examples/ex07_vec.pi"))
  }

  describe("Fin REPL should process `examples/ex09_fin.pi` without errors") {
    FinREPLMain.main(Array("examples/ex09_fin.pi"))
  }

  describe("All REPL should process `examples/ex10_tt.pi` without errors") {
    TTREPLMain.main(Array("examples/ex10_tt.pi"))
  }

  describe("All REPL should process `tutorial/01.tt` without errors") {
    TTREPLMain.main(Array("tutorial/01.tt"))
  }


  describe("All REPL should process `tutorial/03.tt` without errors") {
    TTREPLMain.main(Array("tutorial/03.tt"))
  }

  /*
  describe("All REPL should process `tutorial/04.tt` without errors") {
    TTREPLMain.main(Array("tutorial/04.tt"))
  }
  */

}

class ReplSpec2 extends org.scalatest.FunSpec {

  describe("Core REPL should process `examples/ex01_core.pi` without errors") {
    CoreREPLMain2.main(Array("examples/ex01_core.pi"))
  }

  describe("Nat REPL should process `examples/ex02_nat.pi` without errors") {
    NatREPLMain2.main(Array("examples/ex02_nat.pi"))
  }

  describe("Product REPL should process `examples/ex03_product.pi` without errors") {
    ProductREPLMain2.main(Array("examples/ex03_product.pi"))
  }

  describe("Sum REPL should process `examples/ex04_sum.pi` without errors") {
    SumREPLMain2.main(Array("examples/ex04_sum.pi"))
  }

  describe("List REPL should process `examples/ex05_list.pi` without errors") {
    ListREPLMain2.main(Array("examples/ex05_list.pi"))
  }

  describe("Eq REPL should process `examples/ex06_eq.pi` without errors") {
    EqREPLMain2.main(Array("examples/ex06_eq.pi"))
  }

  describe("Vector REPL should process `examples/ex07_vec.pi` without errors") {
    VectorREPLMain2.main(Array("examples/ex07_vec.pi"))
  }

  describe("Fin REPL should process `examples/ex09_fin.pi` without errors") {
    FinREPLMain2.main(Array("examples/ex09_fin.pi"))
  }

  describe("All REPL should process `examples/ex10_tt.pi` without errors") {
    TTREPLMain2.main(Array("examples/ex10_tt.pi"))
  }
}

