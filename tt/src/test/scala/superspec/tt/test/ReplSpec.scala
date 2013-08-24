package superspec.tt.test

import superspec.tt._

class ReplSpec2 extends org.scalatest.FunSpec {

  describe("Core REPL should process `tests/ex01_core.pi` without errors") {
    TTREPLMain2.main(Array("tests/ex01_core.pi"))
  }

  describe("DProduct REPL should process `tests/ex01_product.tt` without errors") {
    TTREPLMain2.main(Array("tests/ex01_product.tt"))
  }

  describe("Nat REPL should process `tests/ex02_nat.pi` without errors") {
    TTREPLMain2.main(Array("tests/ex02_nat.pi"))
  }

  describe("Product REPL should process `tests/ex03_product.pi` without errors") {
    TTREPLMain2.main(Array("tests/ex03_product.pi"))
  }


  describe("Sum REPL should process `tests/ex04_sum.pi` without errors") {
    TTREPLMain2.main(Array("tests/ex04_sum.pi"))
  }


  describe("List REPL should process `tests/ex05_list.pi` without errors") {
    TTREPLMain2.main(Array("tests/ex05_list.pi"))
  }

  describe("Eq REPL should process `tests/ex06_eq.pi` without errors") {
    TTREPLMain2.main(Array("tests/ex06_eq.pi"))
  }


  describe("Vector REPL should process `tests/ex07_vec.pi` without errors") {
    TTREPLMain2.main(Array("tests/ex07_vec.pi"))
  }

  describe("Fin REPL should process `tests/ex09_fin.pi` without errors") {
    TTREPLMain2.main(Array("tests/ex09_fin.pi"))
  }

  describe("All REPL should process `tests/ex10_tt.pi` without errors") {
    TTREPLMain2.main(Array("tests/ex10_tt.pi"))
  }

}

