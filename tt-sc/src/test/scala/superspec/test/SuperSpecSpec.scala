package superspec.test

import superspec.TTScREPL2

class Sc2Spec extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in examples/sc01.tt") {
    TTScREPL2.main(Array("examples/sc01.tt"))
  }
}

class Proof2Spec extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in examples/sc02.tt") {
    TTScREPL2.main(Array("examples/sc02.tt"))
  }
}

class Sc2SpecWIP extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in examples/sc03.tt") {
    TTScREPL2.main(Array("examples/sc03.tt"))
  }
}

