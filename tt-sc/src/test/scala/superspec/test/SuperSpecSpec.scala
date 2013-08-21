package superspec.test

import superspec.{TTScREPL, TTScREPL2}

class ScSpec extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in examples/sc01.pi") {
    TTScREPL.main(Array("examples/sc01.pi"))
  }
}

class Sc2Spec extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in examples/sc01.tt") {
    TTScREPL2.main(Array("examples/sc01.tt"))
  }
}

class ProofSpec extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in examples/sc02.pi") {
    TTScREPL.main(Array("examples/sc02.pi"))
  }
}

// refactored with assumed vars
class ScSpecWIP extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in examples/sc03.pi") {
    TTScREPL.main(Array("examples/sc03.pi"))
  }
}
