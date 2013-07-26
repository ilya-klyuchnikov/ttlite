package superspec.test

import superspec.TTScREPL

class ScSpec extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in examples/sc01.pi") {
    TTScREPL.main(Array("examples/sc01.pi"))
  }
}

class ProofSpec extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in examples/sc02.pi") {
    TTScREPL.main(Array("examples/sc02.pi"))
  }
}
