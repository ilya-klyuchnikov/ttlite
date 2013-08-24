package superspec.test

import superspec.TTScREPL2

class SuperSpecExamples extends org.scalatest.FunSpec {
  describe("SuperSpec") {
    it ("should prove: Succ x = Succ x") {
      TTScREPL2.main(Array("examples/proofs/00.tt"))
    }
    it ("should prove: plus x (plus y z) = plus (plus x y) z") {
      TTScREPL2.main(Array("examples/proofs/01.tt"))
    }
    it ("should prove: compose (map f) unit = compose unit f") {
      TTScREPL2.main(Array("examples/proofs/02.tt"))
    }
    it ("should prove: append x (append y z) = append (append x y) z") {
      TTScREPL2.main(Array("examples/proofs/03.tt"))
    }
    it ("should prove: map (comp f g) xs = (comp (map f)(map g)) xs") {
      TTScREPL2.main(Array("examples/proofs/04.tt"))
    }
    it ("should prove: map f (append xs ys) = append (map f xs) (map f ys)") {
      TTScREPL2.main(Array("examples/proofs/05.tt"))
    }
  }

  describe("Coverage Test") {
    it ("coverage") {
      TTScREPL2.main(Array("examples/tests/coverage.tt"))
    }
  }
}

/*
class Sc2Spec extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in tests/sc01.tt") {
    TTScREPL2.main(Array("tests/sc01.tt"))
  }
}

class Proof2Spec extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in tests/sc02.tt") {
    TTScREPL2.main(Array("tests/sc02.tt"))
  }
}

class Sc2SpecWIP extends org.scalatest.FunSpec {
  describe("ScREPL should supercompile all tasks in tests/sc03.tt") {
    TTScREPL2.main(Array("tests/sc03.tt"))
  }
}
*/
