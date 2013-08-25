package superspec.test

import superspec.TTScREPL2

class SuperSpecExamples extends org.scalatest.FunSpec {
  describe("SuperSpec") {
    it ("should prove: Succ x = Succ x") {
      TTScREPL2.main(Array("examples/proofs/00.hs"))
    }
    it ("should prove: plus x (plus y z) = plus (plus x y) z") {
      TTScREPL2.main(Array("examples/proofs/01.hs"))
    }
    it ("should prove: compose (map f) unit = compose unit f") {
      TTScREPL2.main(Array("examples/proofs/02.hs"))
    }
    it ("should prove: append x (append y z) = append (append x y) z") {
      TTScREPL2.main(Array("examples/proofs/03.hs"))
    }
    it ("should prove: map (comp f g) xs = (comp (map f)(map g)) xs") {
      TTScREPL2.main(Array("examples/proofs/04.hs"))
    }
    it ("should prove: map f (append xs ys) = append (map f xs) (map f ys)") {
      TTScREPL2.main(Array("examples/proofs/05.hs"))
    }
  }

  describe("Coverage Test") {
    it ("ids") {
      TTScREPL2.main(Array("examples/tests/ids.hs"))
    }
  }
}
