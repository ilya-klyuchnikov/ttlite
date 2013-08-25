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
    it ("dproduct") {
      TTScREPL2.main(Array("examples/tests/dproduct.tt"))
    }
    it ("sum") {
      TTScREPL2.main(Array("examples/tests/sum.tt"))
    }
    it ("eq") {
      TTScREPL2.main(Array("examples/tests/eq.tt"))
    }
    it ("list") {
      TTScREPL2.main(Array("examples/tests/list.tt"))
    }
    it ("nat") {
      TTScREPL2.main(Array("examples/tests/nat.tt"))
    }
    it ("product") {
      TTScREPL2.main(Array("examples/tests/product.tt"))
    }
    it ("fin") {
      TTScREPL2.main(Array("examples/tests/fin.tt"))
    }
  }
}
