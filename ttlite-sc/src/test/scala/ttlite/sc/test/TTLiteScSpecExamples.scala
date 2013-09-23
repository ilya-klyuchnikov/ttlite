package ttlite.sc.test

import ttlite.sc.TTScREPL

class TTLiteScSpecExamples extends org.scalatest.FunSpec {
  describe("TTLiteSc") {
    it ("should prove: Succ x = Succ x") {
      TTScREPL.main(Array("examples/proofs/00.hs"))
    }
    it ("should prove: plus x (plus y z) = plus (plus x y) z") {
      TTScREPL.main(Array("examples/proofs/01.hs"))
    }
    it ("should prove: compose (map f) unit = compose unit f") {
      TTScREPL.main(Array("examples/proofs/02.hs"))
    }
    it ("should prove: append x (append y z) = append (append x y) z") {
      TTScREPL.main(Array("examples/proofs/03.hs"))
    }
    it ("should prove: map (comp f g) xs = (comp (map f)(map g)) xs") {
      TTScREPL.main(Array("examples/proofs/04.hs"))
    }
    it ("should prove: map f (append xs ys) = append (map f xs) (map f ys)") {
      TTScREPL.main(Array("examples/proofs/05.hs"))
    }
    it ("should prove: XXX") {
      TTScREPL.main(Array("examples/proofs/06.hs"))
    }
    it ("should prove: commutativity of AND operation") {
      TTScREPL.main(Array("examples/proofs/07.hs"))
    }

    it ("should process preprint.hs") {
      TTScREPL.main(Array("examples/preprint.hs"))
    }

    it ("should process slides.hs") {
      TTScREPL.main(Array("examples/slides.hs"))
    }

    it ("should process power.hs") {
      TTScREPL.main(Array("examples/power.hs"))
    }
  }

  describe("Coverage Test") {
    it ("ids") {
      TTScREPL.main(Array("examples/tests/ids.hs"))
    }
  }
}
