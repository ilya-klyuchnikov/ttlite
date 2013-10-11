package ttlite.sc.test

import ttlite.sc.TTScREPL

class HoscExamples extends org.scalatest.FunSpec {
  describe("Hosc Examples") {
    it ("1. compose (map f) unit x = compose unit f x") {
      TTScREPL.main(Array("examples/hosc/01.hs"))
    }
    it ("2. compose (map f) join xs = compose join (map (map f)) xs") {
      TTScREPL.main(Array("examples/hosc/02.hs"))
    }
    it ("3. append (map f xs) (map f ys) = map f (append xs ys)") {
      TTScREPL.main(Array("examples/hosc/03.hs"))
    }
    it ("4. filter p (map f xs) = map f (filter (compose p f) xs) - NEED REBUILDING HERE!") {
      //TTScREPL.main(Array("examples/hosc/05.hs"))
    }
    it ("5. map (compose f g) xs = (compose (map f)(map g)) xs") {
      TTScREPL.main(Array("examples/hosc/05.hs"))
    }
    it ("6. rep (append xs ys) zs = compose (rep xs) (rep ys) zs") {
      TTScREPL.main(Array("examples/hosc/06.hs"))
    }
    it ("7. compose abs rep xs = idList xs") {
      TTScREPL.main(Array("examples/hosc/07.hs"))
    }
    it ("8. map (fp (P f g)) (zip (P x y)) = zip (fp (P (map f) (map g)) (P x y)) -- NEED more smart program generator!") {
      //TTScREPL.main(Array("examples/hosc/08.hs"))
    }
    it ("9. append lemma") {
      TTScREPL.main(Array("examples/hosc/09.hs"))
    }
  }
}
