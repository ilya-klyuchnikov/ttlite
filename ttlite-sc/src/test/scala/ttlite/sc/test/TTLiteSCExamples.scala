package ttlite.sc.test

import org.scalatest.funspec._

import ttlite.TTScREPL

class TTLiteSCExamples extends AnyFunSpec {
  describe("Hosc Examples") {
    it("01. compose (map f) unit x = compose unit f x") {
      TTScREPL.main(Array("examples/hosc/01.hs"))
    }
    it("02. compose (map f) join xs = compose join (map (map f)) xs") {
      TTScREPL.main(Array("examples/hosc/02.hs"))
    }
    it("03. append (map f xs) (map f ys) = map f (append xs ys)") {
      TTScREPL.main(Array("examples/hosc/03.hs"))
    }
    // needs a generalization
    // case (p x) of ... ->
    // let y = p x in case y of ...
    ignore("04. filter p (map f xs) = map f (filter (compose p f) xs)") {
      TTScREPL.main(Array("examples/hosc/05.hs"))
    }
    it("05. map (compose f g) xs = (compose (map f)(map g)) xs") {
      TTScREPL.main(Array("examples/hosc/05.hs"))
    }
    it("06. rep (append xs ys) zs = compose (rep xs) (rep ys) zs") {
      TTScREPL.main(Array("examples/hosc/06.hs"))
    }
    it("07. compose abs rep xs = idList xs") {
      TTScREPL.main(Array("examples/hosc/07.hs"))
    }
    // it can be proved via folding on renaming,
    // however, we need a more smart program generator here
    // because there will be folding after 2 steps of elimination,
    // but these eliminations are for different variables,
    // so codegen should introduce "higher-order" eliminator
    ignore("08. map (fp (P f g)) (zip (P x y)) = zip (fp (P (map f) (map g)) (P x y))") {
      TTScREPL.main(Array("examples/hosc/08.hs"))
    }
    it("09. append lemma") {
      TTScREPL.main(Array("examples/hosc/09.hs"))
    }
    it("10. plus x (plus y z) = plus (plus x y) z") {
      TTScREPL.main(Array("examples/hosc/10.hs"))
    }
    it("11. append x (append y z) = append (append x y) z") {
      TTScREPL.main(Array("examples/hosc/11.hs"))
    }
    it("12. unchurch (churchPlus (church x) (church y)) = nat_id (plus x y)") {
      TTScREPL.main(Array("examples/hosc/12.hs"))
    }
  }

  describe("Misc Examples") {
    it("ids.hs - smoke test: supercompiling identities") {
      TTScREPL.main(Array("examples/misc-sc/ids.hs"))
    }
    // see paper submitted to PEPM'14 for explanation of the problem
    it("kmp.hs") {
      TTScREPL.main(Array("examples/misc-sc/kmp.hs"))
    }
    it("kmp2.hs") {
      TTScREPL.main(Array("examples/misc-sc/kmp.hs"))
    }
    it("preprint.hs - example from preprint.hs") {
      TTScREPL.main(Array("examples/misc-sc/preprint.hs"))
    }
  }

  describe("Experiments") {
    it("01.hs") {
      TTScREPL.main(Array("examples/experiments/01.hs"))
    }
  }
}
