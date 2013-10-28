package ttlite.core.test

import org.scalatest.matchers.MustMatchers
import org.scalatest.FunSpec

import ttlite.core._

// a lot of boilerplate error checking
class ErrorHandlingSpec extends FunSpec with MustMatchers {
  describe("Error handling of translation") {

    val root = "examples/test/err/meta"

    it("should report unknown binder as incorrect syntax") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/01_binder.hs")) } must produce [TranslationError]
      thrown.file must equal (s"$root/01_binder.hs")
      thrown.getMessage must startWith("incorrect syntax")
      thrown.origin must equal("(fun (x : Nat) -> x)")
      thrown.line must equal (3)
      thrown.column must equal (10)
    }

    it("should report correct file when an error in an imported module") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/02_import.hs")) } must produce [TranslationError]
      thrown.file must equal (s"$root/01_binder.hs")
      thrown.getMessage must startWith("incorrect syntax")
      thrown.origin must equal("(fun (x : Nat) -> x)")
      thrown.line must equal (3)
      thrown.column must equal (10)
    }

    it("should report not saturated eliminator") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/03_elim.hs")) } must produce [TranslationError]
      thrown.file must equal (s"$root/03_elim.hs")
      thrown.getMessage must startWith("incorrect eliminator")
      thrown.origin must startWith("elim")
      thrown.line must equal (3)
      thrown.column must equal (5)
    }

    ignore("should report not saturated constructor application") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/04_ctr.hs")) } must produce [TranslationError]
      thrown.file must equal (s"$root/04_ctr.hs")
      thrown.getMessage must startWith("incorrect constructor application")
      thrown.origin must startWith("Succ")
      thrown.line must equal (2)
      thrown.column must equal (5)
    }
  }

  describe("Basic type-checking errors") {
    val root = "examples/test/err/type"

    it("should report error on unknown id in definition") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/01_unknown_id.hs")) } must produce [TypeError]
      thrown.file must equal (s"$root/01_unknown_id.hs")
      thrown.getMessage must startWith("unknown id")
      thrown.origin must startWith("y")
      thrown.line must equal (2)
      thrown.column must equal (10)
    }

    it("should report error on unknown id in declaration") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/02_unknown_id.hs")) } must produce [TypeError]
      thrown.file must equal (s"$root/02_unknown_id.hs")
      thrown.getMessage must startWith("unknown id")
      thrown.origin must startWith("y")
      thrown.line must equal (3)
      thrown.column must equal (13)
    }

    it("should report error on declaration `x : y` when y is not a type") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/03_not_a_type.hs")) } must produce [TypeError]
      thrown.file must equal (s"$root/03_not_a_type.hs")
      thrown.getMessage must startWith("expected: Set*")
      thrown.origin must startWith("True")
      thrown.line must equal (1)
      thrown.column must equal (6)
    }
  }
}
