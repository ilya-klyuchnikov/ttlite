package ttlite.core.test

import org.scalatest.matchers.MustMatchers
import org.scalatest.FunSpec

import ttlite.common._
import ttlite.TTREPL

// a lot of boilerplate error checking
class ErrorHandlingSpec extends FunSpec with MustMatchers {
  describe("Error handling of shallow parsing") {
    val root = "examples/test/err/in"
    it("should report parse errors") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/01_lexical.hs")) } must produce [FiledTTLiteError]
      thrown.errorKind must equal("Lexical")
      thrown.file must equal (s"$root/01_lexical.hs")
      thrown.line must equal (2)
      thrown.column must equal (58)
    }
  }

  describe("Error handling of translation") {

    val root = "examples/test/err/meta"

    it("should report unknown binder as incorrect syntax") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/01_binder.hs")) } must produce [FiledTTLiteError]
      thrown.file must equal (s"$root/01_binder.hs")
      thrown.getMessage must startWith("incorrect syntax")
      thrown.origin must equal("(fun (x : Nat) -> x)")
      thrown.line must equal (3)
      thrown.column must equal (10)
    }

    it("should report correct file when an error in an imported module") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/02_import.hs")) } must produce [FiledTTLiteError]
      thrown.file must equal (s"$root/01_binder.hs")
      thrown.getMessage must startWith("incorrect syntax")
      thrown.origin must equal("(fun (x : Nat) -> x)")
      thrown.line must equal (3)
      thrown.column must equal (10)
    }

    it("should report not saturated eliminator") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/03_elim.hs")) } must produce [FiledTTLiteError]
      thrown.file must equal (s"$root/03_elim.hs")
      thrown.getMessage must startWith("incorrect eliminator")
      thrown.origin must startWith("elim")
      thrown.line must equal (3)
      thrown.column must equal (5)
    }

    ignore("should report not saturated constructor application") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/04_ctr.hs")) } must produce [FiledTTLiteError]
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
      val thrown = evaluating { TTREPL.main(Array(s"$root/01_unknown_id.hs")) } must produce [FiledTTLiteError]
      thrown.file must equal (s"$root/01_unknown_id.hs")
      thrown.getMessage must startWith("unknown id")
      thrown.origin must startWith("y")
      thrown.line must equal (2)
      thrown.column must equal (10)
    }

    it("should report error on unknown id in declaration") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/02_unknown_id.hs")) } must produce [FiledTTLiteError]
      thrown.file must equal (s"$root/02_unknown_id.hs")
      thrown.getMessage must startWith("unknown id")
      thrown.origin must startWith("y")
      thrown.line must equal (3)
      thrown.column must equal (13)
    }

    it("should report error on declaration `x : y` when y is not a type") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/03_not_a_type.hs")) } must produce [FiledTTLiteError]
      thrown.file must equal (s"$root/03_not_a_type.hs")
      thrown.getMessage must startWith("expected: Set*")
      thrown.origin must startWith("True")
      thrown.line must equal (1)
      thrown.column must equal (6)
    }

    it("""abs = \ (f : forall (_ : List Nat) . Nat) -> f (forall (_ : Set) . Set)""") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/04_subterm.hs")) } must produce [FiledTTLiteError]
      thrown.file must equal (s"$root/04_subterm.hs")
      thrown.getMessage must startWith("expected: List Nat")
      thrown.origin must equal ("(forall (_ : Set) . Set)")
      thrown.line must equal (2)
      thrown.column must equal (48)
    }

    it("""should restore shallow subterm from path""") {
      val thrown = evaluating { TTREPL.main(Array(s"$root/05_subterm.hs")) } must produce [FiledTTLiteError]
      thrown.file must equal (s"$root/05_subterm.hs")
      thrown.getMessage must startWith("unknown id")
      thrown.origin must equal ("x")
      thrown.line must equal (6)
      thrown.column must equal (40)
    }
  }
}
