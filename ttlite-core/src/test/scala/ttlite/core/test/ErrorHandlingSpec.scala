package ttlite.core.test

import org.scalatest.Matchers
import org.scalatest.FunSpec

import ttlite.common._
import ttlite.TTREPL

// a lot of boilerplate error checking
class ErrorHandlingSpec extends FunSpec with Matchers {
  describe("Error handling of shallow parsing") {
    val root = "examples/test/err/in"
    it("should report parse errors") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/01_lexical.hs")) }
      thrown.errorKind should equal("Lexical")
      thrown.file should equal (s"$root/01_lexical.hs")
      thrown.line should equal (2)
      thrown.column should equal (58)
    }
  }

  describe("Error handling of translation") {

    val root = "examples/test/err/meta"

    it("should report unknown binder as incorrect syntax") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/01_binder.hs")) }
      thrown.file should equal (s"$root/01_binder.hs")
      thrown.getMessage should startWith("incorrect syntax")
      thrown.origin should equal("(fun (x : Nat) -> x)")
      thrown.line should equal (3)
      thrown.column should equal (10)
    }

    it("should report correct file when an error in an imported module") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/02_import.hs")) }
      thrown.file should equal (s"$root/01_binder.hs")
      thrown.getMessage should startWith("incorrect syntax")
      thrown.origin should equal("(fun (x : Nat) -> x)")
      thrown.line should equal (3)
      thrown.column should equal (10)
    }

    it("should report incorrect eliminator") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/03_elim.hs")) }
      thrown.file should equal (s"$root/03_elim.hs")
      thrown.getMessage should startWith("incorrect eliminator")
      thrown.origin should startWith("elim")
      thrown.line should equal (3)
      thrown.column should equal (5)
    }

    ignore("should report not saturated constructor application") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/04_ctr.hs")) }
      thrown.file should equal (s"$root/04_ctr.hs")
      thrown.getMessage should startWith("incorrect constructor application")
      thrown.origin should startWith("Succ")
      thrown.line should equal (2)
      thrown.column should equal (5)
    }
  }

  describe("Error handling of duplicate ids") {
    val root = "examples/test/err/dup"
    it("should report duplicate id in let declaration") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/01_let.hs")) }
      thrown.file should equal (s"$root/01_let.hs")
      thrown.getMessage should startWith("Identifier x is already")
      thrown.origin should startWith("x")
      thrown.line should equal (3)
      thrown.column should equal (1)
    }

    it("should report duplicate id in typed-let declaration") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/02_typed_let.hs")) }
      thrown.file should equal (s"$root/02_typed_let.hs")
      thrown.getMessage should startWith("Identifier y is already")
      thrown.origin should startWith("y")
      thrown.line should equal (3)
      thrown.column should equal (1)
    }

    it("should report duplicate id for assumption") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/03_assume.hs")) }
      thrown.file should equal (s"$root/03_assume.hs")
      thrown.getMessage should startWith("Identifier $z is already")
      thrown.origin should startWith("$z")
      thrown.line should equal (3)
      thrown.column should equal (1)
    }
  }

  describe("Basic type-checking errors") {
    val root = "examples/test/err/type"

    it("should report error on unknown id in definition") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/01_unknown_id.hs")) }
      thrown.file should equal (s"$root/01_unknown_id.hs")
      thrown.getMessage should startWith("unknown id")
      thrown.origin should startWith("y")
      thrown.line should equal (2)
      thrown.column should equal (10)
    }

    it("should report error on unknown id in declaration") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/02_unknown_id.hs")) }
      thrown.file should equal (s"$root/02_unknown_id.hs")
      thrown.getMessage should startWith("unknown id")
      thrown.origin should startWith("y")
      thrown.line should equal (3)
      thrown.column should equal (13)
    }

    it("should report error on declaration `x : y` when y is not a type") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/03_not_a_type.hs")) }
      thrown.file should equal (s"$root/03_not_a_type.hs")
      thrown.getMessage should startWith("expected: Set*")
      thrown.origin should startWith("True")
      thrown.line should equal (1)
      thrown.column should equal (6)
    }

    it("""abs = \ (f : forall (_ : List Nat) . Nat) -> f (forall (_ : Set) . Set)""") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/04_subterm.hs")) }
      thrown.file should equal (s"$root/04_subterm.hs")
      thrown.getMessage should startWith("expected: List Nat")
      thrown.origin should equal ("(forall (_ : Set) . Set)")
      thrown.line should equal (2)
      thrown.column should equal (48)
    }

    it("""should restore shallow subterm from path""") {
      val thrown = the[FiledTTLiteError] thrownBy { TTREPL.main(Array(s"$root/05_subterm.hs")) }
      thrown.file should equal (s"$root/05_subterm.hs")
      thrown.getMessage should startWith("unknown id")
      thrown.origin should equal ("x")
      thrown.line should equal (6)
      thrown.column should equal (40)
    }
  }
}
