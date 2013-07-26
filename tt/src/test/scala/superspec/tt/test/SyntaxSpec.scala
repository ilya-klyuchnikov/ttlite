package superspec.tt.test

import superspec.tt._

class SyntaxSpec extends org.scalatest.FunSpec {

  val coreRepl = new CoreREPL with CoreSubst {
    def initialState: State = State(interactive = false, emptyNEnv, emptyNEnv, Set())

    def parseTerm(s: String) =
      int.parseIO(int.iParse, s).get
  }

  import coreRepl._

  def testSubOK(s1: String, s2: String) =
    it(s"$s1, $s2 - should find a substitution") {

    val ta = parseTerm(s1)
    val tb = parseTerm(s2)

    val sub = findSubst(ta, tb)
    assert(sub.isDefined)
    val tc = applySubst(ta, sub.get)
    assert(tb === tc)
  }

  def testSubNO(s1: String, s2: String) =
    it(s"$s1, $s2 - should NOT find a substitution") {
      val ta = parseTerm(s1)
      val tb = parseTerm(s2)

      val sub = findSubst(ta, tb)
      assert(sub.isEmpty)
    }

  describe("the simplest substitutions") {

    testSubOK("<1> <2>", "<3> <4>")
    testSubNO("<1> <1>", "<3> <4>")
    testSubOK("f <1>", "f <2>")
    testSubNO("f x", "f y")

    testSubOK("forall x :: Nat. x -> Nat", "forall y :: Nat. y -> Nat")
    testSubOK("forall x :: Nat. x -> <1>", "forall y :: Nat. y -> <2>")

    testSubNO("forall x :: Bool. x -> Nat", "forall y :: Nat. y -> Nat")
  }
}
