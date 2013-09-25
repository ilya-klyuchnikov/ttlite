package ttlite.core.test

import ttlite.core.TTREPL

class ArrayRulesSpec extends org.scalatest.FunSpec {

  describe("TT REPL should process without errors") {
    it("monoid") {
      TTREPL.main(Array("examples/rules/monoid.hs"))
    }
    it("rule01") {
      TTREPL.main(Array("examples/rules/rule01.hs"))
    }
  }
}
