package superspec.tt.test

import superspec.tt._

class ReplSpec extends org.scalatest.FunSpec {

  describe("TT REPL should process without errors") {
    it("core") {
      TTREPL.main(Array("examples/core.tt"))
    }
    it("dproduct") {
      TTREPL.main(Array("examples/dproduct.tt"))
    }
    it("nat") {
      TTREPL.main(Array("examples/nat.tt"))
    }
    it("product") {
      TTREPL.main(Array("examples/product.tt"))
    }
    it("sum") {
      TTREPL.main(Array("examples/sum.tt"))
    }
    it("list") {
      TTREPL.main(Array("examples/list.tt"))
    }
    it("eq") {
      TTREPL.main(Array("examples/eq.tt"))
    }
    it("vec") {
      TTREPL.main(Array("examples/vec.tt"))
    }
    it("fin") {
      TTREPL.main(Array("examples/fin.tt"))
    }
    it("misc") {
      TTREPL.main(Array("examples/misc.tt"))
    }
  }
}

