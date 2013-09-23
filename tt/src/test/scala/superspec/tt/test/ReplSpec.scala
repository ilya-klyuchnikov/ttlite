package superspec.tt.test

import superspec.tt._

class ReplSpec extends org.scalatest.FunSpec {

  describe("TT REPL should process without errors") {
    it("core") {
      TTREPL.main(Array("examples/core.hs"))
    }
    it("dproduct") {
      TTREPL.main(Array("examples/dproduct.hs"))
    }
    it("nat") {
      TTREPL.main(Array("examples/nat.hs"))
    }
    it("product") {
      TTREPL.main(Array("examples/product.hs"))
    }
    it("sum") {
      TTREPL.main(Array("examples/sum.hs"))
    }
    it("list") {
      TTREPL.main(Array("examples/list.hs"))
    }
    it("id") {
      TTREPL.main(Array("examples/id.hs"))
    }
    it("vec") {
      TTREPL.main(Array("examples/vec.hs"))
    }
    it("fin") {
      TTREPL.main(Array("examples/fin.hs"))
    }
    it("wnat") {
      TTREPL.main(Array("examples/wnat.hs"))
    }
    it("wlist") {
      TTREPL.main(Array("examples/wlist.hs"))
    }
    it("logic") {
      TTREPL.main(Array("examples/logic.hs"))
    }
    it("misc") {
      TTREPL.main(Array("examples/misc.hs"))
    }
  }
}

