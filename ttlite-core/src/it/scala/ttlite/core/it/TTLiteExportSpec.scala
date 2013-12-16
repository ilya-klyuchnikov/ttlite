package ttlite.core.it

import ttlite.TTREPL

class TTLiteExportSpec extends org.scalatest.FunSpec with org.scalatest.Matchers {
  describe("Export to Agda") {
    it("core.hs") {
      checkAgda("core")
    }
    it("nat.hs") {
      checkAgda("nat")
    }
    it("sigma.hs") {
      checkAgda("sigma")
    }
    it("fin.hs") {
      checkAgda("fin")
    }
    it("id.hs") {
      checkAgda("id")
    }
    it("list.hs") {
      checkAgda("list")
    }
    it("pair.hs") {
      checkAgda("pair")
    }
    it("sum.hs") {
      checkAgda("sum")
    }
    it("map.hs") {
      checkAgda("map")
    }
    it("niter.hs") {
      checkAgda("niter")
    }
  }

  // current export mostly doesn't work because of Idris bug:
  // https://github.com/idris-lang/Idris-dev/issues/733
  // such tests are ignored for now
  describe("Export to Idris") {
    it("core.hs") {
      checkIdris("core")
    }
    it("nat.hs") {
      checkIdris("nat")
    }
    ignore("sigma.hs") {
      checkIdris("sigma")
    }
    ignore("fin.hs") {
      checkIdris("fin")
    }
    ignore("id.hs") {
      checkIdris("id")
    }
    ignore("list.hs") {
      checkIdris("list")
    }
    ignore("pair.hs") {
      checkIdris("pair")
    }
    ignore("sum.hs") {
      checkIdris("sum")
    }
    ignore("map.hs") {
      checkIdris("map")
    }
    ignore("niter.hs") {
      checkIdris("niter")
    }
  }

  describe("Export to Agda with assumed variables in correct order") {
    it("assumed.hs") {
      checkAgda("assumed")
    }
  }

  describe("Export to Idris with assumed variables in correct order") {
    it("assumed.hs") {
      checkIdris("assumed")
    }
  }

  def checkAgda(module : String) {
    import scala.sys.process._
    TTREPL.main(Array(s"examples/test/agda/${module}.hs"))
    val exitCode = s"agda -i generated/ -i syntax/ generated/${module}.agda".!
    exitCode shouldBe 0
  }

  def checkIdris(module : String) {
    import scala.sys.process._
    TTREPL.main(Array(s"examples/test/idris/${module}.hs"))
    val exitCode = s"idris --noprelude --check -i generated/ -i syntax/ generated/${module}.idr".!
    exitCode shouldBe 0
  }
}
