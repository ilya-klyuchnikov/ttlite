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

  describe("Export to Idris") {
    it("core.hs") {
      checkIdris("core")
    }
    it("nat.hs") {
      checkIdris("nat")
    }
    it("sigma.hs") {
      checkIdris("sigma")
    }
    it("fin.hs") {
      checkIdris("fin")
    }
    // Idris: https://github.com/idris-lang/Idris-dev/issues/741
    ignore("id.hs") {
      checkIdris("id")
    }
    it("list.hs") {
      checkIdris("list")
    }
    it("pair.hs") {
      checkIdris("pair")
    }
    it("sum.hs") {
      checkIdris("sum")
    }
    it("map.hs") {
      checkIdris("map")
    }
    it("niter.hs") {
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

  val idrisCmd = "../Idris-dev/dist/build/idris/idris"

  def checkIdris(module : String) {
    import scala.sys.process._
    TTREPL.main(Array(s"examples/test/idris/${module}.hs"))
    val cmd = s"${idrisCmd} --noprelude --check -i generated/ -i syntax/ generated/${module}.idr"
    info(cmd)
    val exitCode = cmd.!
    exitCode shouldBe 0
  }
}
