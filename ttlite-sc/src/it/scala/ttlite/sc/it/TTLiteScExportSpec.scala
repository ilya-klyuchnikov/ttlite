package ttlite.sc.it

import org.scalatest.matchers.MustMatchers
import ttlite.sc.TTScREPL

class TTLiteScExportSpec extends org.scalatest.FunSpec with MustMatchers {
  describe("Export to Agda") {
    it("ids_sc.hs") {
      checkAgda("ids_sc")
    }
    it("hosc01.hs") {
      checkAgda("hosc01")
    }
    it("hosc02.hs") {
      checkAgda("hosc02")
    }
    it("hosc03.hs") {
      checkAgda("hosc03")
    }
    it("hosc05.hs") {
      checkAgda("hosc05")
    }
    it("hosc06.hs") {
      checkAgda("hosc06")
    }
    it("hosc07.hs") {
      checkAgda("hosc07")
    }
    it("hosc09.hs") {
      checkAgda("hosc09")
    }
    it("hosc10.hs") {
      checkAgda("hosc10")
    }
    it("hosc11.hs") {
      checkAgda("hosc11")
    }
    it("hosc12.hs") {
      checkAgda("hosc12")
    }
  }

  def checkAgda(module : String) {
    import scala.sys.process._
    TTScREPL.main(Array(s"examples/test/agda-sc/${module}.hs"))
    val exitCode = s"agda -i agda/ -i doc/ agda/${module}.agda".!
    exitCode mustBe 0
  }
}
