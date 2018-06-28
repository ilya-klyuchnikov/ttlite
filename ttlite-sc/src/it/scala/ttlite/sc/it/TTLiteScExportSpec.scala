package ttlite.sc.it

import org.scalatest.Matchers
import ttlite.TTScREPL

class TTLiteScExportSpec extends org.scalatest.FunSpec with Matchers {
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

  describe("Export to Coq") {
    it("ids_sc.hs") {
      checkCoq("ids_sc")
    }
    it("hosc01.hs") {
      checkCoq("hosc01")
    }
    it("hosc02.hs") {
      checkCoq("hosc02")
    }
    it("hosc03.hs") {
      checkCoq("hosc03")
    }
    it("hosc05.hs") {
      checkCoq("hosc05")
    }
    it("hosc06.hs") {
      checkCoq("hosc06")
    }
    it("hosc07.hs") {
      checkCoq("hosc07")
    }
    it("hosc09.hs") {
      checkCoq("hosc09")
    }
    it("hosc10.hs") {
      checkCoq("hosc10")
    }
    it("hosc11.hs") {
      checkCoq("hosc11")
    }
    it("hosc12.hs") {
      checkCoq("hosc12")
    }
  }

  describe("Export to Idris") {
    it("ids_sc.hs") {
      checkIdris("ids_sc")
    }
    it("hosc01.hs") {
      checkIdris("hosc01")
    }
    it("hosc02.hs") {
      checkIdris("hosc02")
    }
    it("hosc03.hs") {
      checkIdris("hosc03")
    }
    it("hosc05.hs") {
      checkIdris("hosc05")
    }
    it("hosc06.hs") {
      checkIdris("hosc06")
    }
    it("hosc07.hs") {
      checkIdris("hosc07")
    }
    it("hosc09.hs") {
      checkIdris("hosc09")
    }
    it("hosc10.hs") {
      checkIdris("hosc10")
    }
    it("hosc11.hs") {
      checkIdris("hosc11")
    }
    it("hosc12.hs") {
      checkIdris("hosc12")
    }
  }

  def checkAgda(module : String) {
    import scala.sys.process._
    TTScREPL.main(Array(s"examples/test/agda-sc/${module}.hs"))
    val cmd = s"agda -v 0 -i generated/ -i syntax/ generated/${module}.agda"
    info(cmd)
    val exitCode = cmd.!
    exitCode shouldBe 0
  }

  def checkCoq(module : String) {
    import scala.sys.process._
    TTScREPL.main(Array(s"examples/test/coq-sc/${module}.hs"))
    val cmd = s"coqc generated/${module}.v"
    info(cmd)
    val exitCode = cmd.!
    exitCode shouldBe 0
  }

  val idrisCmd = "idris"

  def checkIdris(module : String) {
    import scala.sys.process._
    TTScREPL.main(Array(s"examples/test/idris-sc/${module}.hs"))
    val cmd = s"${idrisCmd} --noprelude --check --allow-capitalized-pattern-variables -i generated/ -i syntax/ generated/${module}.idr"
    info(cmd)
    val exitCode = cmd.!
    exitCode shouldBe 0
  }
}
