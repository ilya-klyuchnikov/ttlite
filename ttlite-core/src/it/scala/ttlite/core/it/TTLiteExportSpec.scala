package ttlite.core.it

import org.scalatest.funspec._
import org.scalatest.matchers._

import ttlite.TTREPL

class TTLiteExportSpec extends AnyFunSpec with should.Matchers {
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
    it("assumed.hs") {
      checkAgda("assumed")
    }
    it("misc_list_gen_rec") {
      checkAgda("misc_list_gen_rec")
    }
    it("vec.hs") {
      checkAgda("vec")
    }
    it("w.hs") {
      checkAgda("w")
    }
  }

  describe("Export to Coq") {
    it("core.hs") {
      checkCoq("core")
    }
    it("nat.hs") {
      checkCoq("nat")
    }
    it("sigma.hs") {
      checkCoq("sigma")
    }
    it("fin.hs") {
      checkCoq("fin")
    }
    it("id.hs") {
      checkCoq("id")
    }
    it("list.hs") {
      checkCoq("list")
    }
    it("pair.hs") {
      checkCoq("pair")
    }
    it("sum.hs") {
      checkCoq("sum")
    }
    it("map.hs") {
      checkCoq("map")
    }
    it("niter.hs") {
      checkCoq("niter")
    }
    it("assumed.hs") {
      checkCoq("assumed")
    }
    it("vec.hs") {
      checkCoq("vec")
    }
    it("w.hs") {
      checkCoq("w")
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
    it("id.hs") {
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
    it("assumed.hs") {
      checkIdris("assumed")
    }
    it("vec.hs") {
      checkIdris("vec")
    }
    it("w.hs") {
      checkIdris("w")
    }
  }

  def checkAgda(module: String): Unit = {
    import scala.sys.process._
    TTREPL.main(Array(s"examples/test/agda/${module}.hs"))
    val cmd = s"agda -v 0 -i generated/ -i syntax/ generated/${module}.agda"
    info(cmd)
    val exitCode = cmd.!
    exitCode shouldBe 0
  }

  def checkCoq(module: String): Unit = {
    import scala.sys.process._
    TTREPL.main(Array(s"examples/test/coq/${module}.hs"))
    val cmd = s"coqc generated/${module}.v"
    info(cmd)
    val exitCode = cmd.!
    exitCode shouldBe 0
  }

  val idrisCmd = "idris"

  def checkIdris(module: String): Unit = {
    import scala.sys.process._
    TTREPL.main(Array(s"examples/test/idris/${module}.hs"))
    val cmd =
      s"${idrisCmd} --noprelude --check --allow-capitalized-pattern-variables -i generated/ -i syntax/ generated/${module}.idr"
    info(cmd)
    val exitCode = cmd.!
    exitCode shouldBe 0
  }
}
