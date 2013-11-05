package ttlite.core.it

import org.scalatest.matchers.MustMatchers
import ttlite.core.TTREPL

class TTLiteExportSpec extends org.scalatest.FunSpec with MustMatchers {
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
  }

  def checkAgda(module : String) {
    import scala.sys.process._
    TTREPL.main(Array(s"examples/test/agda/${module}.hs"))
    val exitCode = s"agda -i agda/ -i doc/ agda/${module}.agda".!
    exitCode mustBe 0
  }
}
