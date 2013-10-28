package ttlite.core.test

import ttlite.core._
import org.scalatest.matchers.MustMatchers

class TTLiteSpec extends org.scalatest.FunSpec with MustMatchers {
  describe("Meta Parser") {
    it("should parse global variable") {
      assert(MetaParser.parseMTerm("x") === MVar(Global("x")))
    }

    it("should parse assumed variable") {
      assert(MetaParser.parseMTerm("$x") === MVar(Assumed("$x")))
    }

    it("should parse assumed application") {
      assert(MetaParser.parseMTerm("$x $x") === MVar(Assumed("$x")) ~ MVar(Assumed("$x")))
      assert(MetaParser.parseMTerm("$x $x $x") === MVar(Assumed("$x")) ~ MVar(Assumed("$x")) ~ MVar(Assumed("$x")))
    }

    it("should parse binder term") {
      assert(MetaParser.parseMTerm("forall (x : a) . x") ==
        MBind("forall", MVar(Global("a")),MVar(Quote(0))))
      assert(MetaParser.parseMTerm("forall (x : a) (y : x). x") ==
        MBind("forall",MVar(Global("a")),MBind("forall",MVar(Quote(0)),MVar(Quote(1)))))
      assert(MetaParser.parseMTerm("forall (x : a) (y : x). y") ==
        MBind("forall",MVar(Global("a")),MBind("forall",MVar(Quote(0)),MVar(Quote(0)))))
      assert(MetaParser.parseMTerm("forall (x : a) . forall (y : x) . x") ==
        MBind("forall",MVar(Global("a")),MBind("forall",MVar(Quote(0)),MVar(Quote(1)))))
      assert(MetaParser.parseMTerm("forall (x : a) . exists (y : x) . f x") ===
        MBind("forall", MVar(Global("a")), MBind("exists",MVar(Quote(0)), MVar(Global("f")) ~ MVar(Quote(1)))))
    }
  }

  describe("Basic examples") {
    it("01. core") {
      TTREPL.main(Array("examples/core.hs"))
    }
    it("02. dproduct") {
      TTREPL.main(Array("examples/dproduct.hs"))
    }
    it("03. nat") {
      TTREPL.main(Array("examples/nat.hs"))
    }
    it("04. product") {
      TTREPL.main(Array("examples/product.hs"))
    }
    it("05. sum") {
      TTREPL.main(Array("examples/sum.hs"))
    }
    it("06. list") {
      TTREPL.main(Array("examples/list.hs"))
    }
    it("07. id") {
      TTREPL.main(Array("examples/id.hs"))
    }
    it("08. vec") {
      TTREPL.main(Array("examples/vec.hs"))
    }
    it("09. fin") {
      TTREPL.main(Array("examples/fin.hs"))
    }
  }

  describe("Misc examples") {
    it("ack.hs") {
      TTREPL.main(Array("examples/misc/ack.hs"))
    }
    it("cong.hs") {
      TTREPL.main(Array("examples/misc/cong.hs"))
    }
    it("eq_class.hs") {
      TTREPL.main(Array("examples/misc/eq_class.hs"))
    }
    it("lf.hs") {
      TTREPL.main(Array("examples/misc/lf.hs"))
    }
    it("list_gen_rec.hs") {
      TTREPL.main(Array("examples/misc/list_gen_rec.hs"))
    }
    it("logic.hs") {
      TTREPL.main(Array("examples/misc/logic.hs"))
    }
    it("misc.hs") {
      TTREPL.main(Array("examples/misc/misc.hs"))
    }
    it("power.hs") {
      TTREPL.main(Array("examples/misc/power.hs"))
    }
    it("slides.hs") {
      TTREPL.main(Array("examples/misc/slides.hs"))
    }
    it("wlist.hs") {
      TTREPL.main(Array("examples/misc/wlist.hs"))
    }
    it("wnat.hs") {
      TTREPL.main(Array("examples/misc/wnat.hs"))
    }
  }

  describe("Rules (to organize)") {
    it("arrays.hs") {
      TTREPL.main(Array("examples/rules/arrays.hs"))
    }
    it("lte.hs") {
      TTREPL.main(Array("examples/rules/lte.hs"))
    }
    it("monoid.hs") {
      TTREPL.main(Array("examples/rules/monoid.hs"))
    }
    it("qsort.hs") {
      TTREPL.main(Array("examples/rules/qsort.hs"))
    }
    it("rule01.hs") {
      TTREPL.main(Array("examples/rules/rule01.hs"))
    }
    it("sugar.hs") {
      TTREPL.main(Array("examples/rules/sugar.hs"))
    }
  }
}
