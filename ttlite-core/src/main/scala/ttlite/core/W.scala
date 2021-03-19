package ttlite.core

import ttlite.common._

// chapter 15: Well-Orderings
trait WAST extends AST {
  case class W(t1: Term, t2: Term) extends Term
  case class Sup(w: Term, t1: Term, t2: Term) extends Term
  // w elim, a - is w, need to re-order later
  case class Rec(w: Term, m: Term, b: Term, a: Term) extends Term

  case class VW(t1: Value, t2: Value => Value) extends Value
  case class VSup(w: Value, t1: Value, t2: Value) extends Value
  case class NRec(w: Value, m: Value, b: Value, a: Neutral) extends Neutral
}

trait WMetaSyntax extends MetaSyntax with WAST {
  private val predefinedGlobals = Set("W", "Sup", "Rec")
  abstract override def isPredefinedGlobal(g: Global): Boolean =
    predefinedGlobals(g.n) || super.isPredefinedGlobal(g)
  abstract override def translate(m: MTerm): Term =
    m match {
      case MBind("W", t1, t2) =>
        W(translate(t1), translate(t2))
      case MVar(Global("Sup")) @@ sigma @@ e1 @@ e2 =>
        Sup(translate(sigma), translate(e1), translate(e2))
      case MVar(Global("Rec")) @@ w @@ m @@ a @@ b =>
        Rec(translate(w), translate(m), translate(a), translate(b))
      case _ => super.translate(m)
    }
}

trait WPrinter extends Printer with WAST {
  import scala.collection.immutable.Seq

  abstract override def print(p: Int, ii: Int, t: Term): Doc =
    t match {
      case W(d, r) =>
        parensIf(
          p > 0,
          sep(Seq("W " <> parens(vars(ii) <> " : " <> print(0, ii, d)) <> " .", nest(print(0, ii + 1, r)))),
        )
      case Sup(s, a, b) =>
        printL(p, ii, "Sup", s, a, b)
      case Rec(w, m, a, b) =>
        printL(p, ii, "Rec", w, m, a, b)
      case _ =>
        super.print(p, ii, t)
    }
}

trait WPrinterAgda extends PrinterAgda with WAST { self: PiAST =>
  abstract override def printA(p: Int, ii: Int, t: Term): Doc =
    t match {
      case W(d, r) =>
        printAL(p, ii, "W", d, Lam(d, r))
      case Sup(W(d, r), a, b) =>
        printAL(p, ii, "sup", d, Lam(d, r), a, b)
      case Sup(_, _, _) =>
        sys.error("Wrong term: " + t)
      case Rec(W(d, r), m, a, b) =>
        printAL(p, ii, "rec", d, Lam(d, r), m, a, b)
      case Rec(_, _, _, _) =>
        sys.error("Wrong term: " + t)
      case _ =>
        super.printA(p, ii, t)
    }
}

trait WPrinterCoq extends PrinterCoq with WAST { self: PiAST =>
  abstract override def printC(p: Int, ii: Int, t: Term): Doc =
    t match {
      case W(d, r) =>
        printCL(p, ii, "W", d, Lam(d, r))
      case Sup(W(d, r), a, b) =>
        printCL(p, ii, "sup", d, Lam(d, r), a, b)
      case Sup(_, _, _) =>
        sys.error("Wrong term: " + t)
      case Rec(W(d, r), m, a, b) =>
        printCL(p, ii, "rec", d, Lam(d, r), m, a, b)
      case Rec(_, _, _, _) =>
        sys.error("Wrong term: " + t)
      case _ =>
        super.printC(p, ii, t)
    }
}

trait WPrinterIdris extends PrinterIdris with WAST { self: PiAST =>
  abstract override def printI(p: Int, ii: Int, t: Term): Doc =
    t match {
      case W(d, r) =>
        printIL(p, ii, "W", d, Lam(d, r))
      case Sup(W(d, r), a, b) =>
        printIL(p, ii, "Sup", d, Lam(d, r), a, b)
      case Sup(_, _, _) =>
        sys.error("Wrong term: " + t)
      case Rec(W(d, r), m, a, b) =>
        printIL(p, ii, "rec", d, Lam(d, r), m, a, b)
      case Rec(_, _, _, _) =>
        sys.error("Wrong term: " + t)
      case _ =>
        super.printI(p, ii, t)
    }
}

trait WQuoting extends Quoting with WAST {
  abstract override def quote(ii: Int, v: Value): Term =
    v match {
      case VW(v, f) =>
        W(quote(ii, v), quote(ii + 1, f(vfree(Quote(ii)))))
      case VSup(sigma, e1, e2) =>
        Sup(quote(ii, sigma), quote(ii, e1), quote(ii, e2))
      case _ => super.quote(ii, v)
    }

  abstract override def neutralQuote(ii: Int, n: Neutral): Term =
    n match {
      case NRec(w, m, a, b) =>
        Rec(quote(ii, w), quote(ii, m), quote(ii, a), neutralQuote(ii, b))
      case _ => super.neutralQuote(ii, n)
    }
}

trait WEval extends Eval with WAST { self: PiAST =>
  abstract override def eval(t: Term, ctx: Context[Value], bound: Env): Value =
    t match {
      case W(t1, t2) =>
        VW(eval(t1, ctx, bound), x => eval(t2, ctx, x :: bound))
      case Sup(w, e1, e2) =>
        VSup(eval(w, ctx, bound), eval(e1, ctx, bound), eval(e2, ctx, bound))
      case Rec(w, m, b, a) =>
        val wVal = eval(w, ctx, bound)
        val mVal = eval(m, ctx, bound)
        val aVal = eval(a, ctx, bound)
        val bVal = eval(b, ctx, bound)
        rec(wVal, mVal, bVal, aVal)
      case _ =>
        super.eval(t, ctx, bound)
    }

  def rec(wVal: Value, mVal: Value, bVal: Value, aVal: Value): Value =
    aVal match {
      case VSup(_, d, e) =>
        // wrec(sup(d, e), b) = b(d, e, (x)wrec(e(x), b))
        val VW(t1, t2) = wVal
        bVal @@ d @@ e @@
          VLam(t2(d), x => rec(wVal, mVal, bVal, e @@ x))
      case VNeutral(n) =>
        VNeutral(NRec(wVal, mVal, bVal, n))
    }
}

trait WCheck extends Check with WAST { self: PiAST =>
  abstract override def iType(i: Int, path: Path, ctx: Context[Value], t: Term): Value =
    t match {
      // this is a bind, so arity = 2
      case W(x, tp) =>
        val xType = iType(i, path / (1, 2), ctx, x)
        val j = checkUniverse(i, xType, path / (1, 2))
        val xVal = eval(x, ctx, Nil)

        val tpType = iType(i + 1, path / (2, 2), ctx.addType(Local(i), xVal), iSubst(0, Free(Local(i)), tp))
        val k = checkUniverse(i, tpType, path / (2, 2))

        VUniverse(math.max(j, k))
      case Sup(w, a, f) =>
        val wType = iType(i, path / (2, 4), ctx, w)
        checkUniverse(i, wType, path / (2, 4))
        val wVal = eval(w, ctx, List())
        wVal match {
          case VW(a1, f1) =>
            val aType = iType(i, path / (3, 4), ctx, a)
            checkEqual(i, aType, a1, path / (3, 4))

            val aVal = eval(a, ctx, Nil)

            val fType = iType(i, path / (4, 4), ctx, f)
            checkEqual(i, fType, VPi(f1(aVal), _ => VW(a1, f1)), path / (4, 4))

            VW(a1, f1)
          case _ =>
            throw TypeError(s"illegal application: $t", path)
        }
      case Rec(w, m, b, a) =>
        val wType = iType(i, path / (2, 5), ctx, w)
        checkUniverse(i, wType, path / (2, 5))
        val wVal = eval(w, ctx, List())
        require(wVal.isInstanceOf[VW], path / (2, 5), "W _ _", w)
        val VW(t1, t2) = wVal

        val mType = iType(i, path / (3, 5), ctx, m)
        checkEqual(i, mType, VPi(VW(t1, t2), { _ => VUniverse(-1) }), path / (3, 5))
        val mVal = eval(m, ctx, List())

        val bType = iType(i, path / (4, 5), ctx, b)
        checkEqual(
          i,
          bType,
          VPi(
            t1,
            a1 =>
              VPi(
                VPi(t2(a1), _ => VW(t1, t2)),
                f => VPi(VPi(t2(a1), y => mVal @@ (f @@ y)), _ => mVal @@ VSup(VW(t1, t2), a1, f)),
              ),
          ),
          path / (4, 5),
        )

        val aType = iType(i, path / (5, 5), ctx, a)
        checkEqual(i, aType, VW(t1, t2), path / (5, 5))
        val aVal = eval(a, ctx, List())

        mVal @@ aVal
      case _ =>
        super.iType(i, path, ctx, t)
    }

  abstract override def iSubst(i: Int, r: Term, it: Term): Term =
    it match {
      case W(t1, t2) =>
        W(iSubst(i, r, t1), iSubst(i + 1, r, t2))
      case Sup(sigma, e1, e2) =>
        Sup(iSubst(i, r, sigma), iSubst(i, r, e1), iSubst(i, r, e2))
      case Rec(w, m, e1, e2) =>
        Rec(iSubst(i, r, w), iSubst(i, r, m), iSubst(i, r, e1), iSubst(i, r, e2))
      case _ => super.iSubst(i, r, it)
    }
}

trait WREPL
    extends CoreREPL
    with WAST
    with WMetaSyntax
    with WPrinter
    with WPrinterAgda
    with WPrinterCoq
    with WPrinterIdris
    with WCheck
    with WEval
    with WQuoting {
  self: PiAST =>
}
