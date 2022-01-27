package ttlite.core

import ttlite.common._

// Chapter 13. Disjoint union of a family of sets
// Dependent pair type, dependent sum type or sigma-type.
trait SigmaAST extends AST {
  // exists
  case class Sigma(c1: Term, c2: Term) extends Term
  case class DPair(sigma: Term, t: Term, e: Term) extends Term
  case class SigmaElim(sigma: Term, m: Term, f: Term, pair: Term) extends Term

  case class VSigma(t: Value, e: Value => Value) extends Value
  case class VDPair(sigma: Value, t: Value, e: Value) extends Value
  case class NSigmaElim(sigma: Value, m: Value, f: Value, pair: Neutral) extends Neutral
}

trait SigmaMetaSyntax extends SigmaAST, MetaSyntax {
  private val predefinedGlobals = Set("dpair", "exists")
  abstract override def isPredefinedGlobal(g: Global): Boolean =
    predefinedGlobals(g.n) || super.isPredefinedGlobal(g)
  abstract override def translate(m: MTerm): Term =
    m match {
      case MVar(Global("elim")) @@ (sigma @ MBind("exists", t1, t2)) @@ m @@ f @@ p =>
        SigmaElim(translate(sigma), translate(m), translate(f), translate(p))
      case MVar(Global("dpair")) @@ sigma @@ e1 @@ e2 =>
        DPair(translate(sigma), translate(e1), translate(e2))
      case MBind("exists", t1, t2) =>
        Sigma(translate(t1), translate(t2))
      case _ => super.translate(m)
    }
}

trait SigmaPrinter extends Printer, SigmaAST {
  import scala.collection.immutable.Seq

  abstract override def print(p: Int, ii: Int, t: Term): Doc =
    t match {
      case Sigma(d, Sigma(d1, r)) =>
        parens(nestedExists(ii + 2, List((ii + 1, d1), (ii, d)), r))
      case Sigma(d, r) =>
        parensIf(
          p > 0,
          sep(Seq("exists " <> parens(vars(ii) <> " : " <> print(0, ii, d)) <> " .", nest(print(0, ii + 1, r)))),
        )
      case DPair(s, a, b) =>
        printL(p, ii, "dpair", s, a, b)
      case SigmaElim(s, m, f, dp) =>
        printL(p, ii, "elim", s, m, f, dp)
      case _ =>
        super.print(p, ii, t)
    }

  def nestedExists(i: Int, fs: List[(Int, Term)], t: Term): Doc =
    t match {
      case Sigma(d, r) =>
        nestedExists(i + 1, (i, d) :: fs, r)
      case x =>
        val fors = fs.reverse.map { case (n, d) => parens(vars(n) <> " : " <> nest(print(0, n, d))) }
        val fors1 = fors.updated(fors.length - 1, fors.last <> " .")
        nest(sep((text("exists") +: fors1) ++ Seq(print(0, i, x))))
    }
}

trait SigmaPrinterAgda extends PrinterAgda, SigmaAST { self: PiAST =>
  abstract override def printA(p: Int, ii: Int, t: Term): Doc =
    t match {
      case Sigma(d, r) =>
        printAL(p, ii, "Sigma", d, Lam(d, r))
      case DPair(Sigma(d, r), a, b) =>
        printAL(p, ii, "sigma", d, Lam(d, r), a, b)
      case SigmaElim(Sigma(d, r), m, f, dp) =>
        printAL(p, ii, "elimSigma", d, Lam(d, r), m, f, dp)
      case _ =>
        super.printA(p, ii, t)
    }
}

trait SigmaPrinterCoq extends PrinterCoq, SigmaAST { self: PiAST =>
  abstract override def printC(p: Int, ii: Int, t: Term): Doc =
    t match {
      case Sigma(d, r) =>
        printCL(p, ii, "Sigma", d, Lam(d, r))
      case DPair(Sigma(d, r), a, b) =>
        printCL(p, ii, "sigma", d, Lam(d, r), a, b)
      case SigmaElim(Sigma(d, r), m, f, dp) =>
        printCL(p, ii, "elimSigma", d, Lam(d, r), m, f, dp)
      case _ =>
        super.printC(p, ii, t)
    }
}

trait SigmaPrinterIdris extends PrinterIdris, SigmaAST { self: PiAST =>
  abstract override def printI(p: Int, ii: Int, t: Term): Doc =
    t match {
      case Sigma(d, r) =>
        printIL(p, ii, "TTSigma", d, Lam(d, r))
      case DPair(Sigma(d, r), a, b) =>
        printIL(p, ii, "Sigma", d, Lam(d, r), a, b)
      case SigmaElim(Sigma(d, r), m, f, dp) =>
        printIL(p, ii, "elimSigma", d, Lam(d, r), m, f, dp)
      case _ =>
        super.printI(p, ii, t)
    }
}

trait SigmaQuoting extends Quoting, SigmaAST {
  abstract override def quote(ii: Int, v: Value): Term =
    v match {
      case VSigma(v, f) =>
        Sigma(quote(ii, v), quote(ii + 1, f(vfree(Quote(ii)))))
      case VDPair(sigma, e1, e2) =>
        DPair(quote(ii, sigma), quote(ii, e1), quote(ii, e2))
      case _ => super.quote(ii, v)
    }

  abstract override def neutralQuote(ii: Int, n: Neutral): Term =
    n match {
      case NSigmaElim(sigma, m, f, p) =>
        SigmaElim(quote(ii, sigma), quote(ii, m), quote(ii, f), neutralQuote(ii, p))
      case _ => super.neutralQuote(ii, n)
    }
}

trait SigmaEval extends Eval, SigmaAST { self: PiAST =>
  abstract override def eval(t: Term, ctx: Context[Value], bound: Env): Value =
    t match {
      case Sigma(ty, ty1) =>
        VSigma(eval(ty, ctx, bound), x => eval(ty1, ctx, x :: bound))
      case DPair(sigma, e1, e2) =>
        VDPair(eval(sigma, ctx, bound), eval(e1, ctx, bound), eval(e2, ctx, bound))
      case SigmaElim(sigma, m, f, p) =>
        val sigmaVal = eval(sigma, ctx, bound)
        val mVal = eval(m, ctx, bound)
        val fVal = eval(f, ctx, bound)
        val pVal = eval(p, ctx, bound)
        sigmaElim(sigmaVal, mVal, fVal, pVal)
      case _ =>
        super.eval(t, ctx, bound)
    }

  def sigmaElim(sigmaVal: Value, mVal: Value, fVal: Value, pVal: Value): Value =
    pVal match {
      case VDPair(_, x, y) => fVal @@ x @@ y
      case VNeutral(n)     => VNeutral(NSigmaElim(sigmaVal, mVal, fVal, n))
    }
}

trait SigmaCheck extends Check, SigmaAST { self: PiAST =>
  abstract override def iType(i: Int, path: Path, ctx: Context[Value], t: Term): Value =
    t match {
      // Sigma is a bind, so arity is 2
      case Sigma(x, tp) =>
        val xType = iType(i, path / (1, 2), ctx, x)
        val j = checkUniverse(i, xType, path / (1, 2))
        val xVal = eval(x, ctx, Nil)

        val tpType = iType(i + 1, path / (2, 2), ctx.addType(Local(i), xVal), iSubst(0, Free(Local(i)), tp))
        val k = checkUniverse(i, tpType, path / (2, 2))

        VUniverse(math.max(j, k))
      case DPair(sigma, x, y) =>
        val sigmaType = iType(i, path / (2, 4), ctx, sigma)
        checkUniverse(i, sigmaType, path / (2, 4))

        eval(sigma, ctx, Nil) match {
          case VSigma(a, f) =>
            val xType = iType(i, path / (3, 4), ctx, x)
            checkEqual(i, xType, a, path / (3, 4))
            val xVal = eval(x, ctx, Nil)

            val yType = iType(i, path / (4, 4), ctx, y)
            checkEqual(i, yType, f(xVal), path / (4, 4))

            VSigma(a, f)
          case _ =>
            throw TypeError(s"illegal application: $t", path)
        }
      case SigmaElim(sigma, m, f, p) =>
        val sigmaType = iType(i, path / (2, 5), ctx, sigma)
        checkUniverse(i, sigmaType, path / (2, 5))

        eval(sigma, ctx, Nil) match {
          case sigmaVal @ VSigma(x1, x2) =>
            val pType = iType(i, path / (5, 5), ctx, p)
            checkEqual(i, pType, sigmaVal, path / (5, 5))
            val pVal = eval(p, ctx, List())

            val mType = iType(i, path / (3, 5), ctx, m)
            checkEqual(i, mType, VPi(sigmaVal, { _ => VUniverse(-1) }), path / (3, 5))
            val mVal = eval(m, ctx, List())

            val fType = iType(i, path / (4, 5), ctx, f)
            checkEqual(i, fType, VPi(x1, { x => VPi(x2(x), y => mVal @@ VDPair(sigmaVal, x, y)) }), path / (3, 5))

            mVal @@ pVal
          case _ =>
            throw TypeError(s"illegal application: $t", path)
        }
      case _ =>
        super.iType(i, path, ctx, t)
    }

  abstract override def iSubst(i: Int, r: Term, it: Term): Term =
    it match {
      case Sigma(ty, ty1) =>
        Sigma(iSubst(i, r, ty), iSubst(i + 1, r, ty1))
      case DPair(sigma, e1, e2) =>
        DPair(iSubst(i, r, sigma), iSubst(i, r, e1), iSubst(i, r, e2))
      case SigmaElim(sigma, m, f, p) =>
        SigmaElim(iSubst(i, r, sigma), iSubst(i, r, m), iSubst(i, r, f), iSubst(i, r, p))
      case _ => super.iSubst(i, r, it)
    }

}

trait SigmaREPL
    extends CoreREPL,
      SigmaAST,
      SigmaMetaSyntax,
      SigmaPrinter,
      SigmaPrinterAgda,
      SigmaPrinterCoq,
      SigmaPrinterIdris,
      SigmaCheck,
      SigmaEval,
      SigmaQuoting {
  self: PiAST =>
}
