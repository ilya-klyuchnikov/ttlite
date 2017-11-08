package ttlite.core

import ttlite.common._

// Chapter 9. Natural numbers
trait NatAST extends AST {
  case object Nat extends Term
  case object Zero extends Term
  case class Succ(e: Term) extends Term
  case class NatElim(a: Term, b: Term, c: Term, d: Term) extends Term

  case object VNat extends Value
  case object VZero extends Value
  case class VSucc(v: Value) extends Value
  case class NNatElim(m: Value, caseZ: Value, caseS: Value, n: Neutral) extends Neutral
}

trait NatMetaSyntax extends MetaSyntax with NatAST {
  abstract override def translate(m: MTerm): Term = m match {
    case MVar(Global("Nat")) =>
      Nat
    case MVar(Global("Zero")) =>
      Zero
    case MVar(Global("Succ")) @@ n =>
      Succ(translate(n))
    case MVar(Global("elim")) @@ MVar(Global("Nat")) @@ m @@ cZ @@ cS @@ n =>
      NatElim(translate(m), translate(cZ), translate(cS), translate(n))
    case _ => super.translate(m)
  }
}

trait NatPrinter extends Printer with NatAST {
  abstract override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Nat =>
      "Nat"
    case NatElim(m, z, s, n) =>
      printL(p, ii, 'elim, Nat, m, z, s, n)
    case Zero =>
      "Zero"
    case Succ(n) =>
      printL(p, ii, 'Succ, n)
    case _ =>
      super.print(p, ii, t)
  }
}

trait NatPrinterAgda extends PrinterAgda with NatAST {
  abstract override def printA(p: Int, ii: Int, t: Term): Doc = t match {
    case Nat =>
      "Nat"
    case NatElim(m, z, s, n) =>
      printAL(p, ii, 'elimNat, m, z, s, n)
    case Zero =>
      "zero"
    case Succ(n) =>
      printAL(p, ii, 'succ, n)
    case _ =>
      super.printA(p, ii, t)
  }
}

trait NatPrinterCoq extends PrinterCoq with NatAST {
  abstract override def printC(p: Int, ii: Int, t: Term): Doc = t match {
    case Nat =>
      "Nat"
    case NatElim(m, z, s, n) =>
      printCL(p, ii, 'elimNat, m, z, s, n)
    case Zero =>
      "zero"
    case Succ(n) =>
      printCL(p, ii, 'succ, n)
    case _ =>
      super.printC(p, ii, t)
  }
}

trait NatPrinterIdris extends PrinterIdris with NatAST {
  abstract override def printI(p: Int, ii: Int, t: Term): Doc = t match {
    case Nat =>
      "Nat"
    case NatElim(m, z, s, n) =>
      printIL(p, ii, 'elimNat, m, z, s, n)
    case Zero =>
      "Zero"
    case Succ(n) =>
      printIL(p, ii, 'Succ, n)
    case _ =>
      super.printI(p, ii, t)
  }
}

trait NatQuoting extends Quoting with NatAST {
  abstract override def quote(ii: Int, v: Value): Term = v match {
    case VNat => Nat
    case VZero => Zero
    case VSucc(n) => Succ(quote(ii, n))
    case _ => super.quote(ii, v)
  }
  abstract override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NNatElim(m, z, s, n) =>
      NatElim(quote(ii, m), quote(ii, z), quote(ii, s), neutralQuote(ii, n))
    case _ => super.neutralQuote(ii, n)
  }
}

trait NatEval extends Eval with NatAST { self: FunAST =>
  abstract override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Zero =>
      VZero
    case Succ(n) =>
      VSucc(eval(n, ctx, bound))
    case Nat =>
      VNat
    case NatElim(m, mz, ms, n) =>
      val mVal = eval(m, ctx, bound)
      val mzVal = eval(mz, ctx, bound)
      val msVal = eval(ms, ctx, bound)
      val nVal = eval(n, ctx, bound)
      natElim(mVal, mzVal, msVal, nVal)
    case _ =>
      super.eval(t, ctx, bound)
  }

  def natElim(mVal: Value, czVal: Value, csVal: Value, nVal: Value): Value = nVal match {
    case VZero =>
      czVal
    case VSucc(k) =>
      csVal @@ k @@ natElim(mVal, czVal, csVal, k)
    case VNeutral(n) =>
      VNeutral(NNatElim(mVal, czVal, csVal, n))
  }
}

trait NatCheck extends Check with NatAST { self: FunAST =>
  abstract override def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value = t match {
    case Nat =>
      VUniverse(0)
    case NatElim(m, mz, ms, n) =>
      val mType = iType(i, path/(3, 6), ctx, m)
      checkEqual(i, mType, VPi(VNat, {_ => VUniverse(-1)}), path/(3, 6))
      val mVal = eval(m, ctx, Nil)

      val mzType = iType(i, path/(4, 6), ctx, mz)
      checkEqual(i, mzType, mVal @@ VZero, path/(4, 6))

      val msType = iType(i, path/(5, 6), ctx, ms)
      checkEqual(i, msType, VPi(VNat, k => VPi(mVal @@ k, x => mVal @@ VSucc(k))), path/(5, 6))

      val nType = iType(i, path/(6, 6), ctx, n)
      checkEqual(i, nType, Nat, path/(6, 6))
      val nVal = eval(n, ctx, Nil)

      mVal @@ nVal
    case Zero =>
      VNat
    case Succ(k) =>
      val kType = iType(i, path/(2, 2), ctx, k)
      checkEqual(i, kType, Nat, path/(2, 2))

      VNat
    case _ =>
      super.iType(i, path, ctx, t)
  }

  abstract override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Nat =>
      Nat
    case NatElim(m, mz, ms, n) =>
      NatElim(iSubst(i, r, m), iSubst(i, r, mz), iSubst(i, r, ms), iSubst(i, r, n))
    case Zero =>
      Zero
    case Succ(n) =>
      Succ(iSubst(i, r, n))
    case _ => super.iSubst(i, r, it)
  }

}

trait NatREPL
  extends CoreREPL
  with NatAST
  with NatMetaSyntax
  with NatPrinter
  with NatPrinterAgda
  with NatPrinterCoq
  with NatPrinterIdris
  with NatCheck
  with NatEval
  with NatQuoting {
  self: FunAST =>
}
