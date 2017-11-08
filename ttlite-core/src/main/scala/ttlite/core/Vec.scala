package ttlite.core

import ttlite.common._

trait VecAST extends CoreAST {
  case class Vec(A: Term, n: Term) extends Term
  case class VecNil(A: Term) extends Term
  case class VecCons(A: Term, n: Term, head: Term, tail: Term) extends Term
  case class VecElim(A: Term, motive: Term, nilCase: Term, consCase: Term, n: Term, vec: Term) extends Term

  case class VVec(A: Value, n: Value) extends Value
  case class VVecNil(A: Value) extends Value
  case class VVecCons(A: Value, n: Value, head: Value, tail: Value) extends Value
  case class NVecElim(A: Value, motive: Value, nilCase: Value, consCase: Value, n: Value, vec: Neutral) extends Neutral
}

trait VecMetaSyntax extends MetaSyntax with VecAST {
  abstract override def translate(m: MTerm): Term = m match {
    case MVar(Global("Vec")) @@ a @@ n =>
      Vec(translate(a), translate(n))
    case MVar(Global("VNil")) @@ a =>
      VecNil(translate(a))
    case MVar(Global("VCons")) @@ a @@ n @@ h @@ t =>
      VecCons(translate(a), translate(n), translate(h), translate(t))
    case MVar(Global("vecElim")) @@ a @@ m @@ cN @@ cC @@ n @@ xs =>
      VecElim(translate(a), translate(m), translate(cN), translate(cC), translate(n), translate(xs))
    case _ => super.translate(m)
  }
}

trait VecPrinter extends Printer with VecAST {
  abstract override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Vec(a, n) =>
      printL(p, ii, 'Vec, a, n)
    case VecNil(a) =>
      printL(p, ii, 'VNil, a)
    case VecCons(a, n, x, xs) =>
      printL(p, ii, 'VCons, a, n, x, xs)
    case VecElim(a, m, mn, mc, n, xs) =>
      printL(p, ii, 'vecElim, a, m, mn, mc, n, xs)
    case _ =>
      super.print(p, ii, t)
  }
}

trait VecPrinterAgda extends PrinterAgda with VecAST {
  abstract override def printA(p: Int, ii: Int, t: Term): Doc = t match {
    case Vec(a, n) =>
      printAL(p, ii, 'Vec, a, n)
    case VecNil(a) =>
      printAL(p, ii, 'vnil, a)
    case VecCons(a, n, x, xs) =>
      printAL(p, ii, 'vcons, a, n, x, xs)
    case VecElim(a, m, mn, mc, n, xs) =>
      printAL(p, ii, 'elimVec, a, m, mn, mc, n, xs)
    case _ =>
      super.printA(p, ii, t)
  }
}

trait VecPrinterCoq extends PrinterCoq with VecAST {
  abstract override def printC(p: Int, ii: Int, t: Term): Doc = t match {
    case Vec(a, n) =>
      printCL(p, ii, 'Vec, a, n)
    case VecNil(a) =>
      printCL(p, ii, 'vnil, a)
    case VecCons(a, n, x, xs) =>
      printCL(p, ii, 'vcons, a, n, x, xs)
    case VecElim(a, m, mn, mc, n, xs) =>
      printCL(p, ii, 'elimVec, a, m, mn, mc, n, xs)
    case _ =>
      super.printC(p, ii, t)
  }
}

trait VecPrinterIdris extends PrinterIdris with VecAST {
  abstract override def printI(p: Int, ii: Int, t: Term): Doc = t match {
    case Vec(a, n) =>
      printIL(p, ii, 'Vec, a, n)
    case VecNil(a) =>
      printIL(p, ii, 'VNil, a)
    case VecCons(a, n, x, xs) =>
      printIL(p, ii, 'VCons, a, n, x, xs)
    case VecElim(a, m, mn, mc, n, xs) =>
      printIL(p, ii, 'elimVec, a, m, mn, mc, n, xs)
    case _ =>
      super.printI(p, ii, t)
  }
}

trait VecEval extends Eval with VecAST { self: FunAST =>
  abstract override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Vec(a, n) =>
      VVec(eval(a, ctx, bound), eval(n, ctx, bound))
    case VecNil(a) =>
      VVecNil(eval(a, ctx, bound))
    case VecCons(a, n, head, tail) =>
      VVecCons(eval(a, ctx, bound), eval(n, ctx, bound), eval(head, ctx, bound), eval(tail, ctx, bound))
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      val nilCaseVal = eval(nilCase, ctx, bound)
      val consCaseVal = eval(consCase, ctx, bound)
      def rec(nVal: Value, vecVal: Value): Value = vecVal match {
        case VVecNil(_) =>
          nilCaseVal
        case VVecCons(_, n, head, tail) =>
          consCaseVal @@ n @@ head @@ tail @@ rec(n, tail)
        case VNeutral(n) =>
          VNeutral(NVecElim(eval(a, ctx, bound), eval(m, ctx, bound), nilCaseVal, consCaseVal, nVal, n))
      }
      rec(eval(n, ctx, bound), eval(vec, ctx, bound))
    case _ =>
      super.eval(t, ctx, bound)
  }
}

trait VecCheck extends Check with VecAST { self: FunAST with NatAST =>
  abstract override def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value = t match {
    case Vec(a, n) =>
      val aType = iType(i, path/(2, 3), ctx, a)
      val j = checkUniverse(i, aType, path/(2, 3))

      val nType = iType(i, path/(3, 3), ctx, n)
      checkEqual(i, nType, VNat, path/(3, 3))

      VUniverse(j)
    case VecNil(a) =>
      val aType = iType(i, path/(1, 2), ctx, a)
      checkUniverse(i, aType, path/(1, 2))
      val aVal = eval(a, ctx, List())

      VVec(aVal, VZero)
    case VecCons(a, n, head, tail) =>
      val aType = iType(i, path/(2, 5), ctx, a)
      checkUniverse(i, aType, path/(2, 5))
      val aVal = eval(a, ctx, List())

      val nType = iType(i, path/(3, 5), ctx, n)
      checkEqual(i, nType, VNat, path/(3, 5))
      val nVal = eval(n, ctx, List())

      val hType = iType(i, path/(4, 5), ctx, head)
      checkEqual(i, hType, aVal, path/(4, 5))

      val tType = iType(i, path/(5, 5), ctx, tail)
      checkEqual(i, tType, VVec(aVal, nVal), path/(5, 5))

      VVec(aVal, VSucc(nVal))
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      val aType = iType(i, path/(2, 7), ctx, a)
      checkUniverse(i, aType, path/(2, 7))
      val aVal = eval(a, ctx, List())

      val mType = iType(i, path/(3, 7), ctx, m)
      checkEqual(i, mType, VPi(VNat, {n => VPi(VVec(aVal, n), {_ => VUniverse(-1)})}), path/(3, 7))
      val mVal = eval(m, ctx, List())

      val nilCaseType = iType(i, path/(4, 7), ctx, nilCase)
      checkEqual(i, nilCaseType, mVal @@ VZero @@ VVecNil(aVal), path/(4, 7))

      val consCaseType = iType(i, path/(5, 7), ctx, consCase)
      checkEqual(i, consCaseType,
        VPi(VNat, {n =>
          VPi(aVal, {y =>
            VPi(VVec(aVal, n), {ys =>
              VPi(mVal @@ n @@ ys, {_ =>
                mVal @@ VSucc(n) @@ VVecCons(aVal, n, y, ys)})})})}),
        path/(5, 7))

      val nType = iType(i, path/(6, 7), ctx, n)
      checkEqual(i, nType, VNat, path/(6, 7))
      val nVal = eval(n, ctx, List())

      val vecType = iType(i, path/(7, 7), ctx, vec)
      checkEqual(i, vecType, VVec(aVal, nVal), path/(7, 7))
      val vecVal = eval(vec, ctx, List())

      mVal @@ nVal @@ vecVal
    case _ =>
      super.iType(i, path, ctx, t)
  }

  abstract override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Vec(a, n) =>
      Vec(iSubst(i, r, a), iSubst(i, r, n))
    case VecNil(a) =>
      VecNil(iSubst(i, r, a))
    case VecCons(a, n, head, tail) =>
      VecCons(iSubst(i, r, a), iSubst(i, r, n), iSubst(i, r, head), iSubst(i, r, tail))
    case VecElim(a, m, nc, cc, n, vec) =>
      VecElim(
        iSubst(i, r, a),
        iSubst(i, r, m),
        iSubst(i, r, nc),
        iSubst(i, r, cc),
        iSubst(i, r, n),
        iSubst(i, r, vec)
      )
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait VecQuoting extends Quoting with VecAST {
  abstract override def quote(ii: Int, v: Value): Term = v match {
    case VVec(a, n) =>
      Vec(quote(ii, a), quote(ii, n))
    case VVecNil(a) =>
      VecNil(quote(ii, a))
    case VVecCons(a, n, head, tail) =>
      VecCons(quote(ii, a), quote(ii, n), quote(ii, head), quote(ii, tail))
    case _ => super.quote(ii, v)
  }
  abstract override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NVecElim(a, m, nilCase, consCase, n, vec) =>
      VecElim(
        quote(ii, a),
        quote(ii, m),
        quote(ii, nilCase),
        quote(ii, consCase),
        quote(ii, n),
        neutralQuote(ii, vec)
      )
    case _ => super.neutralQuote(ii, n)
  }
}

trait VecREPL
  extends CoreREPL
  with VecAST
  with VecMetaSyntax
  with VecPrinter
  with VecPrinterAgda
  with VecPrinterCoq
  with VecPrinterIdris
  with VecCheck
  with VecEval
  with VecQuoting {
  self: FunAST with NatAST =>
}
