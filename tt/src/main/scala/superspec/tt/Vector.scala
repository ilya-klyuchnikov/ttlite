package superspec.tt

trait VectorAST extends CoreAST {
  case class Vec(A: Term, n: Term) extends Term
  case class VecNil(A: Term) extends Term
  case class VecCons(A: Term, n: Term, head: Term, tail: Term) extends Term
  case class VecElim(A: Term, motive: Term, nilCase: Term, consCase: Term, n: Term, vec: Term) extends Term

  case class VVec(A: Value, n: Value) extends Value
  case class VVecNil(A: Value) extends Value
  case class VVecCons(A: Value, n: Value, head: Value, tail: Value) extends Value
  case class NVecElim(A: Value, motive: Value, nilCase: Value, consCase: Value, n: Value, vec: Neutral) extends Neutral
}

trait VectorMetaSyntax extends MNat with VectorAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Vec")) @@ a @@ n =>
      Vec(fromM(a), fromM(n))
    case MVar(Global("VNil")) @@ a =>
      VecNil(fromM(a))
    case MVar(Global("VCons")) @@ a @@ n @@ h @@ t =>
      VecCons(fromM(a), fromM(n), fromM(h), fromM(t))
    case MVar(Global("vecElim")) @@ a @@ m @@ cN @@ cC @@ n @@ xs =>
      VecElim(fromM(a), fromM(m), fromM(cN), fromM(cC), fromM(n), fromM(xs))
    case _ => super.fromM(m)
  }
}

trait VectorPrinter extends FunPrinter with VectorAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Vec(a, n) =>
      print(p, ii, 'Vec @@ a @@ n)
    case VecNil(a) =>
      print(p, ii, 'VNil @@ a)
    case VecCons(a, n, x, xs) =>
      print(p, ii, 'VCons @@ a @@ n @@ x @@ xs)
    case VecElim(a, m, mn, mc, n, xs) =>
      print(p, ii, 'vecElim @@ a @@ m @@ mn @@ mc @@ n @@ xs)
    case _ =>
      super.print(p, ii, t)
  }
}

trait VectorEval extends FunEval with VectorAST {
  override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
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

trait VectorCheck extends FunCheck with VectorAST with NatAST {
  override def iType(i: Int, ctx: Context[Value], t: Term): Value = t match {
    case Vec(a, n) =>
      val aType = iType(i, ctx, a)
      val j = checkUniverse(i, aType)

      val nType = iType(i, ctx, n)
      checkEqual(i, nType, VNat)

      VUniverse(j)
    case VecNil(a) =>
      val aVal = eval(a, ctx, List())

      val aType = iType(i, ctx, a)
      checkUniverse(i, aType)

      VVec(aVal, VZero)
    case VecCons(a, n, head, tail) => //, VVec(bVal, VSucc(k))) =>
      val aVal = eval(a, ctx, List())
      val nVal = eval(n, ctx, List())

      val aType = iType(i, ctx, a)
      checkUniverse(i, aType)

      val nType = iType(i, ctx, n)
      checkEqual(i, nType, VNat)

      val hType = iType(i, ctx, head)
      checkEqual(i, hType, aVal)

      val tType = iType(i, ctx, tail)
      checkEqual(i, tType, VVec(aVal, nVal))

      VVec(aVal, VSucc(nVal))
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      val aVal = eval(a, ctx, List())
      val mVal = eval(m, ctx, List())
      val nVal = eval(n, ctx, List())
      val vecVal = eval(vec, ctx, List())

      val aType = iType(i, ctx, a)
      checkUniverse(i, aType)

      val mType = iType(i, ctx, m)
      checkEqual(i, mType, VPi(VNat, {n => VPi(VVec(aVal, n), {_ => VUniverse(-1)})}))

      val nilCaseType = iType(i, ctx, nilCase)
      checkEqual(i, nilCaseType, mVal @@ VZero @@ VVecNil(aVal))

      val consCaseType = iType(i, ctx, consCase)
      checkEqual(i, consCaseType, VPi(VNat, {n =>
        VPi(aVal, {y =>
          VPi(VVec(aVal, n), {ys =>
            VPi(mVal @@ n @@ ys, {_ =>
              mVal @@ VSucc(n) @@ VVecCons(aVal, n, y, ys)})})})}))

      val nType = iType(i, ctx, n)
      checkEqual(i, nType, VNat)

      val vecType = iType(i, ctx, vec)
      checkEqual(i, vecType, VVec(aVal, nVal))

      mVal @@ nVal @@ vecVal
    case _ =>
      super.iType(i, ctx, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
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

trait VectorQuote extends CoreQuote with VectorAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VVec(a, n) =>
      Vec(quote(ii, a), quote(ii, n))
    case VVecNil(a) =>
      VecNil(quote(ii, a))
    case VVecCons(a, n, head, tail) =>
      VecCons(quote(ii, a), quote(ii, n), quote(ii, head), quote(ii, tail))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
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

trait VectorREPL extends NatREPL with VectorAST with VectorMetaSyntax with VectorPrinter with VectorCheck with VectorEval with VectorQuote
