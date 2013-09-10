package superspec.tt

trait SumAST extends CoreAST {
  case class Sum(A: Term, B: Term) extends Term
  case class InL(et: Term, l: Term) extends Term
  case class InR(et: Term, r: Term) extends Term
  case class SumElim(et: Term, m: Term, lCase: Term, rCase: Term, sum: Term) extends Term

  case class VSum(L: Value, R: Value) extends Value
  case class VInL(et: Value, l: Value) extends Value
  case class VInR(et: Value, r: Value) extends Value
  case class NSumElim(et: Value, m: Value, lCase: Value, rCase: Value, sum: Neutral) extends Neutral
}

trait SumMetaSyntax extends CoreMetaSyntax with SumAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Sum")) @@ l @@ r =>
      Sum(fromM(l), fromM(r))
    case MVar(Global("InL")) @@ et @@ inj =>
      InL(fromM(et), fromM(inj))
    case MVar(Global("InR")) @@ et @@ inj =>
      InR(fromM(et), fromM(inj))
    case MVar(Global("elim")) @@ (MVar(Global("Sum")) @@ l @@ r) @@ m @@ lc @@ rc @@ inj =>
      SumElim(Sum(fromM(l), fromM(r)), fromM(m), fromM(lc), fromM(rc), fromM(inj))
    case _ => super.fromM(m)
  }
}

trait SumPrinter extends FunPrinter with SumAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Sum(a, b) =>
      print(p, ii, 'Sum @@ a @@ b)
    case InL(et, l) =>
      print(p, ii, 'InL @@ et @@ l)
    case InR(et, r) =>
      print(p, ii, 'InR @@ et @@ r)
    case SumElim(et, m, lc, rc, sum) =>
      print(p, ii, 'elim @@ et @@ m @@ lc @@ rc @@ sum)
    case _ =>
      super.print(p, ii, t)
  }
}

trait SumEval extends FunEval with SumAST {
  override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Sum(lt, rt) =>
      VSum(eval(lt, ctx, bound), eval(rt, ctx, bound))
    case InL(et, l) =>
      VInL(eval(et, ctx, bound), eval(l, ctx, bound))
    case InR(et, r) =>
      VInR(eval(et, ctx, bound), eval(r, ctx, bound))
    case SumElim(et@Sum(lt, rt), m, lc, rc, sum) =>
      val etVal = eval(et, ctx, bound)
      val mVal = eval(m, ctx, bound)
      val lcVal = eval(lc, ctx, bound)
      val rcVal = eval(rc, ctx, bound)
      val sumVal = eval(sum, ctx, bound)
      sumElim(etVal, mVal, lcVal, rcVal, sumVal)
    case _ =>
      super.eval(t, ctx, bound)
  }

  def sumElim(etVal: Value, mVal: Value, lcVal: Value, rcVal: Value, sumVal: Value): Value =
    sumVal match {
      case VInL(_, lVal) =>
        lcVal @@ lVal
      case VInR(_, rVal) =>
        rcVal @@ rVal
      case VNeutral(n) =>
        VNeutral(NSumElim(etVal, mVal, lcVal, rcVal, n))
    }
}

trait SumCheck extends FunCheck with SumAST {
  override def iType(i: Int, ctx: Context[Value], t: Term): Value = t match {
    case Sum(a, b) =>
      val aType = iType(i, ctx, a)
      val j = checkUniverse(i, aType)

      val bType = iType(i, ctx, b)
      val k = checkUniverse(i, bType)

      VUniverse(math.max(j, k))
    case InL(Sum(a, b), l) =>
      val aVal = eval(a, ctx, List())
      val bVal = eval(b, ctx, List())

      val aType = iType(i, ctx, a)
      checkUniverse(i, aType)

      val bType = iType(i, ctx, b)
      checkUniverse(i, bType)

      val lType = iType(i, ctx, l)
      checkEqual(i, lType, aVal)

      VSum(aVal, bVal)
    case InR(Sum(a, b), r) =>
      val aVal = eval(a, ctx, List())
      val bVal = eval(b, ctx, List())

      val aType = iType(i, ctx, a)
      checkUniverse(i, aType)

      val bType = iType(i, ctx, b)
      checkUniverse(i, bType)

      val rType = iType(i, ctx, r)
      checkEqual(i, rType, bVal)

      VSum(aVal, bVal)
    case SumElim(Sum(a, b), m, lc, rc, sum) =>
      val mVal = eval(m, ctx, List())
      val ltVal = eval(a, ctx, List())
      val rtVal = eval(b, ctx, List())
      val etVal = VSum(ltVal, rtVal)
      val sumVal = eval(sum, ctx, List())

      val aType = iType(i, ctx, a)
      checkUniverse(i, aType)

      val bType = iType(i, ctx, b)
      checkUniverse(i, bType)

      val mType = iType(i, ctx, m)
      checkEqual(i, mType, VPi(VSum(ltVal, rtVal), {_ => VUniverse(-1)}))

      val lcType = iType(i, ctx, lc)
      checkEqual(i, lcType, VPi(ltVal, {lVal => mVal @@ VInL(etVal, lVal)}))

      val rcType = iType(i, ctx, rc)
      checkEqual(i, rcType, VPi(rtVal, {rVal => mVal @@ VInR(etVal, rVal)}))

      val sumType = iType(i, ctx, sum)
      checkEqual(i, sumType, VSum(ltVal, rtVal))

      mVal @@ sumVal
    case _ =>
      super.iType(i, ctx, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Sum(a, b) =>
      Sum(iSubst(i, r, a), iSubst(i, r, b))
    case InL(et, x) =>
      InL(iSubst(i, r, et), iSubst(i, r, x))
    case InR(et, x) =>
      InR(iSubst(i, r, et), iSubst(i, r, x))
    case SumElim(et, m, lc, rc, sum) =>
      SumElim(iSubst(i, r, et), iSubst(i, r, m), iSubst(i, r, lc), iSubst(i, r, rc), iSubst(i, r, sum))
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait SumQuote extends CoreQuote with SumAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VSum(a, b) =>
      Sum(quote(ii, a), quote(ii, b))
    case VInL(et, x) =>
      InL(quote(ii, et), quote(ii, x))
    case VInR(et, x) =>
      InR(quote(ii, et), quote(ii, x))
    case _ =>
      super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NSumElim(et, m, lc, rc, sum) =>
      SumElim(quote(ii, et), quote(ii, m), quote(ii, lc), quote(ii, rc), neutralQuote(ii, sum))
    case _ => super.neutralQuote(ii, n)
  }
}

trait SumREPL extends CoreREPL with SumAST with SumMetaSyntax with SumPrinter with SumCheck with SumEval with SumQuote
