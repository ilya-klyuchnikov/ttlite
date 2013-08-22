package superspec.tt

trait SumAST extends CoreAST {
  case class Sum(A: Term, B: Term) extends Term
  case class InL(L: Term, R: Term, l: Term) extends Term
  case class InR(L: Term, R: Term, r: Term) extends Term
  case class SumElim(L: Term, R: Term, m: Term, lCase: Term, rCase: Term, sum: Term) extends Term

  case class VSum(L: Value, R: Value) extends Value
  case class VInL(L: Value, R: Value, l: Value) extends Value
  case class VInR(L: Value, R: Value, r: Value) extends Value
  case class NSumElim(L: Value, R: Value, m: Value, lCase: Value, rCase: Value, sum: Neutral) extends Neutral
}

trait MSum extends MCore with SumAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Sum")) @@ l @@ r =>
      Sum(fromM(l), fromM(r))
    case MVar(Global("InL")) @@ l @@ r @@ inj =>
      InL(fromM(l), fromM(r), fromM(inj))
    case MVar(Global("InR")) @@ l @@ r @@ inj =>
      InR(fromM(l), fromM(r), fromM(inj))
    case MVar(Global("sumElim")) @@ l @@ r @@ m @@ lc @@ rc @@ inj =>
      SumElim(fromM(l), fromM(r), fromM(m), fromM(lc), fromM(rc), fromM(inj))
    case _ => super.fromM(m)
  }
}

trait SumPrinter extends FunPrinter with SumAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Sum(a, b) =>
      print(p, ii, 'Sum @@ a @@ b)
    case InL(lt, rt, l) =>
      print(p, ii, 'InL @@ lt @@ rt @@ l)
    case InR(lt, rt, r) =>
      print(p, ii, 'InR @@ lt @@ rt @@ r)
    case SumElim(lt, rt, m, lc, rc, sum) =>
      print(p, ii, 'sumElim @@ lt @@ rt @@ m @@ lc @@ rc @@ sum)
    case _ =>
      super.print(p, ii, t)
  }
}

trait SumEval extends FunEval with SumAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Sum(lt, rt) =>
      VSum(eval(lt, named, bound), eval(rt, named, bound))
    case InL(lt, rt, l) =>
      VInL(eval(lt, named, bound), eval(rt, named, bound), eval(l, named, bound))
    case InR(lt, rt, r) =>
      VInR(eval(lt, named, bound), eval(rt, named, bound), eval(r, named, bound))
    case SumElim(lt, rt, m, lc, rc, sum) =>
      val ltVal = eval(lt, named, bound)
      val rtVal = eval(rt, named, bound)
      val mVal = eval(m, named, bound)
      val lcVal = eval(lc, named, bound)
      val rcVal = eval(rc, named, bound)
      val sumVal = eval(sum, named, bound)
      sumElim(ltVal, rtVal, mVal, lcVal, rcVal, sumVal)
    case _ =>
      super.eval(t, named, bound)
  }

  def sumElim(ltVal: Value, rtVal: Value, mVal: Value, lcVal: Value, rcVal: Value, sumVal: Value): Value =
    sumVal match {
      case VInL(_, _, lVal) =>
        lcVal @@ lVal
      case VInR(_, _, rVal) =>
        rcVal @@ rVal
      case VNeutral(n) =>
        VNeutral(NSumElim(ltVal, rtVal, mVal, lcVal, rcVal, n))
    }
}

trait SumCheck extends FunCheck with SumAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Sum(a, b) =>
      val aType = iType(i, named, bound, a)
      val j = checkUniverse(i, aType)

      val bType = iType(i, named, bound, b)
      val k = checkUniverse(i, bType)

      VUniverse(math.max(j, k))
    case InL(a, b, l) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())

      val aType = iType(i, named, bound, a)
      checkUniverse(i, aType)

      val bType = iType(i, named, bound, b)
      checkUniverse(i, bType)

      val lType = iType(i, named, bound, l)
      checkEqual(i, lType, aVal)

      VSum(aVal, bVal)
    case InR(a, b, r) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())

      val aType = iType(i, named, bound, a)
      checkUniverse(i, aType)

      val bType = iType(i, named, bound, b)
      checkUniverse(i, bType)

      val rType = iType(i, named, bound, r)
      checkEqual(i, rType, bVal)

      VSum(aVal, bVal)
    case SumElim(a, b, m, lc, rc, sum) =>
      val mVal = eval(m, named, List())
      val ltVal = eval(a, named, List())
      val rtVal = eval(b, named, List())
      val sumVal = eval(sum, named, List())

      val aType = iType(i, named, bound, a)
      checkUniverse(i, aType)

      val bType = iType(i, named, bound, b)
      checkUniverse(i, bType)

      val mType = iType(i, named, bound, m)
      checkEqual(i, mType, VPi(VSum(ltVal, rtVal), {_ => VUniverse(-1)}))

      val lcType = iType(i, named, bound, lc)
      checkEqual(i, lcType, VPi(ltVal, {lVal => mVal @@ VInL(ltVal, rtVal, lVal)}))

      val rcType = iType(i, named, bound, rc)
      checkEqual(i, rcType, VPi(rtVal, {rVal => mVal @@ VInR(ltVal, rtVal, rVal)}))

      val sumType = iType(i, named, bound, sum)
      checkEqual(i, sumType, VSum(ltVal, rtVal))

      mVal @@ sumVal
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Sum(a, b) =>
      Sum(iSubst(i, r, a), iSubst(i, r, b))
    case InL(a, b, x) =>
      InL(iSubst(i, r, a), iSubst(i, r, b), iSubst(i, r, x))
    case InR(a, b, x) =>
      InR(iSubst(i, r, a), iSubst(i, r, b), iSubst(i, r, x))
    case SumElim(lt, rt, m, lc, rc, sum) =>
      SumElim(iSubst(i, r, lt), iSubst(i, r, rt), iSubst(i, r, m), iSubst(i, r, lc), iSubst(i, r, rc), iSubst(i, r, sum))
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait SumQuote extends CoreQuote with SumAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VSum(a, b) =>
      Sum(quote(ii, a), quote(ii, b))
    case VInL(a, b, x) =>
      InL(quote(ii, a), quote(ii, b), quote(ii, x))
    case VInR(a, b, x) =>
      InR(quote(ii, a), quote(ii, b), quote(ii, x))
    case _ =>
      super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NSumElim(lt, rt, m, lc, rc, sum) =>
      SumElim(quote(ii, lt), quote(ii, rt), quote(ii, m), quote(ii, lc), quote(ii, rc), neutralQuote(ii, sum))
    case _ => super.neutralQuote(ii, n)
  }
}

trait SumREPL2 extends CoreREPL2 with SumAST with MSum with SumPrinter with SumCheck with SumEval with SumQuote
