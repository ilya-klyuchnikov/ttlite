package superspec.tt

trait ListAST extends CoreAST {
  case class PiList(A: Term) extends Term
  case class PiNil(A: Term) extends Term
  case class PiCons(A: Term, head: Term, tail: Term) extends Term
  case class PiListElim(A: Term, motive: Term, nilCase: Term, consCase: Term, l: Term) extends Term

  case class VPiList(A: Value) extends Value
  case class VPiNil(A: Value) extends Value
  case class VPiCons(A: Value, head: Value, tail: Value) extends Value
  case class NPiListElim(A: Value, motive: Value, nilCase: Value, consCase: Value, l: Neutral) extends Neutral
}

trait ListMetaSyntax extends CoreMetaSyntax with ListAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("List")) @@ a =>
      PiList(fromM(a))
    case MVar(Global("Nil")) @@ a =>
      PiNil(fromM(a))
    case MVar(Global("Cons")) @@ a @@ h @@ t =>
      PiCons(fromM(a), fromM(h), fromM(t))
    case MVar(Global("listElim")) @@ a @@ m @@ cN @@ cC @@ n =>
      PiListElim(fromM(a), fromM(m), fromM(cN), fromM(cC), fromM(n))
    case _ => super.fromM(m)
  }
}

trait ListPrinter extends FunPrinter with ListAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case PiList(a) =>
      print(p, ii, 'List @@ a)
    case PiNil(a) =>
      print(p, ii, 'Nil @@ a)
    case PiCons(a, x, xs) =>
      print(p, ii, 'Cons @@ a @@ x @@ xs)
    case PiListElim(a, m, mn, mc, xs) =>
      print(p, ii, 'listElim @@ a @@ m @@ mn @@ mc @@ xs)
    case _ =>
      super.print(p, ii, t)
  }
}

trait ListEval extends FunEval with ListAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case PiList(a) =>
      VPiList(eval(a, named, bound))
    case PiNil(a) =>
      VPiNil(eval(a, named, bound))
    case PiCons(a, head, tail) =>
      VPiCons(eval(a, named, bound), eval(head, named, bound), eval(tail, named, bound))
    case PiListElim(a, m, nilCase, consCase, ls) =>
      val aVal = eval(a, named, bound)
      val mVal = eval(m, named, bound)
      val nilCaseVal = eval(nilCase, named, bound)
      val consCaseVal = eval(consCase, named, bound)
      val listVal = eval(ls, named, bound)
      listElim(aVal, mVal, nilCaseVal, consCaseVal, listVal)
    case _ =>
      super.eval(t, named, bound)
  }

  def listElim(aVal: Value, mVal: Value, nilCaseVal: Value, consCaseVal: Value, listVal: Value): Value = listVal match {
    case VPiNil(_) =>
      nilCaseVal
    case VPiCons(_, head, tail) =>
      consCaseVal @@ head @@ tail @@ listElim(aVal, mVal, nilCaseVal, consCaseVal, tail)
    case VNeutral(n) =>
      VNeutral(NPiListElim(aVal, mVal, nilCaseVal, consCaseVal, n))
  }
}

trait ListCheck extends FunCheck with ListAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case PiList(a) =>
      val aType = iType(i, named, bound, a)
      val j = checkUniverse(i, aType)
      VUniverse(j)
    case PiNil(a) =>
      val aVal = eval(a, named, List())

      val aType = iType(i, named, bound, a)
      checkUniverse(i, aType)

      VPiList(aVal)
    case PiCons(a, head, tail) =>
      val aVal = eval(a, named, List())

      val aType = iType(i, named, bound, a)
      checkUniverse(i, aType)

      val hType = iType(i, named, bound, head)
      checkEqual(i, hType, aVal)

      val tType = iType(i, named, bound, tail)
      checkEqual(i, tType, VPiList(aVal))

      VPiList(aVal)
    case PiListElim(a, m, nilCase, consCase, xs) =>
      val aVal = eval(a, named, List())
      val mVal = eval(m, named, List())
      val xsVal = eval(xs, named, List())

      val aType = iType(i, named, bound, a)
      checkUniverse(i, aType)

      val mType = iType(i, named, bound, m)
      checkEqual(i, mType, VPi(VPiList(aVal), {_ => VUniverse(-1)}))

      val nilCaseType = iType(i, named, bound, nilCase)
      checkEqual(i, nilCaseType, mVal @@ VPiNil(aVal))

      val consCaseType = iType(i, named, bound, consCase)
      checkEqual(i, consCaseType,
        VPi(aVal, {y => VPi(VPiList(aVal), {ys => VPi(mVal @@ ys, {_ => mVal @@ VPiCons(aVal, y, ys) }) }) })
      )

      val xsType = iType(i, named, bound, xs)
      checkEqual(i, xsType, VPiList(aVal))

      mVal @@ xsVal
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case PiList(a) =>
      PiList(iSubst(i, r, a))
    case PiNil(a) =>
      PiNil(iSubst(i, r, a))
    case PiCons(a, head, tail) =>
      PiCons(iSubst(i, r, a), iSubst(i, r, head), iSubst(i, r, tail))
    case PiListElim(a, m, nilCase, consCase, xs) =>
      PiListElim(iSubst(i, r, a), iSubst(i, r, m), iSubst(i, r, nilCase), iSubst(i, r, consCase), iSubst(i, r, xs))
    case _ => super.iSubst(i, r, it)
  }
}

trait ListQuote extends CoreQuote with ListAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VPiList(a) =>
      PiList(quote(ii, a))
    case VPiNil(a) =>
      PiNil(quote(ii, a))
    case VPiCons(a, head, tail) =>
      PiCons(quote(ii, a), quote(ii, head), quote(ii, tail))
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NPiListElim(a, m, nilCase, consCase, vec) =>
      PiListElim(quote(ii, a), quote(ii, m), quote(ii, nilCase), quote(ii, consCase), neutralQuote(ii, vec))
    case _ => super.neutralQuote(ii, n)
  }
}

trait ListREPL extends CoreREPL with ListAST with ListMetaSyntax with ListPrinter with ListCheck with ListEval with ListQuote
