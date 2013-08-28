package superspec.tt

trait ListAST extends CoreAST {
  case class PiList(A: Term) extends Term
  case class PiNil(et: Term) extends Term
  case class PiCons(et: Term, head: Term, tail: Term) extends Term
  case class PiListElim(et: Term, motive: Term, nilCase: Term, consCase: Term, l: Term) extends Term

  case class VPiList(A: Value) extends Value
  case class VPiNil(et: Value) extends Value
  case class VPiCons(et: Value, head: Value, tail: Value) extends Value
  case class NPiListElim(et: Value, motive: Value, nilCase: Value, consCase: Value, l: Neutral) extends Neutral
}

trait ListMetaSyntax extends CoreMetaSyntax with ListAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("List")) @@ a =>
      PiList(fromM(a))
    case MVar(Global("Nil")) @@ a =>
      PiNil(fromM(a))
    case MVar(Global("Cons")) @@ a @@ h @@ t =>
      PiCons(fromM(a), fromM(h), fromM(t))
    case MVar(Global("elim")) @@ (MVar(Global("List")) @@ a) @@ m @@ cN @@ cC @@ n =>
      PiListElim(PiList(fromM(a)), fromM(m), fromM(cN), fromM(cC), fromM(n))
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
      print(p, ii, 'elim @@ a @@ m @@ mn @@ mc @@ xs)
    case _ =>
      super.print(p, ii, t)
  }
}

trait ListEval extends FunEval with ListAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case PiList(a) =>
      VPiList(eval(a, named, bound))
    case PiNil(et) =>
      VPiNil(eval(et, named, bound))
    case PiCons(et, head, tail) =>
      VPiCons(eval(et, named, bound), eval(head, named, bound), eval(tail, named, bound))
    case PiListElim(et, m, nilCase, consCase, ls) =>
      val etVal = eval(et, named, bound)
      val mVal = eval(m, named, bound)
      val nilCaseVal = eval(nilCase, named, bound)
      val consCaseVal = eval(consCase, named, bound)
      val listVal = eval(ls, named, bound)
      listElim(etVal, mVal, nilCaseVal, consCaseVal, listVal)
    case _ =>
      super.eval(t, named, bound)
  }

  def listElim(etVal: Value, mVal: Value, nilCaseVal: Value, consCaseVal: Value, listVal: Value): Value = listVal match {
    case VPiNil(_) =>
      nilCaseVal
    case VPiCons(_, head, tail) =>
      consCaseVal @@ head @@ tail @@ listElim(etVal, mVal, nilCaseVal, consCaseVal, tail)
    case VNeutral(n) =>
      VNeutral(NPiListElim(etVal, mVal, nilCaseVal, consCaseVal, n))
  }
}

trait ListCheck extends FunCheck with ListAST {
  override def iType(i: Int, ctx: Context[Value], t: Term): Value = t match {
    case PiList(a) =>
      val aType = iType(i, ctx, a)
      val j = checkUniverse(i, aType)
      VUniverse(j)
    case PiNil(et) =>
      val eType = iType(i, ctx, et)
      checkUniverse(i, eType)

      val VPiList(aVal) = eval(et, ctx.vals, List())
      VPiList(aVal)
    case PiCons(et, head, tail) =>
      val eType = iType(i, ctx, et)
      checkUniverse(i, eType)

      val VPiList(aVal) = eval(et, ctx.vals, List())

      val hType = iType(i, ctx, head)
      checkEqual(i, hType, aVal)

      val tType = iType(i, ctx, tail)
      checkEqual(i, tType, VPiList(aVal))

      VPiList(aVal)
    case PiListElim(et, m, nilCase, consCase, xs) =>
      val eType = iType(i, ctx, et)
      checkUniverse(i, eType)

      val VPiList(aVal) = eval(et, ctx.vals, List())

      val mVal = eval(m, ctx.vals, List())
      val xsVal = eval(xs, ctx.vals, List())

      val mType = iType(i, ctx, m)
      checkEqual(i, mType, VPi(VPiList(aVal), {_ => VUniverse(-1)}))

      val nilCaseType = iType(i, ctx, nilCase)
      checkEqual(i, nilCaseType, mVal @@ VPiNil(aVal))

      val consCaseType = iType(i, ctx, consCase)
      checkEqual(i, consCaseType,
        VPi(aVal, {y => VPi(VPiList(aVal), {ys => VPi(mVal @@ ys, {_ => mVal @@ VPiCons(aVal, y, ys) }) }) })
      )

      val xsType = iType(i, ctx, xs)
      checkEqual(i, xsType, VPiList(aVal))

      mVal @@ xsVal
    case _ =>
      super.iType(i, ctx, t)
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
