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

trait ListPrinter extends CorePrinter with ListAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case PiList(a) =>
      print(p, ii, Free(Global("List")) @@ a)
    case PiNil(a) =>
      print(p, ii, Free(Global("Nil")) @@ a)
    case PiCons(a, x, xs) =>
      print(p, ii, Free(Global("Cons")) @@ a @@ x @@ xs)
    case PiListElim(a, m, mn, mc, xs) =>
      print(p, ii, Free(Global("listElim")) @@ a @@ m @@ mn @@ mc @@ xs)
    case _ =>
      super.print(p, ii, t)
  }
}

trait ListEval extends CoreEval with ListAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case PiList(a) =>
      VPiList(eval(a, named, bound))
    case PiNil(a) =>
      VPiNil(eval(a, named, bound))
    case PiCons(a, head, tail) =>
      VPiCons(eval(a, named, bound), eval(head, named, bound), eval(tail, named, bound))
    case PiListElim(a, m, nilCase, consCase, ls) =>
      val nilCaseVal = eval(nilCase, named, bound)
      val consCaseVal = eval(consCase, named, bound)
      def rec(listVal: Value): Value = listVal match {
        case VPiNil(_) =>
          nilCaseVal
        case VPiCons(_, head, tail) =>
          consCaseVal @@ head @@ tail @@ rec(tail)
        case VNeutral(n) =>
          VNeutral(NPiListElim(eval(a, named, bound), eval(m, named, bound), nilCaseVal, consCaseVal, n))
      }
      rec(eval(ls, named, bound))
    case _ =>
      super.eval(t, named, bound)
  }
}

trait ListCheck extends CoreCheck with ListAST with ListEval {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case PiList(a) =>
      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, Star)
      VStar
    case PiNil(a) =>
      val aVal = eval(a, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, Star)

      VPiList(aVal)
    case PiCons(a, head, tail) =>
      val aVal = eval(a, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, Star)

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
      checkEqual(i, aType, Star)

      val mType = iType(i, named, bound, m)
      checkEqual(i, mType, VPi(VPiList(aVal), {_ => VStar}))

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

trait ListREPL extends CoreREPL with ListAST with ListPrinter with ListCheck with ListEval with ListQuote {
  lazy val listTE: NameEnv[Value] =
    Map(
      Global("List") -> ListType,
      Global("listElim") -> listElimType,
      Global("Nil") -> NilType,
      Global("Cons") -> ConsType
    )

  val ListTypeIn =
    "forall (a :: *) . *"
  val listElimTypeIn =
    """
      |forall (A :: *) .
      |forall (m :: forall (z :: List A) . *) .
      |forall (_ :: m (Nil A)) .
      |forall (_ :: forall (x :: A) . forall (xs :: List A) . forall (d :: m xs) . m (Cons A x xs)) .
      |forall (ys :: List A) .
      |  m ys
    """.stripMargin
  val NilTypeIn =
    "forall (A :: *) . List A"
  val ConsTypeIn =
    "forall (A :: *) . forall (x :: A) . forall (xs :: List A) . List A"

  lazy val ListType = int.ieval(listVE, int.parseIO(int.iParse, ListTypeIn).get)
  lazy val listElimType = int.ieval(listVE, int.parseIO(int.iParse, listElimTypeIn).get)
  lazy val NilType = int.ieval(listVE, int.parseIO(int.iParse, NilTypeIn).get)
  lazy val ConsType = int.ieval(listVE, int.parseIO(int.iParse, ConsTypeIn).get)

  val listVE: NameEnv[Value] =
    Map(
      Global("List") -> VLam(VStar, a => VPiList(a)),
      Global("Nil") -> VLam(VStar, a => VPiNil(a)),
      Global("Cons") -> VLam(VStar, a => VLam(a, x => VLam(VPiList(a), y => VPiCons(a, x, y)))),
      Global("listElim") ->
        VLam(VStar, a =>
          VLam(VPi(VPiList(a), _ => VStar), m =>
            VLam(m @@ VPiNil(a), nilCase =>
              VLam(VPi(a, x => VPi(VPiList(a), xs => VPi(m @@ xs, _ => m @@ VPiCons(a, x, xs)))), consCase =>
                VLam(VPiList(a), {xs =>
                  eval(PiListElim(Bound(4), Bound(3), Bound(2), Bound(1), Bound(0)), listVE,
                    List(xs, consCase, nilCase, m, a))
                })))))
    )
}
