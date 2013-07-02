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

trait SumPrinter extends CorePrinter with SumAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Sum(a, b) =>
      print(p, ii, Free(Global("Sum")) @@ a @@ b)
    case InL(lt, rt, l) =>
      print(p, ii, Free(Global("InL")) @@ lt @@ rt @@ l)
    case InR(lt, rt, r) =>
      print(p, ii, Free(Global("InL")) @@ lt @@ rt @@ r)
    case SumElim(lt, rt, m, lc, rc, sum) =>
      print(p, ii, Free(Global("cases")) @@ lt @@ rt @@ m @@ lc @@ rc @@ sum)
    case _ =>
      super.print(p, ii, t)
  }
}

trait SumEval extends CoreEval with SumAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Sum(lt, rt) =>
      VSum(eval(lt, named, bound), eval(rt, named, bound))
    case InL(lt, rt, l) =>
      VInL(eval(lt, named, bound), eval(rt, named, bound), eval(l, named, bound))
    case InR(lt, rt, r) =>
      VInR(eval(lt, named, bound), eval(rt, named, bound), eval(r, named, bound))
    case SumElim(lt, rt, m, lc, rc, sum) =>
      val sumVal = eval(sum, named, bound)
      sumVal match {
        case VInL(_, _, lVal) =>
          val lcVal = eval(lc, named, bound)
          lcVal @@ lVal
        case VInR(_, _, rVal) =>
          val rcVal = eval(rc, named, bound)
          rcVal @@ rVal
        case VNeutral(n) =>
          VNeutral(
            NSumElim(
              eval(lt, named, bound),
              eval(rt, named, bound),
              eval(m, named, bound),
              eval(lc, named, bound),
              eval(rc, named, bound), n)
          )
      }
    case _ =>
      super.eval(t, named, bound)
  }
}

trait SumCheck extends CoreCheck with SumAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Sum(a, b) =>
      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val bType = iType(i, named, bound, b)
      checkEqual(bType, Star)

      VStar
    case InL(a, b, l) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val bType = iType(i, named, bound, b)
      checkEqual(bType, Star)

      val lType = iType(i, named, bound, l)
      checkEqual(lType, aVal)

      VSum(aVal, bVal)
    case InR(a, b, r) =>
      val aVal = eval(a, named, List())
      val bVal = eval(b, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val bType = iType(i, named, bound, b)
      checkEqual(bType, Star)

      val rType = iType(i, named, bound, r)
      checkEqual(rType, bVal)

      VSum(aVal, bVal)
    case SumElim(a, b, m, lc, rc, sum) =>
      val mVal = eval(m, named, List())
      val ltVal = eval(a, named, List())
      val rtVal = eval(b, named, List())
      val sumVal = eval(sum, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val bType = iType(i, named, bound, b)
      checkEqual(bType, Star)

      val mType = iType(i, named, bound, m)
      checkEqual(mType, VPi(VSum(ltVal, rtVal), {_ => VStar}))

      val lcType = iType(i, named, bound, lc)
      checkEqual(lcType, VPi(ltVal, {lVal => mVal @@ VInL(ltVal, rtVal, lVal)}))

      val rcType = iType(i, named, bound, lc)
      checkEqual(rcType, VPi(rtVal, {rVal => mVal @@ VInL(ltVal, rtVal, rVal)}))

      val sumType = iType(i, named, bound, sum)
      checkEqual(sumType, VSum(ltVal, rtVal))

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

trait SumREPL extends CoreREPL with SumAST with SumPrinter with SumCheck with SumEval with SumQuote {
  lazy val sumTE: NameEnv[Value] =
    Map(
      Global("Sum") ->
        VPi(VStar, _ => VPi(VStar, _ => VStar)),
      Global("InL") ->
        VPi(VStar, a => VPi(VStar, b => VPi(a, _ => VSum(a, b)))),
      Global("InR") ->
        VPi(VStar, a => VPi(VStar, b => VPi(b, _ => VSum(a, b)))),
      Global("cases") -> sumElimType
    )
  val sumElimTypeIn =
    """
      |forall (A :: *) .
      |forall (B :: *) .
      |forall (m :: forall (_ :: Sum A B) . *) .
      |forall (_ :: forall (l :: A) . m (InL A B l)) .
      |forall (_ :: forall (r :: B) . m (InR A B r)) .
      |forall (s :: Sum A B) .
      |  m s
    """.stripMargin

  lazy val sumElimType = int.ieval(sumVE, int.parseIO(int.iParse, sumElimTypeIn).get)

  val sumVE: NameEnv[Value] =
    Map(
      Global("Sum") ->
        VLam(VStar, a => VLam(VStar, b => VSum(a, b))),
      Global("InL") ->
        VLam(VStar, a => VLam(VStar, b => VLam(a, x => VInL(a, b, x)))),
      Global("InR") ->
        VLam(VStar, a => VLam(VStar, b => VLam(b, y => VInR(a, b, y)))),
      Global("cases") ->
        VLam(VStar, a =>
          VLam(VStar, b =>
            VLam(VPi(VSum(a, b), _ => VStar), m =>
              VLam(VPi(a, l => m @@ VInL(a, b, l)) , lc =>
                VLam(VPi(b, r => m @@ VInR(a, b, r)), rc =>
                  VLam(VSum(a, b), {n =>
                    eval(quote0(VNeutral(NSumElim(a, b, m, lc, rc, NFree(tmp)))), sumVE + (tmp -> n), Nil)
                  }))))))
    )

}
