package superspec.tt

trait SumAST extends CoreAST {
  // left injection
  case class InL(L: CTerm, R: CTerm, l: CTerm) extends CTerm
  // righ injection
  case class InR(L: CTerm, R: CTerm, r: CTerm) extends CTerm

  case class Sum(A: CTerm, B: CTerm) extends ITerm
  // cases (m = motive)
  case class SumElim(L: CTerm, R: CTerm, m: CTerm, lCase: CTerm, rCase: CTerm, sum: CTerm) extends ITerm

  case class VSum(L: Value, R: Value) extends Value
  case class VInL(L: Value, R: Value, l: Value) extends Value
  case class VInR(L: Value, R: Value, r: Value) extends Value

  case class NSumElim(L: Value, R: Value, m: Value, lCase: Value, rCase: Value, sum: Neutral) extends Neutral
}

trait SumPrinter extends CorePrinter with SumAST {
  override def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Sum(a, b) =>
      iPrint(p, ii, Free(Global("Sum")) @@ a @@ b)
    case SumElim(lt, rt, m, lc, rc, sum) =>
      iPrint(p, ii, Free(Global("cases")) @@ lt @@ rt @@ m @@ lc @@ rc @@ sum)
    case _ =>
      super.iPrint(p, ii, t)
  }

  override def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case InL(lt, rt, l) =>
      iPrint(p, ii, Free(Global("InL")) @@ lt @@ rt @@ l)
    case InR(lt, rt, r) =>
      iPrint(p, ii, Free(Global("InL")) @@ lt @@ rt @@ r)
    case _ =>
      super.cPrint(p, ii, t)
  }
}

trait SumEval extends CoreEval with SumAST {
  override def eval(t: CTerm, named: NameEnv[Value], bound: Env): Value = t match {
    case InL(lt, rt, l) =>
      VInL(eval(lt, named, bound), eval(rt, named, bound), eval(l, named, bound))
    case InR(lt, rt, r) =>
      VInR(eval(lt, named, bound), eval(rt, named, bound), eval(r, named, bound))
    case _ =>
      super.eval(t, named, bound)
  }

  override def eval(t: ITerm, named: NameEnv[Value], bound: Env): Value = t match {
    case Sum(lt, rt) =>
      VSum(eval(lt, named, bound), eval(rt, named, bound))
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
  // I have an assumption, that there is not need of this
  // It will be done automatically
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: ITerm): Result[Type] = t match {
    case Sum(a, b) =>
      assert(cType(i, named, bound, a, VStar).isRight)
      assert(cType(i, named, bound, b, VStar).isRight)
      Right(VStar)
    case SumElim(lt, rt, m, lc, rc, sum) =>
      // checking types
      assert(cType(i, named, bound, lt, VStar).isRight)
      assert(cType(i, named, bound, rt, VStar).isRight)

      val ltVal = eval(lt, named, List())
      val rtVal = eval(rt, named, List())

      // checking motive
      assert(cType(i, named, bound, m, VPi(VSum(ltVal, rtVal), {_ => VStar})).isRight)
      val mVal = eval(m, named, List())

      // checking branches
      assert(cType(i, named, bound, lc, VPi(ltVal, {lVal => mVal @@ VInL(ltVal, rtVal, lVal)})).isRight)
      assert(cType(i, named, bound, rc, VPi(rtVal, {rVal => mVal @@ VInL(ltVal, rtVal, rVal)})).isRight)

      // checking sum
      assert(cType(i, named, bound, sum, VSum(ltVal, rtVal)).isRight)
      val sumVal = eval(sum, named, List())

      Right(mVal @@ sumVal)
    case _ =>
      super.iType(i, named, bound, t)
  }


  override def cType(ii: Int, named: NameEnv[Value], bound: NameEnv[Value], ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (InL(lt, rt, l), VSum(ltVal, rtVal)) =>
      assert(cType(ii, named, bound, lt, VStar).isRight)
      assert(cType(ii, named, bound, rt, VStar).isRight)
      if (quote0(eval(lt, named, List())) != quote0(ltVal))
        return Left("type mismatch")
      if (quote0(eval(rt, named, List())) != quote0(rtVal))
        return Left("type mismatch")
      assert(cType(ii, named, bound, l, ltVal).isRight)
      Right(())
    case (InR(lt, rt, r), VSum(ltVal, rtVal)) =>
      assert(cType(ii, named, bound, lt, VStar).isRight)
      assert(cType(ii, named, bound, rt, VStar).isRight)
      if (quote0(eval(lt, named, List())) != quote0(ltVal))
        return Left("type mismatch")
      if (quote0(eval(rt, named, List())) != quote0(rtVal))
        return Left("type mismatch")
      assert(cType(ii, named, bound, r, rtVal).isRight)
      Right(())
    case _ =>
      super.cType(ii, named, bound, ct, t)
  }

  override def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Sum(a, b) =>
      Sum(cSubst(i, r, a), cSubst(i, r, b))
    case SumElim(lt, rt, m, lc, rc, sum) =>
      SumElim(cSubst(i, r, lt), cSubst(i, r, rt), cSubst(i, r, m), cSubst(i, r, lc), cSubst(i, r, rc), cSubst(i, r, sum))
    case _ => super.iSubst(i, r, it)
  }

  override def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case InL(a, b, x) =>
      InL(cSubst(ii, r, a), cSubst(ii, r, b), cSubst(ii, r, x))
    case InR(a, b, x) =>
      InR(cSubst(ii, r, a), cSubst(ii, r, b), cSubst(ii, r, x))
    case _ =>
      super.cSubst(ii, r, ct)
  }

}

trait SumQuote extends CoreQuote with SumAST {
  override def quote(ii: Int, v: Value): CTerm = v match {
    case VSum(a, b) => Inf(Sum(quote(ii, a), quote(ii, b)))
    case VInL(a, b, x) => InL(quote(ii, a), quote(ii, b), quote(ii, x))
    case VInR(a, b, x) => InR(quote(ii, a), quote(ii, b), quote(ii, x))
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): ITerm = n match {
    case NSumElim(lt, rt, m, lc, rc, sum) =>
      SumElim(quote(ii, lt), quote(ii, rt), quote(ii, m), quote(ii, lc), quote(ii, rc), Inf(neutralQuote(ii, sum)))
    case _ => super.neutralQuote(ii, n)
  }
}

trait SumREPL extends CoreREPL with SumAST with SumPrinter with SumCheck with SumEval with SumQuote {
  lazy val sumTE: Ctx[Value] =
    List(
      Global("Sum") -> VPi(VStar, _ => VPi(VStar, _ => VStar)),
      Global("InL") -> VPi(VStar, a => VPi(VStar, b => VPi(a, _ => VSum(a, b)))),
      Global("InR") -> VPi(VStar, a => VPi(VStar, b => VPi(b, _ => VSum(a, b)))),
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

  lazy val sumElimType = int.ieval(sumVE, int.parseIO(int.iiparse, sumElimTypeIn).get)

  val sumVE: Ctx[Value] =
    List(
      Global("Sum") -> VLam(a => VLam(b => VSum(a, b))),
      Global("InL") -> VLam(a => VLam(b => VLam(x => VInL(a, b, x)))),
      Global("InR") -> VLam(a => VLam(b => VLam(x => VInR(a, b, x)))),
      Global("cases") ->
        eval(
          Lam(Lam(Lam(Lam(Lam(Lam(
            Inf(SumElim(Inf(Bound(5)), Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0))))
          )))))), Nil, Nil)
    )

}
