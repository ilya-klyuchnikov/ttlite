package superspec.lambdapi

trait ListAST extends CoreAST {
  case class PiNil(A: CTerm) extends CTerm
  case class PiCons(A: CTerm, head: CTerm, tail: CTerm) extends CTerm

  case class PiList(A: CTerm) extends ITerm
  case class PiListElim(A: CTerm, motive: CTerm, nilCase: CTerm, consCase: CTerm, l: CTerm) extends ITerm

  case class VPiList(A: Value) extends Value
  case class VPiNil(A: Value) extends Value
  case class VPiCons(A: Value, head: Value, tail: Value) extends Value

  case class NPiListElim(A: Value, motive: Value, nilCase: Value, consCase: Value, l: Neutral) extends Neutral
}

trait ListPrinter extends CorePrinter with ListAST {
  override def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case PiList(a) =>
      iPrint(p, ii, Free(Global("List")) @@ a)
    case PiListElim(a, m, mn, mc, xs) =>
      iPrint(p, ii, Free(Global("listElim")) @@ a @@ m @@ mn @@ mc @@ xs)
    case _ =>
      super.iPrint(p, ii, t)
  }

  override def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case PiNil(a) =>
      iPrint(p, ii, Free(Global("Nil")) @@ a)
    case PiCons(a, x, xs) =>
      iPrint(p, ii, Free(Global("VCons")) @@ a @@ x @@ xs)
    case _ =>
      super.cPrint(p, ii, t)
  }
}

trait ListEval extends CoreEval with ListAST {
  override def cEval(c: CTerm, nEnv: NameEnv[Value], bEnv: Env): Value = c match {
    case PiNil(a) =>
      VPiNil(cEval(a, nEnv, bEnv))
    case PiCons(a, head, tail) =>
      VPiCons(cEval(a, nEnv, bEnv), cEval(head, nEnv, bEnv), cEval(tail, nEnv, bEnv))
    case _ =>
      super.cEval(c, nEnv, bEnv)
  }

  override def iEval(i: ITerm, nEnv: NameEnv[Value], bEnv: Env): Value = i match {
    case PiList(a) =>
      VPiList(cEval(a, nEnv, bEnv))
    case PiListElim(a, m, nilCase, consCase, ls) =>
      val nilCaseVal = cEval(nilCase, nEnv, bEnv)
      val consCaseVal = cEval(consCase, nEnv, bEnv)
      def rec(listVal: Value): Value = listVal match {
        case VPiNil(_) =>
          nilCaseVal
        case VPiCons(_, head, tail) =>
          consCaseVal @@ head @@ tail @@ rec(tail)
        case VNeutral(n) =>
          VNeutral(NPiListElim(cEval(a, nEnv, bEnv), cEval(m, nEnv, bEnv), nilCaseVal, consCaseVal, n))
      }
      rec(cEval(ls, nEnv, bEnv))
    case _ =>
      super.iEval(i, nEnv, bEnv)
  }
}

trait ListCheck extends CoreCheck with ListAST with ListEval {
  override def iType(i: Int, nEnv: NameEnv[Value], ctx: Context, t: ITerm): Result[Type] = t match {
    case PiList(a) =>
      assert(cType(i, nEnv, ctx, a, VStar).isRight)
      Right(VStar)
    case PiListElim(a, m, nilCase, consCase, xs) =>
      assert(cType(i, nEnv, ctx, a, VStar).isRight)
      val aVal = cEval(a, nEnv, List())
      assert(cType(i, nEnv, ctx, m, VPi(VPiList(aVal), {_ => VStar})).isRight)

      val mVal = cEval(m, nEnv, List())
      assert(cType(i, nEnv, ctx, nilCase, mVal @@ VPiNil(aVal)).isRight)

      assert(cType(i, nEnv, ctx, consCase,
        VPi(aVal, {y => VPi(VPiList(aVal), {ys => VPi(mVal @@ ys, {_ => mVal @@ VPiCons(aVal, y, ys) }) }) })
      ).isRight)

      assert(cType(i, nEnv, ctx, xs, VPiList(aVal)).isRight)
      val vecVal = cEval(xs, nEnv, List())
      Right(mVal @@ vecVal)
    case _ =>
      super.iType(i, nEnv, ctx, t)
  }

  override def cType(ii: Int, nEnv: NameEnv[Value], ctx: Context, ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (PiNil(a), VPiList(bVal)) =>
      assert(cType(ii, nEnv, ctx, a, VStar).isRight)
      val aVal = cEval(a, nEnv, List())
      if (quote0(aVal) != quote0(bVal)) return Left("type mismatch")
      Right()
    case (PiCons(a, head, tail), VPiList(bVal)) =>
      assert(cType(ii, nEnv, ctx, a, VStar).isRight)
      val aVal = cEval(a, nEnv, List())
      if (quote0(aVal) != quote0(bVal)) return Left("type mismatch")
      assert(cType(ii, nEnv, ctx, head, aVal).isRight)
      assert(cType(ii, nEnv, ctx, tail, VPiList(bVal)).isRight)
      Right()
    case _ =>
      super.cType(ii, nEnv, ctx, ct, t)
  }

  override def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case PiList(a) =>
      PiList(cSubst(i, r, a))
    case PiListElim(a, m, nilCase, consCase, xs) =>
      PiListElim(cSubst(i, r, a), cSubst(i, r, m), cSubst(i, r, nilCase), cSubst(i, r, consCase), cSubst(i, r, xs))
    case _ => super.iSubst(i, r, it)
  }

  override def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case PiNil(a) =>
      PiNil(cSubst(ii, r, a))
    case PiCons(a, head, tail) =>
      PiCons(cSubst(ii, r, a), cSubst(ii, r, head), cSubst(ii, r, tail))
    case _ =>
      super.cSubst(ii, r, ct)
  }
}

trait ListQuote extends CoreQuote with ListAST {
  override def quote(ii: Int, v: Value): CTerm = v match {
    case VPiList(a) => Inf(PiList(quote(ii, a)))
    case VPiNil(a) => PiNil(quote(ii, a))
    case VPiCons(a, head, tail) => PiCons(quote(ii, a), quote(ii, head), quote(ii, tail))
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): ITerm = n match {
    case NPiListElim(a, m, nilCase, consCase, vec) =>
      PiListElim(quote(ii, a), quote(ii, m), quote(ii, nilCase), quote(ii, consCase), Inf(neutralQuote(ii, vec)))
    case _ => super.neutralQuote(ii, n)
  }
}

trait ListREPL extends CoreREPL with ListAST with ListPrinter with ListCheck with ListEval with ListQuote {
  lazy val listTE: Ctx[Value] =
    List(
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
    "forall A :: * . List A"
  val ConsTypeIn =
    "forall (A :: *) . forall (x :: A) . forall (xs :: List A) . List A"

  lazy val ListType = int.ieval(listVE, int.parseIO(int.iiparse, ListTypeIn).get)
  lazy val listElimType = int.ieval(listVE, int.parseIO(int.iiparse, listElimTypeIn).get)
  lazy val NilType = int.ieval(listVE, int.parseIO(int.iiparse, NilTypeIn).get)
  lazy val ConsType = int.ieval(listVE, int.parseIO(int.iiparse, ConsTypeIn).get)

  val listVE: Ctx[Value] =
    List(
      Global("List") -> VLam(a => VPiList(a)),
      Global("listElim") ->
        cEval(
          Lam(Lam(Lam(Lam(Lam(
            Inf(PiListElim(Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)))
            )))))),
          List(),List()),
      Global("Nil") -> VLam(a => VPiNil(a)),
      Global("Cons") -> VLam(a => VLam(x => VLam(y => VPiCons(a, x, y))))
    )
}