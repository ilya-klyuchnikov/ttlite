package superspec.tt

import mrsc.core._
import superspec._

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

trait ListSubst extends CoreSubst with ListAST {
  override def findSubst0(from: CTerm, to: CTerm): Option[Subst] = (from, to) match {
    case (PiNil(a1), PiNil(a2)) =>
      findSubst0(a1, a2)
    case (PiCons(a1, h1, t1), PiCons(a2, h2, t2)) =>
      mergeOptSubst(
        findSubst0(a1, a2),
        findSubst0(h1, h2),
        findSubst0(t1, t2)
      )
    case _ =>
      super.findSubst0(from, to)
  }

  override def findSubst0(from: ITerm, to: ITerm): Option[Subst] = (from, to) match {
    case (PiList(a1), PiList(a2)) =>
      findSubst0(a1, a2)
    case (PiListElim(a1, m1, nCase1, cCase1, xs1), PiListElim(a2, m2, nCase2, cCase2, xs2)) =>
      mergeOptSubst(
        findSubst0(a1, a2),
        findSubst0(m1, m2),
        findSubst0(nCase1, nCase2),
        findSubst0(cCase1, cCase2),
        findSubst0(xs1, xs2)
      )
    case _ =>
      super.findSubst0(from, to)
  }

  override def isFreeSubTerm(t: CTerm, depth: Int): Boolean = t match {
    case PiNil(a) =>
      isFreeSubTerm(a, depth)
    case PiCons(a, h, t) =>
      isFreeSubTerm(a, depth) && isFreeSubTerm(h, depth) && isFreeSubTerm(t, depth)
    case _ =>
      super.isFreeSubTerm(t, depth)
  }

  override def isFreeSubTerm(t: ITerm, depth: Int): Boolean = t match {
    case PiList(a) =>
      isFreeSubTerm(a, depth)
    case PiListElim(a, m, nCase, cCase, xs) =>
      isFreeSubTerm(a, depth) && isFreeSubTerm(m, depth) &&
        isFreeSubTerm(nCase, depth) && isFreeSubTerm(cCase, depth) && isFreeSubTerm(xs, depth)
    case _ =>
      super.isFreeSubTerm(t, depth)
  }
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
  override def eval(t: CTerm, named: NameEnv[Value], bound: Env): Value = t match {
    case PiNil(a) =>
      VPiNil(eval(a, named, bound))
    case PiCons(a, head, tail) =>
      VPiCons(eval(a, named, bound), eval(head, named, bound), eval(tail, named, bound))
    case _ =>
      super.eval(t, named, bound)
  }

  override def eval(t: ITerm, named: NameEnv[Value], bound: Env): Value = t match {
    case PiList(a) =>
      VPiList(eval(a, named, bound))
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

trait ListDriver extends CoreDriver with ListAST {

  // boilerplate/indirections
  case object NilLabel extends Label
  case object ConsLabel extends Label

  case class NilStep(a: CTerm) extends Step {
    override val graphStep =
      AddChildNodesStep[CTerm, Label](List(a -> NilLabel))
  }
  case class NilDStep(a: CTerm) extends DriveStep {
    override def step(t: CTerm) = NilStep(a)
  }
  case class ConsStep(a: CTerm, h: CTerm, t: CTerm) extends Step {
    override val graphStep =
      AddChildNodesStep[CTerm, Label](List(a -> ConsLabel, h -> ConsLabel, t -> ConsLabel))
  }
  case class ConsDStep(a: CTerm, head: CTerm, tail: CTerm) extends DriveStep {
    override def step(t: CTerm) = ConsStep(a, head, tail)
  }

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NPiListElim(a, m, nilCase, consCase, l) =>
      l match {
        case NFree(n) =>
          val aType = quote0(a)
          val caseNil = ElimBranch(PiNil(aType), Map())

          val hName = freshName
          val h1 = Inf(Free(hName))

          val tName = freshName
          val t1 = Inf(Free(tName))

          val caseCons = ElimBranch(PiCons(aType, h1, t1), Map(tName -> Inf(Free(n))))

          val motive = quote0(m)

          ElimDStep(n, List(caseNil, caseCons), motive)
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def decompose(c: CTerm): DriveStep = c match {
    case PiNil(a) =>
      NilDStep(a)
    case PiCons(a, h, t) =>
      ConsDStep(a, h, t)
    case _ =>
      super.decompose(c)
  }

}


trait ListResiduator extends BaseResiduator with ListDriver {
  override def fold(g: TGraph[CTerm, Label], node: TNode[CTerm, Label], nEnv: NameEnv[Value], bEnv: Env, dRed: Map[CTerm, Value], tps: NameEnv[Value], tp: Value): Value =
    node.outs match {
      case
        TEdge(nodeZ, CaseBranchLabel(sel, ElimBranch(PiNil(a), _), m)) ::
          TEdge(nodeS, CaseBranchLabel(_, ElimBranch(PiCons(_, Inf(Free(hN)), Inf(Free(tN))), _), _)) ::
          Nil =>

        val motive =
          VLam(n => eval(quote0(tp), sel -> n :: nEnv, bEnv))


        val aType = eval(a, nEnv, bEnv)
        val nilType =
          eval(quote0(tp), sel -> VPiNil(aType) :: nEnv, bEnv)
        val nilCase =
          fold(g, nodeZ, nEnv, bEnv, dRed, tps, nilType)

        val consType = eval(quote0(tp), sel -> VPiCons(aType, vfree(hN), vfree(tN)) :: nEnv, bEnv)

        val consCase =
          VLam {h => VLam {t => VLam {rec =>
            fold(g, nodeS, hN -> h :: tN -> t :: nEnv, bEnv, dRed + (node.conf -> rec), tps, consType)
          }}}

        VNeutral(NFree(Global("listElim"))) @@ aType @@ motive @@ nilCase @@ consCase @@ lookup(sel, nEnv).get

      case TEdge(n1, NilLabel) :: Nil =>
        VNeutral(NFree(Global("Nil"))) @@ fold(g, n1, nEnv, bEnv, dRed, tps, tp)

      case TEdge(a, ConsLabel) :: TEdge(h, ConsLabel) :: TEdge(t, ConsLabel) :: Nil =>
        val VPiList(aType) = tp
        VNeutral(NFree(Global("Cons"))) @@
          fold(g, a, nEnv, bEnv, dRed, tps, VStar) @@
          fold(g, h, nEnv, bEnv, dRed, tps, aType) @@
          fold(g, t, nEnv, bEnv, dRed, tps, tp)
      case _ =>
        super.fold(g, node, nEnv, bEnv, dRed, tps, tp)
    }
}

trait ListCheck extends CoreCheck with ListAST with ListEval {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: ITerm): Result[Value] = t match {
    case PiList(a) =>
      assert(cType(i, named, bound, a, VStar).isRight)
      Right(VStar)
    case PiListElim(a, m, nilCase, consCase, xs) =>
      assert(cType(i, named, bound, a, VStar).isRight)
      val aVal = eval(a, named, List())
      assert(cType(i, named, bound, m, VPi(VPiList(aVal), {_ => VStar})).isRight)

      val mVal = eval(m, named, List())
      assert(cType(i, named, bound, nilCase, mVal @@ VPiNil(aVal)).isRight)

      assert(cType(i, named, bound, consCase,
        VPi(aVal, {y => VPi(VPiList(aVal), {ys => VPi(mVal @@ ys, {_ => mVal @@ VPiCons(aVal, y, ys) }) }) })
      ).isRight)

      assert(cType(i, named, bound, xs, VPiList(aVal)).isRight)
      val vecVal = eval(xs, named, List())
      Right(mVal @@ vecVal)
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def cType(ii: Int, named: NameEnv[Value], bound: NameEnv[Value], ct: CTerm, t: Value): Result[Unit] = (ct, t) match {
    case (PiNil(a), VPiList(bVal)) =>
      assert(cType(ii, named, bound, a, VStar).isRight)
      val aVal = eval(a, named, List())
      if (quote0(aVal) != quote0(bVal)) return Left("type mismatch")
      Right()
    case (PiCons(a, head, tail), VPiList(bVal)) =>
      assert(cType(ii, named, bound, a, VStar).isRight)
      val aVal = eval(a, named, List())
      if (quote0(aVal) != quote0(bVal)) return Left("type mismatch")
      assert(cType(ii, named, bound, head, aVal).isRight)
      assert(cType(ii, named, bound, tail, VPiList(bVal)).isRight)
      Right()
    case _ =>
      super.cType(ii, named, bound, ct, t)
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
  lazy val listTE: NameEnv[Value] =
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

  lazy val ListType = int.ieval(listVE, int.parseIO(int.iParse, ListTypeIn).get)
  lazy val listElimType = int.ieval(listVE, int.parseIO(int.iParse, listElimTypeIn).get)
  lazy val NilType = int.ieval(listVE, int.parseIO(int.iParse, NilTypeIn).get)
  lazy val ConsType = int.ieval(listVE, int.parseIO(int.iParse, ConsTypeIn).get)

  val listVE: NameEnv[Value] =
    List(
      Global("List") -> VLam(a => VPiList(a)),
      Global("listElim") ->
        eval(
          Lam(Lam(Lam(Lam(Lam(
            Inf(PiListElim(Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)))
            )))))),
          List(),List()),
      Global("Nil") -> VLam(a => VPiNil(a)),
      Global("Cons") -> VLam(a => VLam(x => VLam(y => VPiCons(a, x, y))))
    )
}