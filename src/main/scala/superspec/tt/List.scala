package superspec.tt

import mrsc.core._
import superspec._

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

trait ListSubst extends CoreSubst with ListAST {
  override def findSubst0(from: Term, to: Term): Option[Subst] = (from, to) match {
    case (PiList(a1), PiList(a2)) =>
      findSubst0(a1, a2)
    case (PiNil(a1), PiNil(a2)) =>
      findSubst0(a1, a2)
    case (PiCons(a1, h1, t1), PiCons(a2, h2, t2)) =>
      mergeOptSubst(
        findSubst0(a1, a2),
        findSubst0(h1, h2),
        findSubst0(t1, t2)
      )
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

  override def isFreeSubTerm(t: Term, depth: Int): Boolean = t match {
    case PiList(a) =>
      isFreeSubTerm(a, depth)
    case PiNil(a) =>
      isFreeSubTerm(a, depth)
    case PiCons(a, h, t) =>
      isFreeSubTerm(a, depth) && isFreeSubTerm(h, depth) && isFreeSubTerm(t, depth)
    case PiListElim(a, m, nCase, cCase, xs) =>
      isFreeSubTerm(a, depth) && isFreeSubTerm(m, depth) &&
        isFreeSubTerm(nCase, depth) && isFreeSubTerm(cCase, depth) && isFreeSubTerm(xs, depth)
    case _ =>
      super.isFreeSubTerm(t, depth)
  }
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


trait ListDriver extends CoreDriver with ListAST {

  // boilerplate/indirections
  case object NilLabel extends Label
  case object ConsLabel extends Label

  case class NilStep(a: DConf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(a -> NilLabel))
  }
  case class NilDStep(a: DConf) extends DriveStep {
    override def step(t: Conf) = NilStep(a)
  }
  case class ConsStep(a: Conf, h: Conf, t: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(a -> ConsLabel, h -> ConsLabel, t -> ConsLabel))
  }
  case class ConsDStep(a: Conf, head: Conf, tail: Conf) extends DriveStep {
    override def step(t: Conf) = ConsStep(a, head, tail)
  }

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NPiListElim(a, m, nilCase, consCase, l) =>
      l match {
        case NFree(n) =>
          val aType = quote0(a)
          val caseNil = ElimBranch(PiNil(aType), Map())

          val hName = freshName(quote0(a))
          val h1 = Free(hName)

          val tName = freshName(quote0(VPiList(a)))
          val t1 = Free(tName)

          val caseCons = ElimBranch(PiCons(aType, h1, t1), Map(tName -> Free(n)))

          ElimDStep(n, List(caseNil, caseCons))
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def decompose(c: Conf): DriveStep = c.ct match {
    case PiNil(a) =>
      val PiList(tp) = c.tp
      NilDStep(DConf(a, Star))
    case PiCons(a, h, t) =>
      ConsDStep(DConf(a, Star), DConf(h, a), DConf(t, c.ct))
    case _ =>
      super.decompose(c)
  }

}

trait ListResiduator extends BaseResiduator with ListDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case
        TEdge(nodeZ, CaseBranchLabel(sel, ElimBranch(PiNil(a), _))) ::
          TEdge(nodeS, CaseBranchLabel(_, ElimBranch(PiCons(_, Free(hN), Free(tN)), _))) ::
          Nil =>

        val aVal = eval(a, env, bound)
        val motive =
          VLam(VPiList(aVal), n => eval(node.conf.tp, env + (sel -> n), n :: bound))
          //Lam(VPi)

        val nilType =
          eval(node.conf.tp, env + (sel -> VPiNil(aVal)), bound)
        val nilCase =
          fold(nodeZ, env, bound, recM)
        val consCase =
          VLam (aVal, h => VLam (VPiList(aVal), t => VLam (motive @@ t, rec =>
            fold(nodeS, env + (hN -> h) + (tN -> t), rec :: t :: h :: bound, recM + (node.tPath -> rec)))))
        VNeutral(NFree(Global("listElim"))) @@
          aVal @@
          motive @@
          nilCase @@
          consCase @@
          env(sel)
      case TEdge(n1, NilLabel) :: Nil =>
        VNeutral(NFree(Global("Nil"))) @@ fold(n1, env, bound, recM)
      case TEdge(a, ConsLabel) :: TEdge(h, ConsLabel) :: TEdge(t, ConsLabel) :: Nil =>
        val VPiList(aType) = eval(node.conf.tp, env, bound)
        VNeutral(NFree(Global("Cons"))) @@
          fold(a, env, bound, recM) @@
          fold(h, env, bound, recM) @@
          fold(t, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait ListCheck extends CoreCheck with ListAST with ListEval {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case PiList(a) =>
      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)
      VStar
    case PiNil(a) =>
      val aVal = eval(a, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      VPiList(aVal)
    case PiCons(a, head, tail) =>
      val aVal = eval(a, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val hType = iType(i, named, bound, head)
      checkEqual(hType, aVal)

      val tType = iType(i, named, bound, tail)
      checkEqual(tType, VPiList(aVal))

      VPiList(aVal)
    case PiListElim(a, m, nilCase, consCase, xs) =>
      val aVal = eval(a, named, List())
      val mVal = eval(m, named, List())
      val xsVal = eval(xs, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(aType, Star)

      val mType = iType(i, named, bound, m)
      checkEqual(mType, VPi(VPiList(aVal), {_ => VStar}))

      val nilCaseType = iType(i, named, bound, nilCase)
      checkEqual(nilCaseType, mVal @@ VPiNil(aVal))

      val consCaseType = iType(i, named, bound, consCase)
      checkEqual(consCaseType,
        VPi(aVal, {y => VPi(VPiList(aVal), {ys => VPi(mVal @@ ys, {_ => mVal @@ VPiCons(aVal, y, ys) }) }) })
      )

      val xsType = iType(i, named, bound, xs)
      checkEqual(xsType, VPiNil(aVal))

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
    "forall A :: * . List A"
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
