package superspec.tt

import mrsc.core._
import superspec._

trait NatAST extends CoreAST {
  case object Nat extends Term
  case object Zero extends Term
  case class Succ(e: Term) extends Term
  case class NatElim(a: Term, b: Term, c: Term, d: Term) extends Term

  case object VNat extends Value
  case object VZero extends Value
  case class VSucc(v: Value) extends Value
  case class NNatElim(m: Value, caseZ: Value, caseS: Value, n: Neutral) extends Neutral
}

trait NatPrinter extends CorePrinter with NatAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Nat =>
      "Nat"
    case NatElim(m, z, s, n) =>
      print(p, ii, Free(Global("natElim")) @@ m @@ z @@ s @@ n)
    case Zero =>
      print(p, ii, Free(Global("Zero")))
    case Succ(n) =>
      print(p, ii, Free(Global("Succ")) @@ n)
    case _ =>
      super.print(p, ii, t)
  }

  def fromNat(n: Int, ii: Int, t: Term): Doc = t match {
    case Zero =>
      "Zero"
    case Succ(k) =>
      fromNat(n + 1, ii, k)
    case _ =>
      parens(n.toString <> " + " <> print(3, ii, t))
  }
}

trait NatEval extends CoreEval with NatAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Zero =>
      VZero
    case Succ(n) =>
      VSucc(eval(n, named, bound))
    case Nat =>
      VNat
    case NatElim(m, mz, ms, n) =>
      val mzVal = eval(mz, named, bound)
      val msVal = eval(ms, named, bound)
      def rec(nVal: Value): Value = nVal match {
        case VZero =>
          mzVal
        case VSucc(k) =>
          msVal @@ k @@ rec(k)
        case VNeutral(n) =>
          VNeutral(NNatElim(eval(m, named, bound), mzVal, msVal, n))
      }
      rec(eval(n, named, bound))
    case _ =>
      super.eval(t, named, bound)
  }
}

trait NatDriver extends CoreDriver with NatAST {

  // boilerplate/indirections
  case object SuccLabel extends Label
  case class SuccStep(next: Term) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(DConf(next, Nat) -> SuccLabel))
  }
  case class SuccDStep(next: Term) extends DriveStep {
    override def step(t: Conf) = SuccStep(next)
  }

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case natElim: NNatElim =>
      natElim.n match {
        case NFree(n) =>
          val caseZ = ElimBranch(Zero, Map())
          val n1 = freshName(Nat)
          val v1 = Free(n1)
          val caseS = ElimBranch(Succ(v1), Map(n1 -> Free(n)))
          ElimDStep(n, List(caseZ, caseS))
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def elimFreeVar(c: Conf, fv: Local): List[ElimDStep] = typeMap(fv) match {
    case Nat =>
      val caseZ = ElimBranch(Zero, Map())
      val n1 = freshName(Nat)
      val v1 = Free(n1)
      val caseS = ElimBranch(Succ(v1), Map(n1 -> Free(fv)))
      List(ElimDStep(fv, List(caseZ, caseS)))
    case _ =>
      super.elimFreeVar(c, fv)
  }

  override def decompose(c: Conf): DriveStep = c.ct match {
    case Succ(c1) =>
      val Nat = c.tp
      SuccDStep(c1)
    case _ =>
      super.decompose(c)
  }

}

trait NatResiduator extends BaseResiduator with NatDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case
        TEdge(nodeZ, CaseBranchLabel(sel, ElimBranch(Zero, _, _))) ::
          TEdge(nodeS, CaseBranchLabel(_, ElimBranch(Succ(Free(fresh)), _, _))) ::
          Nil =>
        val motive =
          VLam(VNat, n => eval(node.conf.tp, env + (sel -> n), n :: bound))
        val zCase =
          fold(nodeZ, env, bound, recM)
        val sCase =
          VLam(VNat, n => VLam(motive @@ n, rec =>
            fold(nodeS, env + (fresh -> n), rec :: n :: bound, recM + (node.tPath -> rec))
          ))
        VNeutral(NFree(Global("natElim"))) @@ motive @@ zCase @@ sCase @@ env(sel)
      case TEdge(n1, SuccLabel) :: Nil =>
        VNeutral(NFree(Global("Succ"))) @@ fold(n1, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait NatCheck extends CoreCheck with NatAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Nat =>
      VStar
    case NatElim(m, mz, ms, n) =>
      val mVal = eval(m, named, Nil)
      val nVal = eval(n, named, Nil)

      val mType = iType(i, named, bound, m)
      checkEqual(mType, Pi(Nat, Star))

      val mzType = iType(i, named, bound, mz)
      checkEqual(mzType, mVal @@ VZero)

      val msType = iType(i, named, bound, ms)
      checkEqual(msType, VPi(VNat, k => VPi(mVal @@ k, x => mVal @@ VSucc(k))))

      val nType = iType(i, named, bound, n)
      checkEqual(nType, Nat)

      mVal @@ nVal
    case Zero =>
      VNat
    case Succ(k) =>
      val kType = iType(i, named, bound, k)
      checkEqual(kType, Nat)

      VNat
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Nat =>
      Nat
    case NatElim(m, mz, ms, n) =>
      NatElim(iSubst(i, r, m), iSubst(i, r, mz), iSubst(i, r, ms), iSubst(i, r, n))
    case Zero =>
      Zero
    case Succ(n) =>
      Succ(iSubst(i, r, n))
    case _ => super.iSubst(i, r, it)
  }

}

trait NatQuote extends CoreQuote with NatAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VNat => Nat
    case VZero => Zero
    case VSucc(n) => Succ(quote(ii, n))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NNatElim(m, z, s, n) =>
      NatElim(quote(ii, m), quote(ii, z), quote(ii, s), neutralQuote(ii, n))
    case _ => super.neutralQuote(ii, n)
  }
}

trait NatREPL extends CoreREPL with NatAST with NatPrinter with NatCheck with NatEval with NatQuote {
  lazy val natTE: NameEnv[Value] =
    Map(
      Global("Zero") -> VNat,
      Global("Succ") -> VPi(VNat, _ => VNat),
      Global("Nat") -> VStar,
      Global("natElim") -> natElimType
    )
  val natElimTypeIn =
    """
      |forall (m :: forall x :: Nat . *) .
      |forall (zCase :: m Zero) .
      |forall (sCase :: forall (n :: Nat) (a :: m n) . m (Succ n)) .
      |forall (n :: Nat) .
      |m n
    """.stripMargin
  lazy val natElimType = int.ieval(natVE, int.parseIO(int.iParse, natElimTypeIn).get)
  val natVE: NameEnv[Value] =
    Map(
      Global("Zero") -> VZero,
      Global("Succ") -> VLam(VNat, n => VSucc(n)),
      Global("Nat") -> VNat,
      Global("natElim") ->
        VLam(VPi(VNat, _ => VStar), m =>
          VLam( m @@ VZero, zCase =>
            VLam(VPi(VNat, n => VPi(m @@ n, a => m @@ VSucc(n))), sCase =>
              VLam(VNat, {n =>
                eval(NatElim(Bound(3), Bound(2), Bound(1), Bound(0)), natVE, List(n, sCase, zCase, m))
              }))))
    )

  def toNat1(n: Int): Term =
    if (n == 0) Zero else Succ(toNat1(n - 1))

  override def toNat(i: Int): Term =
    Ann(toNat1(i), Nat)
}
