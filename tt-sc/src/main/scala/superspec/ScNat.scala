package superspec

import superspec.tt._
import mrsc.core._

trait NatDriver extends CoreDriver with NatAST {

  case object SuccLabel extends Label
  case class SuccStep(next: Term) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(Conf(next, Nat) -> SuccLabel))
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

  override def decompose(c: Conf): DriveStep = c.term match {
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
        TEdge(nodeZ, CaseBranchLabel(sel, ElimBranch(Zero, _))) ::
          TEdge(nodeS, CaseBranchLabel(_, ElimBranch(Succ(Free(fresh)), _))) ::
          Nil =>
        val motive =
          VLam(VNat, n => eval(node.conf.tp, env + (sel -> n), n :: bound))
        val zCase =
          fold(nodeZ, env, bound, recM)
        val sCase =
          VLam(VNat, n => VLam(motive @@ n, rec =>
            fold(nodeS, env + (fresh -> n), rec :: n :: bound, recM + (node.tPath -> rec))))
        'natElim @@ motive @@ zCase @@ sCase @@ env(sel)
      case TEdge(n1, SuccLabel) :: Nil =>
        'Succ @@ fold(n1, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

// we need 2 maps here! - one for proof and one for ordinary!!!!
trait NatProofResiduator extends NatResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case
        TEdge(nodeZ, CaseBranchLabel(sel, ElimBranch(Zero, _))) ::
          TEdge(nodeS, CaseBranchLabel(_, ElimBranch(Succ(Free(fresh)), _))) ::
          Nil =>

        val motive =
          VLam(VNat, n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM))
          )

        val zCase =
          proofFold(nodeZ,
            env, bound, recM,
            env2, bound2, recM2)

        val sCase =
          VLam(VNat, n => VLam(motive @@ n, {rec =>
            // SIC!! - node, not nodeS!!
            val rec1 = fold(node, env + (sel -> n), n :: bound, recM)
            proofFold(nodeS,
              env + (fresh -> n),
              rec1 :: n :: bound,
              recM + (node.tPath -> rec1),
              env2 + (fresh -> n),
              rec :: n :: bound2,
              recM2 + (node.tPath -> rec))}))

        'natElim @@ motive @@ zCase @@ sCase @@ env(sel)
      case TEdge(n1, SuccLabel) :: Nil =>
        println("---")
        println(recM2)
        'cong1 @@
          VNat @@
          VNat @@
          'Succ @@
          eval(n1.conf.term, env, bound) @@
          fold(n1, env, bound, recM) @@
          proofFold(n1, env, bound, recM, env2, bound2, recM2)
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
