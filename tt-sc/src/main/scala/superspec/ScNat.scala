package superspec

import superspec.tt._
import mrsc.core._

trait NatDriver extends CoreDriver with NatAST with NatEval {

  case object SuccLabel extends Label

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case natElim: NNatElim =>
      natElim.n match {
        case NFree(n) =>
          val caseZ = ElimLabel(n, Zero, Map(), Map())
          val v1 = freshName
          val caseS = ElimLabel(n, Succ(v1), Map(n -> v1), Map(v1 -> VNat))
          ElimDStep(caseZ, caseS)
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case Succ(c1) =>
      val Nat = c.tp
      DecomposeDStep(SuccLabel, Conf(c1, c.ctx))
    case _ =>
      super.decompose(c)
  }

}

trait NatResiduator extends BaseResiduator with NatDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case
        TEdge(nodeZ, ElimLabel(sel, Zero, _, _)) ::
          TEdge(nodeS, ElimLabel(_, Succ(Free(fresh)), _, _)) ::
          Nil =>
        val motive =
          VLam(VNat, n => eval(node.conf.tp, env + (sel -> n), n :: bound))
        val zCase =
          fold(nodeZ, env, bound, recM)
        val sCase =
          VLam(VNat, n => VLam(motive @@ n, rec =>
            fold(nodeS, env + (fresh -> n), rec :: n :: bound, recM + (node.tPath -> rec))))
        natElim(motive, zCase, sCase, env(sel))
      case TEdge(n1, SuccLabel) :: Nil =>
        VSucc(fold(n1, env, bound, recM))
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
        TEdge(nodeZ, ElimLabel(sel, Zero, _, _)) ::
          TEdge(nodeS, ElimLabel(_, Succ(Free(fresh)), _, _)) ::
          Nil =>

        val motive =
          VLam(VNat, n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))

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

        natElim(motive, zCase, sCase, env(sel))
      case TEdge(n1, SuccLabel) :: Nil =>
        'cong1 @@
          VNat @@
          VNat @@
          VLam(VNat, n => VSucc(n)) @@
          eval(n1.conf.term, env, bound) @@
          fold(n1, env, bound, recM) @@
          proofFold(n1, env, bound, recM, env2, bound2, recM2)
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
