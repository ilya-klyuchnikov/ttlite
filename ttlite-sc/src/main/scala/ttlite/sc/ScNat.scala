package ttlite.sc

import mrsc.core._
import ttlite.common._
import ttlite.core._

trait NatDriver extends Driver with NatAST with NatEval { self: PiAST =>

  case object SuccLabel extends Label

  override def nv(t: Neutral): Option[Name] =
    t match {
      case NNatElim(_, _, _, NFree(n)) => Some(n)
      case NNatElim(_, _, _, n)        => nv(n)
      case _                           => super.nv(t)
    }

  override def elimVar(n: Name, nt: Value): DriveStep =
    nt match {
      case VNat =>
        val caseZ = ElimLabel(n, Zero, Map(), Map())
        val v1 = freshName()
        val caseS = ElimLabel(n, Succ(v1), Map(n -> v1), Map(v1 -> VNat))
        ElimDStep(caseZ, caseS)
      case _ =>
        super.elimVar(n, nt)
    }

  override def decompose(c: Conf): DriveStep =
    c.term match {
      case Succ(c1) =>
        val Nat = c.tp
        DecomposeDStep(SuccLabel, Conf(c1, c.ctx))
      case _ =>
        super.decompose(c)
    }

}

trait NatResiduator extends Residuator with NatDriver { self: PiAST =>
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeZ, ElimLabel(sel, Zero, _, _)) ::
          TEdge(nodeS, ElimLabel(_, Succ(Free(fresh)), _, _)) ::
          Nil =>
        val motive =
          VLam(VNat, n => eval(node.conf.tp, env + (sel -> n), n :: bound))
        val zCase =
          fold(nodeZ, env, bound, recM)
        val sCase =
          VLam(
            VNat,
            n =>
              VLam(motive @@ n, rec => fold(nodeS, env + (fresh -> n), rec :: n :: bound, recM + (node.tPath -> rec))),
          )
        natElim(motive, zCase, sCase, env(sel))
      case TEdge(n1, SuccLabel) :: Nil =>
        VSucc(fold(n1, env, bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

// we need 2 maps here! - one for proof and one for ordinary!!!!
trait NatProofResiduator extends NatResiduator with ProofResiduator { self: PiAST with IdAST =>
  override def proofFold(
      node: N,
      env1: NameEnv[Value],
      bound1: Env,
      recM1: Map[TPath, Value],
      env2: NameEnv[Value],
      bound2: Env,
      recM2: Map[TPath, Value],
  ): Value =
    node.outs match {
      case TEdge(nodeZ, ElimLabel(sel, Zero, _, _)) ::
          TEdge(nodeS, ElimLabel(_, Succ(Free(fresh)), _, _)) ::
          Nil =>
        val motive =
          VLam(
            VNat,
            n =>
              VId(
                eval(node.conf.tp, env1 + (sel -> n), n :: bound1),
                eval(node.conf.term, env1 + (sel -> n), n :: bound1),
                fold(node, env1 + (sel -> n), n :: bound1, recM1),
              ),
          )

        val zCase =
          proofFold(nodeZ, env1, bound1, recM1, env2, bound2, recM2)

        val sCase =
          VLam(
            VNat,
            n =>
              VLam(
                motive @@ n,
                { rec =>
                  // SIC!! - node, not nodeS!!
                  val rec1 = fold(node, env1 + (sel -> n), n :: bound1, recM1)
                  proofFold(
                    nodeS,
                    env1 + (fresh -> n),
                    rec1 :: n :: bound1,
                    recM1 + (node.tPath -> rec1),
                    env2 + (fresh -> n),
                    rec :: n :: bound2,
                    recM2 + (node.tPath -> rec),
                  )
                },
              ),
          )

        natElim(motive, zCase, sCase, env1(sel))
      case TEdge(n1, SuccLabel) :: Nil =>
        "cong1" @@
          VNat @@
          VNat @@
          VLam(VNat, n => VSucc(n)) @@
          eval(n1.conf.term, env1, bound1) @@
          fold(n1, env1, bound1, recM1) @@
          proofFold(n1, env1, bound1, recM1, env2, bound2, recM2)
      case _ =>
        super.proofFold(node, env1, bound1, recM1, env2, bound2, recM2)
    }
}
