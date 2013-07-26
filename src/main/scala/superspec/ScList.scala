package superspec

import superspec.tt._
import mrsc.core._

trait ListDriver extends CoreDriver with ListAST {

  // boilerplate/indirections
  case object ConsLabel extends Label

  case class ConsStep(h: Conf, t: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(h -> ConsLabel, t -> ConsLabel))
  }
  case class ConsDStep(head: Conf, tail: Conf) extends DriveStep {
    override def step(t: Conf) = ConsStep(head, tail)
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

  override def decompose(c: Conf): DriveStep = c.term match {
    case PiCons(a, h, t) =>
      ConsDStep(Conf(h, a), Conf(t, c.term))
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

        val nilCase =
          fold(nodeZ, env, bound, recM)
        val consCase =
          VLam (aVal, h => VLam (VPiList(aVal), t => VLam (motive @@ t, rec =>
            fold(nodeS, env + (hN -> h) + (tN -> t), rec :: t :: h :: bound, recM + (node.tPath -> rec)))))
        VNeutral(NFree(Global("listElim"))) @@
          aVal @@ motive @@ nilCase @@ consCase @@ env(sel)
      case TEdge(h, ConsLabel) :: TEdge(t, ConsLabel) :: Nil =>
        val VPiList(a) = eval(node.conf.tp, env, bound)
        VNeutral(NFree(Global("Cons"))) @@ a @@
          fold(h, env, bound, recM) @@
          fold(t, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait ListProofResiduator extends ListResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value = {
    node.outs match {
      case
        TEdge(nodeZ, CaseBranchLabel(sel, ElimBranch(PiNil(a), _))) ::
          TEdge(nodeS, CaseBranchLabel(_, ElimBranch(PiCons(_, Free(hN), Free(tN)), _))) ::
          Nil =>

        val aVal = eval(a, env, bound)

        val motive =
          VLam(VPiList(aVal), n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))

        val nilCase =
          proofFold(nodeZ,
            env, bound, recM,
            env2, bound2, recM2)

        val consCase =
          VLam (aVal, h => VLam (VPiList(aVal), t => VLam (motive @@ t, rec =>
            proofFold(nodeS,
              env + (hN -> h) + (tN -> t),
              rec :: t :: h :: bound,
              recM + (node.tPath -> rec),

              env2 + (hN -> h) + (tN -> t),
              rec :: t :: h :: bound,
              recM2 + (node.tPath -> fold(nodeS, env + (hN -> h) + (tN -> t), rec :: t :: h :: bound, recM + (node.tPath -> rec)))))))

        VNeutral(NFree(Global("listElim"))) @@ aVal @@
          motive @@ nilCase @@ consCase @@ env(sel)
      case TEdge(h, ConsLabel) :: TEdge(t, ConsLabel) :: Nil =>
        val VPiList(a) = eval(node.conf.tp, env, bound)
        VNeutral(NFree(Global("Cons"))) @@ a @@
          fold(h, env, bound, recM) @@
          fold(t, env, bound, recM)


      case _ =>
        super.proofFold(node,
          env, bound, recM,
          env2, bound2, recM2)
    }
  }
}
