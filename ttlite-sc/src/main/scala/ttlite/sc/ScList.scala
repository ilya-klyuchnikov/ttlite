package ttlite.sc

import mrsc.core._
import ttlite.common._
import ttlite.core._

trait ListDriver extends Driver with ListAST with ListEval { self: PiAST =>

  case object ConsLabel extends Label
  case object ListLabel extends Label

  override def nv(t: Neutral): Option[Name] = t match {
    case NPiListElim(_, _, _, _, NFree(n)) => Some(n)
    case NPiListElim(_, _, _, _, n) => nv(n)
    case _ => super.nv(t)
  }

  override def elimVar(n: Name, nt: Value): DriveStep = nt match {
    case VPiList(a) =>
      val aType = quote0(a)
      val caseNil = ElimLabel(n, PiNil(PiList(aType)), Map(), Map())

      val h1 = freshName()
      val t1 = freshName()
      val caseCons = ElimLabel(n, PiCons(PiList(aType), h1, t1), Map(n -> t1), Map(h1 -> a, t1 -> VPiList(a)))

      ElimDStep(caseNil, caseCons)
    case _ =>
      super.elimVar(n, nt)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case PiCons(PiList(a), h, t) =>
      DecomposeDStep(ConsLabel, Conf(h, c.ctx), Conf(t, c.ctx))
    case PiList(a) =>
      DecomposeDStep(ListLabel, Conf(a, c.ctx))
    case _ =>
      super.decompose(c)
  }

}

trait ListResiduator extends Residuator with ListDriver { self: PiAST =>
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case
        TEdge(nodeZ, ElimLabel(sel, PiNil(PiList(a)), _, _)) ::
          TEdge(nodeS, ElimLabel(_, PiCons(_, Free(hN), Free(tN)), _, _)) ::
          Nil =>

        val aVal = eval(a, env, bound)
        val motive =
          VLam(VPiList(aVal), n => eval(node.conf.tp, env + (sel -> n), n :: bound))

        val nilCase =
          fold(nodeZ, env, bound, recM)
        val consCase =
          VLam (aVal, h => VLam (VPiList(aVal), t => VLam (motive @@ t, rec =>
            fold(nodeS, env + (hN -> h) + (tN -> t), rec :: t :: h :: bound, recM + (node.tPath -> rec)))))

        listElim(VPiList(aVal), motive, nilCase, consCase, env(sel))
      case TEdge(h, ConsLabel) :: TEdge(t, ConsLabel) :: Nil =>
        val a = eval(node.conf.tp, env, bound)
        VPiCons(a, fold(h, env, bound, recM), fold(t, env, bound, recM))
      case TEdge(a, ListLabel) :: Nil =>
        VPiList(fold(a, env, bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait ListProofResiduator extends ListResiduator with ProofResiduator { self: PiAST with IdAST =>
  override def proofFold(node: N,
                         env1: NameEnv[Value], bound1: Env, recM1: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case
        TEdge(nodeZ, ElimLabel(sel, PiNil(PiList(a)), _, _)) ::
          TEdge(nodeS, ElimLabel(_, PiCons(_, Free(hN), Free(tN)), _, _)) ::
          Nil =>

        val aVal = eval(a, env1, bound1)

        val motive =
          VLam(VPiList(aVal), n =>
            VId(
              eval(node.conf.tp, env1 + (sel -> n), n :: bound1),
              eval(node.conf.term, env1 + (sel -> n), n :: bound1),
              fold(node, env1 + (sel -> n), n :: bound1, recM1)))

        val nilCase =
          proofFold(nodeZ,
            env1, bound1, recM1,
            env2, bound2, recM2)

        val consCase =
          VLam (aVal, h => VLam (VPiList(aVal), t => VLam (motive @@ t, {rec =>
            // SIC!! - node, not nodeS!!
            val rec1 = fold(node, env1 + (sel -> t), t :: bound1, recM1)
            proofFold(nodeS,
              env1 + (hN -> h) + (tN -> t),
              rec1 :: t :: h :: bound1,
              recM1 + (node.tPath -> rec1),

              env2 + (hN -> h) + (tN -> t),
              rec :: t :: h :: bound2,
              recM2 + (node.tPath -> rec))})))

        listElim(VPiList(aVal), motive, nilCase, consCase, env1(sel))
      case TEdge(h, ConsLabel) :: TEdge(t, ConsLabel) :: Nil =>
        val VPiList(a) = eval(node.conf.tp, env1, bound1)
        val h1 = eval(h.conf.term, env1, bound1)
        val h2 = fold(h, env1, bound1, recM1)
        val eq_h1_h2 = proofFold(h, env1, bound1, recM1, env2, bound2, recM2)

        val t1 = eval(t.conf.term, env1, bound1)
        val t2 = fold(t, env1, bound1, recM1)
        val eq_t1_t2 = proofFold(t, env1, bound1, recM1, env2, bound2, recM2)

        "cong2" @@ a @@ VPiList(a) @@ VPiList(a) @@
          VLam(a, x => VLam(VPiList(a), y => VPiCons(VPiList(a), x, y))) @@
          h1 @@ h2 @@ eq_h1_h2 @@
          t1 @@ t2 @@ eq_t1_t2
      case TEdge(n1, ListLabel) :: Nil =>
        val tp = eval(node.conf.tp, env1, bound1)
        "cong1" @@
          tp @@
          tp @@
          VLam(tp, a => VPiList(a)) @@
          eval(n1.conf.term, env1, bound1) @@
          fold(n1, env1, bound1, recM1) @@
          proofFold(n1, env1, bound1, recM1, env2, bound2, recM2)
      case _ =>
        super.proofFold(node, env1, bound1, recM1, env2, bound2, recM2)
    }
}
