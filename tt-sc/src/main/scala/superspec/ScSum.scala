package superspec

import superspec.tt._
import mrsc.core._

trait SumDriver extends CoreDriver with SumAST {

  case object InLLabel extends Label
  case object InRLabel extends Label

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NSumElim(l, r, _, _, _, s) =>
      s match {
        case NFree(n) =>
          val lType = quote0(l)
          val rType = quote0(r)

          val lCase = ElimLabel(n, InL(lType, rType, freshLocal(lType)), Map())
          val rCase = ElimLabel(n, InR(lType, rType, freshLocal(rType)), Map())

          ElimDStep(lCase, rCase)
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case InL(lType, rType, l) =>
      val Sum(_, _) = c.tp
      DecomposeDStep(InLLabel, Conf(l, lType))
    case InR(lType, rType, r) =>
      val Sum(_, _) = c.tp
      DecomposeDStep(InRLabel, Conf(r, rType))
    case _ =>
      super.decompose(c)
  }
}

trait SumResiduator extends BaseResiduator with SumDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, ElimLabel(sel, InL(a, b, Free(lN)), _)) ::
        TEdge(nodeR, ElimLabel(_, InR(_, _, Free(rN)), _)) ::
        Nil =>

        val aVal = eval(a, env, bound)
        val bVal = eval(b, env, bound)
        val motive =
          VLam(VSum(aVal, bVal), s => eval(node.conf.tp, env + (sel -> s), s :: bound))

        val lCase = VLam(aVal, l => fold(nodeL, env + (lN -> l), l :: bound, recM))
        val rCase = VLam(bVal, r => fold(nodeR, env + (rN -> r), r :: bound, recM))

        'sumElim @@
          aVal @@
          bVal @@
          motive @@
          lCase @@
          rCase @@
          env(sel)
      case TEdge(l, InLLabel) :: Nil =>
        val VSum(a, b) = eval(node.conf.tp, env, bound)
        'InL @@
          a @@
          b @@
          fold(l, env, bound, recM)
      case TEdge(r, InRLabel) :: Nil =>
        val VSum(a, b) = eval(node.conf.tp, env, bound)
        'InR @@
          a @@
          b @@
          fold(r, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait SumProofResiduator extends SumResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, ElimLabel(sel, InL(a, b, Free(lN)), _)) ::
        TEdge(nodeR, ElimLabel(_, InR(_, _, Free(rN)), _)) ::
        Nil =>

        val aVal = eval(a, env, bound)
        val bVal = eval(b, env, bound)
        val motive =
          VLam(VSum(aVal, bVal), n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))

        val lCase = VLam(aVal, l =>
          proofFold(nodeL,
            env + (lN -> l), l :: bound, recM,
            env2 + (lN -> l), l :: bound2, recM2))

        val rCase = VLam(bVal, r =>
          proofFold(nodeR,
            env + (rN -> r), r :: bound, recM,
            env2 + (rN -> r), r :: bound2, recM2))

        'sumElim @@
          aVal @@
          bVal @@
          motive @@
          lCase @@
          rCase @@
          env(sel)

      case TEdge(l, InLLabel) :: Nil =>
        val VSum(a, b) = eval(node.conf.tp, env, bound)
        'cong1 @@
          a @@
          VSum(a, b) @@
          ('InL @@ a @@ b) @@
          eval(l.conf.term, env, bound) @@
          fold(l, env, bound, recM) @@
          proofFold(l, env, bound, recM, env2, bound2, recM2)

      case TEdge(r, InRLabel) :: Nil =>
        val VSum(a, b) = eval(node.conf.tp, env, bound)
        'cong1 @@
          b @@
          VSum(a, b) @@
          ('InR @@ a @@ b) @@
          eval(r.conf.term, env, bound) @@
          fold(r, env, bound, recM) @@
          proofFold(r, env, bound, recM, env2, bound2, recM2)
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
