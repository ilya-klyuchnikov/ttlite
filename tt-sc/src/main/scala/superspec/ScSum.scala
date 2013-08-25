package superspec

import superspec.tt._
import mrsc.core._

trait SumDriver extends CoreDriver with SumAST with SumEval {

  case object InLLabel extends Label
  case object InRLabel extends Label

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NSumElim(etVal, _, _, _, s) =>
      val VSum(l, r) = etVal
      s match {
        case NFree(n) =>
          val lType = quote0(l)
          val rType = quote0(r)
          val et = Sum(lType, rType)

          val lCase = ElimLabel(n, InL(et, freshLocal(lType)), Map())
          val rCase = ElimLabel(n, InR(et, freshLocal(rType)), Map())

          ElimDStep(lCase, rCase)
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case InL(et@Sum(lType, _), l) =>
      val Sum(_, _) = c.tp
      DecomposeDStep(InLLabel, Conf(l, lType))
    case InR(et@Sum(_, rType), r) =>
      val Sum(_, _) = c.tp
      DecomposeDStep(InRLabel, Conf(r, rType))
    case _ =>
      super.decompose(c)
  }
}

trait SumResiduator extends BaseResiduator with SumDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, ElimLabel(sel, InL(et, Free(lN)), _)) ::
        TEdge(nodeR, ElimLabel(_, InR(_, Free(rN)), _)) ::
        Nil =>

        val etVal@VSum(aVal, bVal) =
          eval(et, env, bound)
        val motive =
          VLam(etVal, s => eval(node.conf.tp, env + (sel -> s), s :: bound))

        val lCase = VLam(aVal, l => fold(nodeL, env + (lN -> l), l :: bound, recM))
        val rCase = VLam(bVal, r => fold(nodeR, env + (rN -> r), r :: bound, recM))

        sumElim(etVal, motive, lCase, rCase, env(sel))
      case TEdge(l, InLLabel) :: Nil =>
        val etVal = eval(node.conf.tp, env, bound)
        VInL(etVal, fold(l, env, bound, recM))
      case TEdge(r, InRLabel) :: Nil =>
        val etVal = eval(node.conf.tp, env, bound)
        VInR(etVal, fold(r, env, bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait SumProofResiduator extends SumResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, ElimLabel(sel, InL(et, Free(lN)), _)) ::
        TEdge(nodeR, ElimLabel(_, InR(_, Free(rN)), _)) ::
        Nil =>

        val etVal@VSum(aVal, bVal) =
          eval(et, env, bound)
        val motive =
          VLam(etVal, n =>
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

        sumElim(etVal, motive, lCase, rCase, env(sel))

      case TEdge(l, InLLabel) :: Nil =>
        val VSum(a, b) = eval(node.conf.tp, env, bound)
        'cong1 @@
          a @@
          VSum(a, b) @@
          VLam(a, x => VInL(VSum(a, b), x)) @@
          eval(l.conf.term, env, bound) @@
          fold(l, env, bound, recM) @@
          proofFold(l, env, bound, recM, env2, bound2, recM2)

      case TEdge(r, InRLabel) :: Nil =>
        val VSum(a, b) = eval(node.conf.tp, env, bound)
        'cong1 @@
          b @@
          VSum(a, b) @@
          VLam(b, y => VInR(VSum(a, b), y)) @@
          eval(r.conf.term, env, bound) @@
          fold(r, env, bound, recM) @@
          proofFold(r, env, bound, recM, env2, bound2, recM2)
      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
