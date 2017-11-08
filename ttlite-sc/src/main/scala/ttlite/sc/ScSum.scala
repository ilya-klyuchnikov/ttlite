package ttlite.sc

import mrsc.core._
import ttlite.common._
import ttlite.core._

trait SumDriver extends Driver with SumAST with SumEval { self: PiAST =>

  case object SumLabel extends Label
  case object InLLabel extends Label
  case object InRLabel extends Label

  override def nv(t: Neutral): Option[Name] = t match {
    case NSumElim(_, _, _, _, NFree(n)) => Some(n)
    case NSumElim(_, _, _, _, n) => nv(n)
    case _ => super.nv(t)
  }

  override def elimVar(n: Name, nt: Value): DriveStep = nt match {
    case VSum(l, r) =>
      val lType = quote0(l)
      val rType = quote0(r)
      val et = Sum(lType, rType)

      val v1 = freshName()
      val v2 = freshName()

      val lCase = ElimLabel(n, InL(et, v1), Map(), Map(v1 -> l))
      val rCase = ElimLabel(n, InR(et, v2), Map(), Map(v2 -> r))

      ElimDStep(lCase, rCase)
    case _ =>
      super.elimVar(n, nt)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case InL(et@Sum(lType, _), l) =>
      val Sum(_, _) = c.tp
      DecomposeDStep(InLLabel, Conf(l, c.ctx))
    case InR(et@Sum(_, rType), r) =>
      val Sum(_, _) = c.tp
      DecomposeDStep(InRLabel, Conf(r, c.ctx))
    case Sum(lt, rt) =>
      DecomposeDStep(SumLabel, Conf(lt, c.ctx), Conf(rt, c.ctx))
    case _ =>
      super.decompose(c)
  }
}

trait SumResiduator extends Residuator with SumDriver { self: PiAST =>
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, ElimLabel(sel, InL(et, Free(lN)), _, _)) ::
        TEdge(nodeR, ElimLabel(_, InR(_, Free(rN)), _, _)) ::
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
      case TEdge(x, SumLabel) :: TEdge(y, SumLabel) :: Nil =>
        VSum(fold(x, env, bound, recM), fold(y, env, bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait SumProofResiduator extends SumResiduator with ProofResiduator { self: PiAST with IdAST =>
  override def proofFold(node: N,
                         env1: NameEnv[Value], bound1: Env, recM1: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeL, ElimLabel(sel, InL(et, Free(lN)), _, _)) ::
        TEdge(nodeR, ElimLabel(_, InR(_, Free(rN)), _, _)) ::
        Nil =>

        val etVal@VSum(aVal, bVal) =
          eval(et, env1, bound1)
        val motive =
          VLam(etVal, n =>
            VId(
              eval(node.conf.tp, env1 + (sel -> n), n :: bound1),
              eval(node.conf.term, env1 + (sel -> n), n :: bound1),
              fold(node, env1 + (sel -> n), n :: bound1, recM1)))

        val lCase = VLam(aVal, l =>
          proofFold(nodeL,
            env1 + (lN -> l), l :: bound1, recM1,
            env2 + (lN -> l), l :: bound2, recM2))

        val rCase = VLam(bVal, r =>
          proofFold(nodeR,
            env1 + (rN -> r), r :: bound1, recM1,
            env2 + (rN -> r), r :: bound2, recM2))

        sumElim(etVal, motive, lCase, rCase, env1(sel))

      case TEdge(l, InLLabel) :: Nil =>
        val VSum(a, b) = eval(node.conf.tp, env1, bound1)
        'cong1 @@
          a @@
          VSum(a, b) @@
          VLam(a, x => VInL(VSum(a, b), x)) @@
          eval(l.conf.term, env1, bound1) @@
          fold(l, env1, bound1, recM1) @@
          proofFold(l, env1, bound1, recM1, env2, bound2, recM2)

      case TEdge(r, InRLabel) :: Nil =>
        val VSum(a, b) = eval(node.conf.tp, env1, bound1)
        'cong1 @@
          b @@
          VSum(a, b) @@
          VLam(b, y => VInR(VSum(a, b), y)) @@
          eval(r.conf.term, env1, bound1) @@
          fold(r, env1, bound1, recM1) @@
          proofFold(r, env1, bound1, recM1, env2, bound2, recM2)
      case TEdge(x, SumLabel) :: TEdge(y, SumLabel) :: Nil =>
        val tp = eval(node.conf.tp, env1, bound1)
        val xtp = eval(x.conf.tp, env1, bound1)
        val ytp = eval(y.conf.tp, env1, bound1)

        val x1 = eval(x.conf.term, env1, bound1)
        val x2 = fold(x, env1, bound1, recM1)
        val eq_x1_x2 = proofFold(x, env1, bound1, recM1, env2, bound2, recM2)

        val y1 = eval(y.conf.term, env1, bound1)
        val y2 = fold(y, env1, bound1, recM1)
        val eq_y1_y2 = proofFold(y, env1, bound1, recM1, env2, bound2, recM2)

        'cong2 @@ xtp @@ ytp @@ tp @@
          VLam(xtp, x => VLam(ytp, y => VSum(x, y))) @@
          x1 @@ x2 @@ eq_x1_x2 @@
          y1 @@ y2 @@ eq_y1_y2
      case _ =>
        super.proofFold(node, env1, bound1, recM1, env2, bound2, recM2)
    }
}
