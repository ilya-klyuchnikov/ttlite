package superspec

import superspec.tt._
import mrsc.core._

trait ProductDriver extends CoreDriver with ProductAST {

  case object PairLabel extends Label

  override def driveNeutral(n: Neutral): DriveStep = n match {
    case NProductElim(a, b, _, _, p) =>
      p match {
        case NFree(n) =>
          val aType = quote0(a)
          val bType = quote0(b)

          val xName = freshName(aType)
          val x = Free(xName)

          val yName = freshName(bType)
          val y = Free(yName)

          val pairCase = ElimLabel(n, Pair(aType, bType, x, y), Map())

          ElimDStep(pairCase)
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def decompose(c: Conf): DriveStep = c.term match {
    case Pair(a, b, x, y) =>
      val Product(a1, b1) = c.tp
      DecomposeDStep(PairLabel, Conf(x, a), Conf(y, b))
    case _ =>
      super.decompose(c)
  }

}

trait ProductResiduator extends BaseResiduator with ProductDriver {
  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeS, ElimLabel(sel, Pair(a, b, Free(xN), Free(yN)), _)) :: Nil =>
        val aVal = eval(a, env, bound)
        val bVal = eval(b, env, bound)
        val motive =
          VLam(VProduct(aVal, bVal), p => eval(node.conf.tp, env + (sel -> p), p :: bound))

        val pairCase = VLam(aVal, x => VLam(bVal, y =>
          fold(nodeS, env + (xN -> x) + (yN -> y), y :: x :: bound, recM)))

        'productElim @@
          aVal @@
          bVal @@
          motive @@
          pairCase @@
          env(sel)
      case TEdge(x, PairLabel) :: TEdge(y, PairLabel) :: Nil =>
        val VProduct(aType, bType) = eval(node.conf.tp, env, bound)
        'Pair @@
          aType @@
          bType @@
          fold(x, env, bound, recM) @@
          fold(y, env, bound, recM)
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait ProductProofResiduator extends ProductResiduator with ProofResiduator {
  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(nodeS, ElimLabel(sel, Pair(a, b, Free(xN), Free(yN)), _)) :: Nil =>
        val aVal = eval(a, env, bound)
        val bVal = eval(b, env, bound)
        val motive =
          VLam(VProduct(aVal, bVal), n =>
            VEq(
              eval(node.conf.tp, env + (sel -> n), n :: bound),
              eval(node.conf.term, env + (sel -> n), n :: bound),
              fold(node, env + (sel -> n), n :: bound, recM)))

        val pairCase = VLam(aVal, x => VLam(bVal, y =>
          proofFold(nodeS,
            env + (xN -> x) + (yN -> y), y :: x :: bound, recM,
            env2 + (xN -> x) + (yN -> y), y :: x :: bound2, recM2)))

        'productElim @@
          aVal @@
          bVal @@
          motive @@
          pairCase @@
          env(sel)

      case TEdge(x, PairLabel) :: TEdge(y, PairLabel) :: Nil =>
        val VProduct(a, b) = eval(node.conf.tp, env, bound)
        val x1 = eval(x.conf.term, env, bound)
        val x2 = fold(x, env, bound, recM)
        val eq_x1_x2 = proofFold(x, env, bound, recM, env2, bound2, recM2)

        val y1 = eval(y.conf.term, env, bound)
        val y2 = fold(y, env, bound, recM)
        val eq_y1_y2 = proofFold(y, env, bound, recM, env2, bound2, recM2)

        'cong2 @@ a @@ b @@ ('Product @@ a @@ b) @@
          ('Pair @@ a @@ b) @@
          x1 @@ x2 @@ eq_x1_x2 @@
          y1 @@ y2 @@ eq_y1_y2

      case _ =>
        super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
