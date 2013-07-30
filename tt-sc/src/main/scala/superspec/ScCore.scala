package superspec

import superspec.tt._
import mrsc.core._

trait CoreSubst extends CoreEval with CoreQuote {
  type Subst = Map[Name, Term]

  def findRenaming(from: Term, to: Term): Option[Subst] =
    for (s <- findSubst(from, to) if findSubst(to, from).isDefined) yield  s

  def findSubst(from: Term, to: Term): Option[Subst] =
    for (sub <- findSubst0(from, to))
    yield sub.filter { case (k, v) => v != Free(k) }

  def findSubst0(from: Any, to: Any): Option[Subst] = (from, to) match {
    case (Free(n@Local(_)), t: Term) =>
      if (isFreeSubTerm(t, 0)) Some(Map(n -> t)) else None
    case (Free(n@Assumed(_)), t: Term) =>
      if (isFreeSubTerm(t, 0)) Some(Map(n -> t)) else None
    case (Free(Global(n)), Free(Global(m))) =>
      if (n == m) Some(Map()) else None
    case (Free(Global(n)), _) =>
      None
    case (Bound(i), Bound(j)) =>
      if (i == j) Some(Map()) else None
    case (f@Free(Quote(_)), _) =>
      sys.error("Hey, I do note expect quoted variables here!")
    case (Lam(t1, e1), Lam(t2, e2)) =>
      mergeOptSubst(
        findSubst0(t1, t2),
        findSubst0(e1, e2)
      )
    case (from: scala.Product, to: scala.Product)
      if from.getClass == to.getClass =>
      val subs = (from.productIterator.toList zip to.productIterator.toList).map {
        case (f1, t1) => findSubst0(f1, t1)
      }
      mergeOptSubst(subs: _*)
    case _ =>
      None
  }

  def mergeSubst(sub1: Subst, sub2: Subst): Option[Subst] = {
    val merged1 = sub1 ++ sub2
    val merged2 = sub2 ++ sub1
    if (merged1 == merged2)
      Some(merged1)
    else
      None
  }

  def mergeOptSubst(subs: Option[Subst]*): Option[Subst] = {
    var res = Map():Subst
    for (sub <- subs) {
      sub match {
        case None =>
          return None
        case Some(s) =>
          mergeSubst(res, s) match {
            case None =>
              return None
            case Some(s) =>
              res = s
          }
      }
    }
    Some(res)
  }


  def applySubst(t: Term, subst: Subst): Term = {
    val env: NameEnv[Value] = subst.map {case (n, t) => (n, eval(t, emptyNEnv, Nil))}
    quote0(eval(t, env, Nil))
  }

  def isFreeSubTerm(t: Any, depth: Int): Boolean = t match {
    case Pi(c1, c2) =>
      isFreeSubTerm(c1, depth) && isFreeSubTerm(c2, depth + 1)
    case Lam(t, e) =>
      isFreeSubTerm(t, depth) && isFreeSubTerm(e, depth + 1)
    case Bound(i) =>
      i < depth
    case Free(_) =>
      true
    case t1: scala.Product =>
      t1.productIterator.forall(isFreeSubTerm(_, depth))
    case _ => true
  }

}

trait CoreDriver extends TTSc with CoreCheck {
  var v = 100
  def freshName(tp: Term): Name = {
    v += 1;
    val res = Local(v)
    typeMap = typeMap + (res -> tp)
    res
  }

  def freshLocal(tp: Term): Term =
    Free(freshName(tp))

  // current ad-hoc solution for mapping variables and types of new free variables

  // knowledge about which variable has which type
  // todo ; put bound here
  var typeMap: Map[Name, Term] = Map()

  // boilerplate/indirections
  case class LamLabel(f: Name) extends Label
  case class LamStep(f: Name, next: Conf) extends Step {
    override val graphStep =
      AddChildNodesStep[Conf, Label](List(next -> LamLabel(f)))
  }
  case class LamDStep(f: Name, next: Conf) extends DriveStep {
    override def step(t: Conf) =
      LamStep(f, next)
  }

  // logic
  override def driveTerm(c: Conf): DriveStep = eval0(c.term) match {
    case VNeutral(n) => driveNeutral(n)
    case _ => decompose(c)
  }

  // TODO: if override returns stop, then we can decompose
  def driveNeutral(n: Neutral): DriveStep = n match {
    case NApp(n, _) => driveNeutral(n)
    case _ => StopDStep
  }

  def decompose(c: Conf): DriveStep = c.term match {
    // TODO: into separate trait "WithLambda" and use axiom for extensional equality
    /*
    case Lam(t, f) =>
      val Pi(t1, t2) = c.tp
      val fn = freshName(t1)
      val nextTerm = iSubst(0, Free(fn), f)
      val nextType = iSubst(0, Free(fn), t2)
      LamDStep(fn, Conf(nextTerm, nextType))
    */
    case _ => StopDStep
  }

  override def elimFreeVar(c: Conf, fv: Local): List[ElimDStep] =
    Nil

}

trait CoreResiduator extends BaseResiduator with CoreDriver {
  import mrsc.core._

  override def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.outs match {
      case TEdge(n1, LamLabel(fn)) :: Nil =>
        val Pi(t1, _) = node.conf.tp
        VLam(eval(t1, env, bound), v => fold(n1, env + (fn -> v), v :: bound, recM))
      case _ =>
        super.fold(node, env, bound, recM)
    }
}

trait CoreProofResiduator extends ProofResiduator with CoreResiduator {

  override def proofFold(node: N,
                         env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                         env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.outs match {
      case _ =>  super.proofFold(node, env, bound, recM, env2, bound2, recM2)
    }
}
