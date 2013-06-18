package superspec

import superspec.lambdapi.{CoreAST, CoreREPL}
import mrsc.core._

trait Meta extends CoreAST {
  //============================================
  // Syntax
  type Subst = Map[Free, CTerm]

  sealed trait DriveStep
  case class NormDStep(next: CTerm) extends DriveStep
  case class VariantsDStep(sel: Free, cases: List[CTerm]) extends DriveStep
  case object StopDStep extends DriveStep

  // should be extended in sub-classes
  def driveTerm(c: CTerm): DriveStep

  def findSubst(from: CTerm, to: CTerm): Option[Subst]

  def applySubst(t: CTerm, subst: Subst): CTerm

  def isFreeSubTerm(t: CTerm, depth: Int): Boolean = t match {
    case Inf(i) =>
      isFreeSubTerm(i, depth)
    case Lam(c) =>
      isFreeSubTerm(c, depth + 1)
  }

  def isFreeSubTerm(t: ITerm, depth: Int): Boolean = t match {
    case Ann(c1, c2) =>
      isFreeSubTerm(c1, depth) && isFreeSubTerm(c2, depth)
    case Star =>
      true
    case Pi(c1, c2) =>
      isFreeSubTerm(c1, depth) && isFreeSubTerm(c2, depth + 1)
    case Bound(i) =>
      i < depth
    case Free(_) =>
      true
    case (c1 @ c2) =>
      isFreeSubTerm(c1, depth) && isFreeSubTerm(c2, depth)
  }
}

trait SuperSpec extends CoreREPL with Meta {
  // configuration supercompiler dealing with
  type Conf = (CTerm, CTerm)
  // transitions
  trait Label
  case object NormLabel extends Label {
    override def toString = "->"
  }
  case class CaseBranchLabel(sel: Free, ptr: CTerm) extends Label {
    override def toString = sel + " = " + ptr
  }

  def findConfSub(from: Conf, to: Conf): Option[Subst] = {
    val (from1, from2) = from
    val (to1, to2) = to
    (findSubst(from1, to1), findSubst(from2, to2)) match {
      case (Some(sub1), Some(sub2)) if sub1 ++ sub2 == sub2 ++ sub1 =>
        Some(sub1 ++ sub2)
      case _ =>
        None
    }
  }

  //============================================
  // A super-trait for a supercompiler
  trait ProofRules extends MRSCRules[Conf, Label]

  sealed trait MStep {
    val graphStep: GraphRewriteStep[Conf, Label]
  }
  // Reduction
  case class TransientMStep(next1: CTerm, next2: CTerm) extends MStep {
    val graphStep = AddChildNodesStep[Conf, Label](List(((next1, next2), NormLabel)))
  }
  case object StopMStep extends MStep {
    val graphStep = CompleteCurrentNodeStep[Conf, Label]()
  }
  case class VariantsMStep(sel: Free, cases: List[(CTerm, Conf)]) extends MStep {
    val graphStep = {
      val ns = cases map { v => (v._2, CaseBranchLabel(sel, v._1)) }
      AddChildNodesStep[Conf, Label](ns)
    }
  }

  // three generic components for building graph:
  // driving, folding, termination

  // POINT of multi-resultness
  trait Driving extends ProofRules {
    override def drive(signal: Signal, g: G): List[S] = {
      val (t1, t2) = g.current.conf
      val proofSteps: List[MStep] = (driveTerm(t1), driveTerm(t2)) match {
        case (NormDStep(n1), _) =>
          List(TransientMStep(n1, t2))
        case (_, NormDStep(n2)) =>
          List(TransientMStep(t1, n2))
        case (StopDStep, StopDStep) =>
          List(StopMStep)
        case (VariantsDStep(sel1, cases1), VariantsDStep(sel2, cases2)) =>
          List(
            VariantsMStep(sel1, cases1.map{t => (t, (applySubst(t1, Map(sel1 -> t)), applySubst(t2, Map(sel1 -> t))))}),
            VariantsMStep(sel2, cases2.map{t => (t, (applySubst(t1, Map(sel2 -> t)), applySubst(t2, Map(sel2 -> t))))})
          )
        case (VariantsDStep(sel1, cases1), _) =>
          List(
            VariantsMStep(sel1, cases1.map{t => (t, (applySubst(t1, Map(sel1 -> t)), applySubst(t2, Map(sel1 -> t))))})
          )
        case (_, VariantsDStep(sel2, cases2)) =>
          List(
            VariantsMStep(sel2, cases2.map{t => (t, (applySubst(t1, Map(sel2 -> t)), applySubst(t2, Map(sel2 -> t))))})
          )
      }
      proofSteps.map(_.graphStep)
    }
  }

  // folds as soon as there is a substitution
  // However, there is a huge difference from traditional supercompilation:
  // we investigate all possible foldings - cause not all folding may lead to
  // construction of a proof.
  // POINT of multi-resultness
  trait Folding extends ProofRules {
    override def fold(signal: Signal, g: G): List[S] = {
      val c = g.current.conf
      g.current.ancestors.filter(n => findConfSub(c, n.conf).isDefined).map(n => FoldStep(n.sPath): S)
    }
  }

  // The simplest termination strategy
  trait Termination extends ProofRules {
    val maxDepth: Int
    override def steps(g: G): List[S] =
      if (g.depth > maxDepth) List() else super.steps(g)
  }

}
