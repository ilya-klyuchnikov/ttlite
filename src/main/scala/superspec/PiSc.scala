package superspec

import mrsc.core._
import superspec.lambdapi._

// single configuration
trait Driver extends CoreSubst {
  sealed trait DriveStep
  case class NormDStep(next: CTerm) extends DriveStep
  case class VariantsDStep(sel: Name, cases: List[ElimCase]) extends DriveStep
  case object StopDStep extends DriveStep
  case class LeibnizDStep(cong: CTerm, rec: CTerm) extends DriveStep

  // the only concern is driving neutral terms!!
  // everything else we get from evaluation!!
  def driveTerm(c: CTerm): DriveStep

  // ptr - a case that was taken: Zero, Succ(N)
  // sub - a substitution, using only this substitution we can perform a fold
  case class ElimCase(ptr: CTerm, sub: Subst)
}

// simple supercompiler for lambda-pi
trait PiSc extends Driver {

  trait Label
  case object NormLabel extends Label {
    override def toString = "->"
  }
  // case branch is for eliminator,
  // since any eliminator knows recursion pattern,
  // this should be specialized in order of folder to
  // perform folding using correct renaming.
  case class CaseBranchLabel(sel: Name, ptr: CTerm, sub: Option[Subst]) extends Label {
    override def toString = sel + " = " + ptr
  }
  // todo: move into Eq.scala
  case class LeibnizLabel(f: CTerm) extends Label {
    override def toString = "Leibniz: " + f
  }

  // higher-level steps performed by supercompiler
  // this higher-level steps are translated into low-level
  sealed trait Step {
    val graphStep: GraphRewriteStep[CTerm, Label]
  }
  case class NormStep(next: CTerm) extends Step {
    override val graphStep = AddChildNodesStep[CTerm, Label](List((next, NormLabel)))
  }
  case object StopStep extends Step {
    override val graphStep = CompleteCurrentNodeStep[CTerm, Label]()
  }

  case class VariantsStep(sel: Name, cases: List[(CTerm, CTerm)]) extends Step {
    override val graphStep = {
      val ns = cases map { v => (v._2, CaseBranchLabel(sel, v._1, null)) }
      AddChildNodesStep[CTerm, Label](ns)
    }
  }
  case class LeibnizStep(f: CTerm, next: CTerm) extends Step {
    override val graphStep = AddChildNodesStep[CTerm, Label](List((next, LeibnizLabel(f))))
  }

  trait PiRules extends MRSCRules[CTerm, Label] {
    type Signal = Option[N]
    def inspect(g: G): Signal = {
      val c = g.current.conf
      g.current.ancestors.filter(n => findSubst(c, n.conf).isDefined).headOption
    }
  }

}
