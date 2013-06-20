package superspec

import mrsc.core._
import superspec.lambdapi._

trait Driver extends CoreSubst {
  sealed trait DriveStep
  case class NormDStep(next: CTerm) extends DriveStep
  case class VariantsDStep(sel: Name, cases: List[CTerm]) extends DriveStep
  case object StopDStep extends DriveStep

  // the only concern is driving neutral terms!!
  // everything else we get from evaluation!!
  def driveTerm(c: CTerm): DriveStep
}

trait SuperSpec extends Driver {
  // configuration supercompiler dealing with
  type Conf = (CTerm, CTerm)
  // transitions
  trait Label
  case object NormLabel extends Label {
    override def toString = "->"
  }
  case class CaseBranchLabel(sel: Name, ptr: CTerm) extends Label {
    override def toString = sel + " = " + ptr
  }

  def findConfSub(from: Conf, to: Conf): Option[Subst] = {
    val (from1, from2) = from
    val (to1, to2) = to
    mergeOptSubst(findSubst(from1, to1), findSubst(from2, to2))
  }

  //============================================
  // A super-trait for a supercompiler
  trait ProofRules extends MRSCRules[Conf, Label] {
    type Signal = None.type
    def inspect(g: G): Signal = None
  }

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
  case class VariantsMStep(sel: Name, cases: List[(CTerm, Conf)]) extends MStep {
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

  trait NoRebuildings extends ProofRules {
    override def rebuild(signal: Signal, g: G) = List()
  }


  // The simplest termination strategy
  trait Termination extends ProofRules {
    val maxDepth: Int
    override def steps(g: G): List[S] =
      if (g.depth > maxDepth) List(StopMStep.graphStep) else super.steps(g)
  }

}

case class SC(in: String) extends Command

object SuperSpecREPL
  extends SuperSpec
  with CoreREPL
  with CoreSubst
  with CoreDriver
  with EqREPL
  with EqSubst
  with EqDriver
  with NatREPL
  with NatSubst
  with NatDriver
  with PiGraphPrettyPrinter {

  val te = natTE ++ eqTE
  val ve = natVE ++ eqVE
  override def initialState = State(interactive = true, ve, te, Set())
  override def commands: List[Cmd] =
    Cmd(List(":sc"),      "<expr>, <expr>", x => SC(x), "supercompile") :: super.commands

  override def handleCommand(state: State, cmd: Command): State = cmd match {
    case SC(in) =>
      import int._
      val parsed = int.parseIO(int.iiparse ~ "," ~ int.iiparse ^^ {case t1 ~ _ ~ t2 => (t1, t2)}, in)
      parsed match {
        case Some((t1, t2)) =>
          val l = iquote(ieval(state.ne, t1))
          val r = iquote(ieval(state.ne, t2))
          val goal = (l, r)
          val rules = new SpecSc
          val gs = GraphGenerator(rules, goal).toList
          for (g <- gs) {
            val tGraph = Transformations.transpose(g)
            println(tgToString(tGraph))
          }
        case None =>
      }
      state
    case _ =>
      super.handleCommand(state, cmd)
  }

  class SpecSc extends ProofRules with Driving with Folding with Termination with NoRebuildings {
    val maxDepth = 10
  }
}