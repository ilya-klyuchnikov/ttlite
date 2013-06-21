package superspec

import mrsc.core._
import superspec.lambdapi._

// very simple supercompiler for supercompilation
// of pair of terms
trait SuperSpec extends Driver {
  // configuration supercompiler dealing with
  type Conf = (CTerm, CTerm)
  // transitions
  trait Label
  case object NormLabel extends Label {
    override def toString = "->"
  }
  case class CaseBranchLabel(sel: Name, ptr: ElimCase) extends Label {
    override def toString = sel + " = " + ptr
  }
  // congruence
  case class LeibnizLabel(f: CTerm) extends Label {
    override def toString = "Leibniz: " + f
  }

  def findConfSub(from: Conf, to: Conf): Option[Subst] = {
    val (from1, from2) = from
    val (to1, to2) = to
    mergeOptSubst(findSubst(from1, to1), findSubst(from2, to2))
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
  case class VariantsMStep(sel: Name, cases: List[(ElimCase, Conf)]) extends MStep {
    val graphStep = {
      val ns = cases map { v => (v._2, CaseBranchLabel(sel, v._1)) }
      AddChildNodesStep[Conf, Label](ns)
    }
  }
  case class LeibnizMStep(f: CTerm, next1: CTerm, next2: CTerm) extends MStep {
    val graphStep = AddChildNodesStep[Conf, Label](List(((next1, next2), LeibnizLabel(f))))
  }

  //============================================
  // A super-trait for a supercompiler
  trait ProofRules extends MRSCRules[Conf, Label] {
    type Signal = Option[N]
    def inspect(g: G): Signal = {
      val c = g.current.conf
      g.current.ancestors.filter(n => findConfSub(c, n.conf).isDefined).headOption
    }
  }

  // three generic components for building graph:
  // driving, folding, termination

  // POINT of multi-resultness
  // TODO: make it more generic
  // handling new possibility should be easy
  trait ProofDriving extends ProofRules {
    override def drive(signal: Signal, g: G): List[S] = {
      if (signal.isDefined)
        return List()
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
            VariantsMStep(sel1, cases1.map{t => (t, (applySubst(t1, Map(sel1 -> t.ptr)), applySubst(t2, Map(sel1 -> t.ptr))))}),
            VariantsMStep(sel2, cases2.map{t => (t, (applySubst(t1, Map(sel2 -> t.ptr)), applySubst(t2, Map(sel2 -> t.ptr))))})
          )
        case (VariantsDStep(sel1, cases1), _) =>
          List(
            VariantsMStep(sel1, cases1.map{t => (t, (applySubst(t1, Map(sel1 -> t.ptr)), applySubst(t2, Map(sel1 -> t.ptr))))})
          )
        case (_, VariantsDStep(sel2, cases2)) =>
          List(
            VariantsMStep(sel2, cases2.map{t => (t, (applySubst(t1, Map(sel2 -> t.ptr)), applySubst(t2, Map(sel2 -> t.ptr))))})
          )
        case (LeibnizDStep(f1, t1), LeibnizDStep(f2, t2)) =>
          if (f1 == f2) List(LeibnizMStep(f1, t1, t2)) else List(StopMStep)
        case (LeibnizDStep(_, _), StopDStep) =>
          List(StopMStep)
        case (StopDStep, LeibnizDStep(_, _)) =>
          List(StopMStep)
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
      signal.map(n => FoldStep(n.sPath): S).toList
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

// currently it is hard-coded for nats
// for one-variable case -> really it will be like interpreter!!!
trait Residuator extends SuperSpec with CoreAST with EqAST with NatAST with CoreEval with CoreSubst {

  // TODO
  def freeLocals(ct: CTerm): List[Name] = List(Local(1))

  def residuateToVal(g: TGraph[Conf, Label], nEnv: NameEnv[Value], bEnv: Env): Value = {
    val startRed: Map[Conf, Value] = Map()
    val (c1, c2) = g.root.conf
    val locals = (freeLocals(c1) ++ freeLocals(c2)).distinct
    val startFun : (NameEnv[Value], Env) => Value = (n, b) => fold(g, g.root, n, b, startRed)
    val fun = locals.foldLeft(startFun){(f, local) => (n, b) => VLam(x => f(local -> x :: n, b))}
    fun(nEnv, bEnv)
  }

  /// context!!!!!
  def fold(g: TGraph[Conf, Label], node: TNode[Conf, Label], nEnv: NameEnv[Value], bEnv: Env, dRed: Map[Conf, Value]): Value =
    node.base match {
      // recursive node
      case Some(tPath) =>
        dRed(g.get(tPath).conf)
      case None =>
        node.outs match {
          case List() =>
            VRefl(VNat, cEval0(node.conf._1))
          case
            TEdge(nodeZ, CaseBranchLabel(sel1, ElimCase(Zero, _))) ::
              TEdge(nodeS, CaseBranchLabel(sel2, ElimCase(Succ(Inf(Free(fresh))), _))) ::
              Nil =>

            val (c1, c2) = node.conf
            val motive =
              VLam {n => VEq(VNat, cEval(c1,(sel1, n) :: nEnv, bEnv), cEval(c2, sel1 -> n :: nEnv, bEnv))}
            val zCase =
              fold(g, nodeZ, nEnv, bEnv, dRed)

            val sCase =
              VLam {n => VLam {rec => fold(g, nodeS, fresh -> n :: nEnv, bEnv, dRed + (node.conf -> rec))}}

            VNeutral(NFree(Global("natElim"))) @@ motive @@ zCase @@ sCase @@ lookup(sel1, nEnv).get
          case TEdge(n1, LeibnizLabel(f)) :: Nil =>
            val (c1, c2) = n1.conf
            VNeutral(NFree(Global("leibniz"))) @@
              VNat @@
              VNat @@
              cEval(f, nEnv, bEnv) @@
              cEval(c1, nEnv, bEnv) @@
              cEval(c2, nEnv, bEnv) @@
              fold(g, n1, nEnv, bEnv, dRed)
        }
    }
}

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
  with PiGraphPrettyPrinter
  with Residuator {

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
            val resVal = residuateToVal(tGraph, state.ne, List())
            val tRes = iquote(resVal)
            println(int.icprint(tRes))

          }
        case None =>
      }
      state
    case _ =>
      super.handleCommand(state, cmd)
  }

  class SpecSc extends ProofRules with ProofDriving with Folding with Termination with NoRebuildings {
    val maxDepth = 10
  }
}