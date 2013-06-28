package superspec

import mrsc.core._
import superspec.tt._

// TODO
trait Rebuilder extends CoreSubst

// base supercompiler for type theory
trait TTSc extends CoreSubst {

  type Conf = DConf

  case class DConf(ct: CTerm, tp: CTerm)

  // sub - a substitution, using only this substitution we can perform a fold
  case class ElimBranch(ptr: CTerm, sub: Subst)
  trait DriveStep {
    def step(t: Conf): Step
  }

  case class ElimDStep(sel: Name, cases: List[ElimBranch], motive: CTerm) extends DriveStep {
    override def step(t: Conf) =
      VariantsStep(sel, cases.map{
        branch => branch -> DConf(applySubst(t.ct, Map(sel -> branch.ptr)), applySubst(t.tp, Map(sel -> branch.ptr)))
      }, motive)
  }
  case object StopDStep extends DriveStep {
    override def step(t: Conf) = StopStep
  }
  // the only concern is driving neutral terms!!
  // everything else we get from evaluation!!
  def driveTerm(c: Conf): DriveStep


  trait Label
  case object NormLabel extends Label {
    override def toString = "->"
  }
  case class CaseBranchLabel(sel: Name, elim: ElimBranch, motive: CTerm) extends Label {
    override def toString = sel + " = " + elim
  }

  // higher-level steps performed by supercompiler
  // this higher-level steps are translated into low-level
  trait Step {
    val graphStep: GraphRewriteStep[Conf, Label]
  }
  case class NormStep(next: Conf) extends Step {
    override val graphStep = AddChildNodesStep[Conf, Label](List(next -> NormLabel))
  }
  case object StopStep extends Step {
    override val graphStep = CompleteCurrentNodeStep[Conf, Label]()
  }
  case class VariantsStep(sel: Name, cases: List[(ElimBranch, Conf)], motive: CTerm) extends Step {
    override val graphStep = {
      val ns = cases map { v => (v._2, CaseBranchLabel(sel, v._1, motive)) }
      AddChildNodesStep[Conf, Label](ns)
    }
  }

  trait PiRules extends MRSCRules[Conf, Label] {
    type Signal = Option[N]

    // we check elimBranch for subst
    // in order to ensure that we respect eliminator recursion
    def inspect(g: G): Signal = {
      var current = g.current
      while (current.in != null) {
        val parConf = current.in.node.conf
        val label = current.in.driveInfo
        findRenaming(g.current.conf.ct, parConf.ct) match {
          case Some(ren) =>
            label match {
              case CaseBranchLabel(_, ElimBranch(_, sub), _) if sub == ren =>
                return Some(current.in.node)
              case _ =>
            }
          case _ =>

        }
        current = current.in.node
      }
      None
      //g.current.ancestors.find(n => findRenaming(g.current.conf, n.conf).isDefined)
    }
  }
  trait Folding extends PiRules {
    override def fold(signal: Signal, g: G): List[S] = {
      signal.map(n => FoldStep(n.sPath): S).toList
    }
  }
  trait NoRebuildings extends PiRules {
    override def rebuild(signal: Signal, g: G) = List()
  }
  // The simplest termination strategy
  trait Termination extends PiRules {
    val maxDepth: Int
    override def steps(g: G): List[S] =
      if (g.depth > maxDepth) List(StopStep.graphStep) else super.steps(g)
  }
  trait Driving extends PiRules {
    override def drive(signal: Signal, g: G): List[S] = {
      if (signal.isDefined)
        return List()
      val t = g.current.conf
      val piStep = driveTerm(t).step(t)
      List(piStep.graphStep)
    }
  }

}

trait BaseResiduator extends TTSc with CoreAST with CoreEval with CoreSubst with CoreREPL {

  def residuate(g: TGraph[Conf, Label], nEnv: NameEnv[Value], bEnv: Env, tps: NameEnv[Value], tp: Value): Value = {
    fold(g, g.root, nEnv, bEnv, Map(), tps, tp)
  }

  /// context!!!!!
  /// tp - current type of expression
  def fold(g: TGraph[Conf, Label], node: TNode[Conf, Label], nEnv: NameEnv[Value], bEnv: Env, dRed: Map[CTerm, Value], tps: NameEnv[Value], tp: Value): Value = {
    //println("===")
    //println("conf=" + int.icprint(node.conf))
    //println("raw type=" + tp)
    //println("type=" + quote0(tp))
    //println("type=" + int.icprint(quote0(tp)))
    node.base match {
      case Some(tPath) =>
        dRed(g.get(tPath).conf.ct)
      case None =>
        node.outs match {
          case Nil =>
            eval(node.conf.ct, nEnv, bEnv)
          case outs =>
            sys.error(s"Residualization of non-trivial constructions should be implemented in subclasses. Edges: $outs")
        }
    }
  }
}

object TTScREPL
  extends TTSc
  with CoreREPL
  with CoreSubst
  with CoreDriver
  with NatREPL
  with NatSubst
  with NatDriver
  with ListREPL
  with ListSubst
  with ListDriver
  with BaseResiduator
  with CoreResiduator
  with NatResiduator
  with ListResiduator
  with GraphPrettyPrinter {

  val te = natTE ++ listTE
  val ve = natVE ++ listVE
  override def initialState = State(interactive = true, ve, te, Set())

  override def handleStmt(state: State, stmt: Stmt[I, TInf]): State = stmt match {
    case Supercompile(it) =>
      import int._
      iinfer(state.ne, state.ctx, it) match {
        case None =>
          handleError()
          state
        case Some(tp) =>
          val goal: DConf = DConf(iquote(ieval(state.ne, it)), iquote(tp))
          val rules: MRSCRules[Conf, Label] = new Rules
          val gs = GraphGenerator(rules, goal).toList
          for (g <- gs) {
            val tGraph = Transformations.transpose(g)
            println(tgToString(tGraph))
            val resVal = residuate(tGraph, state.ne, List(), state.ctx, tp)
            val cTerm = iquote(resVal)
            val cType = iquote(tp)

            val iTerm = Ann(cTerm, cType)
            val t2 = iinfer(state.ne, state.ctx, iTerm)
            t2 match {
              case None =>
                println("(" + icprint(cTerm) + ") :: " + icprint(cType) + ";")
                handleError()
                state
              case Some(_) =>
                println("(" + icprint(cTerm) + ") :: " + icprint(cType) + ";")
            }
          }
      }
      state
    case _ =>
      super.handleStmt(state, stmt)
  }

  class Rules extends PiRules with Driving with Folding with Termination with NoRebuildings {
    val maxDepth = 10
  }
}