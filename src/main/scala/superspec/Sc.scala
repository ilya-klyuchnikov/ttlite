package superspec

import mrsc.core._
import superspec.tt._

// TODO
trait Rebuilder extends CoreSubst

// base supercompiler for type theory
trait TTSc extends CoreSubst {

  type Conf = DConf

  case class DConf(ct: Term, tp: Term)

  // sub - a substitution, using only this substitution we can perform a fold
  case class ElimBranch(ptr: Term, sub: Subst)
  trait DriveStep {
    def step(t: Conf): Step
  }

  case class ElimDStep(sel: Name, cases: List[ElimBranch]) extends DriveStep {
    override def step(t: Conf) =
      VariantsStep(sel, cases.map{
        branch => branch -> DConf(applySubst(t.ct, Map(sel -> branch.ptr)), applySubst(t.tp, Map(sel -> branch.ptr)))
      })
  }
  case object StopDStep extends DriveStep {
    override def step(t: Conf) = StopStep
  }
  // the only concern is driving neutral terms!!
  // everything else we get from evaluation!!
  def driveTerm(c: Conf): DriveStep

  def elimFreeVar(c: Conf, fv: Local): List[ElimDStep]

  trait Label
  case object NormLabel extends Label {
    override def toString = "->"
  }
  case class CaseBranchLabel(sel: Name, elim: ElimBranch) extends Label {
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
  case class VariantsStep(sel: Name, cases: List[(ElimBranch, Conf)]) extends Step {
    override val graphStep = {
      val ns = cases map { v => (v._2, CaseBranchLabel(sel, v._1)) }
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
              case CaseBranchLabel(_, ElimBranch(_, sub)) if sub == ren =>
                return Some(current.in.node)
              case _ =>
            }
          case _ =>

        }
        current = current.in.node
      }
      None
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
      debug(t)
      val piStep = driveTerm(t).step(t)

      //val fv = freeLocals(g.current.conf.ct).toList
      //val ss = fv.flatMap(x => elimFreeVar(g.current.conf, x).map(_.step(g.current.conf)))
      // This part generates too much results for now
      // piStep.graphStep :: ss.map(_.graphStep)
      piStep.graphStep :: Nil
    }
  }
  def debug(t: Conf)
}

trait BaseResiduator extends TTSc with CoreAST with CoreEval with CoreSubst with CoreREPL {
  type TG = TGraph[Conf, Label]
  type N = TNode[Conf, Label]
  def residuate(g: TG, nEnv: NameEnv[Value]): Value = {
    fold(g.root, nEnv, Nil, Map())
  }

  def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value = {
    node.base match {
      case Some(tPath) =>
        recM(tPath)
      case None =>
        node.outs match {
          case Nil =>
            eval(node.conf.ct, env, bound)
          case outs =>
            sys.error(s"Residualization of non-trivial constructions should be implemented in subclasses. Edges: $outs")
        }
    }
  }
}

object TTScREPL
  extends TTSc
  with BaseResiduator
  with GraphPrettyPrinter
  with CoreREPL
  with CoreSubst
  with CoreDriver
  with CoreResiduator
  with NatREPL
  with NatSubst
  with NatDriver
  with NatResiduator
  with ListREPL
  with ListSubst
  with ListDriver
  with ListResiduator
  with ProductREPL
  with ProductSubst
  with ProductDriver
  with ProductResiduator
   {

  val te = natTE ++ listTE ++ productTE
  val ve = natVE ++ listVE ++ productVE

  override def initialState = State(interactive = true, ve, te, Set())

  def debug(t: Conf) {
    //println(toString(t))
  }

  override def handleStmt(state: State, stmt: Stmt[I, TInf]): State = stmt match {
    case Supercompile(it) =>
      import int._
      iinfer(state.ne, state.ctx, it) match {
        case None =>
          handleError()
          state
        case Some(tp) =>
          val goal = DConf(iquote(ieval(state.ne, it)), iquote(tp))
          val rules = new Rules
          val gs = GraphGenerator(rules, goal)
          for (g <- gs) {
            val tGraph = Transformations.transpose(g)
            println(tgToString(tGraph))
            val resVal = residuate(tGraph, state.ne)
            val cTerm = iquote(resVal)
            val cType = iquote(tp)

            //val iTerm = Ann(cTerm, cType)
            //val t2 = iinfer(state.ne, state.ctx, iTerm)
            val t2 = iinfer(state.ne, state.ctx, cTerm)
            println("(" + icprint(cTerm) + ") ????)")
            t2 match {
              case None =>
                println("(" + icprint(cTerm) + ") ???? " + icprint(cType) + ";")
                println("handling error")
                handleError()
                state
              case Some(t3) =>
                println("(" + icprint(cTerm) + ") :: " + icprint(iquote(t3)) + ";")
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
