package superspec

import mrsc.core._
import superspec.tt._

trait TTSc extends CoreSubst {

  case class Conf(term: Term, tp: Term)

  trait Label
  case class ElimLabel(sel: Name, ptr: Term, sub: Subst) extends Label {
    override def toString = s"$sel = $ptr"
  }

  // drive steps are very high level
  sealed trait DriveStep {
    def step(t: Conf): Step
  }
  case class ElimDStep(cases: ElimLabel*) extends DriveStep {
    override def step(t: Conf) =
      VariantsStep(cases.toList.map(b => b -> Conf(t.term / Map(b.sel -> b.ptr), t.tp / Map(b.sel -> b.ptr))))
  }
  case class DecomposeDStep(label: Label, args: Conf*) extends DriveStep {
    override def step(t: Conf) = DecomposeStep(label, args.toList)
  }
  case object StopDStep extends DriveStep {
    override def step(t: Conf) = StopStep
  }

  sealed trait Step {
    val graphStep: GraphRewriteStep[Conf, Label]
  }
  case class VariantsStep(cases: List[(ElimLabel, Conf)]) extends Step {
    override val graphStep = AddChildNodesStep[Conf, Label](cases.map(v => (v._2, v._1)))
  }
  case class DecomposeStep(label: Label, args: List[Conf]) extends Step {
    override val graphStep = AddChildNodesStep[Conf, Label](args.map(_ -> label))
  }
  case object StopStep extends Step {
    override val graphStep = CompleteCurrentNodeStep[Conf, Label]()
  }

  // the only concern is driving neutral terms!!
  // everything else we get from evaluation!!
  def driveTerm(c: Conf): DriveStep

  trait PiRules extends MRSCRules[Conf, Label] {
    type Signal = Option[N]

    // we check elimBranch for subst
    // in order to ensure that we respect eliminator recursion
    def inspect(g: G): Signal = {
      val term = g.current.conf.term
      var node = g.current
      while (node.in != null) {
        node.in.driveInfo match {
          case ElimLabel(_, _, sub)
            if node.in.node.conf.term / sub == term =>
              return Some(node.in.node)
          case _ =>
        }
        node = node.in.node
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
      if (signal.isDefined) return List()
      val t = g.current.conf
      val piStep = driveTerm(t).step(t)
      piStep.graphStep :: Nil
    }
  }
}

trait BaseResiduator extends TTSc with CoreAST with CoreEval with CoreSubst with CoreREPL {
  type TG = TGraph[Conf, Label]
  type N = TNode[Conf, Label]
  def residuate(g: TG, nEnv: NameEnv[Value]): Value = {
    fold(g.root, nEnv.withDefault(vfree), Nil, Map())
  }

  def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.base match {
      case Some(tPath) => recM(tPath)
      case None => node.outs match {
        case Nil => eval(node.conf.term, env, bound)
        case outs => sys.error(s"Do not know how to fold $outs")
      }
    }
}

trait ProofResiduator extends BaseResiduator with EqAST {
  def proofResiduate(g: TG, nEnv: NameEnv[Value]): Value = {
    val env = nEnv.withDefault(vfree)
    proofFold(g.root, env, Nil, Map(), env, Nil, Map())
  }

  def proofFold(node: N,
                env: NameEnv[Value], bound: Env, recM: Map[TPath, Value],
                env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.base match {
      case Some(tPath) =>
        recM2(tPath)
      case None =>
        node.outs match {
          case Nil => eval(Refl(node.conf.tp, node.conf.term), env, bound)
          case outs => sys.error(s"Do not know how to fold $outs")
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
  with NatDriver
  with NatResiduator
  with ListREPL
  with ListDriver
  with ListResiduator
  with ProductREPL
  with ProductDriver
  with ProductResiduator
  with EqREPL
  with EqDriver
  with EqResiduator
  with EqProofResiduator
  with SumREPL
  with SumDriver
  with SumResiduator
  with FinREPL
  with FinDriver
  with FinResiduator
  with ProofResiduator
  with CoreProofResiduator
  with NatProofResiduator
  with ListProofResiduator
  with ProductProofResiduator
  with SumProofResiduator
  with FinProofResiduator
  with DProductDriver
  with DProductResiduator
  with DProductProofResiduator
{

  val te = natTE ++ listTE ++ productTE ++ eqTE ++ sumTE ++ finTE
  val ve = natVE ++ listVE ++ productVE ++ eqVE ++ sumVE ++ finVE

  case class Supercompile[I](e: I) extends Stmt[I, Nothing]
  case class Supercompile2[I](e: I) extends Stmt[I, Nothing]

  override lazy val int = new ScInterpreter
  class ScInterpreter extends CoreInterpreter {

    lazy val scStmt: PackratParser[Stmt[Term, Term]] =
      "sc" ~> term <~ ";" ^^ {t => Supercompile(t(Nil))}
    lazy val sc2Stmt: PackratParser[Stmt[Term, Term]] =
      "sc2" ~> term <~ ";" ^^ {t => Supercompile2(t(Nil))}

    lazy val scStmts = scStmt :: sc2Stmt :: stmts
    override lazy val stmt: PackratParser[Stmt[Term, Term]] = scStmts.reduce( _ | _)
  }

  override def initialState = State(interactive = true, ve, te, Set())

  override def handleStmt(state: State, stmt: Stmt[T, T]): State = stmt match {
    case Supercompile(it) =>
      import int._
      iinfer(state.ne, state.ctx, it) match {
        case None =>
          handleError()
          state
        case Some(tp) =>
          val goal = Conf(iquote(ieval(state.ne, it)), iquote(tp))

          val rules = new Rules
          val gs = GraphGenerator(rules, goal)
          for (g <- gs) {
            val tGraph = Transformations.transpose(g)
            output(tgToString(tGraph))
            val resVal = residuate(tGraph, state.ne)
            val cTerm = iquote(resVal)
            val cType = iquote(tp)

            output("input: [\n" + icprint(iquote(ieval(state.ne, it))) + "\n]")
            output("output: [\n" + icprint(cTerm) + "\n]")

            val iTerm = Ann(cTerm, cType)
            val t2 = iinfer(state.ne, state.ctx, iTerm)

            t2 match {
              case None =>
                println("error for term: \n" + icprint(cTerm))
                handleError()
              case Some(t3) =>
                output("input: [\n" + icprint(iquote(ieval(state.ne, it))) + "\n]")
                output("output: [\n" + icprint(cTerm) + "\n]")
                output("output type: " + icprint(iquote(t3)))
            }
          }
      }
      state
    case Supercompile2(it) =>
      import int._
      iinfer(state.ne, state.ctx, it) match {
        case None =>
          handleError()
          state
        case Some(tp) =>
          val goal = Conf(iquote(ieval(state.ne, it)), iquote(tp))
          val rules = new Rules
          val gs = GraphGenerator(rules, goal)
          for (g <- gs) {
            val tGraph = Transformations.transpose(g)
            //output(tgToString(tGraph))
            val resVal = residuate(tGraph, state.ne)
            val cTerm = iquote(resVal)
            val cType = iquote(tp)

            val iTerm = Ann(cTerm, cType)

            val t2 = iinfer(state.ne, state.ctx, iTerm)
            t2 match {
              case None =>
                handleError()
              case Some(t3) =>
                output(icprint(cTerm) + " :: " + icprint(iquote(t3)) + ";")
                val proof = proofResiduate(tGraph, state.ne)
                val proofTerm = /*iquote(proof)*/ iquote(ieval(state.ne, iquote(proof)))
                val annProofTerm = Ann(proofTerm, Eq(cType, it, cTerm))
                val t4 = iinfer(state.ne, state.ctx, annProofTerm)
                output("proof:")
                output(icprint(proofTerm))
                //output("expected type:")
                //output(icprint(Eq(cType, it, cTerm)))
                output("::")
                output(icprint(iquote(t4.get)))
            }
          }
      }
      state
    case _ =>
      super.handleStmt(state, stmt)
  }

  class Rules extends PiRules with Driving with Folding with Termination with NoRebuildings {
    val maxDepth = 20
  }
}
