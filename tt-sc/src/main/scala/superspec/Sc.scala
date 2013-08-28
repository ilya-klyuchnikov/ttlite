package superspec

import mrsc.core._
import superspec.tt._

trait TTSc extends CoreSubst {

  // todo: it should be a term + context
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

  // just steps are more low-level
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
          case ElimLabel(_, _, sub) if node.in.node.conf.term / sub == term =>
            return Some(node.in.node)
          case _ =>
        }
        node = node.in.node
      }
      None
    }
  }
  trait Folding extends PiRules {
    override def fold(signal: Signal, g: G): List[S] =
      signal.map(n => FoldStep(n.sPath): S).toList
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

trait BaseResiduator extends TTSc with CoreAST with CoreEval with CoreSubst with CoreQuote {
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

case class LetSC[I](id1: String, id2: String, e: I) extends Stmt[I]

trait ScParser extends MetaParser {
  lexical.delimiters += ","
  lexical.reserved += "sc"
  override def stmts = List(letScStmt) ++ super.stmts
  lazy val letScStmt: PackratParser[Stmt[MTerm]] =
    ("(" ~> ident <~ ",") ~ ident ~ (")" ~ "=" ~ "sc" ~> term <~ ";") ^^ {
      case id1 ~ id2 ~ t => LetSC(id1, id2, t(Nil))
    }
}

object ScParser extends ScParser

trait ScREPL extends TTSc with BaseResiduator with ProofResiduator with GraphPrettyPrinter2 {
  override val parser = ScParser
  override def handleStmt(state: Context, stmt: Stmt[MTerm]): Context = stmt match {
    case LetSC(scId, proofId, it0) =>
      val it = fromM(it0)
      iinfer(state.vals, state.types, it) match {
        case None =>
          handleError("")
          state
        case Some(inTpVal) =>
          // start configuration is a normalized one!
          // it is a self contained!
          val conf = Conf(iquote(ieval(state.vals, it)), iquote(inTpVal))
          val sGraph = GraphGenerator(Rules, conf).toList.head
          val tGraph = Transformations.transpose(sGraph)

          //output(tgToString(tGraph))
          val resVal = ieval(state.vals, iquote(residuate(tGraph, state.vals)))
          val resTerm = iquote(resVal)
          val resType = iquote(inTpVal)

          val iTerm = Ann(resTerm, resType)

          val t2 = iinfer(state.vals, state.types, iTerm)
          t2 match {
            case None =>
              handleError("")
              state
            case Some(t3) =>
              output(icprint(resTerm) + " :: " + icprint(iquote(t3)) + ";")


              // this place is a bit unsafe:
              // we normalize a proof without first type-checking it
              // this is why we can use combinators cong1, cong2, ... as generic combinators -
              // that are applicable for *any* type, not only for small types (Set0).
              val rawProofVal = proofResiduate(tGraph, state.vals)
              val rawProofTerm = iquote(rawProofVal)
              val rawAnnProofTerm = Ann(rawProofTerm, Eq(resType, it, resTerm))

              val proofVal = ieval(state.vals, iquote(rawProofVal))
              val proofTerm = iquote(ieval(state.vals, iquote(proofVal)))
              // to check that it really built correctly
              val annProofTerm = Ann(proofTerm, Eq(resType, it, resTerm))
              val proofTypeVal = iinfer(state.vals, state.types, annProofTerm)
              output("raw proof:")
              output(icprint(rawProofTerm))
              output("proof:")
              output(icprint(proofTerm))

              // in general, this line will fail
              //iinfer(state.ne, state.ctx, rawAnnProofTerm).get

              //output("expected type:")
              //output(icprint(Eq(cType, it, cTerm)))
              output("::")
              output(icprint(iquote(proofTypeVal.get)))
              Context(
                state.vals + (Global(scId) -> resVal) + (Global(proofId) -> proofVal) + (Global(s"${proofId}_raw") -> proofVal),
                state.types + (Global(scId) -> inTpVal) + (Global(proofId) -> proofTypeVal.get))
          }
      }
    case _ =>
      super.handleStmt(state, stmt)
  }

  object Rules extends PiRules with Driving with Folding with Termination with NoRebuildings {
    val maxDepth = 10
  }
}

object TTScREPL
  extends ScREPL
  with CoreREPL with CoreDriver with CoreResiduator with CoreProofResiduator
  with FunREPL with FunDriver with FunResiduator with FunProofResiduator
  with DProductREPL with DProductDriver with DProductResiduator with DProductProofResiduator
  with SumREPL with SumDriver with SumResiduator with SumProofResiduator
  with EqREPL with EqDriver with EqResiduator with EqProofResiduator
  with NatREPL with NatDriver with NatResiduator with NatProofResiduator
  with ListREPL with ListDriver with ListResiduator with ListProofResiduator
  with ProductREPL with ProductDriver with ProductResiduator with ProductProofResiduator
  with FinREPL with FinDriver with FinResiduator with FinProofResiduator {
  override val name = "TT-SC"
}
