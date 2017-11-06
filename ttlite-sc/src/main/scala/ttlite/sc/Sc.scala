package ttlite.sc

import mrsc.core._
import ttlite.core._
import ttlite.common._

trait TTSc extends CoreSubst with CoreCheck {

  case class Conf(term: Term, ctx: Context[Value]) {
    val tpVal = iType0(ctx, term)
    val tp = quote0(tpVal)
  }

  trait Label
  case class ElimLabel(sel: Name, ptr: Term, sub: Subst, types: NameEnv[Value]) extends Label {
    override def toString = s"$sel = $ptr"
  }

  // drive steps are very high level
  sealed trait DriveStep {
    def step(t: Conf): Step
  }
  case class ElimDStep(cases: ElimLabel*) extends DriveStep {
    override def step(t: Conf) =
      VariantsStep(
        cases.toList.map { lbl: ElimLabel =>
          lbl -> Conf(
            t.term / Map(lbl.sel -> lbl.ptr),
            lbl.types.foldLeft(t.ctx)((ctx, nt) => ctx.addType(nt._1, nt._2)))})
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

  def singleDrive(c: Conf): DriveStep

  def multiDrive(c: Conf): List[DriveStep]
}

trait BaseResiduator extends TTSc with CoreAST with CoreEval with CoreSubst with CoreQuoting {
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

trait ProofResiduator extends BaseResiduator with IdAST with FunAST {
  import scala.language.implicitConversions
  implicit def sym2appV(s: Symbol): VApplicable =
    VNeutral(NFree(Global(s.name)))

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

case class SC[I](outId: Id, proofId: Id, e: I) extends Stmt[I]

trait ScParser extends MetaParser {
  lexical.delimiters += ","
  lexical.reserved += ("sc", "mrsc")
  override def stmts = List(scStmt) ++ super.stmts
  lazy val scStmt: PackratParser[Stmt[MTerm]] =
    ("(" ~> globalId <~ ",") ~ globalId ~ (")" ~ "=" ~ "sc" ~> term <~ ";") ^^ {
      case id1 ~ id2 ~ t => SC(id1, id2, t(Nil))
    }
}

object ScParser extends ScParser

trait ScREPL extends CoreREPL with TTSc with BaseResiduator with ProofResiduator with GraphPrettyPrinter2 {
  import ttlite.common.IoUtil._
  override val parser = ScParser
  override def handleStmt(state: Context[V], stmt: Stmt[MTerm]): Context[V] = stmt match {
    case SC(scId, proofId, mTerm) =>
      val inputTerm = translate(mTerm)
      val inputTypeValue = infer(state, inputTerm)
      val inputType = quote(inputTypeValue)

      // JFYI: start configuration is a normalized one and it is a self-contained
      val startConf = Conf(quote(eval(state, inputTerm)), state)
      val sGraphs = GraphGenerator(SingleRules, startConf).toList
      assert(sGraphs.size == 1)
      val sGraph = sGraphs.head
      val tGraph = Transformations.transpose(sGraph)

      val outputValue = eval(state, quote(residuate(tGraph, state.vals)))
      val outputTerm = quote(outputValue)

      if (verbose) {
        output(tgToString(tGraph))
      }

      // this is just smoke testing - output type should be the same as the input one
      infer(state, Ann(outputTerm, inputType))

      // This place is a bit tricky (and a bit unsafe):
      // when we construct a proof we construct it as a value.
      // (unfolding functions like `cong1`, `cong2`) without type-checking.
      // This is why we can use combinators cong1, cong2, ... as generic combinators -
      // that are applicable for *any* type, not only for small types (Set0).
      // Otherwise, we should implement indexed universes - see https://github.com/ilya-klyuchnikov/ttlite/issues/61
      // Caveat: this line may not terminate if there is an error in proof generator
      val rawProofVal = proofResiduate(tGraph, state.vals)

      // in general case it may fail since proof combinators (symm, cong) are defined for Set0
      // proof combinators
      // val rawProofTerm = quote(rawProofVal)
      // infer(state, Ann(rawProofTerm, Id(inputType, inputTerm, outputTerm)))

      val proofVal = eval(state, quote(rawProofVal))
      val proofTerm = quote(eval(state, quote(proofVal)))

      // to check that it really built correctly
      val proofTypeVal = infer(state, Ann(proofTerm, Id(inputType, inputTerm, outputTerm)))
      val proofType = quote(proofTypeVal)

      if (scId.n != "_") {
        output(ansi(s"@|bold ${scId.n}|@ : ${pretty(inputType)};"))
        output(ansi(s"@|bold ${scId.n}|@ = ${pretty(outputTerm)};\n"))
      }

      if (proofId.n != "_") {
        output(ansi(s"@|bold ${proofId.n}|@ : ${pretty(proofType)};"))
        output(ansi(s"@|bold ${proofId.n}|@ = ${pretty(proofTerm)};\n"))
      }

      if (state.ids.contains(scId.n)) {
        throw DuplicateIdError(scId)
      }
      val state1 = if (scId.n != "_") state.addVal(Global(scId.n), outputValue, inputTypeValue) else state
      if (state1.ids.contains(proofId.n)) {
        throw DuplicateIdError(proofId)
      }
      val state2 = if (proofId.n != "_") state1.addVal(Global(proofId.n), proofVal, proofTypeVal) else state1

      state2
    case _ =>
      super.handleStmt(state, stmt)
  }

  trait BaseRules extends MRSCRules[Conf, Label] {
    type Signal = Option[N]

    // we check elimBranch for subst
    // in order to ensure that we respect eliminator recursion
    def inspect(g: G): Signal = {
      val term = g.current.conf.term
      var node = g.current
      while (node.in != null) {
        node.in.driveInfo match {
          case ElimLabel(_, _, sub, _) if node.in.node.conf.term / sub == term =>
            return Some(node.in.node)
          case _ =>
        }
        node = node.in.node
      }
      None
    }
  }

  trait Folding extends BaseRules {
    override def fold(signal: Signal, g: G): List[S] =
      signal.map(n => FoldStep(n.sPath): S).toList
  }
  trait NoRebuildings extends BaseRules {
    override def rebuild(signal: Signal, g: G) = List()
  }
  // The simplest termination strategy
  trait Termination extends BaseRules {
    val maxDepth: Int
    override def steps(g: G): List[S] =
      if (g.depth > maxDepth) List(StopStep.graphStep) else super.steps(g)
  }

  trait SingleDriving extends BaseRules {
    override def drive(signal: Signal, g: G): List[S] =
      if (signal.isEmpty) {
        val t = g.current.conf
        val piStep = singleDrive(t).step(t)
        piStep.graphStep :: Nil
      } else
        Nil
  }

  trait MultiDriving extends BaseRules {
    override def drive(signal: Signal, g: G): List[S] = {
      val t = g.current.conf
      multiDrive(t).map(_.step(t).graphStep)
    }
  }

  object SingleRules extends BaseRules with SingleDriving with Folding with Termination with NoRebuildings {
    val maxDepth = 4
  }
}

class TTScREPL
  extends TTSc
  with CoreREPL with CoreDriver with CoreResiduator with CoreProofResiduator
  with FunREPL with FunDriver with FunResiduator with FunProofResiduator
  with DPairREPL with DPairDriver with DPairResiduator with DPairProofResiduator
  with SumREPL with SumDriver with SumResiduator with SumProofResiduator
  with IdREPL with IdDriver with IdResiduator with IdProofResiduator
  with NatREPL with NatDriver with NatResiduator with NatProofResiduator
  with ListREPL with ListDriver with ListResiduator with ListProofResiduator
  with PairREPL with PairDriver with PairResiduator with PairProofResiduator
  with FinREPL with FinDriver with FinResiduator with FinProofResiduator
  with ScREPL {
  override val name = "TT-SC"
}

object TTScREPL {
  def main(args: Array[String]): Unit = {
    new TTScREPL().mainRepl(args)
  }
}
