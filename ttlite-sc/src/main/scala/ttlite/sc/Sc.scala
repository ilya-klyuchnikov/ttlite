package ttlite.sc

import mrsc.core._
import ttlite.core._

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
      VariantsStep(cases.toList.map { b =>
        b -> Conf(t.term / Map(b.sel -> b.ptr), Context(t.ctx.vals, t.ctx.types ++ b.types))
      })
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

trait ProofResiduator extends BaseResiduator with IdAST {
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

case class SC[I](id1: String, id2: String, e: I) extends Stmt[I]
case class MRSC[I](id: String, e: I) extends Stmt[I]

trait ScParser extends MetaParser {
  lexical.delimiters += ","
  lexical.reserved += ("sc", "mrsc")
  override def stmts = List(mrscStmt, scStmt) ++ super.stmts
  lazy val scStmt: PackratParser[Stmt[MTerm]] =
    ("(" ~> ident <~ ",") ~ ident ~ (")" ~ "=" ~ "sc" ~> term <~ ";") ^^ {
      case id1 ~ id2 ~ t => SC(id1, id2, t(Nil))
    }

  lazy val mrscStmt: PackratParser[Stmt[MTerm]] =
     ident ~ ("=" ~ "mrsc" ~> term <~ ";") ^^ {
      case id ~ t => MRSC(id, t(Nil))
    }
}

object ScParser extends ScParser

trait ScREPL extends TTSc with BaseResiduator with ProofResiduator with GraphPrettyPrinter2 { self: NatAST =>
  override val parser = ScParser
  override def handleStmt(state: Context[V], stmt: Stmt[MTerm]): Context[V] = stmt match {
    case SC(scId, proofId, mTerm) =>
      val inputTerm = fromM(mTerm)
      iinfer(state, inputTerm) match {
        case None =>
          handleError("")
          state
        case Some(inTpVal) =>
          // start configuration is a normalized one!
          // it is a self contained!
          val conf = Conf(iquote(ieval(state, inputTerm)), state)
          val sGraph = GraphGenerator(SingleRules, conf).toList.head
          val tGraph = Transformations.transpose(sGraph)

          //output(tgToString(tGraph))
          val resVal = ieval(state, iquote(residuate(tGraph, state.vals)))
          val resTerm = iquote(resVal)
          val inType = iquote(inTpVal)

          val resTermAnn = Ann(resTerm, inType)
          iinfer(state, resTermAnn) match {
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
              val rawAnnProofTerm = Ann(rawProofTerm, Id(inType, inputTerm, resTerm))

              val proofVal = ieval(state, iquote(rawProofVal))
              val proofTerm = iquote(ieval(state, iquote(proofVal)))
              // to check that it really built correctly
              val annProofTerm = Ann(proofTerm, Id(inType, inputTerm, resTerm))
              val proofTypeVal = iinfer(state, annProofTerm)
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
                state.vals +
                  (Global(scId) -> resVal) +
                  (Global(proofId) -> proofVal) +
                  (Global(s"${proofId}_raw") -> proofVal),
                state.types +
                  (Global(scId) -> inTpVal) +
                  (Global(proofId) -> proofTypeVal.get)
              )
          }
      }
    case MRSC(res, mTerm) =>
      val inputTerm = fromM(mTerm)
      iinfer(state, inputTerm) match {
        case None =>
          handleError("")
          state
        case Some(inTpVal) =>
          // start configuration is a normalized one!
          // it is a self contained!
          val conf = Conf(iquote(ieval(state, inputTerm)), state)
          val sGraphs = GraphGenerator(MultiRules, conf).toList
          val tGraphs = sGraphs.map(Transformations.transpose)

          var s = state
          var i = 0

          for (tGraph <- tGraphs) {
            i += 1
            //output(tgToString(tGraph))
            val resVal = ieval(state, iquote(residuate(tGraph, state.vals)))
            val resTerm = iquote(resVal)
            val inType = iquote(inTpVal)

            val resTermAnn = Ann(resTerm, inType)
            iinfer(state, resTermAnn) match {
              case None =>
                handleError("")
                state
              case Some(t3) =>
                output(s"res #$i")
                output(icprint(resTerm) + " :: " + icprint(iquote(t3)) + ";")
                // this place is a bit unsafe:
                // we normalize a proof without first type-checking it
                // this is why we can use combinators cong1, cong2, ... as generic combinators -
                // that are applicable for *any* type, not only for small types (Set0).
                val rawProofVal = proofResiduate(tGraph, state.vals)
                val rawProofTerm = iquote(rawProofVal)
                val rawAnnProofTerm = Ann(rawProofTerm, Id(inType, inputTerm, resTerm))

                val proofVal = ieval(state, iquote(rawProofVal))
                val proofTerm = iquote(ieval(state, iquote(proofVal)))
                // to check that it really built correctly
                val annProofTerm = Ann(proofTerm, Id(inType, inputTerm, resTerm))
                val proofTypeVal = iinfer(state, annProofTerm)
                //output("raw proof:")
                //output(icprint(rawProofTerm))
                //output(s"proof #$i:")
                //output(icprint(proofTerm))

                // in general, this line will fail
                //iinfer(state.ne, state.ctx, rawAnnProofTerm).get

                //output("expected type:")
                //output(icprint(Eq(cType, it, cTerm)))
                output("::")
                output(icprint(iquote(proofTypeVal.get)))
                s = Context(
                  s.vals +
                    (Global(s"${res}_${i}") -> resVal) +
                    (Global(s"${res}_${i}_proof") -> proofVal),
                  s.types +
                    (Global(s"${res}_${i}") ->  inTpVal) +
                    (Global(s"${res}_${i}_proof") -> proofTypeVal.get)
                )
            }
          }
          s = Context(
            s.vals + (Global(s"${res}_count") -> intToVNat(i)),
            s.types + (Global(s"${res}_count") ->  VNat)
          )
          s
      }
    case _ =>
      super.handleStmt(state, stmt)
  }

  def intToVNat(i: Int): Value =
    (1 to i).foldLeft(VZero: Value){(v: Value, _: Int) => VSucc(v)}

  object SingleRules extends BaseRules with SingleDriving with Folding with Termination with NoRebuildings {
    val maxDepth = 10
  }

  object MultiRules extends BaseRules with MultiDriving with Folding with Termination with NoRebuildings {
    val maxDepth = 20
  }
}

object TTScREPL
  extends ScREPL
  with CoreREPL with CoreDriver with CoreResiduator with CoreProofResiduator
  with FunREPL with FunDriver with FunResiduator with FunProofResiduator
  with DPairREPL with DPairDriver with DPairResiduator with DPairProofResiduator
  with SumREPL with SumDriver with SumResiduator with SumProofResiduator
  with IdREPL with IdDriver with IdResiduator with IdProofResiduator
  with NatREPL with NatDriver with NatResiduator with NatProofResiduator
  with ListREPL with ListDriver with ListResiduator with ListProofResiduator
  with PairREPL with PairDriver with PairResiduator with PairProofResiduator
  with FinREPL with FinDriver with FinResiduator with FinProofResiduator {
  override val name = "TT-SC"
}
