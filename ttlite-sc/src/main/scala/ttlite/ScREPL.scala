package ttlite

import mrsc.core._
import ttlite.common._
import ttlite.core._
import ttlite.sc._

case class ScStmt[I](outId: Id, proofId: Id, e: I) extends Stmt[I]

trait ScParser extends MetaParser {
  lexical.delimiters += ","
  lexical.reserved += "sc"
  override def stmts = List(scStmt) ++ super.stmts
  lazy val scStmt: PackratParser[Stmt[MTerm]] =
    ("(" ~> globalId <~ ",") ~ globalId ~ (")" ~ "=" ~ "sc" ~> term <~ ";") ^^ { case id1 ~ id2 ~ t =>
      ScStmt(id1, id2, t(Nil))
    }
}

object ScParser extends ScParser

trait ScREPL extends CoreREPL with SC with Residuator with ProofResiduator with GraphPrettyPrinter2 {
  self: PiAST with IdAST =>
  import ttlite.common.IoUtil._
  override val parser = ScParser
  override def handleStmt(state: Context[V], stmt: Stmt[MTerm]): Context[V] =
    stmt match {
      case ScStmt(scId, proofId, mTerm) =>
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
      signal.map(n => GraphRewriteStep.FoldStep(n.sPath): S).toList
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
      } else Nil
  }

  object SingleRules extends BaseRules with SingleDriving with Folding with Termination with NoRebuildings {
    val maxDepth = 4
  }
}

class TTScREPL
    extends SC
    with CoreREPL
    with Driver
    with Residuator
    with ProofResiduator
    with PiREPL
    with PiDriver
    with PiResiduator
    with PiProofResiduator
    with SigmaREPL
    with SigmaDriver
    with SigmaResiduator
    with SigmaProofResiduator
    with SumREPL
    with SumDriver
    with SumResiduator
    with SumProofResiduator
    with IdREPL
    with IdDriver
    with IdResiduator
    with IdProofResiduator
    with NatREPL
    with NatDriver
    with NatResiduator
    with NatProofResiduator
    with ListREPL
    with ListDriver
    with ListResiduator
    with ListProofResiduator
    with ProductREPL
    with ProductDriver
    with ProductResiduator
    with ProductProofResiduator
    with EnumREPL
    with EnumDriver
    with EnumResiduator
    with EnumProofResiduator
    with ScREPL {
  override val name = "TT-SC"
}

object TTScREPL {
  def main(args: Array[String]): Unit = {
    new TTScREPL().mainRepl(args)
  }
}
