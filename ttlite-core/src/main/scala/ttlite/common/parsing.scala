package ttlite.common

import scala.language.postfixOps

import scala.collection.mutable.ArrayBuffer
import scala.util.parsing.input._
import scala.util.parsing.combinator._

/** RichPositional stores information about start/end positions of a term
  * in the input.
  *
  * Usage scenario: mix this trait into a class of your AST.
  * When you get a result of parsing, call `setPs(startPos, endPos)`.
  *
  * The usage of this trait implies late binding.
  */
trait RichPositional {
  var startPos: Position = NoPosition
  var endPos: Position = NoPosition
  def setPs(start: Position, end: Position): this.type = {
    startPos = start
    endPos = end
    this
  }

  lazy val source: java.lang.CharSequence =
    startPos.asInstanceOf[OffsetPosition].source

  // TODO: can we wrap a CharSequence (LinedInput)? Then this index may be calculated once.
  /** An index that contains all line starts, including first line, and eof. */
  private lazy val index: Array[Int] = {
    var lineStarts = new ArrayBuffer[Int]
    lineStarts += 0
    for (i <- 0 until source.length)
      if (source.charAt(i) == '\n') lineStarts += (i + 1)
    lineStarts += source.length
    lineStarts.toArray
  }

  /** Returns a piece of the input text that directly corresponds to this term.
    */
  def lines: String =
    source.subSequence(index(startPos.line - 1), index(endPos.line)).toString

  /** Returns lines of the input texts where this term spans.
    */
  def origin: String =
    source
      .subSequence(index(startPos.line - 1) + startPos.column - 1, index(endPos.line - 1) + endPos.column - 1)
      .toString

  /** Returns a part of the first line of the fragment BEFORE this term.
    */
  def originPrefix: String =
    source
      .subSequence(
        index(startPos.line - 1),
        index(startPos.line - 1) + startPos.column - 1,
      )
      .toString

  /** Returns a part of the last line of the fragment AFTER this term.
    */
  def originSuffix: String =
    source
      .subSequence(
        index(endPos.line - 1) + endPos.column - 1,
        index(endPos.line),
      )
      .toString
}

/** Lexer that parser haskell-like language.
  * Differences from `StdLexical`:
  * 1) Haskell comments (`--` and `{-`/`-}`)
  * 2) Identifier may contain extra characters:
  *    `$` - used for assumed variables
  *    `/` - used in hack for import (to have nice syntax coloring of import statements on github)
  *    `'` - widely used in Haskell for names of auxiliary functions/variables
  *    `\` - for lambda
  */
class MetaLexical extends lexical.StdLexical {
  import scala.util.parsing.input.CharArrayReader._
  override final lazy val whitespace: Parser[Any] = rep(
    whitespaceChar
      | '{' ~ '-' ~ comment
      | '-' ~ '-' ~ rep(chrExcept(EofCh, '\n'))
      | '{' ~ '-' ~ failure("unclosed comment")
  )
  override final lazy val comment: Parser[Any] = (
    '-' ~ '}' ^^ { _ => ' ' }
      | chrExcept(EofCh) ~ comment
  )
  override final lazy val identChar: Parser[Char] =
    super.identChar | elem('$') | elem('/') | elem('\'') | elem('\\')
}

// TODO: it seems to be logical to separate this into 2 traits: MetaTermParser + StmtParser
// MetaTermParser is fixed, but StmtParser is customizable
/** Parser of "concrete shallow-terms". See documentation for the syntax of "shallow-language".
  * Entry points are `parseStatements` and `parseMTerm`
  */
trait MetaParser extends syntactical.StandardTokenParsers with PackratParsers with ImplicitConversions {

  def parseStatements(in: String): List[Stmt[MTerm]] =
    parseIO(stmt +, in)
  def parseStatement(in: String): Stmt[MTerm] =
    parseIO(stmt, in)
  def parseMTerm(in: String): MTerm =
    parseIO(term, in)(Nil)

  // Setting up lexer
  override val lexical = new MetaLexical
  lexical.reserved ++=
    Seq("assume", "let", "import", "sc", "sc2", "quit", "reload", "exportToAgda", "exportToCoq", "exportToIdris")
  lexical.delimiters ++=
    Seq("(", ")", ":", ".", "=", "->", ";")
  // Ctx is a sequence of named binders. In the spirit of TAPL implementation.
  private type Ctx = List[String]
  private type Res = Ctx => MTerm
  // PosRes propagates positional information to the final result
  case class RichPosRes(res: Ctx => MTerm) extends (Ctx => MTerm) with RichPositional {
    override def apply(c: Ctx): MTerm = res(c).setPs(startPos, endPos)
  }
  // Parser combinator which enriches/updates the result of a parser `p` with positional information
  // Caveat: it works up to whitespaces/comments
  private def pos[T <: RichPositional](p: => Parser[T]): Parser[T] =
    Parser { in1 =>
      p(in1) match {
        case Success(t, in2) => Success(t.setPs(in1.pos, in2.pos), in2)
        case r               => r
      }
    }
  private case class Arg(name: String, tp: RichPosRes) extends RichPositional

  lazy val term: PackratParser[RichPosRes] = bind | app
  private lazy val aTerm: PackratParser[RichPosRes] =
    pos(mVar | "(" ~> term <~ ")")
  private lazy val mVar: PackratParser[RichPosRes] =
    pos(ident ^^ { i =>
      RichPosRes { ctx: Ctx =>
        ctx.indexOf(i) match {
          case -1 => MVar(s2name(i))
          case j  => MVar(Quote(j))
        }
      }
    })
  private lazy val app: PackratParser[RichPosRes] =
    pos((aTerm +) ^^ { ts => RichPosRes { ctx: Ctx => ts.map { _(ctx) }.reduce(_ ~ _) } })

  private lazy val bind: PackratParser[RichPosRes] =
    pos(ident ~ (arg +) ~ (("." | "->") ~> term) ^^ { case id ~ args ~ body =>
      RichPosRes { ctx: Ctx =>
        def mkBind(args: List[Arg], c: Ctx): MTerm =
          args match {
            case Nil => body(c)
            case x :: xs =>
              val bind = MBind(id, x.tp(c), mkBind(xs, x.name :: c))
              bind.setPs(x.startPos, body.endPos)
              bind
          }
        mkBind(args, ctx)
      }
    })

  private val arg: PackratParser[Arg] =
    pos("(" ~> (ident ~ (":" ~> term)) <~ ")" ^^ { case i ~ x => Arg(i, x) })

  private lazy val stmt: PackratParser[Stmt[MTerm]] = stmts.reduce(_ | _)
  def stmts =
    List(
      quitStmt,
      assumeStmt,
      typedLetStmt,
      letStmt,
      importStmt,
      reloadStmt,
      exportToAgdaStmt,
      exportToCoqStmt,
      exportToIdrisStmt,
      evalStmt,
    )

  private lazy val letStmt: PackratParser[Stmt[MTerm]] =
    globalId ~ ("=" ~> term <~ ";") ^^ { case x ~ y => Let(x, y(Nil)) }
  private lazy val typedLetStmt: PackratParser[Stmt[MTerm]] =
    (globalId ~ (":" ~> term) <~ ";") >> { case id ~ tp =>
      (ident ^? ({ case n if n == id.n => id }, _ => s"definition of ${id.n} expected")) ~ ("=" ~> term <~ ";") ^^ {
        case x ~ y => TypedLet(x, y(Nil), tp(Nil))
      }
    }
  private lazy val assumeStmt: PackratParser[Stmt[MTerm]] =
    (assumedId ~ (":" ~> term) <~ ";") ^^ { case x ~ y => Assume(x, y(Nil)) }
  private lazy val importStmt: PackratParser[Stmt[MTerm]] =
    "import" ~> (stringLit | ident ^^ { x => s"$x.hs" }) <~ ";" ^^ Import
  private lazy val exportToAgdaStmt: PackratParser[Stmt[MTerm]] =
    "exportToAgda" ~> ident <~ ";" ^^ ExportToAgda
  private lazy val exportToCoqStmt: PackratParser[Stmt[MTerm]] =
    "exportToCoq" ~> ident <~ ";" ^^ ExportToCoq
  private lazy val exportToIdrisStmt: PackratParser[Stmt[MTerm]] =
    "exportToIdris" ~> ident <~ ";" ^^ ExportToIdris
  private lazy val reloadStmt: PackratParser[Stmt[MTerm]] =
    "reload" ~> (stringLit | ident ^^ { x => s"$x.hs" }) <~ ";" ^^ Reload
  private lazy val evalStmt: PackratParser[Stmt[MTerm]] =
    term <~ ";" ^^ { t => EvalStmt(t(Nil)) }
  private lazy val quitStmt: PackratParser[Stmt[MTerm]] =
    "quit" <~ ";" ^^ { t => Quit }

  private def assumedId: PackratParser[Id] =
    pos(ident ^? { case id if id.startsWith("$") => Id(id) })
  def globalId: PackratParser[Id] =
    pos(ident ^? { case id if !id.startsWith("$") => Id(id) })
  def s2name(s: String): Name =
    if (s.startsWith("$")) Assumed(s) else Global(s)

  def parseIO[A](p: Parser[A], in: String): A =
    phrase(p)(new lexical.Scanner(in)) match {
      case Success(res, _) => res
      case Failure(msg, next) =>
        throw ParsingError(msg, next.pos.line, next.pos.column, next.pos.longString)
      case Error(msg, next) =>
        throw ParsingError(msg, next.pos.line, next.pos.column, next.pos.longString)
    }
}

object MetaParser extends MetaParser
