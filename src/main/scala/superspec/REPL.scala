package superspec

import scala.language.postfixOps

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import org.kiama.util.JLineConsole
import scala.util.parsing.combinator.lexical.StdLexical
import scala.util.parsing.input.CharArrayReader._
import scala.util.parsing.combinator.PackratParsers

class HaskellLikeLexical extends StdLexical {
  override def whitespace: Parser[Any] = rep(
    whitespaceChar
      | '/' ~ '*' ~ comment
      | '/' ~ '/' ~ rep( chrExcept(EofCh, '\n') )
      | '-' ~ '-' ~ rep( chrExcept(EofCh, '\n') )
      | '/' ~ '*' ~ failure("unclosed comment")
  )
}

trait Command
case class TypeOf(in: String) extends Command
case class Compile(cf: CompileForm) extends Command
case class Reload(f: String) extends Command
case object Browse extends Command
case object Quit extends Command
case object Help extends Command
case object Noop extends Command

trait CompileForm
case class CompileInteractive(s: String) extends CompileForm
case class CompileFile(f: String) extends CompileForm

case class Cmd(cs: List[String], argDesc: String, f: String => Command, info: String)

trait REPL extends Common {

  type I // inferable term
  type C // checkable term
  type V // value
  type TInf // type info

  val int: Interpreter
  def initialState: State
  private var batch: Boolean = false

  case class State(interactive: Boolean, ne: NameEnv[V], ctx: NameEnv[V], modules: Set[String])

  def handleError() {
    if (batch) {
      throw new Exception
    }
  }

  trait Interpreter extends StandardTokenParsers with PackratParsers {
    override val lexical = new HaskellLikeLexical

    val prompt: String
    def itype(ne: NameEnv[V], ctx: NameEnv[V], i: I): Result[V]
    def iquote(v: V): C
    def ieval(ne: NameEnv[V], i: I): V
    def icprint(c: C): String
    def itprint(t: V): String
    val iParse: Parser[I]
    val stmtParse: Parser[Stmt[I, TInf]]
    def assume(s: State, x: (String, TInf)): State

    def parseIO[A](p: Parser[A], in: String): Option[A] = phrase(p)(new lexical.Scanner(in)) match {
      case t if t.successful =>
        Some(t.get)
      case t              =>
        Console.println(s"cannot parse: $t")
        None
    }

    def iinfer(ne: NameEnv[V], ctx: NameEnv[V], i: I): Option[V] = {
      itype(ne, ctx, i) match {
        case Right(t) =>
          Some(t)
        case Left(msg) =>
          Console.println(msg)
          None
      }
    }
  }
  // TODO
  def helpTxt(cs: List[Cmd]): String = ""
  def commands: List[Cmd] =
    List(
      Cmd(List(":type"),      "<expr>", x => TypeOf(x),               "print type of expression"),
      Cmd(List(":browse"),    "",       x => Browse,                  "browse names in scope"),
      Cmd(List(":load"),      "<file>", x => Compile(CompileFile(x)), "load program from file"),
      Cmd(List(":reload"),    "<file>", x => Reload(x),               "reload program from file"),
      Cmd(List(":quit"),      "",       x => Quit,                    "exit interpreter"),
      Cmd(List(":help",":?"), "",       x => Help,                    "display this list of commands")
    )

  def interpretCommand(s: String): Command = {
    val in = s.trim.replaceAll(" +", " ")
    if (in.startsWith(":")) {
      val (cmd, t) = in.span(!_.isWhitespace)
      commands.filter(_.cs.exists(_.startsWith(cmd))) match {
        case Nil =>
          Console.println(s"Unknown command `$cmd'. Type :? for help.")
          Noop
        case c :: Nil =>
          c.f(t.trim)
        case matching =>
          Console.println(s"Ambiguous command, could be ${matching.map(_.cs.head).mkString(", ")}.")
          Noop
      }
    } else {
      Compile(CompileInteractive(in))
    }
  }

  def handleCommand(state: State, cmd: Command): State =
    cmd match {
      case Quit =>
        sys.exit()
      case Noop =>
        state
      case Help =>
        Console.println(helpTxt(commands))
        state
      case Browse =>
        state.ne.map(_._1).distinct.reverse.foreach{case Global(n) => Console.println(n)}
        state
      case TypeOf(x) =>
        int.parseIO(int.iParse, x) match {
          case Some(e) => int.iinfer(state.ne, state.ctx, e) match {
            case Some(t) =>
              Console.println(s"${int.itprint(t)};")
            case None =>
              handleError()
          }
          case None =>
            handleError()
        }
        state
      case Compile(CompileInteractive(s)) =>
        int.parseIO(int.stmtParse, s) match {
          case Some(stm) => handleStmt(state, stm)
          case None => state
        }
      case Compile(CompileFile(f)) =>
        load(f, state, reload = false)
      case Reload(f) =>
        load(f, state, reload = true)
    }

  private def handleStmt(state: State, stmt: Stmt[I, TInf]): State = {
    def checkEval(s: String, i: I): State = {
      int.iinfer(state.ne, state.ctx, i) match {
        case None =>
          handleError()
          state
        case Some(y) =>
          val v = int.ieval(state.ne, i)
          if (s == "it"){
            Console.println(int.icprint(int.iquote(v)) + " :: " + int.itprint(y) + ";")
          } else {
            Console.println(s"$s :: ${int.itprint(y)};")
          }
          State(state.interactive, (Global(s), v) :: state.ne, (Global(s), y) :: state.ctx, state.modules)
      }
    }
    stmt match {
      case Assume(ass) => ass.foldLeft(state)(int.assume)
      case Let(x, e) => checkEval(x, e)
      case Eval(e) => checkEval("it", e)
      case PutStrLn(x) => Console.println(x); state
      case Import(f) => load(f, state, reload = false)
    }
  }

  private def load(f: String, state: State, reload: Boolean): State = {
    if (state.modules(f) && ! reload) return state
    try {
      val input = scala.io.Source.fromFile(f).mkString("")
      val parsed = int.parseIO(int.stmtParse+, input)
      parsed match {
        case Some(stmts) =>
          val s1 = stmts.foldLeft(state){(s, stm) => handleStmt(s, stm)}
          s1.copy(modules = s1.modules + f)
        case None =>
          handleError()
          state
      }
    } catch {
      case io: java.io.IOException =>
        handleError()
        Console.println(s"Error: ${io.getMessage}")
        state
    }
  }

  var state: State = _

  def loop() {
    val in = JLineConsole.readLine(int.prompt)
    val cmd = interpretCommand(in)
    state = handleCommand(state, cmd)
    loop()
  }

  def init() {
    state = initialState
  }

  def main(args: Array[String]) {
    init()
    args match {
      case Array() =>
        loop()
      case _ =>
        batch = true
        val cmds = args.map(f => Compile(CompileFile(f)))
        for (cmd <- cmds) {
          state = handleCommand(state, cmd)
        }
    }

  }
}
