package tapl

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.{ImplicitConversions, PackratParsers}

// generic component for REPL
trait REPL extends Common {
  trait Command
  case class TypeOf(in: String) extends Command
  case class Compile(cf: CompileForm) extends Command
  case object Browse extends Command
  case object Quit extends Command
  case object Help extends Command
  case object Noop extends Command

  trait CompileForm
  case class CompileInteractive(s: String) extends CompileForm
  case class CompileFile(f: String) extends CompileForm

  case class Cmd(cs: List[String], argDesc: String, f: String => Command, info: String)
  type Ctx[Inf] = List[(Name, Inf)]

  case class State[V, Inf](interactive: Boolean, outFile: String, ne: NameEnv[V], ctx: Ctx[Inf])

  trait Interpreter[I, C, V, T, TInf, Inf] extends StandardTokenParsers with PackratParsers {
    val iname: String
    val iprompt: String
    def iitype(ne: NameEnv[V], ctx: Ctx[Inf], i: I): Result[T]
    def iquote(v: V): C
    def ieval(ne: NameEnv[V], i: I): V
    def ihastype(t: T): Inf
    def icprint(c: C): String
    def itprint(t: T): String
    val iiparse: PackratParser[I]
    val isparse: PackratParser[Stmt[I, TInf]]
    def iassume(s: State[V, Inf], x: (String, TInf)): State[V, Inf]

    def parseIO[A](p: Parser[A], in: String): Option[A] = phrase(p)(new lexical.Scanner(in)) match {
      case t if t.successful =>
        Some(t.get)
      case t              =>
        Console.println(s"cannot parse: $t")
        None
    }

    def iinfer(ne: NameEnv[V], ctx: Ctx[Inf], i: I): Option[T] = {
      iitype(ne, ctx, i) match {
        case Right(t) => Some(t)
        case Left(msg) => Console.println(msg); None
      }
    }
  }
  // TODO
  def helpTxt(cs: List[Cmd]): String = ""
  val commands: List[Cmd] =
    List(
      Cmd(List(":type"),      "<expr>", x => TypeOf(x),               "print type of expression"),
      Cmd(List(":browse"),    "",       x => Browse,                  "browse names in scope"),
      Cmd(List(":load"),      "<file>", x => Compile(CompileFile(x)), "load program from file"),
      Cmd(List(":quit"),      "",       x => Quit,                    "exit interpreter"),
      Cmd(List(":help",":?"), "",       x => Help,                    "display this list of commands")
    )

  def interpretCommand(s: String): Command = {
    val in = s.trim.replaceAll(" +", " ")
    if (in.startsWith(":")) {
      val (cmd, t) = in.span(_.isWhitespace)
      commands.filter(_.cs.exists(cmd.startsWith(_))) match {
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

  def handleCommand[I, C, V, T, TInf, Inf](i: Interpreter[I, C, V, T, TInf, Inf], state: State[V, Inf], cmd: Command): State[V, Inf] =
    cmd match {
      case Quit =>
        sys.exit()
      case Noop =>
        state
      case Help =>
        Console.println(helpTxt(commands))
        state
      case Browse =>
        state.ne.map(_._1).distinct.reverse.foreach(Console.println(_))
        state
      case TypeOf(x) =>
        for {
          e <- i.parseIO(i.iiparse, x)
          t <- i.iinfer(state.ne, state.ctx, e)
        } {
          Console.println(i.itprint(t))
        }
        state
      case Compile(CompileInteractive(s)) =>
        i.parseIO(i.isparse, s) match {
          case Some(stm) => handleStmt(i, state, stm)
          case None => state
        }
      case Compile(CompileFile(f)) =>
        val input = scala.io.Source.fromFile(f).mkString("")
        i.parseIO((i.isparse)+, input) match {
          case Some(stmts) =>
             stmts.foldLeft(state){(s, stm) => handleStmt(i, s, stm)}
          case None => state
        }

    }
  def handleStmt[I, C, V, T, TInf, Inf](int: Interpreter[I, C, V, T, TInf, Inf], state: State[V, Inf], stmt: Stmt[I, TInf]): State[V, Inf] = {
    def checkEval(s: String, i: I): State[V, Inf] = {
      int.iinfer(state.ne, state.ctx, i) match {
        case None =>
          state
        case Some(y) =>
          val v = int.ieval(state.ne, i)
          if (s == "it"){
            Console.println(int.icprint(int.iquote(v)) + " :: " + int.itprint(y))
          } else {
            Console.println(s"$s :: ${int.itprint(y)}")
          }
          State(state.interactive, "", (Global(s), v) :: state.ne, (Global(s), int.ihastype(y)) :: state.ctx)
      }
    }
    stmt match {
      case Assume(ass) => ass.foldLeft(state)(int.iassume)
      case Let(x, e) => checkEval(x, e)
      case Eval(e) => checkEval("it", e)
      case PutStrLn(x) => Console.println(x); state
      case Out(f) => state.copy(outFile = f)
    }
  }

  def loop[I, C, V, T, TInf, Inf](int: Interpreter[I, C, V, T, TInf, Inf], state: State[V, Inf]) {
    val in = Console.readLine()
    val cmd = interpretCommand(in)
    val state1 = handleCommand(int, state, cmd)
    loop(int, state1)
  }
}
