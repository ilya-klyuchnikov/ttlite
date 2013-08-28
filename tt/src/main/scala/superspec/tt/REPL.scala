package superspec.tt

import org.kiama.util.JLineConsole

trait REPL {

  // TO OVERRIDE STARTS
  type T // term
  type V // value
  type Result[A] = Either[String, A]

  private var batch: Boolean = false
  val prompt: String
  def itype(ne: NameEnv[V], ctx: NameEnv[V], i: T): Result[V]
  def iquote(v: V): T
  def ieval(ne: NameEnv[V], i: T): V
  def icprint(c: T): String
  def itprint(t: V): String
  def assume(s: Context, n: String, t: T): Context
  def handleTypedLet(state: Context, s: String, t: T, tp: T): Context
  def fromM(m: MTerm): T
  val parser: MetaParser = MetaParser
  val name: String
  // TO OVERRIDE ENDS

  private var modules: Set[String] = _

  case class Context(vals: NameEnv[V], types: NameEnv[V])

  def handleError(msg: String): Unit =
    if (batch) throw new Exception(msg)

  def output(x: Any): Unit =
    if (!batch) Console.println(s"$x\n")

  def iinfer(ne: NameEnv[V], ctx: NameEnv[V], i: T): Option[V] =
    itype(ne, ctx, i) match {
      case Right(t) =>
        Some(t)
      case Left(msg) =>
        Console.println(msg)
        None
    }

  def handleStmt(state: Context, stmt: Stmt[MTerm]): Context =
    stmt match {
      case Quit =>
        sys.exit()
      case Assume(n, i) =>
        assume(state, n, fromM(i))
      case Let(x, e) =>
        val e1 = fromM(e)
        handleLet(state, x, e1)
      case TypedLet(x, e, tp) =>
        val e1 = fromM(e)
        val tp1 = fromM(tp)
        handleTypedLet(state, x, e1, tp1)
      case Eval(e) =>
        val e1 = fromM(e)
        handleLet(state, "it", e1)
      case Import(f) =>
        loadModule(f, state, reload = false)
      case Reload(f) =>
        loadModule(f, state, reload = true)
    }

  def handleLet(state: Context, s: String, it: T): Context =
    iinfer(state.vals, state.types, it) match {
      case None =>
        handleError(s"Not Inferred type for $it")
        state
      case Some(tp) =>
        val v = ieval(state.vals, it)
        if (s == "it"){
          output(icprint(iquote(v)) + "\n::\n" + itprint(tp) + ";")
        } else {
          output(s"$s\n::\n${itprint(tp)};")
        }
        Context(state.vals + (Global(s) -> v),  state.types + (Global(s) -> tp))
    }

  private def loadModule(f: String, state: Context, reload: Boolean): Context =
    if (modules(f) && !reload)
      return state
    else
      try {
        val input = scala.io.Source.fromFile(f).mkString
        val parsed = parser.parseIO(parser.stmt+, input)
        parsed match {
          case Some(stmts) =>
            val s1 = stmts.foldLeft(state){(s, stm) => handleStmt(s, stm)}
            modules = modules + f
            s1
          case None =>
            handleError("cannot parse")
            state
        }
      } catch {
        case io: java.io.IOException =>
          Console.println(s"Error: ${io.getMessage}")
          handleError("cannot open file")
          state
      }

  def loop(state: Context) {
    val in = JLineConsole.readLine(s"$name> ")
    parser.parseIO(parser.stmt, in) match {
      case Some(stm) =>
        val state1 = handleStmt(state, stm)
        loop(state1)
      case None =>
        loop(state)
    }
  }

  def main(args: Array[String]) {
    var state = Context(Map(), Map())
    modules = Set()
    args match {
      case Array() =>
        loop(state)
      case Array("-i", f) =>
        state = loadModule(f, state, reload = false)
      case _ =>
        batch = true
        args.foreach { f =>
          state = loadModule(f, state, reload = false)
        }
    }
  }

}

object TTREPL
  extends CoreREPL
  with FunREPL
  with DProductREPL
  with NatREPL
  with VectorREPL
  with EqREPL
  with FinREPL
  with ListREPL
  with ProductREPL
  with SumREPL {
  override val name = "TT"
}
