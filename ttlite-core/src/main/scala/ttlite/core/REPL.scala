package ttlite.core

trait REPL {

  // TO OVERRIDE STARTS
  type T // term
  type V // value (normalized term)

  // if batch, we do not output info into console.
  private var batch: Boolean = false
  val prompt: String
  def itype(ctx: Context[V], i: T): V
  def iquote(v: V): T
  def ieval(ctx: Context[V], i: T): V
  // pretty printing of terms
  def tPrint(c: T): String
  def assume(s: Context[V], n: String, t: T): Context[V]
  def handleTypedLet(state: Context[V], s: String, t: T, tp: T): Context[V]
  def fromM(m: MTerm): T

  val parser: MetaParser = MetaParser
  val name: String
  // TO OVERRIDE ENDS

  def vPrint(v: V): String = tPrint(iquote(v))
  private var modules: Set[String] = _

  def handleError(msg: String): Unit =
    if (batch) throw new Exception(msg)

  def output(x: => Any): Unit =
    if (!batch) Console.println(s"$x")

  def iinfer(ctx: Context[V], i: T): V =
    itype(ctx, i)

  def handleStmt(state: Context[V], stmt: Stmt[MTerm]): Context[V] =
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

  def handleLet(state: Context[V], s: String, it: T): Context[V] = {
    val tp = iinfer(state, it)
    val v = ieval(state, it)
    if (s == "it"){
      output(tPrint(iquote(v)) + "\n:\n" + vPrint(tp) + ";")
    } else {
      output(s"$s\n:\n${vPrint(tp)};")
    }
    Context(state.vals + (Global(s) -> v),  state.types + (Global(s) -> tp))
  }

  private def loadModule(f: String, state: Context[V], reload: Boolean): Context[V] =
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
        case ttError : TTLiteError =>
          throw ttError.setFile(f)
      }

  def loop(state: Context[V]) {
    import org.kiama.util.JLineConsole
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
    var state = Context[V](Map(), Map())
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
  with DPairREPL
  with NatREPL
  with VectorREPL
  with IdREPL
  with FinREPL
  with ListREPL
  with PairREPL
  with SumREPL
  with WREPL {
  override val name = "TT"
}

