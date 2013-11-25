package ttlite.common

trait REPL {
  import IoUtil._

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
  // pretty printing of term into Agda
  def tPrintAgda(c: T): String
  def fvs(c : T) : List[Name]
  def assume(s: Context[V], n: String, t: T): Context[V]
  def handleTypedLet(state: Context[V], s: String, t: T, tp: T): Context[V]
  def fromM(m: MTerm): T

  val parser: MetaParser = MetaParser
  val name: String
  // TO OVERRIDE ENDS

  def vPrint(v: V): String = tPrint(iquote(v))
  private var modules: Set[String] = _

  def handleError(tte: TTLiteError): Unit = {
    Console.println(ansi(s"@|bold,red Error in ${tte.location}|@"))
    Console.println(tte.getMessage)
    Console.println()
    Console.println(tte.details)

    //tte.printStackTrace()
  }

  def handleGeneralError(t : Throwable): Unit = {
    Console.println(ansi(s"@|bold,red Error:|@"))
    Console.println(t.getMessage)
  }


  def output(x: => Any): Unit =
    if (!batch) Console.println(s"$x")

  def iinfer(ctx: Context[V], i: T): V =
    itype(ctx, i)

  def handleStmt(state: Context[V], stmt: Stmt[MTerm]): Context[V] =
    stmt match {
      case Quit =>
        throw TTLiteExit
      case Assume(n, mt) =>
        try {
          assume(state, n, fromM(mt))
        } catch {
          case t : TypeError => throw t.setMTerm(mt)
        }
      case Let(x, mt) =>
        val e = fromM(mt)
        try {
          handleLet(state, x, e)
        } catch {
          case t : TypeError => throw t.setMTerm(mt)
        }
      case TypedLet(x, mt1, mt2) =>
        val e = fromM(mt1)
        val tp = fromM(mt2)
        try {
          handleTypedLet(state, x, e, tp)
        } catch {
          case t : TypeError => throw t.setMTerm(MAnn(mt1, mt2))
        }
      case Eval(mt) =>
        val e = fromM(mt)
        try {
          handleLet(state, "it", e)
        } catch {
          case t : TypeError => throw t.setMTerm(mt)
        }
      case Import(f) =>
        loadModule(f, state, reload = false)
      case Reload(f) =>
        loadModule(f, state, reload = true)
      case ExportToAgda(f) =>
        exportToAgda(f, state)
        state
    }

  private def exportToAgda(f : String, state : Context[V]) {
    import java.io.{File, FileWriter}

    val agdaFile = new File(s"agda/${f}.agda")
    new File(s"agda/${f}.agdai").delete()

    agdaFile.getParentFile.mkdirs()
    agdaFile.createNewFile()

    val out = new FileWriter(agdaFile)

    out.write(s"module ${f} where\n")
    out.write(s"open import ttlite\n")

    val assumed = state.ids.reverse

    if (assumed.nonEmpty) {
      out.write("\npostulate\n")
      for {id <- assumed } {
        val tp = iquote(state.types(id))
        out.write(s"  ${id} : ${tPrintAgda(tp)}\n")
      }
    }

    // TODO: hack - remove
    for (id <- state.vals.keys.filterNot(n => List("pair", "cons", "nil", "_").contains(n.toString))) {
      val v = iquote(state.vals(id))
      val tp = iquote(state.types(id))

      out.write(s"\n${id} : ${tPrintAgda(tp)}\n")
      out.write(s"${id} = ${tPrintAgda(v)}\n")
    }

    out.close()
  }

  def handleLet(state: Context[V], s: String, it: T): Context[V] = {
    val tp = iinfer(state, it)
    val v = ieval(state, it)
    if (s == "it"){
      output(tPrint(iquote(v)) + "\n:\n" + vPrint(tp) + ";")
    } else {
      output(s"$s\n:\n${vPrint(tp)};")
    }
    Context(state.vals + (Global(s) -> v),  state.types + (Global(s) -> tp), state.ids)
  }

  private def loadModule(f: String, state: Context[V], reload: Boolean): Context[V] =
    if (modules(f) && !reload)
      return state
    else
      try {
        val input = scala.io.Source.fromFile(f).mkString
        val stmts = parser.parseIO(parser.stmt+, input)
        val s1 = stmts.foldLeft(state){(s, stm) => handleStmt(s, stm)}
        modules = modules + f
        s1
      } catch {
        case ttError : TTLiteError => throw ttError.setFile(f)
      }

  def loop(state : Context[V], console : org.kiama.util.Console) : Unit = {
    val st1 = try {
      step(state, console)
    } catch {
      case TTLiteExit =>
        sys.exit()
      case t : TTLiteError =>
        handleError(t)
        state
      case t : Throwable =>
        handleGeneralError(t)
        state
    }
    loop(st1, console)
  }

  private def loadModuleI(f: String, state: Context[V]): Context[V] = {
    try {
      loadModule(f, state, reload = false)
    } catch {
      case TTLiteExit =>
        sys.exit()
      case t : TTLiteError =>
        handleError(t)
        state
      case t : Throwable =>
        handleGeneralError(t)
        state
    }
  }

  def step(state: Context[V], console : org.kiama.util.Console): Context[V] = {
    val in = console.readLine(ansi(s"@|bold $name> |@"))
    try {
      val stm = parser.parseIO(parser.stmt, in)
      handleStmt(state, stm)
    } catch {
      case ttError : TTLiteError => throw ttError.setFile("repl input")
    }
  }

  def main(args: Array[String]) {
    import org.fusesource.jansi.AnsiConsole
    AnsiConsole.systemInstall()

    var state = Context[V](Map(), Map(), Nil)
    modules = Set()
    args match {
      case Array() =>
        loop(state, org.kiama.util.JLineConsole)
      case Array("-i", f) =>
        state = loadModuleI(f, state)
        loop(state, org.kiama.util.JLineConsole)
      case Array("-t", f) =>
        state = loadModuleI(f, state)
      case _ =>
        batch = true
        args.foreach { f =>
          state = loadModule(f, state, reload = false)
        }
    }
  }
}