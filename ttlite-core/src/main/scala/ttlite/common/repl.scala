package ttlite.common

trait REPL {
  import IoUtil._

  /**
   * The type of terms.
   */
  type T
  /**
   * The type of values
   */
  type V

  /**
   * Infers a type for a term.
   *
   * @param ctx a context
   * @param term a term
   * @return a type of a term `term` in the context `ctx`. A type is a value (`V`)
   */
  def infer(ctx: Context[V], term: T): V

  /**
   * Evaluates (= normalizes) a given term in the context.
   * In a sense, this is reification. (AST => Value)
   *
   * @param ctx a context
   * @param term a term
   * @return a value of this term
   */
  def eval(ctx: Context[V], term: T): V

  /**
   * Quotes given value.
   * In a sense, this is reflection. (Value => AST)
   *
   * @param value value
   * @return a corresponding term
   */
  def quote(value: V): T

  /**
   * Translates a term from shallow syntax into an abstract syntax.
   *
   * @param shallowTerm
   * @return
   */
  def translate(shallowTerm: MTerm): T

  /**
   * Pretty printing of terms into a concrete syntax.
   *
   * @param term
   * @return
   */
  def pretty(term: T): String

  /**
   * Pretty printing of terms into Agda syntax
   *
   * @param term
   * @return
   */
  def prettyAgda(term: T): String

  /**
   * Extends a context with an assumption
   *
   * @param ctx context
   * @param id id of a term
   * @param term term
   * @return
   */
  def assume(ctx: Context[V], id: String, term: T): Context[V]

  def handleTypedLet(state: Context[V], s: String, t: T, tp: T): Context[V]

  // if batch, we do not output info into console.
  private var batch: Boolean = false
  val prompt: String

  val parser: MetaParser = MetaParser
  val name: String
  // TO OVERRIDE ENDS

  def vPrint(v: V): String = pretty(quote(v))
  private var modules: Set[String] = _


  def handleError(tte: TTLiteError): Unit = {
    Console.println(ansi(s"@|bold,red ${tte.errorKind} error in ${tte.location}|@"))
    Console.println(tte.getMessage)
    Console.println()
    Console.println(tte.details)
  }

  // we assume that it is input/output error
  def handleGeneralError(t : Throwable): Unit = {
    Console.println(ansi(s"@|bold,red IO error:|@"))
    Console.println(t.getMessage)
  }

  def output(x: => Any): Unit =
    if (!batch) Console.println(s"$x")

  def handleStmt(state: Context[V], stmt: Stmt[MTerm]): Context[V] =
    stmt match {
      case Quit =>
        throw TTLiteExit
      case Assume(n, mt) =>
        try {
          assume(state, n, translate(mt))
        } catch {
          case t : TypeError => throw t.withMTerm(mt)
        }
      case Let(x, mt) =>
        val e = translate(mt)
        try {
          handleLet(state, x, e)
        } catch {
          case t : TypeError => throw t.withMTerm(mt)
        }
      case TypedLet(x, mt1, mt2) =>
        val e = translate(mt1)
        val tp = translate(mt2)
        try {
          handleTypedLet(state, x, e, tp)
        } catch {
          case t : TypeError => throw t.withMTerm(MAnn(mt1, mt2))
        }
      case Eval(mt) =>
        val e = translate(mt)
        try {
          handleLet(state, "it", e)
        } catch {
          case t : TypeError => throw t.withMTerm(mt)
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

    out.write(s"open import ttlite\n\n")
    out.write(s"module ${f}")

    val assumed = state.ids.filter(_.isInstanceOf[Assumed])
    for {id <- assumed} {
      val tp = quote(state.types(id))
      out.write(s" (${id} : ${prettyAgda(tp)})")
    }
    out.write(s" where\n")

    def internalName(n : Name): Boolean = List("pair", "cons", "nil", "_").contains(n.toString)
    def globalName(n : Name): Boolean = n.isInstanceOf[Global]

    for (id <- state.ids.filterNot(internalName).filter(globalName)) {
      val v = quote(state.vals(id))
      val tp = quote(state.types(id))

      out.write(s"\n${id} : ${prettyAgda(tp)}\n")
      out.write(s"${id} = ${prettyAgda(v)}\n")
    }

    out.close()
  }

  def handleLet(state: Context[V], s: String, it: T): Context[V] = {
    val tp = infer(state, it)
    val v = eval(state, it)
    if (s == "it"){
      output(pretty(quote(v)) + "\n:\n" + vPrint(tp) + ";")
    } else {
      output(s"$s\n:\n${vPrint(tp)};")
    }
    state.addVal(Global(s), v, tp)
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
        case ttError : TTLiteError => throw ttError.withFile(f)
      }

  def loop(state : Context[V], console : org.kiama.util.Console) : Unit = {
    val st1 = try {
      step(state, console)
    } catch {
      case TTLiteExit =>
        throw TTLiteExit
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
        throw TTLiteExit
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
      case ttError : TTLiteError => throw ttError.withFile("repl input")
    }
  }

  def main(args: Array[String]) {
    org.fusesource.jansi.AnsiConsole.systemInstall()
    org.kiama.util.JLineConsole.reader.addCompletor(new jline.FileNameCompletor())

    var state = Context.empty[V]
    modules = Set()
    try {
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
    } catch {
      case TTLiteExit =>
        Console.println("Bye")
    }
  }
}
