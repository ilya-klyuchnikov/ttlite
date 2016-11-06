package ttlite.common

import scala.language.postfixOps

trait REPL {
  import IoUtil._

  /** The type of terms */
  type T

  /** The type of values */
  type V

  /** Infers a type for a term. */
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
   */
  def quote(value: V): T

  def translate(shallowTerm: MTerm): T

  /** Pretty printing of terms into a concrete syntax. */
  def pretty(term: T): String

  /** Pretty printing of terms into Agda syntax */
  def prettyAgda(term: T): String

  /** Pretty printing of terms into Coq syntax */
  def prettyCoq(term: T): String

  /** Pretty printing of terms into Idris syntax */
  def prettyIdris(term: T): String

  /**
   * Extends a context with an assumption
   */
  def assume(ctx: Context[V], id: Id, term: T): Context[V]

  // if batch, we do not output info into console.
  private var batch: Boolean = false
  // in verbose mode we output stack traces of errors
  protected var verbose: Boolean = false
  val prompt: String

  val parser: MetaParser = MetaParser
  val name: String

  def vPrint(v: V): String = pretty(quote(v))
  private var modules: Set[String] = _

  def handleError(tte: TTLiteError): Unit = {
    Console.println(ansi(s"@|bold,red ${tte.errorKind} error in ${tte.location}|@"))
    Console.println(tte.getMessage)
    Console.println()
    Console.println(tte.details)
    if  (verbose) {
      tte.printStackTrace()
    }
  }

  // we assume that it is input/output error
  def handleGeneralError(t : Throwable): Unit = {
    Console.println(ansi(s"@|bold,red IO error:|@"))
    Console.println(t.getMessage)
    if (verbose) {
      t.printStackTrace()
    }
  }

  def output(x: => Any): Unit =
    if (!batch) Console.println(s"$x")

  var res = 0

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
        val mtAnn = MAnn(mt1, mt2)
        val e = translate(mtAnn)
        try {
          handleLet(state, x, e)
        } catch {
          case t : TypeError => throw t.withMTerm(mtAnn)
        }
      case Eval(mt) =>
        val e = translate(mt)
        try {
          res += 1
          handleLet(state, Id(s"res_${res}"), e)
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
      case ExportToCoq(f) =>
        exportToCoq(f, state)
        state
      case ExportToIdris(f) =>
        exportToIdris(f, state)
        state
    }

  private def exportToAgda(f : String, state : Context[V]) {
    import java.io.{File, FileWriter}

    val agdaFile = new File(s"generated/${f}.agda")
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

  private def exportToCoq(f : String, state : Context[V]) {
    import java.io.{File, FileWriter}

    val coqFile = new File(s"generated/${f}.v")

    coqFile.getParentFile.mkdirs()
    coqFile.createNewFile()

    val out = new FileWriter(coqFile)

    out.write(s"""Add LoadPath "syntax".\n""")
    out.write(s"Load ttlite.\n\n")

    val assumed = state.ids.filter(_.isInstanceOf[Assumed])
    for {Assumed(id) <- assumed} {
      val tp = quote(state.types(Assumed(id)))
      out.write(s"Parameter ${id.replace("$", "")}__ : ${prettyCoq(tp)}.\n")
    }

    def internalName(n : Name): Boolean = List("pair", "cons", "nil", "_").contains(n.toString)
    def globalName(n : Name): Boolean = n.isInstanceOf[Global]

    for (id <- state.ids.filterNot(internalName).filter(globalName)) {
      val id1 = if (id.toString == "if") "if__" else id.toString
      val v = quote(state.vals(id))
      val tp = quote(state.types(id))
      out.write(s"Definition $id1 : ${prettyCoq(tp)} := ${prettyCoq(v)}.\n")
    }

    out.close()
  }

  private def exportToIdris(f : String, state : Context[V]) {
    import java.io.{File, FileWriter}

    val idrisFile = new File(s"generated/${f}.idr")
    new File(s"idr/${f}.ibc").delete()

    idrisFile.getParentFile.mkdirs()
    idrisFile.createNewFile()

    val out = new FileWriter(idrisFile)

    out.write(s"module ${f}\n\n")
    out.write(s"import ttlite\n\n")

    val assumed = state.ids.filter(_.isInstanceOf[Assumed])
    for {Assumed(id) <- assumed} {
      val tp = quote(state.types(Assumed(id)))
      out.write(s"${id.replace("$", "")}__ : ${prettyIdris(tp)}\n")
    }

    def internalName(n : Name): Boolean = List("pair", "cons", "nil", "_").contains(n.toString)
    def globalName(n : Name): Boolean = n.isInstanceOf[Global]

    for (id <- state.ids.filterNot(internalName).filter(globalName)) {
      val v = quote(state.vals(id))
      val tp = quote(state.types(id))

      out.write(s"\n${id} : ${prettyIdris(tp)}\n")
      out.write(s"${id} = ${prettyIdris(v)}\n")
    }

    out.close()
  }

  def handleLet(state: Context[V], id: Id, it: T): Context[V] = {
    val name = Global(id.n)
    if (state.ids.contains(name)) {
      throw DuplicateIdError(id)
    }
    val tp = infer(state, it)
    val v = eval(state, it)

    output(ansi(s"@|bold ${id.n}|@ : ${vPrint(tp)};"))
    output(ansi(s"@|bold ${id.n}|@ = ${vPrint(v)};\n"))

    state.addVal(name, v, tp)
  }

  private def loadModule(f: String, state: Context[V], reload: Boolean): Context[V] = {
    if (reload) {
      modules = Set()
    }
    val state1 = if (reload) Context.empty[V] else state
    if (modules(f))
      return state1
    try {
      val input = scala.io.Source.fromFile(f).mkString
      val stmts = parser.parseIO(parser.stmt+, input)
      val s1 = stmts.foldLeft(state1){(s, stm) => handleStmt(s, stm)}
      modules = modules + f
      s1
    } catch {
      case ttError : TTLiteError => throw ttError.withFile(f)
    }
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
    org.kiama.util.JLineConsole.reader.addCompleter(new ImportCompleter())

    var state = Context.empty[V]
    modules = Set()
    try {
      args match {
        case Array() =>
          loop(state, org.kiama.util.JLineConsole)
        case Array("-v") =>
          verbose = true
          loop(state, org.kiama.util.JLineConsole)
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
