package ttlite.common

object IoUtil {
  import org.fusesource.jansi._
  def ansi(s : String) : String =
    Ansi.ansi.render(s).toString

  // This is a hack, but allows to detect that Eclipse/Idea consoles are not ANSI once
  private def isAnsi_? : Boolean =
    !AnsiConsole.wrapOutputStream(null).isInstanceOf[AnsiOutputStream]

  // left marker
  lazy val lm: String = if (isAnsi_?) "" else "▶"
  //right marker
  lazy val rm: String = if (isAnsi_?) "" else "◀"
}

trait TTLiteError extends Exception {
  val errorKind : String
  val msg : String
  val details: String
  val location: String = ""
  val line : Int
  val column : Int
  val origin: String = ""
  override def getMessage: String = msg
  def withFile(f : String) : TTLiteError = FiledTTLiteError(this, f)
}

case class FiledTTLiteError(err : TTLiteError, file : String) extends TTLiteError {
  val errorKind: String = err.errorKind
  val msg : String = err.msg
  val details: String = err.details
  val line : Int = err.line
  val column : Int = err.column
  override val location: String = s"$file[$line:$column]"
  override val origin: String = err.origin
  override def withFile(f : String) : TTLiteError = this
}

case class ParsingError(msg : String, line : Int, column : Int, longString : String) extends TTLiteError {
  val errorKind = "Lexical"
  val details: String =
    longString.replace("\n\n", "\n")
}

case class TranslationError(override val mt : MTerm, override val msg : String) extends MTermError("Lexical", mt, msg)

class MTermError(val errorKind : String, val mt : MTerm, val msg : String) extends TTLiteError {
  import IoUtil._
  val details: String =
    ansi(s"${mt.originPrefix}${lm}@|magenta,bold ${mt.origin}|@${rm}${mt.originSuffix}")
  val line: Int = mt.startPos.line
  val column: Int = mt.startPos.column
  override val origin: String = mt.origin
}

case class DuplicateIdError(id : Id) extends TTLiteError {
  import IoUtil._
  val details: String =
    ansi(s"${id.originPrefix}${lm}@|magenta,bold ${id.origin}|@${rm}${id.originSuffix}")
  val line: Int = id.startPos.line
  val column: Int = id.startPos.column
  override val origin: String = id.origin
  val errorKind: String = "Syntax"
  val msg: String = s"Identifier ${id.n} is already defined"
}

case class TypeError(msg : String, path : Path) extends Exception(msg) {
  def withMTerm(mterm : MTerm) : TTLiteError = MTermTypeError(this, mterm)
}
case class MTermTypeError(te : TypeError, topTerm : MTerm) extends MTermError("Type", Path.subterm(topTerm, te.path), te.msg)

object TTLiteExit extends TTLiteError {
  val line : Int = 0
  val column : Int = 0
  val errorKind  = "System"
  val msg : String = "Signal to exit repl"
  val details: String = msg
  override def withFile(f : String): TTLiteError = this
}

trait PrettyPrinter extends org.kiama.output.PrettyPrinter {
  def parensIf(b: Boolean, d: Doc): Doc = if (b) parens(d) else d
}
