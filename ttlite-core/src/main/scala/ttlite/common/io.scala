package ttlite.common

object IoUtil {
  import org.fusesource.jansi._
  def ansi(s : String) : String =
    Ansi.ansi.render(s).toString

  def isAscii(): Boolean =
    !AnsiConsole.wrapOutputStream(null).isInstanceOf[AnsiOutputStream]

  // left marker
  lazy val lm: String = if (isAscii()) "" else "▶"
  //right marker
  lazy val rm: String = ""//if (isAscii()) "" else "◀"
}

abstract class TTLiteError(msg: String) extends Exception(msg) {
  var file : String = "_$_"
  def setFile(f : String) : this.type = {
    if (file == "_$_")
      file = f
    this
  }
  //override def getMessage(): String = "XXX"
  def details: String = ""
  def location: String = s"$file[${line}:${column}]"
  def line : Int
  def column : Int
}

case class ParsingError(msg : String, line : Int, column : Int, longString : String) extends TTLiteError(msg) {
  override def details: String =
    longString.replace("\n\n", "\n")
}

case class TranslationError(mt : MTerm, msg : String) extends TTLiteError(msg) {
  import IoUtil._
  override def details =
    ansi(s"${mt.originPrefix}${lm}@|magenta,bold ${mt.origin}|@${rm}${mt.originSuffix}")
  val line = mt.startPos.line
  val column = mt.startPos.column
  def origin = mt.origin
}

case class TypeError(msg : String, path : Path) extends TTLiteError(msg) {
  import IoUtil._
  var mterm : MTerm = null

  def setMTerm(mt : MTerm): TypeError = {
    if (mterm == null) {
      mterm = mt
    }
    this
  }

  override def details = {
    val mt = mterm.subTerm(path)
    ansi(s"${mt.originPrefix}${lm}@|magenta,bold ${mt.origin}|@${rm}${mt.originSuffix}")
  }

  def line =
    mterm.subTerm(path).startPos.line

  def column =
    mterm.subTerm(path).startPos.column

  def origin =
    mterm.subTerm(path).origin
}

object TTLiteExit extends TTLiteError("Exit") {
  val line : Int = 0
  val column : Int = 0
}

trait PrettyPrinter extends org.kiama.output.PrettyPrinter {
  def parensIf(b: Boolean, d: Doc) = if (b) parens(d) else d
}
