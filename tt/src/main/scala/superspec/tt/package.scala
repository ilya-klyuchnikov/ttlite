package superspec

package object tt {
  type NameEnv[V] = Map[Name, V]
  val ids = "abcdefghijklmnopqrstuvwxyz"
  val suffs = List("", "1")
  val vars = for {j <- suffs; i <- ids} yield s"$i$j"
}

package tt {
// meta-syntax
sealed trait Name
case class Global(n: String) extends Name
case class Assumed(n: String) extends Name
case class Local(i: Int) extends Name
case class Quote(i: Int) extends Name

sealed trait MetaTerm
case class MApp(t1: MetaTerm, t2: MetaTerm) extends MetaTerm
case class MAnn(t1: MetaTerm, t2: MetaTerm) extends MetaTerm
// typed binders
case class Binder(tp: MetaTerm, body: MetaTerm) extends MetaTerm
// commands
trait Stmt[+I, +TInf]
case class Let[I](n: String, i: I) extends Stmt[I, Nothing]
case class Assume[TInf](ns: List[(String, TInf)]) extends Stmt[Nothing, TInf]
case class Eval[I](e: I) extends Stmt[I, Nothing]
case class Import(s: String) extends Stmt[Nothing, Nothing]

case class TypeError(msg: String) extends Exception(msg)

import scala.language.postfixOps
import scala.util.parsing.combinator.{PackratParsers, ImplicitConversions}
import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.combinator.lexical.StdLexical

class MetaLexical extends StdLexical {
  import scala.util.parsing.input.CharArrayReader._
  override def whitespace: Parser[Any] = rep(
    whitespaceChar
      | '/' ~ '*' ~ comment
      | '/' ~ '/' ~ rep( chrExcept(EofCh, '\n') )
      | '-' ~ '-' ~ rep( chrExcept(EofCh, '\n') )
      | '/' ~ '*' ~ failure("unclosed comment")
  )
  override def identChar = letter | elem('_') | elem('$')
}

object MetaParser extends StandardTokenParsers with PackratParsers with ImplicitConversions {
  type C = List[String]
  type Res[A] = C => A
  lazy val term: PackratParser[Res[MetaTerm]] = null
}
}

