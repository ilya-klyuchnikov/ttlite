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
// TODO: do we need local and quote together?
// is it possible to use only one of them?
case class Local(i: Int) extends Name
case class Quote(i: Int) extends Name

sealed trait MetaTerm {
  def @@(t1: MetaTerm) = MApp(this, t1)
}
case class MApp(t1: MetaTerm, t2: MetaTerm) extends MetaTerm
case class MAnn(t1: MetaTerm, t2: MetaTerm) extends MetaTerm
case class MVar(n: Name) extends MetaTerm
// "universal binders"
case class Binder(id: String, tp: MetaTerm, body: MetaTerm) extends MetaTerm

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

  override val lexical = new MetaLexical
  lexical.delimiters += ("(", ")", "::", ".")

  type C = List[String]
  type Res[A] = C => A

  lazy val term: PackratParser[Res[MetaTerm]] = maybeTyped
  lazy val aTerm: PackratParser[Res[MetaTerm]] =
    mVar | "(" ~> term <~ ")"
  lazy val mVar: PackratParser[Res[MetaTerm]] =
    ident ^^ {i => ctx: C => ctx.indexOf(i) match {case -1 => MVar(s2name(i)) case j => MVar(Quote(j))}}
  lazy val app: PackratParser[Res[MetaTerm]] =
    (aTerm+) ^^ {ts => ctx: C => ts.map{_(ctx)}.reduce(MApp)}
  lazy val binder: PackratParser[Res[MetaTerm]] =
    ident >> {id => binding(id) ~ bs(id)} ^^ { case b ~ t1 => ctx: C =>
      val (id, n, t) = b(ctx)
      Binder(id, t, t1(n :: ctx))
    }
  lazy val untyped: PackratParser[Res[MetaTerm]] =
    binder | app
  lazy val maybeTyped: PackratParser[Res[MetaTerm]] =
    untyped ~ ("::" ~> untyped) ^^ {case e ~ t => ctx: C => MAnn(e(ctx), t(ctx))} | untyped
  def binding(id: String): PackratParser[Res[(String, String, MetaTerm)]] =
    "(" ~> (ident ~ ("::" ~> term)) <~ ")" ^^ {case i ~ x => ctx: C => (id, i, x(ctx))}
  def bs(id: String): PackratParser[Res[MetaTerm]] = {
    val b: PackratParser[Res[(String, String, MetaTerm)]] = binding(id)
    lazy val parser: PackratParser[Res[MetaTerm]] =
      "." ~> term |
        b ~ parser ^^ { case b ~ t1 => ctx: C =>
          val (_, n, t) = b(ctx)
          Binder(id, t, t1(n :: ctx))
        }
    parser
  }
  def s2name(s: String): Name =
    if (s.startsWith("$")) Assumed(s) else Global(s)

  def parseIO[A](p: Parser[A], in: String): Option[A] = phrase(p)(new lexical.Scanner(in)) match {
    case t if t.successful =>
      Some(t.get)
    case t              =>
      Console.println(s"cannot parse: $t")
      None
  }
  def parseMTerm(in: String) =
    parseIO(term, in).map(_(Nil)).get
}

}
