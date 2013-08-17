package superspec

package object tt {
  type NameEnv[V] = Map[Name, V]
  val ids = "abcdefghijklmnopqrstuvwxyz"
  val suffs = List("", "1")
  val vars = for {j <- suffs; i <- ids} yield s"$i$j"

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
  case class MBind(id: String, tp: MetaTerm, body: MetaTerm) extends MetaTerm

  // statements in the input file
  // TODO: test commands, external commands
  trait Stmt[+I]
  case class Let[I](n: String, i: I) extends Stmt[I]
  case class Assume[I](ns: List[(String, I)]) extends Stmt[I]
  case class Eval[I](e: I) extends Stmt[I]
  case class Import(s: String) extends Stmt[Nothing]
  case class SC[I](e: I) extends Stmt[I]
  case class CertSC[I](e: I) extends Stmt[I]

  case class TypeError(msg: String) extends Exception(msg)

  import scala.util.parsing.combinator._

  class MetaLexical extends lexical.StdLexical {
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

  object MetaParser extends syntactical.StandardTokenParsers with PackratParsers with ImplicitConversions {

    override val lexical = new MetaLexical
    lexical.delimiters += ("(", ")", "::", ".")

    type Ctx = List[String]
    type Res[A] = Ctx => A

    lazy val term: PackratParser[Res[MetaTerm]] = optTyped
    lazy val aTerm: PackratParser[Res[MetaTerm]] =
      mVar | "(" ~> term <~ ")"
    lazy val mVar: PackratParser[Res[MetaTerm]] =
      ident ^^ {i => ctx: Ctx => ctx.indexOf(i) match {case -1 => MVar(s2name(i)) case j => MVar(Quote(j))}}
    lazy val app: PackratParser[Res[MetaTerm]] =
      (aTerm+) ^^ {ts => ctx: Ctx => ts.map{_(ctx)}.reduce(MApp)}
    lazy val bind: PackratParser[Res[MetaTerm]] =
      ident ~ (arg+) ~ ("." ~> term) ^^ {case id ~ args ~ body => ctx: Ctx =>
        def mkBind(xs: List[(String, Res[MetaTerm])], c: Ctx): MetaTerm = xs match {
          case Nil => body(c)
          case (n, tp) :: xs => MBind(id, tp(c), mkBind(xs, n :: c))
        }
        mkBind(args, ctx)
      }
    lazy val untyped: PackratParser[Res[MetaTerm]] = bind | app
    lazy val optTyped: PackratParser[Res[MetaTerm]] =
      untyped ~ ("::" ~> untyped) ^^ {case e ~ t => ctx: Ctx => MAnn(e(ctx), t(ctx))} | untyped
    val arg: PackratParser[(String, Res[MetaTerm])] =
      "(" ~> (ident ~ ("::" ~> term)) <~ ")" ^^ {case i ~ x => (i, x)}
    def s2name(s: String): Name = if (s.startsWith("$")) Assumed(s) else Global(s)
    def parseIO[A](p: Parser[A], in: String): Option[A] =
      phrase(p)(new lexical.Scanner(in)).map(Some(_)).getOrElse(None)

    def parseMTerm(in: String) =
      parseIO(term, in).map(_(Nil)).get
  }

}
