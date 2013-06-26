package superspec.tt

import scala.language.postfixOps
import scala.util.parsing.combinator.{PackratParsers, ImplicitConversions}

import superspec._

trait CoreREPL extends CoreAST with CorePrinter with CoreEval with CoreCheck with CoreQuote with REPL {
  type I = ITerm
  type C = CTerm
  type V = Value
  type TInf = CTerm
  override val int = CoreInterpreter
  object CoreInterpreter extends Interpreter with PackratParsers with ImplicitConversions {
    lexical.reserved += ("assume", "let", "forall", "import")
    lexical.delimiters += ("(", ")", "::", ":=", "->", "=>", ":", "*", "=", "\\", ";", ".", "<", ">", ",")
    val prompt: String = "TT> "

    def itype(ne: NameEnv[Value], ctx: NameEnv[Value], i: ITerm): Result[Value] =
      iType0(ne, ctx, i)
    def iquote(v: Value): CTerm =
      quote0(v)
    def ieval(ne: NameEnv[Value], i: ITerm): Value =
      eval(i, ne, List())
    def typeInfo(t: Value): Value =
      t
    def icprint(c: CTerm): String =
      pretty(cPrint(0, 0, c))
    def itprint(t: Value): String =
      pretty(cPrint(0, 0, quote0(t)))
    def assume(state: State, x: (String, CTerm)): State = {
      itype(state.ne, state.ctx, Ann(x._2, Inf(Star))) match {
        case Right(_) =>
          val v = ieval(state.ne, Ann(x._2, Inf(Star)))
          println(v)
          state.copy(ctx = (Global(x._1), v) :: state.ctx)
        case Left(_) =>
          state
      }
    }
    lazy val iParse: Parser[ITerm] = iterm0 ^^ {_(Nil)}
    val stmtParse: Parser[Stmt[ITerm, CTerm]] = stmt

    type C = List[String]
    type Res[A] = C => A

    lazy val iterm0: PackratParser[Res[ITerm]] =
      ("forall" ~> binding) ~ ("." ~> cterm0) ^^ { case b ~ t1 => ctx: C =>
        val bb = b(ctx)
        val t = bb._2
        Pi(t, t1(bb._1 :: ctx))
      } |
        ("forall" ~> bindingPar) ~ forall ^^ { case b ~ t1 => ctx: C =>
          val bb = b(ctx)
          val t = bb._2
          Pi(t, t1(bb._1 :: ctx))
        } |
        iterm1 ~ ("->" ~> cterm0) ^^ {case x ~ y => ctx: C => Pi(Inf(x(ctx)), y("" :: ctx))} |
        iterm1 |
        ("(" ~> lam <~ ")") ~ ("->" ~> cterm0) ^^ {case x ~ y => ctx: C => Pi(x(ctx), y("" :: ctx))}
    lazy val iterm1: PackratParser[Res[ITerm]] =
      iterm2 ~ ("::" ~> cterm0) ^^ {case e ~ t => ctx: C => Ann(Inf(e(ctx)), t(ctx))} |
        iterm2 |
        ("(" ~> lam <~ ")") ~ ("::" ~> cterm0) ^^ {case e ~ t => ctx: C => Ann(e(ctx), t(ctx))}

    lazy val iterm2: PackratParser[Res[ITerm]] =
      iterm3 ~ (cterm3*) ^^ {case t ~ ts => ctx: C => ts.map{_(ctx)}.foldLeft(t(ctx)){_ @@ _} }
    lazy val iterm3: PackratParser[Res[ITerm]] =
      ident ^^ {i => ctx: C => ctx.indexOf(i) match {case -1 => Free(Global(i)) case j => Bound(j)}} |
        "<" ~> numericLit <~ ">" ^^ {x => ctx: C => Free(Local(x.toInt))} |
        "(" ~> iterm0 <~ ")" | numericLit ^^ {x => ctx: C => toNat(x.toInt)} |
        "*" ^^^ {ctx: C => Star}
    lazy val forall: PackratParser[Res[CTerm]] = {
      "." ~> cterm0 |
        bindingPar ~ forall ^^ { case b ~ t1 => ctx: C =>
          val bb = b(ctx)
          val t = bb._2
          Inf(Pi(t, t1(bb._1 :: ctx)))
        }
    }

    lazy val cterm0: PackratParser[Res[CTerm]] =
      lam | iterm0 ^^ {t => ctx: C => Inf(t(ctx))}
    lazy val cterm1: PackratParser[Res[CTerm]] =
      "(" ~> lam <~ ")" | iterm1 ^^ {t => ctx: C => Inf(t(ctx))}
    lazy val cterm2: PackratParser[Res[CTerm]] =
      "(" ~> lam <~ ")" | iterm2 ^^ {t => ctx: C => Inf(t(ctx))}
    lazy val cterm3: PackratParser[Res[CTerm]] =
      "(" ~> lam <~ ")" | iterm3 ^^ {t => ctx: C => Inf(t(ctx))}

    lazy val lam: PackratParser[Res[CTerm]] =
      "(" ~> lam <~ ")" |
        ("\\" ~> (ident+) <~ "->") ~ cterm0 ^^
          {case ids ~ t => ctx: C => ids.foldLeft(t(ids.reverse ::: ctx)){(t, _) => Lam(t)}}


    lazy val stmt: PackratParser[Stmt[ITerm, CTerm]] =
      "let" ~> ident ~ ("=" ~> iterm0 <~ ";") ^^ {case x ~ y => Let(x, y(Nil))} |
        "assume" ~> (binding | bindingPar) <~ ";" ^^ {b => Assume(List(b(Nil)))} |
        "import" ~> stringLit <~ ";" ^^ Import |
        iterm0 <~ ";" ^^ {t => Eval(t(Nil))}

    lazy val bindingPar: PackratParser[Res[(String, CTerm)]] =
      "(" ~> binding <~ ")"

    lazy val binding: PackratParser[Res[(String, CTerm)]] =
      ident ~ ("::" ~> cterm0) ^^ {case i ~ x => ctx: C => (i, x(ctx))}
  }
  def toNat(i: Int): ITerm = sys.error("not implemented")
}
