package superspec.tt

import scala.language.postfixOps
import scala.util.parsing.combinator.{PackratParsers, ImplicitConversions}

import superspec._

trait CoreREPL extends CoreAST with CorePrinter with CoreEval with CoreCheck with CoreQuote with REPL {

  type I = Term
  type C = Term
  type V = Value
  type TInf = Term
  override val int = CoreInterpreter
  object CoreInterpreter extends Interpreter with PackratParsers with ImplicitConversions {
    lexical.reserved += ("assume", "let", "forall", "import", "sc")
    lexical.delimiters += ("(", ")", "::", ":=", "->", "=>", ":", "*", "=", "\\", ";", ".", "<", ">", ",")
    val prompt: String = "TT> "

    def itype(ne: NameEnv[Value], ctx: NameEnv[Value], i: Term): Result[Value] =
    try {
      Right(iType0(ne, ctx, i))
    } catch {
      case e: Throwable => Left(e.getMessage)
    }
    def iquote(v: Value): Term =
      quote0(v)
    def ieval(ne: NameEnv[Value], i: Term): Value =
      eval(i, ne, List())
    def typeInfo(t: Value): Value =
      t
    def icprint(c: Term): String =
      pretty(print(0, 0, c))
    def itprint(t: Value): String =
      pretty(print(0, 0, quote0(t)))
    // todo: raise arity
    def assume(state: State, x: (String, Term)): State = {
      itype(state.ne, state.ctx, Ann(x._2, Star)) match {
        case Right(_) =>
          val v = ieval(state.ne, Ann(x._2, Star))
          println(v)
          state.copy(ctx = state.ctx + (Global(x._1) -> v))
        case Left(_) =>
          state
      }
    }
    lazy val iParse: Parser[Term] = iterm0 ^^ {_(Nil)}
    val stmtParse: Parser[Stmt[Term, Term]] = stmt

    type C = List[String]
    type Res[A] = C => A

    lazy val iterm0: PackratParser[Res[Term]] =
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
        iterm1 ~ ("->" ~> cterm0) ^^ {case x ~ y => ctx: C => Pi((x(ctx)), y("" :: ctx))} |
        iterm1 | lam
    lazy val iterm1: PackratParser[Res[Term]] =
      iterm2 ~ ("::" ~> cterm0) ^^ {case e ~ t => ctx: C => Ann((e(ctx)), t(ctx))} |
        iterm2 |
        ("(" ~> lam <~ ")") ~ ("::" ~> cterm0) ^^ {case e ~ t => ctx: C => Ann(e(ctx), t(ctx))}

    lazy val iterm2: PackratParser[Res[Term]] =
      iterm3 ~ (cterm3*) ^^ {case t ~ ts => ctx: C => ts.map{_(ctx)}.foldLeft(t(ctx)){_ @@ _} }
    lazy val iterm3: PackratParser[Res[Term]] =
      ident ^^ {i => ctx: C => ctx.indexOf(i) match {case -1 => Free(Global(i)) case j => Bound(j)}} |
        "<" ~> numericLit <~ ">" ^^ {x => ctx: C => Free(Local(x.toInt))} |
        "(" ~> iterm0 <~ ")" | numericLit ^^ {x => ctx: C => toNat(x.toInt)} |
        "*" ^^^ {ctx: C => Star}
    lazy val forall: PackratParser[Res[Term]] = {
      "." ~> cterm0 |
        bindingPar ~ forall ^^ { case b ~ t1 => ctx: C =>
          val bb = b(ctx)
          val t = bb._2
          Pi(t, t1(bb._1 :: ctx))
        }
    }

    lazy val cterm0: PackratParser[Res[Term]] =
      lam | iterm0 ^^ {t => ctx: C => t(ctx)}
    lazy val cterm1: PackratParser[Res[Term]] =
      "(" ~> lam <~ ")" | iterm1 ^^ {t => ctx: C => (t(ctx))}
    lazy val cterm2: PackratParser[Res[Term]] =
      "(" ~> lam <~ ")" | iterm2 ^^ {t => ctx: C => (t(ctx))}
    lazy val cterm3: PackratParser[Res[Term]] =
      "(" ~> lam <~ ")" | iterm3 ^^ {t => ctx: C => (t(ctx))}
    lazy val lam: PackratParser[Res[Term]] =
      "(" ~> lam <~ ")" |
        ("\\" ~> (bindingPar)) ~ forall1 ^^
          {case b ~ t1 => ctx: C =>
            val id = b(ctx)._1
            val t = b(ctx)._2
            var res = Lam(t, t1(id :: ctx))
            res
          }

    lazy val forall1: PackratParser[Res[Term]] = {
      "->" ~> cterm0 |
        bindingPar ~ forall1 ^^ { case b ~ t1 => ctx: C =>
          val bb = b(ctx)
          val t = bb._2
          Lam(t, t1(bb._1 :: ctx))
        }
    }


    lazy val stmt: PackratParser[Stmt[Term, Term]] =
      "let" ~> ident ~ ("=" ~> iterm0 <~ ";") ^^ {case x ~ y => Let(x, y(Nil))} |
        "assume" ~> (binding | bindingPar) <~ ";" ^^ {b => Assume(List(b(Nil)))} |
        "import" ~> stringLit <~ ";" ^^ Import |
        "sc" ~> iterm0 <~ ";" ^^ {t => Supercompile(t(Nil))} |
        iterm0 <~ ";" ^^ {t => Eval(t(Nil))}

    lazy val bindingPar: PackratParser[Res[(String, Term)]] =
      "(" ~> binding <~ ")"

    lazy val binding: PackratParser[Res[(String, Term)]] =
      ident ~ ("::" ~> cterm0) ^^ {case i ~ x => ctx: C => (i, x(ctx))}
  }
  def toNat(i: Int): Term = sys.error("not implemented")
}
