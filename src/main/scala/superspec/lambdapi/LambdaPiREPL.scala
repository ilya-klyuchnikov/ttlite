package superspec.lambdapi

import superspec._

import scala.util.parsing.combinator.{PackratParsers, ImplicitConversions}

object LambdaPiREPLMain extends LambdaPiREPL {
  override def initialState = State(true, Nil, Nil, Set())
}

trait LambdaPiREPL extends LambdaPiAST with LambdaPiPrinter with LambdaPiEval with LambdaPiCheck with LambdaPiQuote with REPL {
  type I = ITerm
  type C = CTerm
  type V = Value
  type T = Value
  type TInf = CTerm
  type Inf = Value
  override val int = LambdaPIInterpreter
  object LambdaPIInterpreter extends Interpreter with PackratParsers with ImplicitConversions {
    lexical.reserved += ("assume", "let", "forall", "import")
    lexical.delimiters += ("(", ")", "::", ":=", "->", "=>", ":", "*", "=", "\\", ";", ".")
    val iname: String = "lambda-Pi"
    val iprompt: String = "LP> "

    def iitype(ne: NameEnv[Value], ctx: Ctx[Value], i: ITerm): Result[Type] =
      iType0((ne, ctx), i)
    def iquote(v: Value): CTerm =
      quote0(v)
    def ieval(ne: NameEnv[Value], i: ITerm): Value =
      iEval(i, (ne, List()))
    def ihastype(t: Type): Type =
      t
    def icprint(c: CTerm): String =
      pretty(cPrint(0, 0, c))
    def itprint(t: Type): String =
      pretty(cPrint(0, 0, quote0(t)))
    def iassume(state: State, x: (String, CTerm)): State = {
      iitype(state.ne, state.ctx, Ann(x._2, Inf(Star))) match {
        case Right(_) =>
          val v = ieval(state.ne, Ann(x._2, Inf(Star)))
          println(v)
          state.copy(ctx = (Global(x._1), v) :: state.ctx)
        case Left(_) =>
          state
      }
    }
    lazy val iiparse: Parser[ITerm] = parseITErm0 ^^ {_(Nil)}
    val isparse: Parser[Stmt[ITerm, CTerm]] = parseStmt

    type C = List[String]
    type Res[A] = C => A

    lazy val parseITErm0: PackratParser[Res[ITerm]] =
      ("forall" ~> parseBinding) ~ ("." ~> parseCTErm0) ^^ { case b ~ t1 => ctx: C =>
        val bb = b(ctx)
        val t = bb._2
        Pi(t, t1(bb._1 :: ctx))
      } |
        ("forall" ~> parseBindingPar) ~ parseForall ^^ { case b ~ t1 => ctx: C =>
          val bb = b(ctx)
          val t = bb._2
          Pi(t, t1(bb._1 :: ctx))
        } |
        parseITErm1 ~ ("->" ~> parseCTErm0) ^^ {case x ~ y => ctx: C => Pi(Inf(x(ctx)), y(""::ctx))} |
        parseITErm1 |
        ("(" ~> parseLam <~ ")") ~ ("->" ~> parseCTErm0) ^^ {case x ~ y => ctx: C => Pi(x(ctx), y(""::ctx))}
    lazy val parseITErm1: PackratParser[Res[ITerm]] =
      parseITErm2 ~ ("::" ~> parseCTErm0) ^^ {case e ~ t => ctx: C => Ann(Inf(e(ctx)), t(ctx))} |
        parseITErm2 |
        ("(" ~> parseLam <~ ")") ~ ("::" ~> parseCTErm0) ^^ {case e ~ t => ctx: C => Ann(e(ctx), t(ctx))}

    lazy val parseITErm2: PackratParser[Res[ITerm]] =
      parseITErm3 ~ (parseCTErm3*) ^^ {case t ~ ts => ctx: C => ts.map{_(ctx)}.foldLeft(t(ctx)){_ @@ _} }
    lazy val parseITErm3: PackratParser[Res[ITerm]] =
      ident ^^ {i => ctx: C => ctx.indexOf(i) match {case -1 => Free(Global(i)) case j => Bound(j)}} |
        "(" ~> parseITErm0 <~ ")" | numericLit ^^ {x => ctx: C => toNat(x.toInt)} |
        "*" ^^^ {ctx: C => Star}
    lazy val parseForall: PackratParser[Res[CTerm]] = {
      "." ~> parseCTErm0 |
        parseBindingPar ~ parseForall ^^ { case b ~ t1 => ctx: C =>
          val bb = b(ctx)
          val t = bb._2
          Inf(Pi(t, t1(bb._1 :: ctx)))
        }
    }

    lazy val parseCTErm0: PackratParser[Res[CTerm]] =
      parseLam | parseITErm0 ^^ {t => ctx: C => Inf(t(ctx))}
    lazy val parseCTErm1: PackratParser[Res[CTerm]] =
      "(" ~> parseLam <~ ")" | parseITErm1 ^^ {t => ctx: C => Inf(t(ctx))}
    lazy val parseCTErm2: PackratParser[Res[CTerm]] =
      "(" ~> parseLam <~ ")" | parseITErm2 ^^ {t => ctx: C => Inf(t(ctx))}
    lazy val parseCTErm3: PackratParser[Res[CTerm]] =
      "(" ~> parseLam <~ ")" | parseITErm3 ^^ {t => ctx: C => Inf(t(ctx))}

    lazy val parseLam: PackratParser[Res[CTerm]] =
      ("\\" ~> (ident+) <~ "->") ~ parseCTErm0 ^^ {case ids ~ t => ctx: C => ids.foldLeft(t(ids.reverse ::: ctx)){(t, z) => Lam(t)}} |
        "(" ~> parseLam <~ ")"

    lazy val parseStmt: PackratParser[Stmt[ITerm, CTerm]] =
      "let" ~> ident ~ ("=" ~> parseITErm0 <~ ";") ^^ {case x ~ y => Let(x, y(Nil))} |
        "assume" ~> (parseBinding | parseBindingPar) <~ ";" ^^ {b => Assume(List(b(Nil)))} |
        "import" ~> stringLit <~ ";" ^^ Import |
        parseITErm0 <~ ";" ^^ {t => Eval(t(Nil))}

    lazy val parseBindingPar: PackratParser[Res[(String, CTerm)]] =
      "(" ~> parseBinding <~ ")"

    lazy val parseBinding: PackratParser[Res[(String, CTerm)]] =
      ident ~ ("::" ~> parseCTErm0) ^^ {case i ~ x => ctx: C => (i, x(ctx))}
  }
  def toNat(i: Int): ITerm = sys.error("not implemented")
}
