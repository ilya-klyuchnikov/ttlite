package tapl

import scala.util.parsing.combinator.ImplicitConversions

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
  object LambdaPIInterpreter extends Interpreter with ImplicitConversions {
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
    lazy val iiparse: Parser[ITerm] = parseITErm0(Nil)
    val isparse: Parser[Stmt[ITerm, CTerm]] = parseStmt(Nil)

    def parseITErm0(ns: List[String]): Parser[ITerm] =
      "forall" ~> parseBinding(ns) >> { b => "." ~> parseCTErm0(b._1 :: ns ) ^^ { t1 =>
        val t = b._2
        Pi(t, t1)
      }} |
        "forall" ~> parseBindingPar(ns) >> { b => parseForall(0, b._1 :: ns ) ^^ { t1 =>
          val t = b._2
          Pi(t, t1)
        }} |
        parseITErm1(ns) ~ ("->" ~> parseCTErm0("" :: ns)) ^^ {case x ~ y => Pi(Inf(x), y)} |
        parseITErm1(ns) |
        ("(" ~> parseLam(ns) <~ ")") ~ ("->" ~> parseCTErm0("" :: ns)) ^^ {case x ~ y => Pi(x, y)}
    def parseITErm1(ns: List[String]): Parser[ITerm] =
      parseITErm2(ns) ~ ("::" ~> parseCTErm0(ns)) ^^ {case e ~ t => Ann(Inf(e), t)} |
        parseITErm2(ns) |
        ("(" ~> parseLam(ns) <~ ")") ~ ("::" ~> parseCTErm0(ns)) ^^ {case e ~ t => Ann(e, t)}
    def parseITErm2(ns: List[String]): Parser[ITerm] =
      parseITErm3(ns) ~ (parseCTErm3(ns)*) ^^ {case t ~ ts => ts.foldLeft(t){_ @@ _} }
    def parseITErm3(ns: List[String]): Parser[ITerm] =
      ident ^^ {i => ns.indexOf(i) match {case -1 => Free(Global(i)) case j => Bound(j)}} |
        "(" ~> parseITErm0(ns) <~ ")" | numericLit ^^ {x => toNat(x.toInt)} |
        "*" ^^^ Star
    def parseForall(i: Int, ns: List[String]): Parser[CTerm] = {
      "." ~> parseCTErm0(ns ) |
        parseBindingPar(ns) >> { b => parseForall(0, b._1 :: ns ) ^^ { t1 =>
          val t = b._2
          Inf(Pi(t, t1))
        }}
    }

    def parseCTErm0(ns: List[String]): Parser[CTerm] =
      parseLam(ns) | parseITErm0(ns) ^^ {Inf(_)}
    def parseCTErm1(ns: List[String]): Parser[CTerm] =
      "(" ~> parseLam(ns) <~ ")" | parseITErm1(ns) ^^ {Inf(_)}
    def parseCTErm2(ns: List[String]): Parser[CTerm] =
      "(" ~> parseLam(ns) <~ ")" | parseITErm2(ns) ^^ {Inf(_)}
    def parseCTErm3(ns: List[String]): Parser[CTerm] =
      "(" ~> parseLam(ns) <~ ")" | parseITErm3(ns) ^^ {Inf(_)}

    def parseLam(ns: List[String]): Parser[CTerm] =
      "\\" ~> (ident+) <~ "->" >> {ids => parseCTErm0(ids.reverse ::: ns) ^^ {t => ids.foldLeft(t){(t, z) => Lam(t)}}}
    def parseStmt(ns: List[String]): Parser[Stmt[ITerm, CTerm]] =
      "let" ~> ident ~ ("=" ~> parseITErm0(ns) <~ ";") ^^ {case x ~ y => Let(x, y)} |
        "assume" ~> (parseBinding(Nil) | parseBindingPar(Nil)) <~ ";" ^^ {b => Assume(List(b))} |
        "import" ~> stringLit <~ ";" ^^ Import |
        parseITErm0(ns) <~ ";" ^^ {Eval(_)}

    def parseBindingPar(e: List[String]): Parser[(String, CTerm)] =
      "(" ~> parseBinding(e) <~ ")"

    def parseBinding(e: List[String]): Parser[(String, CTerm)] =
      ident ~ ("::" ~> parseCTErm0(e)) ^^ {case i ~ x => (i, x)}
  }
  def toNat(i: Int): ITerm = sys.error("not implemented")
}
