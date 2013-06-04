package tapl

import scala.util.parsing.combinator.ImplicitConversions

object LambdaPiREPL extends LambdaPiAST with LambdaPiEval with LambdaPiCheck with LambdaPiQuote with REPL {

  object LambdaInterpreter extends Interpreter[ITerm, CTerm, Value, Value, CTerm, Value] with ImplicitConversions {
    lexical.reserved += ("assume", "let", "forall")
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
      c.toString
    def itprint(t: Type): String =
      t.toString
    def iassume(state: State[Value, Value], x: (String, CTerm)): State[Value, Value] = {
      val t = x._2
      println(iitype(state.ne, state.ctx, Ann(t, Inf(Star))))
      val t1 = iitype(state.ne, state.ctx, Ann(t, Inf(Star))).right.toOption.get
      state.copy(ctx = (Global(x._1), t1) :: state.ctx)
    }
    // TODO: continue here
    lazy val iiparse: Parser[ITerm] = parseITErm(0, Nil)
    val isparse: Parser[Stmt[ITerm, CTerm]] = parseStmt(Nil)

    def parseITErm(i: Int, ns: List[String]): Parser[ITerm] = i match {
      case 0 =>
        ("forall" ~> parseBindings(true, ns)) >> { fe => ("." ~> parseCTErm(0, fe.map(_._1))) ^^ { t1 =>
          val t :: ts = fe.map(_._2)
          ts.foldLeft(Pi(t, t1)){(p, t) => Pi(t, Inf(p))}
        }} |
          parseITErm(1, ns) ~ ("->" ~> parseCTErm(0, "" :: ns)) ^^ {case x ~ y => Pi(Inf(x), y)} |
          parseITErm(1, ns) |
          ("(" ~> parseLam(ns) <~ ")") ~ ("->" ~> parseCTErm(0, "" :: ns)) ^^ {case x ~ y => Pi(x, y)}
      case 1 =>
        parseITErm(2, ns) ~ ("::" ~> parseCTErm(0, ns)) ^^ {case e ~ t => Ann(Inf(e), t)} |
          parseITErm(2, ns) |
          ("(" ~> parseLam(ns) <~ ")") ~ ("::" ~> parseCTErm(0, ns)) ^^ {case e ~ t => Ann(e, t)}
      case 2 =>
        parseITErm(3, ns) ~ (parseCTErm(3, ns)*) ^^ {case t ~ ts => ts.foldLeft(t){_ :@: _} }
      // var
      case 3 =>
        ident ^^ {i => ns.indexOf(i) match {case -1 => Free(Global(i)) case j => Bound(j)}} |
          "(" ~> parseITErm(0, ns) <~ ")" |
        "*" ^^^ {Star}
    }
    def parseCTErm(i: Int, ns: List[String]): Parser[CTerm] = i match {
      case 0 => parseLam(ns) | parseITErm(0, ns) ^^ {Inf(_)}
      case p => "(" ~> parseLam(ns) <~ ")" | parseITErm(p, ns) ^^ {Inf(_)}
    }
    def parseLam(ns: List[String]): Parser[CTerm] =
      ("\\" ~> (ident+) <~ "->") >> {ids => parseCTErm(0, ids.reverse ::: ns) ^^ {t => ids.foldLeft(t){(t, z) => Lam(t)}}}
    def parseStmt(ns: List[String]): Parser[Stmt[ITerm, CTerm]] =
      ("let" ~> ident) ~ ("=" ~> parseITErm(0, ns) <~ ";") ^^ {case x ~ y => Let(x, y)} |
        ("assume" ~> parseBindings(false, Nil) <~ ";") ^^ {Assume(_)} | parseITErm(0, ns) <~ ";" ^^ {Eval(_)}
    def parseBindings(b: Boolean, e: List[String]): Parser[List[(String, CTerm)]] =
      parseBinding(e) ^^ {x => List(x)} | (("(" ~> parseBinding(e) <~ ")")+)
    def parseBinding(e: List[String]): Parser[(String, CTerm)] =
      ident ~ ("::" ~> parseCTErm(0, e)) ^^ {case i ~ x => (i, x)}
  }

  def main(args: Array[String]) {
    loop(LambdaInterpreter, State(true, null, List(), List()))
  }
}
