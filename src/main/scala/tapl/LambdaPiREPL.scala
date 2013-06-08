package tapl

import scala.util.parsing.combinator.ImplicitConversions

object LambdaPiREPLMain extends LambdaPiREPL {
  override def initialState = State(true, Nil, Nil)
}

trait LambdaPiREPL extends LambdaPiAST with LambdaPiEval with LambdaPiCheck with LambdaPiQuote with REPL {
  type I = ITerm
  type C = CTerm
  type V = Value
  type T = Value
  type TInf = CTerm
  type Inf = Value
  override val int = LambdaPIInterpreter
  object LambdaPIInterpreter extends Interpreter with ImplicitConversions {
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
    lazy val iiparse: Parser[ITerm] = parseITErm(0, Nil)
    val isparse: Parser[Stmt[ITerm, CTerm]] = parseStmt(Nil)

    def parseITErm(i: Int, ns: List[String]): Parser[ITerm] = i match {
      case 0 =>
        ("forall" ~> parseBindings(true, ns)) >> { case List(b) => ("." ~> parseCTErm(0, b._1 :: ns )) ^^ { t1 =>
          val t = b._2
          Pi(t, t1)
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
          "(" ~> parseITErm(0, ns) <~ ")" | numericLit ^^ {x => toNat(x.toInt)} |
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
      parseBinding(e) ^^ {x => List(x)} | "(" ~> parseBinding(e) <~ ")" ^^ {x => List(x)} //| parseBindings2(b, e)

    def parseBindings2(b: Boolean, e: List[String]): Parser[List[(String, CTerm)]] =
      "(" ~> parseBinding(e) <~ ")" >> {case (i, x) =>
        val e1 = if (b) i :: e else Nil
        (parseBindings2(b, e1)?) ^^ {o => List((i, x)) ::: o.getOrElse(Nil) }
      }

    def parseBinding(e: List[String]): Parser[(String, CTerm)] =
      ident ~ ("::" ~> parseCTErm(0, e)) ^^ {case i ~ x => (i, x)}
  }
  def toNat(i: Int): ITerm = sys.error("not implemented")
}
