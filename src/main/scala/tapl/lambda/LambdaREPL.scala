package tapl.lambda

import tapl._

import scala.util.parsing.combinator.ImplicitConversions

object LambdaREPL extends LambdaAST with LambdaEval with LambdaCheck with LambdaQuote with LambdaPrinter with REPL {
  type I = ITerm
  type C = CTerm
  type V = Value
  type T = Type
  type TInf = Info
  type Inf = Info
  override val int = LambdaInterpreter
  override val initialState = State(true, List(), List(), Set())
  object LambdaInterpreter extends Interpreter with ImplicitConversions {
    lexical.reserved += ("assume", "let")
    lexical.delimiters += ("(", ")", "::", ":=", "->", "=>", ":", "*", "=", "\\", ";")
    val iname: String = "the simply typed lambda calculus"
    val iprompt: String = "ST> "

    def iitype(ne: NameEnv[Value], ctx: Ctx[Info], i: ITerm): Result[Type] =
      iType0(ctx, i)
    def iquote(v: Value): CTerm =
      quote0(v)
    def ieval(ne: NameEnv[Value], i: ITerm): Value =
      iEval(i, (ne, List()))
    def ihastype(t: Type): Info =
      HasType(t)
    def icprint(c: CTerm): String =
      pretty(cPrint(0, 0, c), 100)
    def itprint(t: Type): String =
      pretty(tPrint(0, t), 100)
    def iassume(state: State, x: (String, Info)): State =
      state.copy(ctx = (Global(x._1), x._2) :: state.ctx)
    lazy val iiparse: Parser[ITerm] = parseITErm(0, Nil)
    val isparse: Parser[Stmt[ITerm, Info]] = parseStmt(Nil)

    def parseType(i: Int, ns: List[String]): Parser[Type] = i match {
      case 0 =>  parseType(1, ns) ~ ("->" ~> parseType(0, ns)) ^^ {case x ~ y => Fun(x, y)} | parseType(1, ns)
      case 1 => ident ^^ {i => TFree(Global(i))} | "(" ~> parseType(0, ns) <~ ")"
    }
    def parseITErm(i: Int, ns: List[String]): Parser[ITerm] = i match {
      case 0 => parseITErm(1, ns)
      case 1 =>
          parseITErm(2, ns) ~ ("::" ~> parseType(0, ns)) ^^ {case e ~ t => Ann(Inf(e), t)} |
            parseITErm(2, ns) |
          ("(" ~> parseLam(ns) <~ ")") ~ ("::" ~> parseType(0, ns)) ^^ {case e ~ t => Ann(e, t)}
      case 2 =>
        parseITErm(3, ns) ~ (parseCTErm(3, ns)*) ^^ {case t ~ ts => ts.foldLeft(t){_ :@: _} }
      case 3 =>
        ident ^^ {i => ns.indexOf(i) match {case -1 => Free(Global(i)) case j => Bound(j)}} |
        "(" ~> parseITErm(0, ns) <~ ")"
    }
    def parseCTErm(i: Int, ns: List[String]): Parser[CTerm] = i match {
      case 0 => parseLam(ns) | parseITErm(0, ns) ^^ {Inf(_)}
      case p => "(" ~> parseLam(ns) <~ ")" | parseITErm(p, ns) ^^ {Inf(_)}
    }
    def parseLam(ns: List[String]): Parser[CTerm] =
      ("\\" ~> (ident+) <~ "->") >> {ids => parseCTErm(0, ids.reverse ::: ns) ^^ {t => ids.foldLeft(t){(t, z) => Lam(t)}}}
    def parseStmt(ns: List[String]): Parser[Stmt[ITerm, Info]] =
      ("let" ~> ident) ~ ("=" ~> parseITErm(0, ns) <~ ";") ^^ {case x ~ y => Let(x, y)} |
        ("assume" ~> parseBindings <~ ";") ^^ {Assume(_)}|
        ("import" ~> stringLit <~ ";") ^^ Import |
        parseITErm(0, ns) <~ ";" ^^ {Eval(_)}
    def parseBindings(): Parser[List[(String, Info)]] =
      parseBinding ^^ {x => List(x)} | (("(" ~> parseBinding <~ ")")+)
    def parseBinding(): Parser[(String, Info)] =
      ident ~ ("::" ~> pInfo()) ^^ {case i ~ x => (i, x)}
    def pInfo(): Parser[Info] = parseType(0, Nil) ^^ HasType | "*" ^^^ {HasKind(Star)}
  }
}
