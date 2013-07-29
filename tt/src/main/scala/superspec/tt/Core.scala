package superspec.tt

trait CoreAST extends Common {
  trait Term {
    def @@(t1: Term) = :@:(this, t1)
  }
  case class Lam(t: Term, e: Term) extends Term
  case class Ann(c1: Term, ct2: Term) extends Term
  case object Star extends Term
  case class Pi(c1: Term, c2: Term) extends Term
  case class Bound(i: Int) extends Term
  case class Free(n: Name) extends Term
  case class :@:(h: Term, t: Term) extends Term

  trait Value {
    def @@(x: Value): Value = vapp(this, x)
  }
  case class VLam(t: Value, e: Value => Value) extends Value
  case object VStar extends Value
  case class VPi(t: Value, e: Value => Value) extends Value
  case class VNeutral(n: Neutral) extends Value

  trait Neutral
  case class NFree(n: Name) extends Neutral
  case class NApp(n: Neutral, v: Value) extends Neutral

  type Env = List[Value]
  val emptyNEnv = Map[Name, Value]()

  def vfree(n: Name): Value = VNeutral(NFree(n))

  private def vapp(x: Value, v: Value): Value = x match {
    case VLam(_, f) => f(v)
    case VNeutral(n) => VNeutral(NApp(n, v))
  }

  def freeLocals(c: Any): Set[Local] = c match {
    case Free(Local(n)) =>
      Set(Local(n))
    case p: scala.Product =>
      p.productIterator.flatMap(freeLocals).toSet
    case _ => Set()
  }

  implicit def sym2val(s: Symbol): Value =
    VNeutral(NFree(Global(s.name)))
  implicit def sym2Term(s: Symbol): Term =
    Free(Global(s.name))
  implicit def s2val(s: String): Value =
    VNeutral(NFree(Global(s)))
  implicit def s2Term(s: String): Term =
    Free(Global(s))

}

trait CorePrinter extends CoreAST {

  def pprint(c: Term): String =
    pretty(print(0, 0, c))

  def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Ann(c, ty) =>
      parensIf(p > 1, nest(sep(Seq(print(2, ii, c) <> " :: " , nest(print(0, ii, ty))))))
    case Star =>
      "*"
    case Pi(d, Pi(d1, r)) =>
      parensIf(p > 0, nestedForall(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Pi(d, r) =>
      parensIf(p > 0, sep(Seq("forall " <> vars(ii) <> " :: " <> print(0, ii, d) <> " .", nest(print(0, ii + 1, r)))))
    case Bound(k) if ii - k - 1 >= 0 =>
      vars(ii - k - 1)
    case Free(Global(s)) =>
      s
    case Free(Local(i)) =>
      s"<$i>"
    case i :@: c =>
      parensIf(p > 2, sep(Seq(print(2, ii, i), nest(print(3, ii, c)))))
    case Lam(t, c) =>
      parensIf(p > 0,  "\\ " <> parens(vars(ii) <> " :: " <> print(0, ii, t)) <> " -> " <> nest(print(0, ii + 1, c)))
    case _ =>
      t.toString
  }

  def nestedForall(i: Int, fs: List[(Int, Term)], t: Term): Doc = t match {
    case Pi(d, r) =>
      nestedForall(i + 1, (i, d) :: fs, r)
    case x =>
      val fors = fs.reverse.map{case (n,d) => parens(vars(n) <> " :: " <> nest(print(0, n, d)))}.toSeq
      val fors1 = fors.updated(fors.length - 1, fors(fors.length - 1) <> " .")
      nest(sep((text("forall") +: fors1).toSeq ++ Seq(print(0, i , x))))
  }
}

trait CoreQuote extends CoreAST {
  def quote0(v: Value): Term =
    quote(0, v)

  def quote(ii: Int, v: Value): Term = v match {
    case VLam(t, f) =>
      Lam(quote(ii, t), quote(ii + 1, f(vfree(Quote(ii)))))
    case VStar =>
      Star
    case VPi(v, f) =>
      Pi(quote(ii, v), quote(ii + 1, f(vfree(Quote(ii)))))
    case VNeutral(n) =>
      neutralQuote(ii, n)
  }

  def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NFree(x) =>
      boundFree(ii, x)
    case NApp(n, v) =>
      neutralQuote(ii, n) @@ quote(ii, v)
  }

  // the problem is here!!!
  def boundFree(ii: Int, n: Name): Term = n match {
    case Quote(k) =>
      Bound(math.max(ii - k - 1, 0))
    case x =>
      Free(x)
  }
}

trait CoreEval extends CoreAST {
  def eval0(c: Term): Value = eval(c, emptyNEnv, Nil)
  def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Ann(e, _) =>
      eval(e, named, bound)
    case Star =>
      VStar
    case Pi(ty, ty1) =>
      VPi(eval(ty, named, bound), x => eval(ty1, named, x :: bound))
    case Free(x) =>
      named.getOrElse(x, vfree(x))
    case Bound(ii) =>
      if (ii < bound.length) bound(ii) else vfree(Quote(ii))
    case e1 :@: e2 =>
      eval(e1, named, bound) @@ eval(e2, named, bound)
    case Lam(t, e) =>
      VLam(eval(t, named, bound), x => eval(e, named, x :: bound))
  }
}

trait CoreSubst extends CoreEval with CoreQuote {
  type Subst = Map[Name, Term]

  def findRenaming(from: Term, to: Term): Option[Subst] =
    for (s <- findSubst(from, to) if findSubst(to, from).isDefined) yield  s

  def findSubst(from: Term, to: Term): Option[Subst] =
    for (sub <- findSubst0(from, to))
    yield sub.filter { case (k, v) => v != Free(k) }

  def findSubst0(from: Any, to: Any): Option[Subst] = (from, to) match {
    case (Free(n@Local(_)), t: Term) =>
      if (isFreeSubTerm(t, 0)) Some(Map(n -> t)) else None
    case (Free(Global(n)), Free(Global(m))) =>
      if (n == m) Some(Map()) else None
    case (Free(Global(n)), _) =>
      None
    case (Bound(i), Bound(j)) =>
      if (i == j) Some(Map()) else None
    case (f@Free(Quote(_)), _) =>
      sys.error("Hey, I do note expect quoted variables here!")
    case (Lam(t1, e1), Lam(t2, e2)) =>
      mergeOptSubst(
        findSubst0(t1, t2),
        findSubst0(e1, e2)
      )
    case (from: scala.Product, to: scala.Product)
      if from.getClass == to.getClass =>
      val subs = (from.productIterator.toList zip to.productIterator.toList).map {
        case (f1, t1) => findSubst0(f1, t1)
      }
      mergeOptSubst(subs: _*)
    case _ =>
      None
  }

  def mergeSubst(sub1: Subst, sub2: Subst): Option[Subst] = {
    val merged1 = sub1 ++ sub2
    val merged2 = sub2 ++ sub1
    if (merged1 == merged2)
      Some(merged1)
    else
      None
  }

  def mergeOptSubst(subs: Option[Subst]*): Option[Subst] = {
    var res = Map():Subst
    for (sub <- subs) {
      sub match {
        case None =>
          return None
        case Some(s) =>
          mergeSubst(res, s) match {
            case None =>
              return None
            case Some(s) =>
              res = s
          }
      }
    }
    Some(res)
  }


  def applySubst(t: Term, subst: Subst): Term = {
    val env: NameEnv[Value] = subst.map {case (n, t) => (n, eval(t, emptyNEnv, Nil))}
    quote0(eval(t, env, Nil))
  }

  def isFreeSubTerm(t: Any, depth: Int): Boolean = t match {
    case Pi(c1, c2) =>
      isFreeSubTerm(c1, depth) && isFreeSubTerm(c2, depth + 1)
    case Lam(t, e) =>
      isFreeSubTerm(t, depth) && isFreeSubTerm(e, depth + 1)
    case Bound(i) =>
      i < depth
    case Free(_) =>
      true
    case t1: scala.Product =>
      t1.productIterator.forall(isFreeSubTerm(_, depth))
    case _ => true
  }

}

trait CoreCheck extends CoreAST with CoreQuote with CoreEval with CorePrinter {
  def iType0(named: NameEnv[Value], bound: NameEnv[Value], i: Term): Value =
    iType(0, named, bound, i)

  def checkEqual(i: Int, inferred: Term, expected: Term) {
    if (inferred != expected) {
      throw new TypeError(s"inferred: ${pprint(inferred)}, expected: ${pprint(expected)}")
    }
  }

  def checkEqual(i: Int, inferred: Value, expected: Term) {
    val infTerm = quote(i, inferred)
    if (infTerm != expected) {
      throw new TypeError(s"inferred: ${pprint(infTerm)}, expected: ${pprint(expected)}")
    }
  }

  def checkEqual(i: Int, inferred: Value, expected: Value) {
    val infTerm = quote(i, inferred)
    val expTerm = quote(i, expected)
    if (infTerm != expTerm) {
      throw new TypeError(s"inferred: ${pprint(infTerm)}, expected: ${pprint(expTerm)}")
    }
  }

  // todo: eval with bound!!!
  def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Ann(e, tp) =>
      val tpVal = eval(tp, named, Nil)

      val tpType = iType(i, named, bound, tp)
      checkEqual(i, tpType, Star)

      val eType = iType(i, named, bound, e)
      checkEqual(i, eType, tpVal)

      tpVal
    case Star =>
      VStar
    case Pi(x, tp) =>
      val xVal = eval(x, named, Nil)

      val xType = iType(i, named, bound, x)
      checkEqual(i, xType, Star)

      val tpType = iType(i + 1, named,  bound + (Local(i) -> xVal), iSubst(0, Free(Local(i)), tp))
      checkEqual(i, tpType, Star)

      VStar
    case Free(x) =>
      bound.get(x) match {
        case Some(ty) => ty
        case None => sys.error(s"unknown id: $x")
      }
    case (e1 :@: e2) =>
      iType(i, named, bound, e1) match {
        case VPi(x, f) =>
          val e2Type = iType(i, named, bound, e2)
          checkEqual(i, e2Type, x)

          f(eval(e2, named, Nil))
        case _ =>
          sys.error(s"illegal application: $t")
      }
    case Lam(t, e) =>
      val tVal = eval(t, named, Nil)
      val tType = iType(i, named, bound, t)

      checkEqual(i, tType, Star)

      VPi(tVal, v => iType(i + 1, named + (Local(i) -> v), bound + (Local(i) -> tVal) , iSubst(0, Free(Local(i)), e)))
  }

  def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Ann(c, c1) =>
      Ann(iSubst(i, r, c), iSubst(i, r, c1))
    case Star =>
      Star
    case Lam(t, e) =>
      Lam(iSubst(i, r, t), iSubst(i + 1, r, e))
    case Pi(ty, ty1) =>
      Pi(iSubst(i, r, ty), iSubst(i + 1, r, ty1))
    case Bound(j) =>
      if (i == j) r else Bound(j)
    case Free(y) =>
      Free(y)
    case (e1 :@: e2) =>
      iSubst(i, r, e1) @@ iSubst(i, r, e2)
  }
}

trait CoreREPL extends CoreAST with CorePrinter with CoreEval with CoreCheck with CoreQuote with REPL {
  import scala.util.parsing.combinator.{PackratParsers, ImplicitConversions}
  import scala.language.postfixOps
  type T = Term
  type V = Value
  override lazy val int = new CoreInterpreter

  trait CoreParser extends Interpreter with PackratParsers with ImplicitConversions {
    lexical.reserved += ("assume", "let", "forall", "import", "sc", "sc2")
    lexical.delimiters += ("(", ")", "::", ":=", "->", "=>", ":", "*", "=", "\\", ";", ".", "<", ">", ",")

    type C = List[String]
    type Res[A] = C => A

    lazy val term: PackratParser[Res[Term]] =
        maybeTyped ~ ("->" ~> term) ^^ {case x ~ y => ctx: C => Pi(x(ctx), y("" :: ctx))} |
        maybeTyped
    lazy val maybeTyped: PackratParser[Res[Term]] =
      app ~ ("::" ~> term) ^^ {case e ~ t => ctx: C => Ann(e(ctx), t(ctx))} |
        ("(" ~> lam <~ ")") ~ ("::" ~> term) ^^ {case e ~ t => ctx: C => Ann(e(ctx), t(ctx))} |
        ("(" ~> forall <~ ")") ~ ("::" ~> term) ^^ {case e ~ t => ctx: C => Ann(e(ctx), t(ctx))} |
        app | lam | forall
    lazy val app: PackratParser[Res[Term]] =
      (aTerm+) ^^ {ts => ctx: C => ts.map{_(ctx)}.reduce{_ @@ _} }
    lazy val aTerm: PackratParser[Res[Term]] = // atomicTerm
      ident ^^ {i => ctx: C => ctx.indexOf(i) match {case -1 => Free(Global(i)) case j => Bound(j)}} |
        "<" ~> numericLit <~ ">" ^^ {x => ctx: C => Free(Local(x.toInt))} |
        "(" ~> term <~ ")" | numericLit ^^ {x => ctx: C => toNat(x.toInt)} |
        "*" ^^^ {ctx: C => Star}

    lazy val forallBs: PackratParser[Res[Term]] = {
      "." ~> term |
        bindingPar ~ forallBs ^^ { case b ~ t1 => ctx: C =>
          val bb = b(ctx)
          val t = bb._2
          Pi(t, t1(bb._1 :: ctx))
        }
    }
    lazy val lamBs: PackratParser[Res[Term]] = {
      "->" ~> term |
        bindingPar ~ lamBs ^^ { case b ~ t1 => ctx: C =>
          val bb = b(ctx)
          val t = bb._2
          Lam(t, t1(bb._1 :: ctx))
        }
    }
    lazy val forall: PackratParser[Res[Term]] =
      ("forall" ~> bindingPar) ~ forallBs ^^ { case b ~ t1 => ctx: C =>
        val bb = b(ctx)
        val t = bb._2
        Pi(t, t1(bb._1 :: ctx))
      }
    lazy val lam: PackratParser[Res[Term]] =
      ("\\" ~> bindingPar) ~ lamBs ^^ {case b ~ t1 => ctx: C =>
          val id = b(ctx)._1
          val t = b(ctx)._2
          var res = Lam(t, t1(id :: ctx))
          res
        }

    lazy val bindingPar: PackratParser[Res[(String, Term)]] =
      "(" ~> (ident ~ ("::" ~> term)) <~ ")" ^^ {case i ~ x => ctx: C => (i, x(ctx))}

    lazy val stmt: PackratParser[Stmt[Term, Term]] = stmts.reduce( _ | _)
    lazy val stmts = List(letStmt, assumeStmt, importStmt, evalStmt)
    lazy val letStmt: PackratParser[Stmt[Term, Term]] =
      "let" ~> ident ~ ("=" ~> term <~ ";") ^^ {case x ~ y => Let(x, y(Nil))}
    lazy val assumeStmt: PackratParser[Stmt[Term, Term]] =
      "assume" ~> bindingPar <~ ";" ^^ {b => Assume(List(b(Nil)))}
    lazy val importStmt: PackratParser[Stmt[Term, Term]] =
      "import" ~> stringLit <~ ";" ^^ Import
    lazy val evalStmt: PackratParser[Stmt[Term, Term]] =
      term <~ ";" ^^ {t => Eval(t(Nil))}
  }

  class CoreInterpreter extends CoreParser {
    val prompt: String = "TT> "

    override def itype(ne: NameEnv[Value], ctx: NameEnv[Value], i: Term): Result[Value] =
      try {
        Right(iType0(ne, ctx, i))
      } catch {
        case e: Throwable =>
          e.printStackTrace()
          Left(e.getMessage)
      }
    override def iquote(v: Value): Term =
      quote0(v)
    override def ieval(ne: NameEnv[Value], i: Term): Value =
      eval(i, ne, List())
    def typeInfo(t: Value): Value =
      t
    override def icprint(c: Term): String =
      pretty(print(0, 0, c))
    override def itprint(t: Value): String =
      pretty(print(0, 0, quote0(t)))
    def assume(state: State, x: (String, Term)): State = {
      itype(state.ne, state.ctx, Ann(x._2, Star)) match {
        case Right(_) =>
          val v = ieval(state.ne, Ann(x._2, Star))
          output(v)
          state.copy(ctx = state.ctx + (Global(x._1) -> v))
        case Left(_) =>
          state
      }
    }
    override lazy val iParse: Parser[Term] = term ^^ {_(Nil)}
    override val stmtParse: Parser[Stmt[Term, Term]] = stmt
  }
  def toNat(i: Int): Term = sys.error("not implemented")
}
