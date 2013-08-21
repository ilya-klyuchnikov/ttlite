package superspec.tt

import org.kiama.output.PrettyPrinter

trait CoreAST {
  trait Term {
    def @@(t1: Term) = :@:(this, t1)
  }
  case class Pi(c1: Term, c2: Term) extends Term
  case class Lam(t: Term, e: Term) extends Term
  case class :@:(h: Term, t: Term) extends Term

  case class Ann(c1: Term, ct2: Term) extends Term
  case object Star extends Term
  case class Bound(i: Int) extends Term
  case class Free(n: Name) extends Term

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

trait MCore extends CoreAST {
  def fromM(m: MTerm): Term = m match {
    case MVar(Global("*")) =>
      Star
    case MVar(Quote(i)) =>
      Bound(i)
    case MVar(n) =>
      Free(n)
    case MAnn(t1, t2) =>
      Ann(fromM(t1), fromM(t2))
    case MVar(Global("elim")) @@ tp =>
      sys.error(s"incorrect eliminator: $m")
    case MBind("forall", t1, t2) =>
      Pi(fromM(t1), fromM(t2))
    case MBind("\\", t1, t2) =>
      Lam(fromM(t1), fromM(t2))
    case t1 @@ t2 =>
      fromM(t1) @@ fromM(t2)
  }
}

trait CorePrinter extends CoreAST with PrettyPrinter {
  def parensIf(b: Boolean, d: Doc) =
    if (b) parens(d) else d
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
      parensIf(p > 0, sep(Seq("forall " <> parens(vars(ii) <> " :: " <> print(0, ii, d)) <> " .", nest(print(0, ii + 1, r)))))
    case Bound(k) if ii - k - 1 >= 0 =>
      vars(ii - k - 1)
    case Free(Global(s)) =>
      s
    case Free(Assumed(s)) =>
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

  // the possible problem is here!!!
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

  // todo: eval with bound - do we need it?? !!!
  def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    // TODO: universes
    case Star => VStar
    case Ann(e, Star) =>
      val eType = iType(i, named, bound, e)
      checkEqual(i, eType, VStar)
      VStar
    case Ann(e, tp) =>
      val tpVal = eval(tp, named, Nil)

      val tpType = iType(i, named, bound, tp)
      checkEqual(i, tpType, Star)

      val eType = iType(i, named, bound, e)
      checkEqual(i, eType, tpVal)

      tpVal

    case Pi(Star, tp) =>
      val tpType = iType(i + 1, named,  bound + (Local(i) -> VStar), iSubst(0, Free(Local(i)), tp))
      checkEqual(i, tpType, Star)
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

    case Lam(Star, e) =>
      // to force early error
      iType(i + 1, named,  bound + (Local(i) -> VStar), iSubst(0, Free(Local(i)), e))
      VPi(VStar, v => iType(i + 1, named + (Local(i) -> v), bound + (Local(i) -> VStar) , iSubst(0, Free(Local(i)), e)))
    case Lam(t, e) =>
      val tVal = eval(t, named, Nil)
      val tType = iType(i, named, bound, t)

      checkEqual(i, tType, Star)
      // to force early error
      iType(i + 1, named,  bound + (Local(i) -> tVal), iSubst(0, Free(Local(i)), e))

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

trait CoreREPL2 extends CoreAST with MCore with CorePrinter with CoreEval with CoreCheck with CoreQuote with MREPL {
  type T = Term
  type V = Value

  val prompt: String = "TT"

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
    x._2 match {
      case Star =>
        output(icprint(iquote(VStar)))
        state.copy(ctx = state.ctx + (s2name(x._1) -> VStar))
      case _ =>
        itype(state.ne, state.ctx, Ann(x._2, Star)) match {
          case Right(_) =>
            val v = ieval(state.ne, Ann(x._2, Star))
            output(icprint(iquote(v)))
            state.copy(ctx = state.ctx + (s2name(x._1) -> v))
          case Left(_) =>
            state
        }
    }
  }

  def s2name(s: String): Name =
    if (s.startsWith("$")) Assumed(s) else Global(s)

}
