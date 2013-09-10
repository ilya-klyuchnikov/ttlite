package superspec.tt

import org.kiama.output.PrettyPrinter

trait CoreAST {
  trait Term
  case class Ann(c1: Term, ct2: Term) extends Term
  case class Bound(i: Int) extends Term
  case class Free(n: Name) extends Term

  case class Universe(i: Int) extends Term {
    override def equals(that: Any) = that match {
      case Universe(k) => i == k || i == -1 || k == -1
      case _ => false
    }
  }

  trait Value
  case class VUniverse(i: Int) extends Value
  case class VNeutral(n: Neutral) extends Value
  trait Neutral
  case class NFree(n: Name) extends Neutral

  type Env = List[Value]
  val emptyNEnv = Map[Name, Value]()

  def vfree(n: Name): Value = VNeutral(NFree(n))
  implicit def sym2val(s: Symbol): Value =
    VNeutral(NFree(Global(s.name)))
  implicit def sym2Term(s: Symbol): Term =
    Free(Global(s.name))
  implicit def s2val(s: String): Value =
    VNeutral(NFree(Global(s)))
  implicit def s2Term(s: String): Term =
    Free(Global(s))
}

trait CoreMetaSyntax extends CoreAST {
  def fromM(m: MTerm): Term = m match {
    case MVar(Global("Set")) =>
      Universe(0)
    case MVar(Global("Set0")) =>
      Universe(0)
    case MVar(Global("Set1")) =>
      Universe(1)
    case MVar(Global("Set2")) =>
      Universe(2)
    case MVar(Quote(i)) =>
      Bound(i)
    case MVar(n) =>
      Free(n)
    case MAnn(t1, t2) =>
      Ann(fromM(t1), fromM(t2))
    case MVar(Global("elim")) @@ tp =>
      sys.error(s"incorrect eliminator: $m")
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
    case Universe(i) =>
      s"Set$i"
    case Bound(k) if ii - k - 1 >= 0 =>
      vars(ii - k - 1)
    case Free(n) =>
      n.toString
    case _ =>
      t.toString
  }
}

trait CoreQuote extends CoreAST {
  def quote0(v: Value): Term =
    quote(0, v)

  def quote(ii: Int, v: Value): Term = v match {
    case VUniverse(i) =>
      Universe(i)
    case VNeutral(n) =>
      neutralQuote(ii, n)
  }

  def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NFree(x) => boundFree(ii, x)
  }

  private def boundFree(ii: Int, n: Name): Term = n match {
    // "shift hack" - for beta reduction
    case Quote(k) if ii - k - 1 == 0 =>
      Bound(0)
    case Quote(k) =>
      Bound(ii - k - 1)
    case x =>
      Free(x)
  }
}

trait CoreEval extends CoreAST {
  def eval0(c: Term): Value = eval(c, emptyContext[Value], Nil)
  @deprecated
  def eval(t: Term, named: NameEnv[Value], bound: Env): Value =
    eval(t, Context(named, emptyEnv), bound)
  def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Ann(e, _) =>
      eval(e, ctx, bound)
    case Universe(i) =>
      VUniverse(i)
    case Free(x) =>
      ctx.vals.getOrElse(x, vfree(x))
    case Bound(ii) =>
      if (ii < bound.length) bound(ii) else vfree(Quote(ii))
  }
}

trait CoreCheck extends CoreAST with CoreQuote with CoreEval with CorePrinter {
  def iType0(ctx: Context[Value], i: Term): Value =
    iType(0, ctx, i)

  def checkEqual(i: Int, inferred: Term, expected: Term) {
    if (inferred != expected) {
      throw new TypeError(s"inferred: ${pprint(inferred)},\n expected: ${pprint(expected)}")
    }
  }

  def checkEqual(i: Int, inferred: Value, expected: Term) {
    val infTerm = quote(i, inferred)
    if (infTerm != expected) {
      throw new TypeError(s"inferred: ${pprint(infTerm)},\n expected: ${pprint(expected)}")
    }
  }

  def checkEqual(i: Int, inferred: Value, expected: Value) {
    val infTerm = quote(i, inferred)
    val expTerm = quote(i, expected)
    if (infTerm != expTerm) {
      throw new TypeError(s"inferred: ${pprint(infTerm)},\n expected: ${pprint(expTerm)}")
    }
  }

  def checkUniverse(i: Int, inferred: Value): Int = inferred match {
    case VUniverse(k) =>
      k
    case _ =>
      val infTerm = quote(i, inferred)
      throw new TypeError(s"inferred: ${pprint(infTerm)},\n expected: Set(_)")
  }

  def iType(i: Int, ctx: Context[Value], t: Term): Value = t match {
    case Universe(i) =>
      VUniverse(i + 1)
    case Ann(e, tp) =>
      val tpVal = eval(tp, ctx, Nil)

      val tpType = iType(i, ctx, tp)
      checkUniverse(i, tpType)

      val eType = iType(i, ctx, e)
      checkEqual(i, eType, tpVal)

      tpVal
    case Free(x) =>
      ctx.types.get(x) match {
        case Some(ty) => ty
        case None => sys.error(s"unknown id: $x")
      }
  }

  def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Ann(c, c1) =>
      Ann(iSubst(i, r, c), iSubst(i, r, c1))
    case Universe(k) =>
      Universe(k)
    case Bound(j) =>
      if (i == j) r else Bound(j)
    case Free(y) =>
      Free(y)
  }
}

trait CoreREPL extends CoreAST with CoreMetaSyntax with CorePrinter with CoreEval with CoreCheck with CoreQuote with REPL {
  type T = Term
  type V = Value

  val prompt: String = "TT"

  override def itype(ctx: Context[V], i: T): Result[V] =
    try {
      Right(iType0(ctx, i))
    } catch {
      case e: Throwable =>
        e.printStackTrace()
        Left(e.getMessage)
    }
  override def iquote(v: V): Term =
    quote0(v)
  override def ieval(ctx: Context[V], i: T): V =
    eval(i, ctx, List())
  def typeInfo(t: V): V =
    t
  override def icprint(c: T): String =
    pretty(print(0, 0, c))
  override def itprint(t: V): String =
    pretty(print(0, 0, quote0(t)))
  def assume(state: Context[V], x: String, t: Term): Context[V] = {
    itype(state, t) match {
      case Right(VUniverse(k)) =>
        val v = ieval(state, Ann(t, Universe(k)))
        output(icprint(iquote(v)))
        state.copy(types = state.types + (s2name(x) -> v))
      case Right(_) =>
        handleError("not a type")
        state
      case Left(_) =>
        handleError("type error")
        state
    }
  }
  def handleTypedLet(state: Context[V], s: String, t: T, tp: T): Context[V] =
    handleLet(state, s, Ann(t, tp))

  def s2name(s: String): Name =
    if (s.startsWith("$")) Assumed(s) else Global(s)

}
