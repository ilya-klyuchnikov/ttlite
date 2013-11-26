package ttlite.core

import ttlite.common._

trait CoreAST {
  trait Term
  case class Ann(c1: Term, ct2: Term) extends Term
  case class Bound(i: Int) extends Term
  // TODO something line generated name/var
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

  // freeVars of an expression
  def freeVars(t: Any): List[Name] = t match {
    case Free(n: Local)   => List(n)
    case Free(n: Assumed) => List(n)
    case p: scala.Product => p.productIterator.flatMap(freeVars).toList.distinct
    case _                => List()
  }
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
    case MVar(Global("elim")) =>
      throw TranslationError(m, s"incorrect eliminator")
    case MVar(Quote(i)) =>
      Bound(i)
    case MVar(n) =>
      Free(n)
    case MAnn(t1, t2) =>
      Ann(fromM(t1), fromM(t2))
    case _ =>
      throw TranslationError(m, s"incorrect syntax `${m.origin}`")
  }
}

trait CorePrinter extends CoreAST with PrettyPrinter {
  def pp(c: Term): String =
    pretty(print(0, 0, c))

  def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Ann(c, ty) =>
      parensIf(p > 1, nest(sep(Seq(print(2, ii, c) <> " : " , nest(print(0, ii, ty))))))
    case Universe(-1) =>
      "Set*"
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

trait CorePrinterAgda extends CoreAST with PrettyPrinter {
  def ppa(c: Term): String =
    pretty(printA(0, 0, c))

  def printA(p: Int, ii: Int, t: Term): Doc = t match {
    case Universe(-1) =>
      "Set*"
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
  def eval0(c: Term): Value = eval(c, Context.empty[Value], Nil)
  @deprecated // used in residuator
  def eval(t: Term, named: NameEnv[Value], bound: Env): Value =
    eval(t, Context.fromVals(named), bound)
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
    iType(0, Path.empty, ctx, i)

  def checkEqual(i: Int, inferred: Term, expected: Term, path : Path) {
    if (inferred != expected) {
      throw new TypeError(s"expected: ${pp(expected)},\ninferred: ${pp(inferred)}", path)
    }
  }

  def checkEqual(i: Int, inferred: Value, expected: Term, path : Path) {
    val infTerm = quote(i, inferred)
    if (infTerm != expected) {
      throw new TypeError(s"expected: ${pp(expected)},\ninferred: ${pp(infTerm)}}", path)
    }
  }

  def checkEqual(i: Int, inferred: Value, expected: Value, path : Path) {
    val infTerm = quote(i, inferred)
    val expTerm = quote(i, expected)
    if (infTerm != expTerm) {
      throw new TypeError(s"expected: ${pp(expTerm)},\ninferred: ${pp(infTerm)}", path)
    }
  }

  def checkUniverse(i: Int, inferred: Value, path : Path): Int = inferred match {
    case VUniverse(k) =>
      k
    case _ =>
      val infTerm = quote(i, inferred)
      throw new TypeError(s"expected: Set*,\ninferred: ${pp(infTerm)}", path)
  }

  def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value = t match {
    case Universe(i) =>
      VUniverse(i + 1)
    case Ann(e, tp) =>
      val tpVal = eval(tp, ctx, Nil)

      val tpType = iType(i, path/(2, 2), ctx, tp)
      checkUniverse(i, tpType, path/(2, 2))

      val eType = iType(i, path/(1, 2), ctx, e)
      checkEqual(i, eType, tpVal, path/(1, 2))

      tpVal
    case Free(x) =>
      ctx.types.get(x) match {
        case Some(ty) => ty
        case None => throw TypeError(s"unknown id: $x", path)
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

trait CoreREPL extends CoreAST with CoreMetaSyntax with CorePrinter with CorePrinterAgda with CoreEval with CoreCheck with CoreQuote with REPL {
  type T = Term
  type V = Value

  val prompt: String = "TT"

  override def itype(ctx: Context[V], i: T): V =
    iType0(ctx, i)
  override def iquote(v: V): Term =
    quote0(v)
  override def ieval(ctx: Context[V], i: T): V =
    eval(i, ctx, List())
  def typeInfo(t: V): V =
    t
  override def tPrint(c: T): String =
    pp(c)
  override def tPrintAgda(c: T): String =
    pretty(nest(printA(0, 0, c)))
  override def fvs(c : T) : List[Name] =
    freeVars(c)
  def assume(state: Context[V], x: String, t: Term): Context[V] = {
    val tp = itype(state, t)
    checkEqual(0, tp, VUniverse(-1), Path.empty)
    val v = ieval(state, t)
    output(tPrint(iquote(v)))
    state.addAssumed(x, v)
  }
  def handleTypedLet(state: Context[V], s: String, t: T, tp: T): Context[V] =
    handleLet(state, s, Ann(t, tp))

  //def s2name(s: String): Name =
    //if (s.startsWith("$")) Assumed(s) else Global(s)

}
