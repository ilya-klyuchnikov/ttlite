package ttlite.core

import ttlite.common._

trait CoreAST extends AST {
  import scala.language.implicitConversions

  case class Ann(c1: Term, ct2: Term) extends Term
  case class Bound(i: Int) extends Term

  case class Universe(i: Int) extends Term {
    override def equals(that: Any): Boolean = that match {
      case Universe(k) => i == k || i == -1 || k == -1
      case _ => false
    }
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

trait CoreMetaSyntax extends CoreAST with MetaSyntax {
  def translate(m: MTerm): Term = m match {
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
      Ann(translate(t1), translate(t2))
    case _ =>
      throw TranslationError(m, s"incorrect syntax `${m.origin}`")
  }
}

trait CorePrinter extends CoreAST with Printer {
  import scala.collection.immutable.Seq

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

trait CorePrinterAgda extends CoreAST with PrinterAgda {
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

trait CorePrinterCoq extends CoreAST with PrinterCoq {
  def printC(p: Int, ii: Int, t: Term): Doc = t match {
    case Universe(-1) =>
      "Type"
    case Universe(_) =>
      "Type"
    case Bound(k) if ii - k - 1 >= 0 =>
      vars(ii - k - 1)
    case Free(Assumed(n)) =>
      s"${n.replace("$", "")}__"
    case Free(n) if n.toString == "if" =>
      "if__"
    case Free(n) =>
      n.toString
    case _ =>
      t.toString
  }
}

trait CorePrinterIdris extends CoreAST with PrinterIdris {
  def printI(p: Int, ii: Int, t: Term): Doc = t match {
    case Universe(_) =>
      "Type"
    case Bound(k) if ii - k - 1 >= 0 =>
      vars(ii - k - 1)
    case Free(Assumed(n)) =>
      s"${n.replace("$", "")}__"
    case Free(n) =>
      n.toString
    case _ =>
      t.toString
  }
}

trait CoreQuoting extends CoreAST with Quoting {
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

trait CoreEval extends CoreAST with Eval {
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

trait CoreCheck extends CoreAST with Quoting with Check {

  def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value = t match {
    case Universe(n) =>
      VUniverse(n + 1)
    case Ann(e, tp) =>
      val tpType = iType(i, path/(2, 2), ctx, tp)
      checkUniverse(i, tpType, path/(2, 2))

      val tpVal = eval(tp, ctx, Nil)

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

trait CoreREPL
  extends REPL
  with CoreAST
  with CoreMetaSyntax
  with CorePrinter
  with CorePrinterAgda
  with CorePrinterCoq
  with CorePrinterIdris
  with CoreEval
  with CoreCheck
  with CoreQuoting {

  type T = Term
  type V = Value

  val prompt: String = "TT"

  override def infer(ctx: Context[V], i: T): V =
    iType0(ctx, i)
  override def quote(v: V): Term =
    quote0(v)
  override def eval(ctx: Context[V], i: T): V =
    eval(i, ctx, List())
  override def pretty(c: T): String =
    pp(c)
  override def prettyAgda(c: T): String =
    pretty(nest(printA(0, 0, c)))
  override def prettyCoq(c: T): String =
    pretty(nest(printC(0, 0, c)))
  override def prettyIdris(c: T): String =
    pretty(nest(printI(0, 0, c)))
  def assume(state: Context[V], id: Id, t: Term): Context[V] = {
    val name = Assumed(id.n)
    if (state.ids.contains(name)) {
      throw DuplicateIdError(id)
    }
    val tp = infer(state, t)
    checkEqual(0, tp, VUniverse(-1), Path.empty)
    val v = eval(state, t)
    output(pretty(quote(v)))
    state.addType(name, v)
  }

}
