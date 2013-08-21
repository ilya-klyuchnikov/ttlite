package superspec.tt

import org.kiama.output.PrettyPrinter

trait CoreAST {
  trait Term
  case class Ann(c1: Term, ct2: Term) extends Term
  case object Star extends Term
  case class Bound(i: Int) extends Term
  case class Free(n: Name) extends Term

  trait Value
  case object VStar extends Value
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
    case VStar =>
      Star
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
  def eval0(c: Term): Value = eval(c, emptyNEnv, Nil)
  def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Ann(e, _) =>
      eval(e, named, bound)
    case Star =>
      VStar
    case Free(x) =>
      named.getOrElse(x, vfree(x))
    case Bound(ii) =>
      if (ii < bound.length) bound(ii) else vfree(Quote(ii))
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


    case Free(x) =>
      bound.get(x) match {
        case Some(ty) => ty
        case None => sys.error(s"unknown id: $x")
      }
  }

  def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Ann(c, c1) =>
      Ann(iSubst(i, r, c), iSubst(i, r, c1))
    case Star =>
      Star
    case Bound(j) =>
      if (i == j) r else Bound(j)
    case Free(y) =>
      Free(y)
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
