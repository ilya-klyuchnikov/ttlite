package superspec.tt

trait WAST extends CoreAST {
  case class W(t1: Term, t2: Term) extends Term
  case class Sup(w: Term, t1: Term, t2: Term) extends Term
  // w elim, a - is w, need to re-order later
  case class Rec(w: Term, m: Term, b: Term, a: Term) extends Term

  case class VW(t1: Value, t2: Value => Value) extends Value
  case class VSup(w: Value, t1: Value, t2: Value) extends Value
  case class NRec(w: Value, m: Value, b: Value, a: Neutral) extends Neutral
}

trait WMetaSyntax extends CoreMetaSyntax with WAST {
  override def fromM(m: MTerm): Term = m match {
    case MBind("W", t1, t2) =>
      W(fromM(t1), fromM(t2))
    case MVar(Global("Sup")) @@ sigma @@ e1 @@ e2 =>
      Sup(fromM(sigma), fromM(e1), fromM(e2))
    case MVar(Global("Rec")) @@ w @@ m @@ a @@ b =>
      Rec(fromM(w), fromM(m), fromM(a), fromM(b))
    case _ => super.fromM(m)
  }
}

trait WPrinter extends FunPrinter with WAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case W(d, r) =>
      parensIf(p > 0, sep(Seq("W " <> parens(vars(ii) <> " :: " <> print(0, ii, d)) <> " .", nest(print(0, ii + 1, r)))))
    case Sup(s, a, b) =>
      print(p, ii, 'Sup @@ s @@ a @@ b)
    case Rec(w, m, a, b) =>
      print(p, ii, 'Rec @@ w @@m @@ a @@ b)
    case _ =>
      super.print(p, ii, t)
  }
}

trait WQuote extends CoreQuote with WAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VW(v, f) =>
      W(quote(ii, v), quote(ii + 1, f(vfree(Quote(ii)))))
    case VSup(sigma, e1, e2) =>
      Sup(quote(ii, sigma), quote(ii, e1), quote(ii, e2))
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NRec(w, m, a, b) =>
      Rec(quote(ii, w), quote(ii, m), quote(ii, a), neutralQuote(ii, b))
    case _ => super.neutralQuote(ii, n)
  }
}

trait WEval extends FunEval with WAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case W(t1, t2) =>
      VW(eval(t1, named, bound), x => eval(t2, named, x :: bound))
    case Sup(w, e1, e2) =>
      VSup(eval(w, named, bound), eval(e1, named, bound), eval(e2, named, bound))
    case Rec(w, m, b, a) =>
      val wVal = eval(w, named, bound)
      val mVal = eval(m, named, bound)
      val aVal = eval(a, named, bound)
      val bVal = eval(b, named, bound)
      rec(wVal, mVal, bVal, aVal)
    case _ =>
      super.eval(t, named, bound)
  }


  def rec(wVal: Value, mVal: Value, bVal: Value, aVal: Value): Value = aVal match {
    case VSup(_, d, e) =>
      // wrec(sup(d, e), b) = b(d, e, (x)wrec(e(x), b))
      val VW(t1, t2) = wVal
      bVal @@ d @@ e @@
        VLam(VPi(t2(d), y => mVal @@ (e @@ y)), x => rec(wVal, mVal, bVal, e @@ x))
    case VNeutral(n) =>
      VNeutral(NRec(wVal, mVal, bVal, n))
  }
}

trait WCheck extends FunCheck with WAST {
  override def iType(i: Int, ctx: Context[Value], t: Term): Value = t match {
    case W(x, tp) =>
      val xVal = eval(x, ctx.vals, Nil)

      val xType = iType(i, ctx, x)
      val j = checkUniverse(i, xType)

      val tpType = iType(i + 1, Context(ctx.vals, ctx.types + (Local(i) -> xVal)), iSubst(0, Free(Local(i)), tp))
      val k = checkUniverse(i, tpType)

      VUniverse(math.max(j, k))
    case Sup(w, a, f) =>
      eval(w, ctx.vals, Nil) match {
        case VW(a1, f1) =>

          val aType = iType(i, ctx, a)
          checkEqual(i, aType, a1)

          val aVal = eval(a, ctx.vals, Nil)

          val fType = iType(i, ctx, f)
          checkEqual(i, fType, VPi(f1(aVal), _ => VW(a1, f1)))

          VW(a1, f1)
        case _ =>
          sys.error(s"illegal application: $t")
      }
    case Rec(w, m, b, a) =>
      val wType = iType(i, ctx, w)
      checkUniverse(i, wType)
      val VW(t1, t2) = eval(w, ctx.vals, List())

      val mVal = eval(m, ctx.vals, List())

      val mType = iType(i, ctx, m)
      checkEqual(i, mType, VPi(VW(t1, t2), {_ => VUniverse(-1)}))

      val aType = iType(i, ctx, a)
      checkEqual(i, aType, VW(t1, t2))
      val aVal = eval(a, ctx.vals, List())

      val bType = iType(i, ctx, b)
      checkEqual(i, bType,
        VPi(t1, a1 =>
          VPi(VPi(t2(a1), _ => VW(t1, t2)), f =>
            VPi(VPi(t2(a1), y => mVal @@ (f @@ y)), _ =>
              mVal @@ VSup(VW(t1, t2), a1, f))))
      )

      mVal @@ aVal
    case _ =>
      super.iType(i, ctx, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case W(t1, t2) =>
      W(iSubst(i, r, t1), iSubst(i + 1, r, t2))
    case Sup(sigma, e1, e2) =>
      Sup(iSubst(i, r, sigma), iSubst(i, r, e1), iSubst(i, r, e2))
    case Rec(w, m, e1, e2) =>
      Rec(iSubst(i, r, w), iSubst(i, r, m), iSubst(i, r, e1), iSubst(i, r, e2))
    case _ => super.iSubst(i, r, it)
  }
}

trait WREPL
  extends CoreREPL
  with WAST
  with WMetaSyntax
  with WPrinter
  with WCheck
  with WEval
  with WQuote