package superspec.tt

trait DProductAST extends CoreAST {
  case class Sigma(c1: Term, c2: Term) extends Term
  case class DPair(sigma: Term, t: Term, e: Term) extends Term
  case class SigmaElim(sigma: Term, m: Term, f: Term, pair: Term) extends Term

  case class VSigma(t: Value, e: Value => Value) extends Value
  case class VDPair(sigma: Value, t: Value, e: Value) extends Value
  case class NSigmaElim(sigma: Value, m: Value, f: Value, pair: Neutral) extends Neutral
}

trait MDProduct extends MCore with DProductAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("sigmaElim")) @@ sigma @@ m @@ f @@ p =>
      SigmaElim(fromM(sigma), fromM(m), fromM(f), fromM(p))
    case MVar(Global("dpair")) @@ sigma @@ e1 @@ e2 =>
      DPair(fromM(sigma), fromM(e1), fromM(e2))
    case MBind("exists", t1, t2) =>
      Sigma(fromM(t1), fromM(t2))
    case _ => super.fromM(m)
  }
}

trait DProductPrinter extends FunPrinter with DProductAST {

  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Sigma(d, Sigma(d1, r)) =>
      parens(nestedExists(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Sigma(d, r) =>
      parensIf(p > 0, sep(Seq("exists " <> parens(vars(ii) <> " :: " <> print(0, ii, d)) <> " .", nest(print(0, ii + 1, r)))))
    case DPair(s, a, b) =>
      print(p, ii, 'dpair @@ s @@ a @@ b)
    case SigmaElim(s, m, f, dp) =>
      print(p, ii, 'sigmaElim @@ s @@ m @@ f @@ dp)
    case _ =>
      super.print(p, ii, t)
  }

  def nestedExists(i: Int, fs: List[(Int, Term)], t: Term): Doc = t match {
    case Sigma(d, r) =>
      nestedExists(i + 1, (i, d) :: fs, r)
    case x =>
      val fors = fs.reverse.map{case (n,d) => parens(vars(n) <> " :: " <> nest(print(0, n, d)))}.toSeq
      val fors1 = fors.updated(fors.length - 1, fors(fors.length - 1) <> " .")
      nest(sep((text("exists") +: fors1).toSeq ++ Seq(print(0, i , x))))
  }
}

trait DProductQuote extends CoreQuote with DProductAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VSigma(v, f) =>
      Sigma(quote(ii, v), quote(ii + 1, f(vfree(Quote(ii)))))
    case VDPair(sigma, e1, e2) =>
      DPair(quote(ii, sigma), quote(ii, e1), quote(ii, e2))
    case _ => super.quote(ii, v)
  }

  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NSigmaElim(sigma, m, f, p) =>
      SigmaElim(quote(ii, sigma), quote(ii, m), quote(ii, f), neutralQuote(ii, p))
    case _ => super.neutralQuote(ii, n)
  }
}

trait DProductEval extends FunEval with DProductAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Sigma(ty, ty1) =>
      VSigma(eval(ty, named, bound), x => eval(ty1, named, x :: bound))
    case DPair(sigma, e1, e2) =>
      VDPair(eval(sigma, named, bound), eval(e1, named, bound), eval(e2, named, bound))
    case SigmaElim(sigma, m, f, p) =>
      val sigmaVal = eval(sigma, named, bound)
      val mVal = eval(m, named, bound)
      val fVal = eval(f, named, bound)
      val pVal = eval(p, named, bound)
      sigmaElim(sigmaVal, mVal, fVal, pVal)
    case _ =>
      super.eval(t, named, bound)
  }

  def sigmaElim(sigmaVal: Value, mVal: Value, fVal: Value, pVal: Value): Value = pVal match {
    case VDPair(_, x, y) => fVal @@ x @@ y
    case VNeutral(n) => VNeutral(NSigmaElim(sigmaVal, mVal, fVal, n))
  }
}

trait DProductCheck extends FunCheck with DProductAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Sigma(x, tp) =>
      val xVal = eval(x, named, Nil)

      val xType = iType(i, named, bound, x)
      val j = checkUniverse(i, xType)

      val tpType = iType(i + 1, named,  bound + (Local(i) -> xVal), iSubst(0, Free(Local(i)), tp))
      val k = checkUniverse(i, tpType)

      VUniverse(math.max(j, k))
    case DPair(sigma, x, y) =>
      eval(sigma, named, Nil) match {
        case VSigma(a, f) =>
          val xType = iType(i, named, bound, x)
          checkEqual(i, xType, a)

          val xVal = eval(x, named, Nil)

          val yType = iType(i, named, bound, y)
          checkEqual(i, yType, f(xVal))

          VSigma(a, f)
        case _ =>
          sys.error(s"illegal application: $t")
      }
    case SigmaElim(sigma, m, f, p) =>
      val sigmaType = iType(i, named, bound, sigma)
      checkUniverse(i, sigmaType)
      eval(sigma, named, Nil) match {
        case sigmaVal@VSigma(x1, x2) =>

          val pType = iType(i, named, bound, p)
          checkEqual(i, pType, sigmaVal)

          val pVal = eval(p, named, List())

          val mType = iType(i, named, bound, m)
          checkEqual(i, mType, VPi(sigmaVal, {_ => VUniverse(-1)}))

          val mVal = eval(m, named, List())

          val fType = iType(i, named, bound, f)
          checkEqual(i, fType, VPi(x1, {x => VPi(x2(x), y => mVal @@ VDPair(sigmaVal, x, y))}))

          mVal @@ pVal
        case _ =>
          sys.error(s"illegal application: $t")
      }
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Sigma(ty, ty1) =>
      Sigma(iSubst(i, r, ty), iSubst(i + 1, r, ty1))
    case DPair(sigma, e1, e2) =>
      DPair(iSubst(i, r, sigma), iSubst(i, r, e1), iSubst(i, r, e2))
    case SigmaElim(sigma, m, f, p) =>
      SigmaElim(iSubst(i, r, sigma), iSubst(i, r, m), iSubst(i, r, f), iSubst(i, r, p))
    case _ => super.iSubst(i, r, it)
  }

}

trait DProductREPL2
  extends CoreREPL2
  with DProductAST
  with MDProduct
  with DProductPrinter
  with DProductCheck
  with DProductEval
  with DProductQuote