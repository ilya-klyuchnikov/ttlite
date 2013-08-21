package superspec.tt

trait FunAST extends CoreAST {
  case class Pi(c1: Term, c2: Term) extends Term
  case class Lam(t: Term, e: Term) extends Term
  case class :@:(h: Term, t: Term) extends Term

  case class VPi(t: Value, e: Value => Value) extends Value
  case class VLam(t: Value, e: Value => Value) extends Value
  case class NApp(n: Neutral, v: Value) extends Neutral

  implicit class TApplicable(t: Term) {
    def @@(t1: Term) = :@:(t, t1)
  }
  implicit class VApplicable(v: Value) {
    def @@(v1: Value) = v match {
      case VLam(_, f) => f(v1)
      case VNeutral(n) => VNeutral(NApp(n, v1))
    }
  }
  implicit def sym2appV(s: Symbol): VApplicable =
    VNeutral(NFree(Global(s.name)))
  implicit def sym2appT(s: Symbol): TApplicable =
    Free(Global(s.name))
}

trait MFun extends MCore with FunAST {
  override def fromM(m: MTerm): Term = m match {
    case MBind("forall", t1, t2) =>
      Pi(fromM(t1), fromM(t2))
    case MBind("\\", t1, t2) =>
      Lam(fromM(t1), fromM(t2))
    case t1 @@ t2 =>
      fromM(t1) @@ fromM(t2)
    case _ => super.fromM(m)
  }
}

trait FunPrinter extends CorePrinter with FunAST {
  // todo: nested lam
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Pi(d, Pi(d1, r)) =>
      parensIf(p > 0, nestedForall(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Pi(d, r) =>
      parensIf(p > 0, sep(Seq("forall " <> parens(vars(ii) <> " :: " <> print(0, ii, d)) <> " .", nest(print(0, ii + 1, r)))))
    case Lam(t, c) =>
      parensIf(p > 0,  "\\ " <> parens(vars(ii) <> " :: " <> print(0, ii, t)) <> " -> " <> nest(print(0, ii + 1, c)))
    case i :@: c =>
      parensIf(p > 2, sep(Seq(print(2, ii, i), nest(print(3, ii, c)))))
    case _ =>
      super.print(p, ii, t)
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

trait FunQuote extends CoreQuote with FunAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VPi(v, f) =>
      Pi(quote(ii, v), quote(ii + 1, f(vfree(Quote(ii)))))
    case VLam(t, f) =>
      Lam(quote(ii, t), quote(ii + 1, f(vfree(Quote(ii)))))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NApp(n, v) =>
      neutralQuote(ii, n) @@ quote(ii, v)
    case _ => super.neutralQuote(ii, n)
  }
}

trait FunEval extends CoreEval with FunAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Pi(ty, ty1) =>
      VPi(eval(ty, named, bound), x => eval(ty1, named, x :: bound))
    case Lam(t, e) =>
      VLam(eval(t, named, bound), x => eval(e, named, x :: bound))
    case e1 :@: e2 =>
      eval(e1, named, bound) @@ eval(e2, named, bound)
    case _ =>
      super.eval(t, named, bound)
  }
}

trait FunCheck extends CoreCheck with FunAST {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
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
    case (e1 :@: e2) =>
      iType(i, named, bound, e1) match {
        case VPi(x, f) =>
          val e2Type = iType(i, named, bound, e2)
          checkEqual(i, e2Type, x)
          f(eval(e2, named, Nil))
        case _ =>
          sys.error(s"illegal application: $t")
      }
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Pi(ty, ty1) =>
      Pi(iSubst(i, r, ty), iSubst(i + 1, r, ty1))
    case Lam(t, e) =>
      Lam(iSubst(i, r, t), iSubst(i + 1, r, e))
    case (e1 :@: e2) =>
      iSubst(i, r, e1) @@ iSubst(i, r, e2)
    case _ => super.iSubst(i, r, it)
  }
}

trait FunREPL2 extends CoreREPL2 with FunAST with MFun with FunPrinter with FunCheck with FunEval with FunQuote