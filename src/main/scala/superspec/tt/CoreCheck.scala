package superspec.tt

// TODO: can we unify type-checking and evaluation -
trait CoreCheck extends CoreAST with CoreQuote with CoreEval with CorePrinter {
  def iType0(named: NameEnv[Value], bound: NameEnv[Value], i: ITerm): Value =
    iType(0, named, bound, i)

  def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: ITerm): Value = t match {
    case Ann(e, tyt) =>
      cType(i, named, bound, tyt, VStar)
      val ty = eval(tyt, named, Nil)
      cType(i, named, bound, e, ty)
      ty
    case Star =>
      VStar
    case Pi(tyt, tyt1) =>
      cType(i, named, bound, tyt, VStar)
      val ty = eval(tyt, named, Nil)
      cType(i + 1, named,  bound + (Local(i) -> ty), cSubst(0, Free(Local(i)), tyt1), VStar)
      VStar
    case Free(x) =>
      bound.get(x) match {
        case Some(ty) => ty
        case None => sys.error(s"unknown id: $x")
      }
    case (e1 :@: e2) =>
      iType(i, named, bound, e1) match {
        case VPi(ty, ty1) =>
          cType(i, named, bound, e2, ty)
          ty1(eval(e2, named, Nil))
        case _ =>
          sys.error(s"illegal application: $t")
      }
  }

  // checks that ct has type t
  // if not, it throws exception
  def cType(ii: Int, named: NameEnv[Value], bound: NameEnv[Value], ct: CTerm, t: Value):Unit = (ct, t) match {
    case (Inf(e), _) =>
      val ty1 = iType(ii, named, bound, e)
      if (quote0(ty1) != quote0(t))
        sys.error(s"type mismatch. inferred: ${pretty(cPrint(0, 0, quote0(ty1)))}. expected: ${pretty(cPrint(0, 0, quote0(t)))}. for expression ${pretty(iPrint(0, 0, e))}")
    case (Lam(e), VPi(ty, ty1)) =>
      cType(ii + 1, named,  bound + (Local(ii) -> ty) , cSubst(0, Free(Local(ii)), e), ty1(vfree(Local(ii))))
    case _ =>
      sys.error(s"type mismatch: $ct")
  }
  def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Ann(c, c1) => Ann(cSubst(i, r, c), cSubst(i, r, c1))
    case Star => Star
    case Pi(ty, ty1) => Pi(cSubst(i, r, ty), cSubst(i + 1, r, ty1))
    case Bound(j) => if (i == j) r else Bound(j)
    case Free(y) => Free(y)
    case (e1 :@: e2) => iSubst(i, r, e1) @@ cSubst(i, r, e2)
  }
  def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case Inf(e) => Inf(iSubst(ii, r, e))
    case Lam(e) => Lam(cSubst(ii + 1, r, e))
  }
}
