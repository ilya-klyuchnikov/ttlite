package superspec.tt

trait CoreCheck extends CoreAST with CoreQuote with CoreEval with CorePrinter {
  def iType0(named: NameEnv[Value], bound: NameEnv[Value], i: Term): Value =
    iType(0, named, bound, i)

  def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Ann(e, tyt) =>
      val tytType = iType(i, named, bound, tyt)
      assert(quote0(tytType) == Star, "wrong types")
      val ty = eval(tyt, named, Nil)
      val eType = iType(i, named, bound, e)
      assert(quote0(eType) == quote0(ty), "wrong types")
      ty
    case Star =>
      VStar
    case Pi(tyt, tyt1) =>
      val tytType = iType(i, named, bound, tyt)
      assert(quote0(tytType) == Star, "wrong types")
      val ty = eval(tyt, named, Nil)
      val tyt1Type = iType(i + 1, named,  bound + (Local(i) -> ty), iSubst(0, Free(Local(i)), tyt1))
      assert(quote0(tyt1Type) == Star, "wrong types")
      VStar
    case Free(x) =>
      bound.get(x) match {
        case Some(ty) => ty
        case None => sys.error(s"unknown id: $x")
      }
    case (e1 :@: e2) =>
      iType(i, named, bound, e1) match {
        case VPi(ty, ty1) =>
          val e2Type = iType(i, named, bound, e2)
          assert(quote0(ty) == quote0(e2Type), "wrong types")
          ty1(eval(e2, named, Nil))
        case _ =>
          sys.error(s"illegal application: $t")
      }
    case Lam(t, e) =>
      val tType = iType(i, named, bound, t)
      val tt = quote0(tType)
      assert(tt == Star, "wrong types")
      val ty = eval(t, named, Nil)
      VPi(ty, v => iType(i + 1, named + (Local(i) -> v), bound + (Local(i) -> ty) , iSubst(0, Free(Local(i)), e)))
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
