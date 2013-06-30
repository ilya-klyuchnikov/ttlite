package superspec.tt

trait CoreCheck extends CoreAST with CoreQuote with CoreEval with CorePrinter {
  def iType0(named: NameEnv[Value], bound: NameEnv[Value], i: Term): Value =
    iType(0, named, bound, i)

  def checkEqual(inferred: Term, expected: Term) {
    if (inferred != expected) {
       throw new TypeError(s"inferred: ${pprint(inferred)}, expected: ${pprint(expected)}")
    }
  }

  def checkEqual(inferred: Value, expected: Term) {
    val infTerm = quote0(inferred)
    if (infTerm != expected) {
      throw new TypeError(s"inferred: ${pprint(infTerm)}, expected: ${pprint(expected)}")
    }
  }

  def checkEqual(inferred: Value, expected: Value) {
    val infTerm = quote0(inferred)
    val expTerm = quote0(expected)
    if (infTerm != expTerm) {
      throw new TypeError(s"inferred: ${pprint(infTerm)}, expected: ${pprint(expTerm)}")
    }
  }

  def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Ann(e, tp) =>
      val tpType = iType(i, named, bound, tp)
      checkEqual(tpType, Star)
      val tpNorm = eval(tp, named, Nil)
      val eType = iType(i, named, bound, e)
      checkEqual(eType, tpNorm)
      tpNorm
    case Star =>
      VStar
    case Pi(x, tp) =>
      val xType = iType(i, named, bound, x)
      checkEqual(xType, Star)
      val xNorm = eval(x, named, Nil)
      val tpType = iType(i + 1, named,  bound + (Local(i) -> xNorm), iSubst(0, Free(Local(i)), tp))
      checkEqual(tpType, Star)
      VStar
    case Free(x) =>
      bound.get(x) match {
        case Some(ty) => ty
        case None => sys.error(s"unknown id: $x")
      }
    case (e1 :@: e2) =>
      iType(i, named, bound, e1) match {
        case VPi(argType, bodyType) =>
          val e2Type = iType(i, named, bound, e2)
          checkEqual(e2Type, argType)
          bodyType(eval(e2, named, Nil))
        case _ =>
          sys.error(s"illegal application: $t")
      }
    case Lam(t, e) =>
      val tType = iType(i, named, bound, t)
      checkEqual(tType, Star)
      val tNorm = eval(t, named, Nil)
      VPi(tNorm, v => iType(i + 1, named + (Local(i) -> v), bound + (Local(i) -> tNorm) , iSubst(0, Free(Local(i)), e)))
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
