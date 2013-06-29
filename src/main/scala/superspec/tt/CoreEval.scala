package superspec.tt

trait CoreEval extends CoreAST {
  def eval0(c: ITerm): Value = eval(c, emptyNEnv, Nil)
  def eval0(c: CTerm): Value = eval(c, emptyNEnv, Nil)
  def eval(t: ITerm, named: NameEnv[Value], bound: Env): Value = t match {
    case Ann(e, _) => eval(e, named, bound)
    case Star => VStar
    case Pi(ty, ty1) => VPi(eval(ty, named, bound), x => eval(ty1, named, x :: bound))
    case Free(x) => named.getOrElse(x, vfree(x))
    case Bound(ii) =>
      if (ii < bound.length) bound(ii) else vfree(Quote(ii)) // hack
    case e1 :@: e2 => vapp(eval(e1, named, bound), eval(e2, named, bound))
  }
  def eval(t: CTerm, named: NameEnv[Value], bound: Env): Value = t match {
    case Inf(ii) => eval(ii, named, bound)
    case Lam(e) => VLam(x => eval(e, named, x :: bound))
  }
}
