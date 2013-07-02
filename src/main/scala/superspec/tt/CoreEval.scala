package superspec.tt

trait CoreEval extends CoreAST {
  def eval0(c: Term): Value = eval(c, emptyNEnv, Nil)
  def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Ann(e, _) =>
      eval(e, named, bound)
    case Star =>
      VStar
    case Pi(ty, ty1) =>
      VPi(eval(ty, named, bound), x => eval(ty1, named, x :: bound))
    case Free(x) =>
      named.getOrElse(x, vfree(x))
    case Bound(ii) =>
      if (ii < bound.length) bound(ii) else vfree(Quote(ii))
    case e1 :@: e2 =>
      eval(e1, named, bound) @@ eval(e2, named, bound)
    case Lam(t, e) =>
      VLam(eval(t, named, bound), x => eval(e, named, x :: bound))
  }
}
