package superspec.lambdapi

trait CoreEval extends CoreAST {
  def iEval0(c: ITerm): Value = iEval(c, Nil, Nil)
  def cEval0(c: CTerm): Value = cEval(c, Nil, Nil)


  def iEval(i: ITerm, nEnv: NameEnv[Value], bEnv: Env): Value = i match {
    case Ann(e, _) => cEval(e, nEnv, bEnv)
    case Star => VStar
    case Pi(ty, ty1) => VPi(cEval(ty, nEnv, bEnv), x => cEval(ty1, nEnv, x :: bEnv))
    case Free(x) => lookup(x, nEnv).getOrElse(vfree(x))
    case Bound(ii) => bEnv(ii)
    case e1 :@: e2 => vapp(iEval(e1, nEnv, bEnv), cEval(e2, nEnv, bEnv))
  }
  def cEval(c: CTerm, nEnv: NameEnv[Value], bEnv: Env): Value = c match {
    case Inf(ii) => iEval(ii, nEnv, bEnv)
    case Lam(e) => VLam(x => cEval(e, nEnv, x :: bEnv))
  }
}
