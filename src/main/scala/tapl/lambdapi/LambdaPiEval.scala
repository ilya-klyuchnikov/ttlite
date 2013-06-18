package tapl.lambdapi

trait LambdaPiEval extends LambdaPiAST {
  def iEval(i: ITerm, d: (NameEnv[Value], Env)): Value = i match {
    case Ann(e, _) => cEval(e, d)
    case Star => VStar
    case Pi(ty, ty1) => VPi(cEval(ty, d), x => cEval(ty1, (d._1, (x :: d._2))))
    case Free(x) => lookup(x, d._1).getOrElse(vfree(x))
    case Bound(ii) => d._2(ii)
    case e1 :@: e2 => vapp(iEval(e1, d), cEval(e2, d))
  }
  def cEval(c: CTerm, d: (NameEnv[Value], Env)): Value = c match {
    case Inf(ii) => iEval(ii, d)
    case Lam(e) => VLam(x => cEval(e, (d._1, x :: d._2)))
  }
}
