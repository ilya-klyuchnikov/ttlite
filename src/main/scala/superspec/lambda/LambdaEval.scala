package superspec.lambda

trait LambdaEval extends LambdaAST {
  def iEval(i: ITerm, d: (NameEnv[Value], Env)): Value = i match {
    case Ann(e, _) => cEval(e, d)
    case Free(x) => lookup(x, d._1).getOrElse(vfree(x))
    case Bound(ii) => d._2(ii)
    case e1 :@: e2 => vapp(iEval(e1, d), cEval(e2, d))
  }
  def cEval(c: CTerm, d: (NameEnv[Value], Env)): Value = c match {
    case Inf(ii) => iEval(ii, d)
    case Lam(e) => VLam(x => cEval(e, (d._1, x :: d._2)))
  }
}
