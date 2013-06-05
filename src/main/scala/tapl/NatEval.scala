package tapl

trait NatEval extends LambdaPiEval with NatAST {
  override def cEval(c: CTerm, d: (NameEnv[Value], Env)): Value = c match {
    case Zero =>
      VZero
    case Succ(n) =>
      VSucc(cEval(n, d))
    case _ => super.cEval(c, d)
  }

  override def iEval(i: ITerm, d: (NameEnv[Value], Env)): Value = i match {
    case Nat =>
      VNat
    case NatElim(m, mz, ms, n) =>
      val mzVal = cEval(mz, d)
      val msVal = cEval(ms, d)
      def rec(nVal: Value): Value = nVal match {
        case VZero =>
          mzVal
        case VSucc(k) =>
          vapp(vapp(msVal, k), rec(k))
        case VNeutral(n) =>
          VNeutral(NNatElim(cEval(m, d), mzVal, msVal, n))
      }
      rec(cEval(n, d))
    case _ =>
      super.iEval(i, d)
  }
}
