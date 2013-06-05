package tapl

trait NatQuote extends LambdaPiQuote with NatAST {
  override def quote(ii: Int, v: Value): CTerm = v match {
    case VNat => Inf(Nat)
    case VZero => Zero
    case VSucc(n) => Succ(quote(ii, n))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): ITerm = n match {
    case NNatElim(m, z, s, n) =>
      NatElim(quote(ii, m), quote(ii, z), quote(ii, s), Inf(neutralQuote(ii, n)))
    case _ => super.neutralQuote(ii, n)
  }
}
