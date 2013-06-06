package tapl

object NatREPLMain extends NatREPL {
  def main(args: Array[String]) {
    loop(new LambdaPIInterpreter{}, State(true, natVE, natTE))
  }
}

trait NatREPL extends LambdaPiREPL with NatAST with NatCheck with NatEval with NatQuote {
  val natTE: Ctx[Value] =
    List(
      Global("Zero") -> VNat,
      Global("Succ") -> VPi(VNat, _ => VNat),
      Global("Nat") -> VStar,
      Global("natElim") ->
        VPi(VPi(VNat, {x => VStar}), {m =>
          VPi(vapp(m, VZero), {_ =>
            VPi(VPi(VNat, {k => VPi( (vapp(m, k)), { _ => (vapp(m,VSucc(k)) )} )} ), { xx =>
              VPi(VNat, {n => vapp(m, n)}) } ) }  ) })
    )
  val natVE: Ctx[Value] =
    List(
      Global("Zero") -> VZero,
      Global("Succ") -> VLam(n => VSucc(n)),
      Global("Nat") -> VNat,
      Global("natElim") ->
        cEval(
          Lam(Lam(Lam(Lam(Inf(NatElim((Inf(Bound(3))), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)))   ))))),
          (Nil, Nil))
    )

  def toNat1(n: Int): CTerm =
    if (n == 0) Zero else Succ(toNat1(n - 1))

  override def toNat(i: Int): ITerm =
    Ann(toNat1(i), Inf(Nat))
}
