package tapl

object LambdaPiREPL1Main extends LambdaPiREPL1 {
  def main(args: Array[String]) {
    loop(new NatInterpreter{}, State(true, lpve, lpte))
  }
}

trait LambdaPiREPL1 extends LambdaPiREPL with NatAST with NatCheck with NatEval with NatQuote {
  val lpte: Ctx[Value] =
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
  val lpve: Ctx[Value] =
    List(
      Global("Zero") -> VZero,
      Global("Succ") -> VLam(n => VSucc(n)),
      Global("Nat") -> VNat,
      Global("natElim") ->
        cEval(
          Lam(Lam(Lam(Lam(Inf(NatElim((Inf(Bound(3))), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)))   ))))),
          (Nil, Nil))
    )
  trait NatInterpreter extends LambdaPIInterpreter
}
