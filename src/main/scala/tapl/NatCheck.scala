package tapl

trait NatCheck extends LambdaPiCheck with NatAST {
  override def iType(i: Int, g: (NameEnv[Value], Context), t: ITerm): Result[Type] = t match {
    case Nat =>
      Right(VStar)
    case NatElim(m, mz, ms, n) =>
      val z = for {
        _ <- cType(i, g, m, VPi(VNat, x => VStar)).right.toOption
        mVal = cEval(m, (g._1, Nil))
        _ <- cType(i, g, mz, vapp(mVal, VZero)).right.toOption
        _ <- cType(i, g, ms, VPi(VNat, k => VPi(vapp(mVal, k), x => vapp(mVal, VSucc(k))))).right.toOption
        _ <- cType(i, g, n, VNat).right.toOption
        nVal = cEval(n, (g._1, Nil))
      } yield
        vapp(mVal, nVal)
      z match {
        case Some(e) => Right(e)
        case None => Left("")
      }
    case _ =>
      super.iType(i, g, t)
  }

  override def cType(ii: Int, g: (NameEnv[Value], Context), ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (Zero, VNat) =>
      Right(())
    case (Succ(k), VNat) =>
      cType(ii, g, k, VNat)
    case _ =>
      super.cType(ii, g, ct, t)
  }

  override def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Nat =>
      Nat
    case NatElim(m, mz, ms, n) =>
      NatElim(cSubst(i, r, m), cSubst(i, r, mz), cSubst(i, r, ms), cSubst(i, r, n))
    case _ => super.iSubst(i, r, it)
  }

  override def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case Zero =>
      Zero
    case Succ(n) =>
      Succ(cSubst(ii, r, n))
    case _ =>
      super.cSubst(ii, r, ct)
  }

}
