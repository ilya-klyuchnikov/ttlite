package superspec.lambdapi

trait NatAST extends LambdaPiAST {
  case object Zero extends CTerm
  case class Succ(e: CTerm) extends CTerm

  case object Nat extends ITerm
  case class NatElim(a: CTerm, b: CTerm, c: CTerm, d: CTerm) extends ITerm

  case object VNat extends Value
  case object VZero extends Value
  case class VSucc(v: Value) extends Value

  case class NNatElim(v1: Value, v2: Value, v3: Value, n: Neutral) extends Neutral
}

trait NatPrinter extends LambdaPiPrinter with NatAST {
  override def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Nat =>
      "Nat"
    case NatElim(m, z, s, n) =>
      iPrint(p, ii, Free(Global("natElim")) @@ m @@ z @@ s @@ n)
    case _ => super.iPrint(p, ii, t)
  }

  override def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case Zero =>
      fromNat(0, ii, Zero)
    case Succ(n) =>
      //iPrint(p, ii, Free(Global("Succ")) @@ n)
      fromNat(0, ii, Succ(n))
    case _ => super.cPrint(p, ii, t)
  }

  def fromNat(n: Int, ii: Int, t: CTerm): Doc = t match {
    case Zero =>
      n.toString
    case Succ(k) =>
      fromNat(n + 1, ii, k)
    case _ =>
      parens(n.toString <> " + " <> cPrint(3, ii, t))
  }
}

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

trait NatREPL extends LambdaPiREPL with NatAST with NatPrinter with NatCheck with NatEval with NatQuote {
  lazy val natTE: Ctx[Value] =
    List(
      Global("Zero") -> VNat,
      Global("Succ") -> VPi(VNat, _ => VNat),
      Global("Nat") -> VStar,
      Global("natElim") -> natElimType
    )
  val natElimTypeIn =
    """
      |forall (m :: forall x :: Nat . *) .
      |forall (zCase :: m Zero) .
      |forall (sCase :: forall (n :: Nat) . forall (a :: m n) . m (Succ n)) .
      |forall (n :: Nat) .
      |m n
    """.stripMargin
  lazy val natElimType = int.ieval(natVE, int.parseIO(int.iiparse, natElimTypeIn).get)
  val natVE: Ctx[Value] =
    List(
      Global("Zero") -> VZero,
      Global("Succ") -> VLam(n => VSucc(n)),
      Global("Nat") -> VNat,
      Global("natElim") ->
        cEval(
          Lam(Lam(Lam(Lam(Inf(NatElim((Inf(Bound(3))), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0)))))))), (Nil, Nil))
    )

  def toNat1(n: Int): CTerm =
    if (n == 0) Zero else Succ(toNat1(n - 1))

  override def toNat(i: Int): ITerm =
    Ann(toNat1(i), Inf(Nat))
}
