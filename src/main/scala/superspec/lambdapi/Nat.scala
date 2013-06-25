package superspec.lambdapi

trait NatAST extends CoreAST {
  case object Zero extends CTerm
  case class Succ(e: CTerm) extends CTerm

  case object Nat extends ITerm
  case class NatElim(a: CTerm, b: CTerm, c: CTerm, d: CTerm) extends ITerm

  case object VNat extends Value
  case object VZero extends Value
  case class VSucc(v: Value) extends Value

  case class NNatElim(m: Value, caseZ: Value, caseS: Value, n: Neutral) extends Neutral
}

trait NatSubst extends CoreSubst with NatAST {
  override def findSubst0(from: CTerm, to: CTerm): Option[Subst] = (from, to) match {
    case (Zero, Zero) =>
      Some(Map())
    case (Succ(x1), Succ(x2)) =>
      findSubst0(x1, x2)
    case _ =>
      super.findSubst0(from, to)
  }

  override def findSubst0(from: ITerm, to: ITerm): Option[Subst] = (from, to) match {
    case (Nat, Nat) =>
      Some(Map())
    case (NatElim(m1, zCase1, sCase1, n1), NatElim(m2, zCase2, sCase2, n2)) =>
      mergeOptSubst(
        findSubst0(m1, m2),
        findSubst0(zCase1, zCase2),
        findSubst0(sCase1, sCase2),
        findSubst0(n1, n2)
      )
    case _ =>
      super.findSubst0(from, to)
  }

  override def isFreeSubTerm(t: CTerm, depth: Int): Boolean = t match {
    case Zero =>
      true
    case Succ(c) =>
      isFreeSubTerm(c, depth)
    case _ =>
      super.isFreeSubTerm(t, depth)
  }

  override def isFreeSubTerm(t: ITerm, depth: Int): Boolean = t match {
    case Nat =>
      true
    case NatElim(a, b, c, d) =>
      isFreeSubTerm(a, depth) && isFreeSubTerm(b, depth + 1) &&
        isFreeSubTerm(c, depth) && isFreeSubTerm(d, depth + 1)
    case _ =>
      super.isFreeSubTerm(t, depth)
  }
}

trait NatPrinter extends CorePrinter with NatAST {
  override def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Nat =>
      "Nat"
    case NatElim(m, z, s, n) =>
      iPrint(p, ii, Free(Global("natElim")) @@ m @@ z @@ s @@ n)
    case _ => super.iPrint(p, ii, t)
  }

  override def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case Zero =>
      iPrint(p, ii, Free(Global("Zero")))
    case Succ(n) =>
      iPrint(p, ii, Free(Global("Succ")) @@ n)
    case _ => super.cPrint(p, ii, t)
  }

  def fromNat(n: Int, ii: Int, t: CTerm): Doc = t match {
    case Zero =>
      "Zero"
    case Succ(k) =>
      fromNat(n + 1, ii, k)
    case _ =>
      parens(n.toString <> " + " <> cPrint(3, ii, t))
  }
}

trait NatEval extends CoreEval with NatAST {
  override def cEval(c: CTerm, nEnv: NameEnv[Value], bEnv: Env): Value = c match {
    case Zero =>
      VZero
    case Succ(n) =>
      VSucc(cEval(n, nEnv, bEnv))
    case _ => super.cEval(c, nEnv, bEnv)
  }

  override def iEval(i: ITerm, nEnv: NameEnv[Value], bEnv: Env): Value = i match {
    case Nat =>
      VNat
    case NatElim(m, mz, ms, n) =>
      val mzVal = cEval(mz, nEnv, bEnv)
      val msVal = cEval(ms, nEnv, bEnv)
      def rec(nVal: Value): Value = nVal match {
        case VZero =>
          mzVal
        case VSucc(k) =>
          vapp(vapp(msVal, k), rec(k))
        case VNeutral(n) =>
          VNeutral(NNatElim(cEval(m, nEnv, bEnv), mzVal, msVal, n))
      }
      rec(cEval(n, nEnv, bEnv))
    case _ =>
      super.iEval(i, nEnv, bEnv)
  }
}

trait NatDriver extends CoreDriver with NatAST {
  override def driveNeutral(n: Neutral): DriveStep = n match {
    case natElim: NNatElim =>
      natElim.n match {
        case NFree(n) =>
          val caseZ = ElimBranch(Zero, Map())
          val n1 = freshName
          val v1 = Inf(Free(n1))
          val caseS = ElimBranch(Succ(v1), Map(n1 -> Inf(Free(n))))
          ElimDStep(n, List(caseZ, caseS))
        case n =>
          driveNeutral(n)
      }
    case _ =>
      super.driveNeutral(n)
  }

  override def driveLeibniz(c: CTerm): DriveStep = c match {
    case Succ(c1) =>
      DecompositionDStep(Inf(Free(Global("Succ"))), c1)
    case _ =>
      super.driveLeibniz(c)
  }

}

trait NatCheck extends CoreCheck with NatAST {
  override def iType(i: Int, nEnv: NameEnv[Value], ctx: Context, t: ITerm): Result[Type] = t match {
    case Nat =>
      Right(VStar)
    case NatElim(m, mz, ms, n) =>
      val z = for {
        _ <- cType(i, nEnv, ctx, m, VPi(VNat, x => VStar)).right.toOption
        mVal = cEval(m, nEnv, Nil)
        _ <- cType(i, nEnv, ctx, mz, vapp(mVal, VZero)).right.toOption
        _ <- cType(i, nEnv, ctx, ms, VPi(VNat, k => VPi(vapp(mVal, k), x => vapp(mVal, VSucc(k))))).right.toOption
        _ <- cType(i, nEnv, ctx, n, VNat).right.toOption
        nVal = cEval(n, nEnv, Nil)
      } yield
        vapp(mVal, nVal)
      z match {
        case Some(e) => Right(e)
        case None => Left("")
      }
    case _ =>
      super.iType(i, nEnv, ctx, t)
  }

  override def cType(ii: Int, nEnv: NameEnv[Value], ctx: Context, ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (Zero, VNat) =>
      Right(())
    case (Succ(k), VNat) =>
      cType(ii, nEnv, ctx, k, VNat)
    case _ =>
      super.cType(ii, nEnv, ctx, ct, t)
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

trait NatQuote extends CoreQuote with NatAST {
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

trait NatREPL extends CoreREPL with NatAST with NatPrinter with NatCheck with NatEval with NatQuote {
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
          Lam(Lam(Lam(Lam(
            Inf(NatElim((Inf(Bound(3))), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0))))
          )))),
          Nil, Nil)
    )

  def toNat1(n: Int): CTerm =
    if (n == 0) Zero else Succ(toNat1(n - 1))

  override def toNat(i: Int): ITerm =
    Ann(toNat1(i), Inf(Nat))
}
