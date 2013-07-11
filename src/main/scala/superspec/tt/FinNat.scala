package superspec.tt

// (Fin n) is the type that contains exactly n elements.
// Fin 0 - empty type
// Fin 1 - unit type
// Fin 2 - booleans
trait FinNat extends CoreAST {
  case class Fin(n: Term) extends Term
  case class FZero(A: Term) extends Term
  case class FSucc(A: Term, n: Term) extends Term
  case class FinElim(A: Term, c1: Term, c2: Term, c3: Term, c4: Term) extends Term

  case class VFZero(A: Value) extends Value
  case class VFSucc(A: Value, n: Value) extends Value
  case class VFin(n: Value) extends Value
  case class NFinElim(A: Value, c1: Value, c2: Value, c3: Value, c4: Neutral) extends Neutral
}

trait FinNatPrinter extends NatPrinter with FinNat {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Fin(n) =>
      print(p, ii, Free(Global("Fin")) @@ n)
    case FZero(n) =>
      print(p, ii, Free(Global("Fin")) @@ n)
    case FSucc(n, f) =>
      print(p, ii, Free(Global("FSucc")) @@ n @@ f)
    case FinElim(m, mz, ms, n, f) =>
      print(p, ii, Free(Global("finElim")) @@ m @@ mz @@ ms @@ n @@ f)
    case _ =>
      super.print(p, ii, t)
  }
}

trait FinNatEval extends CoreEval with FinNat {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Fin(n) =>
      VFin(eval(n, named, bound))
    case FZero(n) =>
      VFZero(eval(n, named, bound))
    case FSucc(n, f) =>
      VFSucc(eval(n, named, bound), eval(n, named, bound))
    case FinElim(m, mz, ms, n, f) =>
      val mzVal = eval(mz, named, bound)
      val msVal = eval(ms, named, bound)

      def rec(fVal: Value): Value = fVal match {
        case VFZero(k) =>
          mzVal @@ k
        case VFSucc(k, g) =>
          msVal @@ k @@ g @@ rec(g)
        case VNeutral(n1) =>
          VNeutral(
            NFinElim(eval(m, named, bound), eval(mz, named, bound), eval(ms, named, bound), eval(n, named, bound), n1)
          )
      }

      rec(eval(f, named, bound))
    case _ => super.eval(t, named, bound)
  }
}

trait FinNatCheck extends CoreCheck with FinNat {
  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Fin(n) =>
      Fin(iSubst(i, r, n))
    case FZero(n) =>
      FZero(iSubst(i, r, n))
    case FSucc(n, k) =>
      FSucc(iSubst(i, r, n), iSubst(i, r, k))
    case FinElim(m, mz, ms, n, f) =>
      FinElim(iSubst(i, r, m), iSubst(i, r, mz), iSubst(i, r, ms), iSubst(i, r, n), iSubst(i, r, f))
    case _ => super.iSubst(i, r, it)
  }
}

trait FinNatQuote extends CoreQuote with FinNat {
  override def quote(ii: Int, v: Value): Term = v match {
    case VFin(n) => Fin(quote(ii, n))
    case VFZero(n) => FZero(quote(ii, n))
    case VFSucc(n, k) => FSucc(quote(ii, n), quote(ii, k))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NFinElim(m, mz, ms, n, f) =>
      FinElim(quote(ii, m), quote(ii, mz), quote(ii, ms), quote(ii, n), neutralQuote(ii, f))
    case _ => super.neutralQuote(ii, n)
  }
}

trait FinNatREPL extends NatREPL with FinNat with FinNatPrinter with FinNatCheck with FinNatEval with FinNatQuote {
  lazy val finTE: NameEnv[Value] =
    Map(
      Global("Fin") -> FinType,
      Global("FZero") -> FZeroType,
      Global("FSucc") -> FSuccType,
      Global("finElim") -> finElimType
    )

  val FinTypeIn =
    "forall x :: Nat . *"
  val FZeroTypeIn =
    "forall x :: Nat . Fin (Succ x)"
  val FSuccTypeIn =
    "forall (x :: Nat) . forall (y :: Fin x) . Fin (Succ x)"
  val finElimTypeIn =
    """
      |forall (m :: forall (x :: Nat) . forall (y :: Fin x) . *) .
      |forall (_ :: forall y :: Nat . m (Succ y) (FZero y)) .
      |forall (_ :: forall (z :: Nat) . forall (a :: Fin z) . forall (b :: m z a) .
      |             m (Succ z) (FSucc z a)) .
      |forall (a :: Nat) .
      |forall (b :: Fin a) .
      |m a b
    """.stripMargin

  lazy val FZeroType = int.ieval(finVE ++ natVE, int.parseIO(int.iParse, FZeroTypeIn).get)
  lazy val FSuccType = int.ieval(finVE ++ natVE, int.parseIO(int.iParse, FSuccTypeIn).get)
  lazy val FinType = int.ieval(finVE ++ natVE, int.parseIO(int.iParse, FinTypeIn).get)
  lazy val finElimType = int.ieval(finVE ++ natVE, int.parseIO(int.iParse, finElimTypeIn).get)

  val finVE: NameEnv[Value] =
    Map(
      Global("Fin") -> VLam(VNat, n => VFin(n)),
      Global("FZero") -> VLam(VNat, n => VFZero(n)),
      Global("FSucc") -> VLam(VNat, n => VLam(VFin(n), f => VFSucc(n, f))),
      Global("finElim") ->
        VLam(VPi(VNat, x => VPi(VFin(x), _ => VStar)), m =>
          VLam(VPi(VNat, y => m @@ VSucc(y) @@ VFZero(y)), zCase =>
          VLam(VPi(VNat, z => VPi(VFin(z), a => VPi(m @@ z @@ a, _ => m @@ VSucc(z) @@ VFSucc(z, a)))), sCase =>
            VLam(VNat, n => VLam(VFin(n), f =>
              eval(FinElim(Bound(4), Bound(3), Bound(2), Bound(1), Bound(0)), finVE, List(f, n, sCase, zCase, m))
            )))))
    )
}
