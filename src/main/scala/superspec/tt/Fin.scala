package superspec.tt

// (Fin n) is the type that contains exactly n elements.
// Fin 0 - empty type
// Fin 1 - unit type
// Fin 2 - booleans
trait FinAST extends CoreAST {
  case class FZero(A: CTerm) extends CTerm
  case class FSucc(A: CTerm, n: CTerm) extends CTerm

  case class Fin(n: CTerm) extends ITerm
  case class FinElim(A: CTerm, c1: CTerm, c2: CTerm, c3: CTerm, c4: CTerm) extends ITerm

  case class VFZero(A: Value) extends Value
  case class VFSucc(A: Value, n: Value) extends Value
  case class VFin(n: Value) extends Value

  case class NFinElim(A: Value, c1: Value, c2: Value, c3: Value, c4: Neutral) extends Neutral
}

trait FinPrinter extends NatPrinter with FinAST {
  override def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Fin(n) =>
      iPrint(p, ii, Free(Global("Fin")) @@ n)
    case FinElim(m, mz, ms, n, f) =>
      iPrint(p, ii, Free(Global("finElim")) @@ m @@ mz @@ ms @@ n @@ f)
    case _ =>
      super.iPrint(p, ii, t)
  }

  override def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case FZero(n) =>
      iPrint(p, ii, Free(Global("Fin")) @@ n)
    case FSucc(n, f) =>
      iPrint(p, ii, Free(Global("FSucc")) @@ n @@ f)
    case _ =>
      super.cPrint(p, ii, t)
  }
}

trait FinEval extends CoreEval with FinAST {
  override def eval(t: CTerm, named: NameEnv[Value], bound: Env): Value = t match {
    case FZero(n) =>
      VFZero(eval(n, named, bound))
    case FSucc(n, f) =>
      VFSucc(eval(n, named, bound), eval(n, named, bound))
    case _ => super.eval(t, named, bound)
  }

  override def eval(t: ITerm, named: NameEnv[Value], bound: Env): Value = t match {
    case Fin(n) =>
      VFin(eval(n, named, bound))
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
    case _ =>
      super.eval(t, named, bound)
  }
}

trait FinCheck extends CoreCheck with FinAST {
  override def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Fin(n) =>
      Fin(cSubst(i, r, n))
    case FinElim(m, mz, ms, n, f) =>
      FinElim(cSubst(i, r, m), cSubst(i, r, mz), cSubst(i, r, ms), cSubst(i, r, n), cSubst(i, r, f))
    case _ => super.iSubst(i, r, it)
  }

  override def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case FZero(n) =>
      FZero(cSubst(ii, r, n))
    case FSucc(n, k) =>
      FSucc(cSubst(ii, r, n), cSubst(ii, r, k))
    case _ =>
      super.cSubst(ii, r, ct)
  }

}

trait FinQuote extends CoreQuote with FinAST {
  override def quote(ii: Int, v: Value): CTerm = v match {
    case VFin(n) => Inf(Fin(quote(ii, n)))
    case VFZero(n) => FZero(quote(ii, n))
    case VFSucc(n, k) => FSucc(quote(ii, n), quote(ii, k))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): ITerm = n match {
    case NFinElim(m, mz, ms, n, f) =>
      FinElim(quote(ii, m), quote(ii, mz), quote(ii, ms), quote(ii, n), Inf(neutralQuote(ii, f)))
    case _ => super.neutralQuote(ii, n)
  }
}

trait FinREPL extends NatREPL with FinAST with FinPrinter with FinCheck with FinEval with FinQuote {
  lazy val finTE: NameEnv[Value] =
    Map(
      Global("FZero") -> FZeroType,
      Global("FSucc") -> FSuccType,
      Global("Fin") -> FinType,
      Global("finElim") -> finElimType
    )

  val FZeroTypeIn =
    "forall x :: Nat . Fin (Succ x)"
  val FSuccTypeIn =
    "forall (x :: Nat) . forall (y :: Fin x) . Fin (Succ x)"
  val FinTypeIn =
    "forall x :: Nat . *"
  val finElimTypeIn =
    """
      |forall (m :: forall (x :: Nat) . forall (y :: Fin x) . *) .
      |forall (_ :: forall y :: Nat . m (Succ y) (FZero y)) .
      |forall (z :: forall (z :: Nat) . forall (a :: Fin z) . forall (b :: m z a) .
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
      Global("FZero") -> VLam(n => VFZero(n)),
      Global("FSucc") -> VLam(n => VLam(f => VFSucc(n, f))),
      Global("Fin") -> VLam(n => VFin(n)),
      Global("finElim") ->
        eval(
          Lam(Lam(Lam(Lam(Lam(
            Inf(FinElim(Inf(Bound(4)), Inf(Bound(3)), Inf(Bound(2)), Inf(Bound(1)), Inf(Bound(0))))
          ))))),
          emptyNEnv, List())
    )
}
