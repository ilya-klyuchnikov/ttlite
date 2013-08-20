package superspec.tt

trait VectorAST extends CoreAST {
  case class Vec(A: Term, n: Term) extends Term
  case class VecNil(A: Term) extends Term
  case class VecCons(A: Term, n: Term, head: Term, tail: Term) extends Term
  case class VecElim(A: Term, motive: Term, nilCase: Term, consCase: Term, n: Term, vec: Term) extends Term

  case class VVec(A: Value, n: Value) extends Value
  case class VVecNil(A: Value) extends Value
  case class VVecCons(A: Value, n: Value, head: Value, tail: Value) extends Value
  case class NVecElim(A: Value, motive: Value, nilCase: Value, consCase: Value, n: Value, vec: Neutral) extends Neutral
}

trait MVector extends MNat with VectorAST {
  override def fromM(m: MTerm): Term = m match {
    case MVar(Global("Vec")) @@ a @@ n =>
      Vec(fromM(a), fromM(n))
    case MVar(Global("VNil")) @@ a =>
      VecNil(fromM(a))
    case MVar(Global("VCons")) @@ a @@ n @@ h @@ t =>
      VecCons(fromM(a), fromM(n), fromM(h), fromM(t))
    case MVar(Global("vecElim")) @@ a @@ m @@ cN @@ cC @@ n @@ xs =>
      VecElim(fromM(a), fromM(m), fromM(cN), fromM(cC), fromM(n), fromM(xs))
    case _ => super.fromM(m)
  }
}

trait VectorPrinter extends NatPrinter with VectorAST {
  override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Vec(a, n) =>
      print(p, ii, 'Vec @@ a @@ n)
    case VecNil(a) =>
      print(p, ii, 'VNil @@ a)
    case VecCons(a, n, x, xs) =>
      print(p, ii, 'VCons @@ a @@ n @@ x @@ xs)
    case VecElim(a, m, mn, mc, n, xs) =>
      print(p, ii, 'vecElim @@ a @@ m @@ mn @@ mc @@ n @@ xs)
    case _ =>
      super.print(p, ii, t)
  }
}

trait VectorEval extends CoreEval with VectorAST {
  override def eval(t: Term, named: NameEnv[Value], bound: Env): Value = t match {
    case Vec(a, n) =>
      VVec(eval(a, named, bound), eval(n, named, bound))
    case VecNil(a) =>
      VVecNil(eval(a, named, bound))
    case VecCons(a, n, head, tail) =>
      VVecCons(eval(a, named, bound), eval(n, named, bound), eval(head, named, bound), eval(tail, named, bound))
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      val nilCaseVal = eval(nilCase, named, bound)
      val consCaseVal = eval(consCase, named, bound)
      def rec(nVal: Value, vecVal: Value): Value = vecVal match {
        case VVecNil(_) =>
          nilCaseVal
        case VVecCons(_, n, head, tail) =>
          consCaseVal @@ n @@ head @@ tail @@ rec(n, tail)
        case VNeutral(n) =>
          VNeutral(NVecElim(eval(a, named, bound), eval(m, named, bound), nilCaseVal, consCaseVal, nVal, n))
      }
      rec(eval(n, named, bound), eval(vec, named, bound))
    case _ =>
      super.eval(t, named, bound)
  }
}

trait VectorCheck extends CoreCheck with VectorAST with NatAST with VectorEval {
  override def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: Term): Value = t match {
    case Vec(a, n) =>
      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, VStar)

      val nType = iType(i, named, bound, n)
      checkEqual(i, nType, VNat)

      VStar
    case VecNil(a) =>
      val aVal = eval(a, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, VStar)

      VVec(aVal, VZero)
    case VecCons(a, n, head, tail) => //, VVec(bVal, VSucc(k))) =>
      val aVal = eval(a, named, List())
      val nVal = eval(n, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, VStar)

      val nType = iType(i, named, bound, n)
      checkEqual(i, nType, VNat)

      val hType = iType(i, named, bound, head)
      checkEqual(i, hType, aVal)

      val tType = iType(i, named, bound, tail)
      checkEqual(i, tType, VVec(aVal, nVal))

      VVec(aVal, VSucc(nVal))
    case VecElim(a, m, nilCase, consCase, n, vec) =>
      val aVal = eval(a, named, List())
      val mVal = eval(m, named, List())
      val nVal = eval(n, named, List())
      val vecVal = eval(vec, named, List())

      val aType = iType(i, named, bound, a)
      checkEqual(i, aType, VStar)

      val mType = iType(i, named, bound, m)
      checkEqual(i, mType, VPi(VNat, {n => VPi(VVec(aVal, n), {_ => VStar})}))

      val nilCaseType = iType(i, named, bound, nilCase)
      checkEqual(i, nilCaseType, mVal @@ VZero @@ VVecNil(aVal))

      val consCaseType = iType(i, named, bound, consCase)
      checkEqual(i, consCaseType, VPi(VNat, {n =>
        VPi(aVal, {y =>
          VPi(VVec(aVal, n), {ys =>
            VPi(mVal @@ n @@ ys, {_ =>
              mVal @@ VSucc(n) @@ VVecCons(aVal, n, y, ys)})})})}))

      val nType = iType(i, named, bound, n)
      checkEqual(i, nType, VNat)

      val vecType = iType(i, named, bound, vec)
      checkEqual(i, vecType, VVec(aVal, nVal))

      mVal @@ nVal @@ vecVal
    case _ =>
      super.iType(i, named, bound, t)
  }

  override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Vec(a, n) =>
      Vec(iSubst(i, r, a), iSubst(i, r, n))
    case VecNil(a) =>
      VecNil(iSubst(i, r, a))
    case VecCons(a, n, head, tail) =>
      VecCons(iSubst(i, r, a), iSubst(i, r, n), iSubst(i, r, head), iSubst(i, r, tail))
    case VecElim(a, m, nc, cc, n, vec) =>
      VecElim(
        iSubst(i, r, a),
        iSubst(i, r, m),
        iSubst(i, r, nc),
        iSubst(i, r, cc),
        iSubst(i, r, n),
        iSubst(i, r, vec)
      )
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait VectorQuote extends CoreQuote with VectorAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VVec(a, n) =>
      Vec(quote(ii, a), quote(ii, n))
    case VVecNil(a) =>
      VecNil(quote(ii, a))
    case VVecCons(a, n, head, tail) =>
      VecCons(quote(ii, a), quote(ii, n), quote(ii, head), quote(ii, tail))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NVecElim(a, m, nilCase, consCase, n, vec) =>
      VecElim(
        quote(ii, a),
        quote(ii, m),
        quote(ii, nilCase),
        quote(ii, consCase),
        quote(ii, n),
        neutralQuote(ii, vec)
      )
    case _ => super.neutralQuote(ii, n)
  }
}

trait VectorREPL extends NatREPL with VectorAST with VectorPrinter with VectorCheck with VectorEval with VectorQuote {
  lazy val vectorTE: NameEnv[Value] =
    Map(
      Global("Vec") -> VecType,
      Global("vecElim") -> vecElimType,
      Global("VNil") -> VNilType,
      Global("VCons") -> VConsType
    )

  val VecTypeIn =
    "forall (a :: *) . forall (n :: Nat) . *"
  val vecElimTypeIn =
    """
      |forall (x :: *) .
      |forall (y :: forall (y :: Nat) . forall (z :: Vec x y) . *) .
      |forall (z :: y Zero (VNil x)) .
      |forall (a :: forall (a :: Nat) . forall (b :: x) . forall (c :: Vec x a) . forall (d :: y a c) . y (Succ a) (VCons x a b c)) .
      |forall (b :: Nat) .
      |forall (c :: Vec x b) .
      |  y b c
    """.stripMargin
  val VNilTypeIn =
    "forall (x :: *) . Vec x Zero"
  val VConsTypeIn =
    "forall (x :: *) . forall (y :: Nat) . forall (z :: x) . forall (a :: Vec x y) . Vec x (Succ y)"

  lazy val VecType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iParse, VecTypeIn).get)
  lazy val vecElimType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iParse, vecElimTypeIn).get)
  lazy val VNilType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iParse, VNilTypeIn).get)
  lazy val VConsType = int.ieval(vectorVE ++ natVE, int.parseIO(int.iParse, VConsTypeIn).get)

  val vectorVE: NameEnv[Value] =
    Map(
      Global("Vec") ->
        VLam(VStar, a => VLam(VNat, n =>  VVec (a, n))),
      Global("VNil") ->
        VLam(VStar, a => VVecNil(a)),
      Global("VCons") ->
        VLam(VStar, a => VLam(VNat, n => VLam(a, x => VLam(VVec(a, n), y => VVecCons(a, n, x, y))))),
      Global("vecElim") ->
        VLam(VStar, a =>
          VLam(VPi(VNat, n => VPi(VVec(a, n), _ => VStar)), m =>
            VLam(m @@ VZero @@ VVecNil(a), nilCase =>
              VLam(null, consCase =>
                VLam(VPi(VNat, a1 => VPi(a, b => VPi(VVec(a, a1), c => VPi(m @@ a1 @@ c, d => m @@ VSucc(a1) @@ VVecCons(a, a1, b, c))))), n =>
                  VLam(VNat, n =>
                    VLam(VVec(a, n), {vec =>
                      eval(VecElim(Bound(5), Bound(4), Bound(3), Bound(2), Bound(1), Bound(0)), vectorVE,
                        List(vec, n, consCase, nilCase, m, a))})))))))
    )
}

trait VectorREPL2 extends NatREPL2 with VectorAST with MVector with VectorPrinter with VectorCheck with VectorEval with VectorQuote
