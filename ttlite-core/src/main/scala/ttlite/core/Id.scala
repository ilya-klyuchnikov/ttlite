package ttlite.core

import ttlite.common._

trait IdAST extends CoreAST {
  case class Id(A: Term, x: Term, y: Term) extends Term
  case class Refl(A: Term, x: Term) extends Term
  case class IdElim(et: Term, prop: Term, propR: Term, eq: Term) extends Term

  case class VId(A: Value, x: Value, y: Value) extends Value
  case class VRefl(A: Value, x: Value) extends Value
  case class NIdElim(et: Value, prop: Value, propR: Value, eq: Neutral) extends Neutral
}

trait IdMetaSyntax extends MetaSyntax with IdAST {
  abstract override def translate(m: MTerm): Term = m match {
    case MVar(Global("Id")) @@ a @@ x @@ y =>
      Id(translate(a), translate(x), translate(y))
    case MVar(Global("Refl")) @@ a @@ x =>
      Refl(translate(a), translate(x))
    case MVar(Global("elim")) @@ (MVar(Global("Id")) @@ a @@ x @@ y) @@ p @@ pr @@ eq =>
      IdElim(Id(translate(a), translate(x), translate(y)), translate(p), translate(pr), translate(eq))
    case _ => super.translate(m)
  }
}

trait IdPrinter extends Printer with IdAST {
  abstract override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Id(a, x, y) =>
      printL(p, ii, 'Id, a, x, y)
    case Refl(a, x) =>
      printL(p, ii, 'Refl, a, x)
    case IdElim(et, m, mr, eq) =>
      printL(p, ii, 'elim, et, m, mr, eq)
    case _ =>
      super.print(p, ii, t)
  }
}

trait IdPrinterAgda extends PrinterAgda with IdAST {
  abstract override def printA(p: Int, ii: Int, t: Term): Doc = t match {
    case Id(a, x, y) =>
      printAL(p, ii, 'Id, a, x, y)
    case Refl(a, x) =>
      printAL(p, ii, 'refl, a, x)
    case IdElim(Id(a, a1, a2), m, mr, eq) =>
      printAL(p, ii, 'elimId, a, a1, a2, m, mr, eq)
    case _ =>
      super.printA(p, ii, t)
  }
}

trait IdPrinterCoq extends PrinterCoq with IdAST {
  abstract override def printC(p: Int, ii: Int, t: Term): Doc = t match {
    case Id(a, x, y) =>
      printCL(p, ii, 'Id, a, x, y)
    case Refl(a, x) =>
      printCL(p, ii, 'refl, a, x)
    case IdElim(Id(a, a1, a2), m, mr, eq) =>
      printCL(p, ii, 'elimId, a, a1, a2, m, mr, eq)
    case _ =>
      super.printC(p, ii, t)
  }
}

trait IdPrinterIdris extends PrinterIdris with IdAST {
  abstract override def printI(p: Int, ii: Int, t: Term): Doc = t match {
    case Id(a, x, y) =>
      printIL(p, ii, 'Id, a, x, y)
    case Refl(a, x) =>
      printIL(p, ii, 'TTRefl, a, x)
    case IdElim(Id(a, a1, a2), m, mr, eq) =>
      printIL(p, ii, 'elimId, a, a1, a2, m, mr, eq)
    case _ =>
      super.printI(p, ii, t)
  }
}

trait IdEval extends Eval with IdAST with CoreQuoting { self: FunAST =>
  abstract override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Id(a, x, y) =>
      VId(eval(a, ctx, bound), eval(x, ctx, bound), eval(y, ctx, bound))
    case Refl(a, x) =>
      VRefl(eval(a, ctx, bound), eval(x, ctx, bound))
    case IdElim(et, prop, propR, eq) =>
      val etVal = eval(et, ctx, bound)
      val propVal = eval(prop, ctx, bound)
      val propRVal = eval(propR, ctx, bound)
      val eqVal = eval(eq, ctx, bound)
      idElim(etVal, propVal, propRVal, eqVal)
    case _ => super.eval(t, ctx, bound)
  }

  private def idElim(etVal: Value, propVal: Value, propRVal: Value, eqVal: Value) = eqVal match {
    case r@VRefl(a, z) =>
      propRVal @@ z
    case VNeutral(n) =>
      VNeutral(NIdElim(etVal, propVal, propRVal, n))
  }
}

trait IdCheck extends Check with IdAST { self: FunAST =>
  abstract override def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value = t match {
    case Id(a, x, y) =>
      val aType = iType(i, path/(2, 4), ctx, a)
      val j = checkUniverse(i, aType, path/(2, 4))
      val aVal = eval(a, ctx, Nil)

      val xType = iType(i, path/(3, 4), ctx, x)
      checkEqual(i, xType, aVal, path/(3, 4))

      val yType = iType(i, path/(4, 4), ctx, y)
      checkEqual(i, yType, aVal, path/(4, 4))

      VUniverse(j)
    case Refl(a, z) =>
      val aType = iType(i, path/(2, 3), ctx, a)
      checkUniverse(i, aType, path/(2, 3))
      val aVal = eval(a, ctx, Nil)

      val zType = iType(i, path/(3, 3), ctx, z)
      checkEqual(i, zType, aVal, path/(3, 3))
      val zVal = eval(z, ctx, Nil)

      VId(aVal, zVal, zVal)
    case IdElim(et, prop, propR, eq) =>
      val eType = iType(i, path/(2, 5), ctx, et)
      checkUniverse(i, eType, path/(2, 5))
      val etVal = eval(et, ctx, List())
      require(etVal.isInstanceOf[VId], path/(2, 5), "Id _ _ _", et)
      val VId(aVal, xVal, yVal) = etVal

      val propType = iType(i, path/(3, 5), ctx, prop)
      checkEqual(i, propType, VPi(aVal, {x => VPi(aVal, {y => VPi(VId(aVal, x, y), {_ => VUniverse(-1)})})}), path/(3, 5))
      val propVal = eval(prop, ctx, Nil)

      val propRType = iType(i, path/(4, 5), ctx, propR)
      checkEqual(i, propRType, VPi(aVal, {x => propVal @@ x @@ x @@ VRefl(aVal, x)}), path/(4, 5))

      val eqType = iType(i, path/(5, 5), ctx, eq)
      checkEqual(i, eqType, VId(aVal, xVal, yVal), path/(5, 5))
      val eqVal = eval(eq, ctx, Nil)

      propVal @@ xVal @@ yVal @@ eqVal
    case _ =>
      super.iType(i, path, ctx, t)
  }

  abstract override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Id(a, x, y) =>
      Id(iSubst(i, r, a), iSubst(i, r, x), iSubst(i, r, y))
    case Refl(a, x) =>
      Refl(iSubst(i, r, a), iSubst(i, r, x))
    case IdElim(et, m, mr, eq) =>
      IdElim(iSubst(i, r, et), iSubst(i, r, m), iSubst(i, r, mr), iSubst(i, r, eq))
    case _ =>
      super.iSubst(i, r, it)
  }
}

trait IdQuoting extends CoreQuoting with IdAST {
  override def quote(ii: Int, v: Value): Term = v match {
    case VId(a, x, y) =>
      Id(quote(ii, a), quote(ii, x), quote(ii, y))
    case VRefl(a, x) =>
      Refl(quote(ii, a), quote(ii, x))
    case _ => super.quote(ii, v)
  }
  override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NIdElim(et, m, mr, eq) =>
      IdElim(quote(ii, et), quote(ii, m), quote(ii, mr), neutralQuote(ii, eq))
    case _ => super.neutralQuote(ii, n)
  }
}

trait IdREPL
  extends CoreREPL
  with IdAST
  with IdMetaSyntax
  with IdPrinter
  with IdPrinterAgda
  with IdPrinterCoq
  with IdPrinterIdris
  with IdCheck
  with IdEval
  with IdQuoting {
  self: FunAST =>
}
