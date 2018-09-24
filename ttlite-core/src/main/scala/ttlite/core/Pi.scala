package ttlite.core

import ttlite.common._

// Chapter 7. Cartesian product of a family of sets.
// Dependent product type, or pi-type.
trait PiAST extends AST {
  import scala.language.implicitConversions

  case class Pi(c1: Term, c2: Term) extends Term
  case class Lam(t: Term, e: Term) extends Term
  case class :@:(h: Term, t: Term) extends Term

  case class VPi(t: Value, e: Value => Value) extends Value
  case class VLam(t: Value, e: Value => Value) extends Value
  case class NApp(n: Neutral, v: Value) extends Neutral

  implicit class VApplicable(v: Value) {
    def @@(v1: Value): Value = v match {
      case VLam(_, f) => f(v1)
      case VNeutral(n) => VNeutral(NApp(n, v1))
    }
  }
}

trait PiMetaSyntax extends MetaSyntax with PiAST {
  private val predefinedGlobals = Set("forall")
  abstract override def isPredefinedGlobal(g: Global): Boolean =
    predefinedGlobals(g.n) || super.isPredefinedGlobal(g)
  abstract override def translate(m: MTerm): Term = m match {
    case MBind("forall", t1, t2) =>
      Pi(translate(t1), translate(t2))
    case MBind("\\", t1, t2) =>
      Lam(translate(t1), translate(t2))
    case t1 @@ t2 =>
      :@:(translate(t1), translate(t2))
    case _ => super.translate(m)
  }
}

trait PiPrinter extends Printer with PiAST {
  import scala.collection.immutable.Seq

  abstract override def print(p: Int, ii: Int, t: Term): Doc = t match {
    case Pi(d, Pi(d1, r)) =>
      parensIf(p > 0, nestedForall(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Pi(d, r) =>
      parensIf(p > 0, sep(Seq("forall " <> parens(vars(ii) <> " : " <> print(0, ii, d)) <> " .", nest(print(0, ii + 1, r)))))
    case Lam(t, Lam(t1, c)) =>
      parensIf(p > 0, nestedLambda(ii + 2, List((ii + 1, t1), (ii, t)), c))
    case Lam(t, c) =>
      parensIf(p > 0,  "\\ " <> parens(vars(ii) <> " : " <> print(0, ii, t)) <> " -> " <> nest(print(0, ii + 1, c)))
    case i :@: c =>
      parensIf(p > 2, sep(Seq(print(2, ii, i), nest(print(3, ii, c)))))
    case _ =>
      super.print(p, ii, t)
  }

  private def nestedForall(i: Int, fs: List[(Int, Term)], t: Term): Doc = t match {
    case Pi(d, r) =>
      nestedForall(i + 1, (i, d) :: fs, r)
    case x =>
      val fors = fs.reverse.map { case (n, d) => parens(vars(n) <> " : " <> nest(print(0, n, d))) }
      val fors1 = fors.updated(fors.length - 1, fors.last <> " .")
      nest(sep((text("forall") +: fors1) ++ Seq(print(0, i , x))))
  }

  private def nestedLambda(i: Int, fs: List[(Int, Term)], t: Term): Doc = t match {
    case Lam(d, r) =>
      nestedLambda(i + 1, (i, d) :: fs, r)
    case x =>
      val lams = fs.reverse.map { case (n, d) => parens(vars(n) <> " : " <> nest(print(0, n, d))) }
      val lams1 = lams.updated(lams.length - 1, lams.last <> " ->")
      nest(sep((text("\\") +: lams1) ++ Seq(print(0, i , x))))
  }
}

trait PiPrinterAgda extends PrinterAgda with PiAST {
  import scala.collection.immutable.Seq

  abstract override def printA(p: Int, ii: Int, t: Term): Doc = t match {
    case Pi(d, Pi(d1, r)) =>
      parensIf(p > 0, nestedForall(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Pi(d, r) =>
      parensIf(p > 0, sep(Seq("forall " <> parens(vars(ii) <> " : " <> printA(0, ii, d)) <> " -> ", nest(printA(0, ii + 1, r)))))
    case Lam(d, Lam(d1, r)) =>
      parensIf(p > 0, nestedLambda(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Lam(d, r) =>
      parensIf(p > 0, sep(Seq("\\ " <> parens(vars(ii) <> " : " <> printA(0, ii, d)) <> " -> ", nest(printA(0, ii + 1, r)))))
    case i :@: c =>
      parensIf(p > 2, sep(Seq(printA(2, ii, i), nest(printA(3, ii, c)))))
    case _ =>
      super.printA(p, ii, t)
  }

  private def nestedForall(i: Int, fs: List[(Int, Term)], t: Term): Doc = t match {
    case Pi(d, r) =>
      nestedForall(i + 1, (i, d) :: fs, r)
    case x =>
      val fors = fs.reverse.map { case (n,d) => parens(vars(n) <> " : " <> nest(printA(0, n, d))) }
      val fors1 = fors.updated(fors.length - 1, fors.last <> " -> ")
      nest(sep((text("forall") +: fors1) ++ Seq(printA(0, i , x))))
  }

  private def nestedLambda(i: Int, fs: List[(Int, Term)], t: Term): Doc = t match {
    case Lam(d, r) =>
      nestedLambda(i + 1, (i, d) :: fs, r)
    case x =>
      val fors = fs.reverse.map { case (n, d) => parens(vars(n) <> " : " <> nest(printA(0, n, d))) }
      val fors1 = fors.updated(fors.length - 1, fors.last <> " -> ")
      nest(sep((text("\\") +: fors1) ++ Seq(printA(0, i , x))))
  }
}

trait PiPrinterCoq extends PrinterCoq with PiAST {
  import scala.collection.immutable.Seq

  abstract override def printC(p: Int, ii: Int, t: Term): Doc = t match {
    case Pi(d, Pi(d1, r)) =>
      parensIf(p > 0, nestedForall(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Pi(d, r) =>
      parensIf(p > 0, sep(Seq("forall " <> parens(vars(ii) <> " : " <> printC(0, ii, d)) <> " ,", nest(printC(0, ii + 1, r)))))
    case Lam(d, Lam(d1, r)) =>
      parensIf(p > 0, nestedLambda(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Lam(d, r) =>
      parensIf(p > 0, sep(Seq("fun " <> parens(vars(ii) <> " : " <> printC(0, ii, d)) <> " =>", nest(printC(0, ii + 1, r)))))
    case i :@: c =>
      parensIf(p > 2, sep(Seq(printC(2, ii, i), nest(printC(3, ii, c)))))
    case _ =>
      super.printC(p, ii, t)
  }

  private def nestedForall(i: Int, fs: List[(Int, Term)], t: Term): Doc = t match {
    case Pi(d, r) =>
      nestedForall(i + 1, (i, d) :: fs, r)
    case x =>
      val fors = fs.reverse.map { case (n, d) => parens(vars(n) <> " : " <> nest(printC(0, n, d))) }
      val fors1 = fors.updated(fors.length - 1, fors.last <> " ,")
      nest(sep((text("forall") +: fors1) ++ Seq(printC(0, i , x))))
  }

  private def nestedLambda(i: Int, fs: List[(Int, Term)], t: Term): Doc = t match {
    case Lam(d, r) =>
      nestedLambda(i + 1, (i, d) :: fs, r)
    case x =>
      val fors = fs.reverse.map { case (n, d) => parens(vars(n) <> " : " <> nest(printC(0, n, d))) }
      val fors1 = fors.updated(fors.length - 1, fors.last <> " =>")
      nest(sep((text("fun") +: fors1) ++ Seq(printC(0, i , x))))
  }
}

trait PiPrinterIdris extends PrinterIdris with PiAST {
  import scala.collection.immutable.Seq

  abstract override def printI(p: Int, ii: Int, t: Term): Doc = t match {
    case Pi(d, r) =>
      parensIf(p > 0, sep(Seq(parens(vars(ii) <> " : " <> printI(0, ii, d)) <> " -> ", nest(printI(0, ii + 1, r)))))
    case Lam(d, r) =>
      parensIf(p > 0, sep(Seq("\\ " <> vars(ii)  <> " => ", nest(printI(0, ii + 1, r)))))
    case i :@: c =>
      parensIf(p > 2, sep(Seq(printI(2, ii, i), nest(printI(3, ii, c)))))
    case _ =>
      super.printI(p, ii, t)
  }
}

trait PiQuoting extends Quoting with PiAST {
  abstract override def quote(ii: Int, v: Value): Term = v match {
    case VPi(v, f) =>
      Pi(quote(ii, v), quote(ii + 1, f(vfree(Quote(ii)))))
    case VLam(t, f) =>
      Lam(quote(ii, t), quote(ii + 1, f(vfree(Quote(ii)))))
    case _ => super.quote(ii, v)
  }
  abstract override def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NApp(n, v) =>
      :@:(neutralQuote(ii, n), quote(ii, v))
    case _ => super.neutralQuote(ii, n)
  }
}

trait PiEval extends Eval with PiAST {
  abstract override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {
    case Pi(ty, ty1) =>
      VPi(eval(ty, ctx, bound), x => eval(ty1, ctx, x :: bound))
    case Lam(t, e) =>
      VLam(eval(t, ctx, bound), x => eval(e, ctx, x :: bound))
    case e1 :@: e2 =>
      eval(e1, ctx, bound) @@ eval(e2, ctx, bound)
    case _ =>
      super.eval(t, ctx, bound)
  }
}

trait PiCheck extends Check with PiAST {
  abstract override def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value = t match {

    case Pi(x, tp) =>
      val xType = iType(i, path/(1, 2), ctx, x)
      val j = checkUniverse(i, xType, path/(1, 2))
      val xVal = eval(x, ctx, Nil)

      val tpType = iType(i + 1, path/(2, 2), ctx.addType(Local(i), xVal), iSubst(0, Free(Local(i)), tp))
      val k = checkUniverse(i, tpType, path/(2, 2))

      VUniverse(math.max(j, k))
    case Lam(t, e) =>
      val tType = iType(i, path/(1, 2), ctx, t)
      checkUniverse(i, tType, path/(1, 2))
      val tVal = eval(t, ctx, Nil)
      // to force an early error, since the type of `e` is calculated in the body lambda (delayed)
      iType(i + 1, path/(2, 2), ctx.addType(Local(i), tVal), iSubst(0, Free(Local(i)), e))
      VPi(tVal, v => iType(i + 1, path/(2, 2), ctx.addVal(Local(i), v, tVal), iSubst(0, Free(Local(i)), e)))
    case (e1 :@: e2) =>
      iType(i, path/(1, 2), ctx, e1) match {
        case VPi(x, f) =>
          val e2Type = iType(i, path/(2, 2), ctx, e2)
          checkEqual(i, e2Type, x, path/(2, 2))
          f(eval(e2, ctx, Nil))
        case _ =>
          throw TypeError(s"illegal application: $t", path)
      }
    case _ =>
      super.iType(i, path, ctx, t)
  }

  abstract override def iSubst(i: Int, r: Term, it: Term): Term = it match {
    case Pi(ty, ty1) =>
      Pi(iSubst(i, r, ty), iSubst(i + 1, r, ty1))
    case Lam(t, e) =>
      Lam(iSubst(i, r, t), iSubst(i + 1, r, e))
    case (e1 :@: e2) =>
      :@:(iSubst(i, r, e1), iSubst(i, r, e2))
    case _ => super.iSubst(i, r, it)
  }
}

trait PiREPL
  extends CoreREPL
  with PiAST
  with PiMetaSyntax
  with PiPrinter
  with PiPrinterAgda
  with PiPrinterCoq
  with PiPrinterIdris
  with PiCheck
  with PiEval
  with PiQuoting
