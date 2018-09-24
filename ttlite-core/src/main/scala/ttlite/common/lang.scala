package ttlite.common

import scala.collection.immutable.Seq

trait AST {

  trait Term
  case class Free(n: Name) extends Term

  trait Neutral
  case class NFree(n: Name) extends Neutral

  trait Value
  case class VNeutral(n: Neutral) extends Value
  case class VUniverse(i: Int) extends Value

  final type Env = List[Value]
  final type NameEnv[V] = Map[Name, V]

  // names of bound variables
  val vars: List[String] = {
    val ids = "abcdefghijklmnopqrstuvwxyz"
    val suffs = List("", "1")
    for {j <- suffs; i <- ids} yield s"$i$j"
  }

  def vfree(n: Name): Value = VNeutral(NFree(n))
}

trait MetaSyntax extends AST {
  def translate(m: MTerm): Term
  def isPredefinedGlobal(g: Global): Boolean
}

trait Printer extends AST with PrettyPrinter {

  def pp(c: Term): String =
    pretty(print(0, 0, c))

  def print(p: Int, ii: Int, t: Term): Doc

  // print left-associative terms (like applications)
  def printL(p: Int, ii: Int, s: Symbol, op2: Term, ops: Term*): Doc = {

    val second: Doc =
      if (ops.nonEmpty) print(3, ii, ops.last) else print(3, ii, op2)
    val first: Doc =
      if (ops.nonEmpty) printL(2, ii, s, op2, ops.init:_*) else s.name

    parensIf(p > 2, sep(Seq(first, nest(second))))
  }
}

trait PrinterAgda extends AST with PrettyPrinter {
  def printA(p: Int, ii: Int, t: Term): Doc

  // print left-associative terms (like applications)
  def printAL(p: Int, ii: Int, s: Symbol, op2: Term, ops: Term*): Doc = {
    val second: Doc =
      if (ops.nonEmpty) printA(3, ii, ops.last) else printA(3, ii, op2)
    val first: Doc =
      if (ops.nonEmpty) printAL(2, ii, s, op2, ops.init:_*) else s.name
    parensIf(p > 2, sep(Seq(first, nest(second))))
  }
}

trait PrinterCoq extends AST with PrettyPrinter {
  def printC(p: Int, ii: Int, t: Term): Doc

  // print left-associative terms (like applications)
  def printCL(p: Int, ii: Int, s: Symbol, op2: Term, ops: Term*): Doc = {
    val second: Doc =
      if (ops.nonEmpty) printC(3, ii, ops.last) else printC(3, ii, op2)
    val first: Doc =
      if (ops.nonEmpty) printCL(2, ii, s, op2, ops.init:_*) else s.name
    parensIf(p > 2, sep(Seq(first, nest(second))))
  }
}

trait PrinterIdris extends AST with PrettyPrinter {
  def printI(p: Int, ii: Int, t: Term): Doc

  // print left-associative terms (like applications)
  def printIL(p: Int, ii: Int, s: Symbol, op2: Term, ops: Term*): Doc = {
    val second: Doc =
      if (ops.nonEmpty) printI(3, ii, ops.last) else printI(3, ii, op2)
    val first: Doc =
      if (ops.nonEmpty) printIL(2, ii, s, op2, ops.init:_*) else s.name
    parensIf(p > 2, sep(Seq(first, nest(second))))
  }
}

trait Quoting extends AST {
  def quote0(v: Value): Term =
    quote(0, v)

  def quote(ii: Int, v: Value): Term

  def neutralQuote(ii: Int, n: Neutral): Term
}

trait Eval extends AST {
  def eval0(c: Term): Value = eval(c, Context.empty[Value], Nil)
  // just for residuator
  def eval(t: Term, named: NameEnv[Value], bound: Env): Value =
    eval(t, Context.fromVals(named), bound)
  def eval(t: Term, ctx: Context[Value], bound: Env): Value
}

trait Check extends AST with Quoting with Eval with Printer {

  final def checkEqual(i: Int, inferred: Term, expected: Term, path : Path) {
    if (inferred != expected) {
      throw TypeError(s"expected: ${pp(expected)},\ninferred: ${pp(inferred)}", path)
    }
  }

  final def checkEqual(i: Int, inferred: Value, expected: Term, path : Path) {
    val infTerm = quote(i, inferred)
    if (infTerm != expected) {
      throw TypeError(s"expected: ${pp(expected)},\ninferred: ${pp(infTerm)}", path)
    }
  }

  final def checkEqual(i: Int, inferred: Value, expected: Value, path : Path) {
    val infTerm = quote(i, inferred)
    val expTerm = quote(i, expected)
    if (infTerm != expTerm) {
      throw TypeError(s"expected: ${pp(expTerm)},\ninferred: ${pp(infTerm)}", path)
    }
  }

  final def require(cond : Boolean, path : Path, expected : String, inferred: Term) {
    if (!cond) {
      throw TypeError(s"expected: ${expected},\nfound: ${pp(inferred)}", path)
    }
  }

  def checkUniverse(i: Int, inferred: Value, path : Path): Int = inferred match {
    case VUniverse(k) =>
      k
    case _ =>
      val infTerm = quote(i, inferred)
      throw TypeError(s"expected: Set*,\ninferred: ${pp(infTerm)}", path)
  }

  def iType0(ctx: Context[Value], i: Term): Value =
    iType(0, Path.empty, ctx, i)
  def iType(i: Int, path : Path, ctx: Context[Value], t: Term): Value
  def iSubst(i: Int, r: Term, it: Term): Term
}