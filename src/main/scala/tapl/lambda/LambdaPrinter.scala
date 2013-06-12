package tapl.lambda

trait LambdaPrinter extends LambdaAST {
  def tPrint(p: Int, t: Type): Doc = t match {
    case TFree(Global(s)) => text(s)
    case Fun(ty, ty1) => parensIf(p > 0, sep(Seq(tPrint(1, ty) <> " ->", nest(tPrint(0, ty1), 2))))
  }

  def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Ann(c, ty) =>
      parensIf(p > 1, cPrint(2, ii, c) <> " :: " <> tPrint(0, ty))
    case Bound(k) =>
      vars(ii - k - 1)
    case Free(Global(s)) =>
      s
    case i :@: c =>
      parensIf(p > 2, sep(Seq(iPrint(2, ii, i), nest(cPrint(3, ii, c), 2))))
  }

  def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case Inf(i) =>
      iPrint(p, ii, i)
    case Lam(c) =>
      parensIf(p > 0, "\\ " <> text(vars(ii)) <> " -> " <> cPrint(0, ii + 1, c))
  }
}
