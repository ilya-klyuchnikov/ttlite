package tapl

trait LambdaPiPrinter extends LambdaPiAST {
  def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Ann(c, ty) =>
      parensIf(p > 1, cPrint(2, ii, c) <> " :: " <> cPrint(0, ii, ty))
    case Star => "*"
    case Pi(d, Inf(Pi(d1, r))) =>
      parensIf(p > 0, nestedForall(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Pi(d, r) =>
      parensIf(p > 0, nest(sep(Seq("forall " <> vars(ii) <> " :: " <> cPrint(0, ii, d) <> " . ", cPrint(0, ii + 1, r))), 0))
    case Bound(k) =>
      vars(ii - k - 1)
    case Free(Global(s)) =>
      s
    case i :@: c =>
      parensIf(p > 2, nest(sep(Seq(iPrint(2, ii, i), cPrint(3, ii, c))), 0))
    case _ => ???
  }

  def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case Inf(i) =>
      iPrint(p, ii, i)
    case Lam(c) =>
      parensIf(p > 0, "\\ " <> vars(ii) <> " -> " <> nest(cPrint(0, ii + 1, c), 2))
    case _ => ???
  }

  def nestedForall(i: Int, fs: List[(Int, CTerm)], t: CTerm): Doc = t match {
    case Inf(Pi(d, r)) =>
      nestedForall(i + 1, (i, d) :: fs, r)
    case x =>
      nest(sep(Seq("forall " <> nest(sep(fs.reverse.map{case (n,d) => parens(vars(n) <> " :: " <> cPrint(0, n, d))}), 2) <> " . ", cPrint(0, i , x))), 2)
  }
}
