package tapl

trait LambdaPiPrinter extends LambdaPiAST {
  def iPrint(p: Int, ii: Int, t: ITerm): Doc = t match {
    case Ann(c, ty) =>
      parensIf(p > 1, cPrint(2, ii, c) <> " :: " <> cPrint(0, ii, ty))
    case Star => "*"
    case Pi(d, Inf(Pi(d1, r))) =>
      parensIf(p > 0, nestedForall(ii + 2, List((ii + 1, d1), (ii, d)), r))
    case Pi(d, r) =>
      parensIf(p > 0, sep(Seq("forall " <> vars(ii) <> " :: " <> cPrint(0, ii, d) <> " .", cPrint(0, ii + 1, r))))
    case Bound(k) =>
      vars(ii - k - 1)
    case Free(Global(s)) =>
      s
    case i :@: c =>
      parensIf(p > 2, sep(Seq(iPrint(2, ii, i), nest(cPrint(3, ii, c), 2))))
    case _ => ???
  }

  def cPrint(p: Int, ii: Int, t: CTerm): Doc = t match {
    case Inf(i) =>
      iPrint(p, ii, i)
    case Lam(c) =>
      parensIf(p > 0, "\\ " <> vars(ii) <> " -> " <> cPrint(0, ii + 1, c))
    case _ => ???
  }

  def nestedForall(i: Int, fs: List[(Int, CTerm)], t: CTerm): Doc = t match {
    case Inf(Pi(d, r)) =>
      nestedForall(i + 1, (i, d) :: fs, r)
    case x =>
      sep(Seq("forall" <> sep(fs.map{case (n,d) => parens(vars(n) <> " :: " <> cPrint(0, n, d))}), cPrint(0, i , x)))
  }
}
