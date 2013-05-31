package tapl

trait LambdaQuote extends LambdaAST {
  def quote0(v: Value): CTerm =
    quote(0, v)

  def quote(ii: Int, v: Value): CTerm = v match {
    case VLam(f) => Lam(quote(ii + 1, f(vfree(Quote(ii)))))
    case VNeutral(n) => Inf(neutralQuote(ii, n))
  }

  def neutralQuote(ii: Int, n: Neutral): ITerm = n match {
    case NFree(x) => boundFree(ii, x)
    case NApp(n, v) => neutralQuote(ii, n) :@: quote(ii, v)
  }

  def boundFree(ii: Int, n: Name): ITerm = n match {
    case Quote(k) => Bound(ii - k - 1)
    case x => Free(x)
  }
}
