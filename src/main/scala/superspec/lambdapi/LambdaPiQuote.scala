package superspec.lambdapi

trait LambdaPiQuote extends LambdaPiAST {
  def quote0(v: Value): CTerm =
    quote(0, v)

  def quote(ii: Int, v: Value): CTerm = v match {
    case VLam(f) => Lam(quote(ii + 1, f(vfree(Quote(ii)))))
    case VStar => Inf(Star)
    case VPi(v, f) => Inf(Pi(quote(ii, v), quote(ii + 1, f(vfree(Quote(ii))))))
    case VNeutral(n) => Inf(neutralQuote(ii, n))
  }

  def neutralQuote(ii: Int, n: Neutral): ITerm = n match {
    case NFree(x) => boundFree(ii, x)
    case NApp(n, v) => neutralQuote(ii, n) @@ quote(ii, v)
  }

  def boundFree(ii: Int, n: Name): ITerm = n match {
    case Quote(k) => Bound(math.max(ii - k - 1, 0))
    case x => Free(x)
  }
}
