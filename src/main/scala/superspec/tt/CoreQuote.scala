package superspec.tt

trait CoreQuote extends CoreAST {
  def quote0(v: Value): Term =
    quote(0, v)

  def quote(ii: Int, v: Value): Term = v match {
    case VLam(t, f) =>
      Lam(quote(ii, t), quote(ii + 1, f(vfree(Quote(ii)))))
    case VStar =>
      Star
    case VPi(v, f) =>
      Pi(quote(ii, v), quote(ii + 1, f(vfree(Quote(ii)))))
    case VNeutral(n) =>
      neutralQuote(ii, n)
  }

  def neutralQuote(ii: Int, n: Neutral): Term = n match {
    case NFree(x) =>
      boundFree(ii, x)
    case NApp(n, v) =>
      neutralQuote(ii, n) @@ quote(ii, v)
  }

  def boundFree(ii: Int, n: Name): Term = n match {
    case Quote(k) =>
      Bound(math.max(ii - k - 1, 0))
    case x =>
      Free(x)
  }
}
