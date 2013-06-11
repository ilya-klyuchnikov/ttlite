package tapl.lambda

trait LambdaPrinter extends LambdaAST {
  def tPrint(p: Int, t: Type): Doc = t match {
    case TFree(Global(s)) => text(s)
    case Fun(ty, ty1) => parensIf(p > 0, sep(Seq(tPrint(0, ty) <> " ->", nest(tPrint(0, ty1), 2))))
  }
}
