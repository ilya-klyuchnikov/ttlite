package tapl

// could we rewrite it better with scalaz??
// this is just terrific strange code
trait LambdaPiCheck extends LambdaPiAST with LambdaPiQuote with LambdaPiEval {
  // TODO
  def iType0(g: (NameEnv[Value], Context), i: ITerm): Result[Type] =
    iType(0, g, i)

  def iType(i: Int, g: (NameEnv[Value], Context), t: ITerm): Result[Type] = t match {
    case Ann(e, tyt) =>
        cType(i, g, tyt, VStar).right.flatMap { _ =>
          val ty = cEval(tyt, (g._1, Nil))
          for { _ <- cType(i, g, e, ty).right} yield ty
      }
    case Star =>
      Right(VStar)
    case Pi(tyt, tyt1) =>
      cType(i, g, tyt, VStar).right.flatMap { _ =>
        val ty = cEval(tyt, (g._1, Nil))
        for {
          _ <- cType(i + 1, (g._1, (Local(i), ty) :: g._2), null, null).right
        } yield VStar
      }
    case Free(x) =>
      lookup(x, g._2) match {
        case Some(ty) => Right(ty)
        case None => Left("unknown id")
      }
    case (e1 :@: e2) =>
      iType(i, g, e1).right.flatMap { si => si match {
        case VPi(ty, ty1) =>
          cType(i, g, e2, ty) match {
            case Right(_) =>
              Right(ty1(cEval(e2, (g._1, Nil))))
            case Left(_) => Left("")
          }
        case _ => Left("")
      }
      }
  }

  def cType(ii: Int, g: (NameEnv[Value], Context), ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (Inf(e), ty) =>
      iType(ii, g, e).right.flatMap(ty1 =>
        if (quote0(ty1) == quote0(ty))
          Right()
        else
          Left("type mismatch")
      )
    case (Lam(e), VPi(ty, ty1)) =>
      cType(ii + 1, (g._1, (Local(ii), ty) :: g._2 ), cSubst(0, Free(Local(ii)), e), ty1(vfree(Local(ii))))
    case _ => Left("type mismatch")
  }
  def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Ann(c, c1) => Ann(cSubst(i, r, c), cSubst(i, r, c1))
    case Star => Star
    case Pi(ty, ty1) => Pi(cSubst(i, r, ty), cSubst(i + 1, r, ty1))
    case Bound(j) => if (i == j) r else Bound(j)
    case Free(y) => Free(y)
    case (e1 :@: e2) => iSubst(i, r, e1) :@: cSubst(i, r, e2)
  }
  def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case Inf(e) => Inf(iSubst(ii, r, e))
    case Lam(e) => Lam(cSubst(ii + 1, r, e))
  }
}
