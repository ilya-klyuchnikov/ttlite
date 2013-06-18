package superspec.lambda

trait LambdaCheck extends LambdaAST {
  // the goal is to throw exception
  def cKind(g: Context, t: Type, k: Kind): Result[Unit] = (t, k) match {
    case (TFree(x), Star) => lookup(x, g) match {
      case Some(HasKind(Star)) => Right()
      case Some(_) => Left("wrong type")
      case None => Left(s"unknown id: $x")
    }
    case (Fun(kk, kk1), Star) =>
      for {x <- cKind(g, kk, Star).right}
      yield cKind(g, kk1, Star)
  }

  def iType0(g: Context, i: ITerm): Result[Type] =
    iType(0, g, i)

  def iType(i: Int, g: Context, t: ITerm) : Result[Type] = t match {
    case Ann(e, ty) =>
      for {
        _ <- cKind(g, ty, Star).right
        _ <- cType(i, g, e, ty).right
      } yield ty
    case Free(x) =>
      lookup(x, g) match {
        case Some(HasType(ty)) => Right(ty)
        case Some(_) => Left("wrong type")
        case None => Left(s"unknown id: $x")
      }
    case (e1 :@: e2) =>
      iType(i, g, e1).right.flatMap { si => si match {
        case Fun(ty, ty1) =>
          for {_ <- cType(i, g, e2, ty).right} yield ty1
        case _ => Left("")
      }
      }
  }

  def cType(ii: Int, g: Context, ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (Inf(e), ty) =>
      iType(ii, g, e).right.flatMap(ty1 =>
        if (ty1 == ty)
          Right()
        else
          Left("type mismatch")
      )
    case (Lam(e), Fun(ty, ty1)) =>
      cType(ii + 1, (Local(ii), HasType(ty)) :: g, cSubst(0, Free(Local(ii)), e), ty1)
    case _ => Left("type mismatch")
  }
  def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Ann(e, ty) => Ann(cSubst(i, r, e), ty)
    case Bound(j) => if (i == j) r else Bound(j)
    case Free(y) => Free(y)
    case (e1 :@: e2) => iSubst(i, r, e1) :@: cSubst(i, r, e2)
  }
  def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case Inf(e) => Inf(iSubst(ii, r, e))
    case Lam(e) => Lam(cSubst(ii + 1, r, e))
  }
}
