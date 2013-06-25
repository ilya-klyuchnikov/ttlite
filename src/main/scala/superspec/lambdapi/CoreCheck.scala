package superspec.lambdapi

// TODO: can we unify type-checking and evaluation -
trait CoreCheck extends CoreAST with CoreQuote with CoreEval with CorePrinter {
  def iType0(named: NameEnv[Value], bound: NameEnv[Value], i: ITerm): Result[Type] =
    iType(0, named, bound, i)

  def iType(i: Int, named: NameEnv[Value], bound: NameEnv[Value], t: ITerm): Result[Type] = t match {
    case Ann(e, tyt) =>
        cType(i, named, bound, tyt, VStar).right.flatMap { _ =>
          val ty = eval(tyt, named, Nil)
          for { _ <- cType(i, named, bound, e, ty).right} yield ty
      }
    case Star =>
      Right(VStar)
    case Pi(tyt, tyt1) =>
      cType(i, named, bound, tyt, VStar).right.flatMap { _ =>
        val ty = eval(tyt, named, Nil)
        for {
          _ <- cType(i + 1, named, (Local(i), ty) :: bound, cSubst(0, Free(Local(i)), tyt1), VStar).right
        } yield VStar
      }
    case Free(x) =>
      lookup(x, bound) match {
        case Some(ty) => Right(ty)
        case None => Left(s"unknown id: $x")
      }
    case (e1 :@: e2) =>
      iType(i, named, bound, e1).right.flatMap { _ match {
        case VPi(ty, ty1) =>
          cType(i, named, bound, e2, ty) match {
            case Right(_) =>
              Right(ty1(eval(e2, named, Nil)))
            case Left(s) => Left(s)
          }
        case _ => Left(s"illegal application: $t")
      }
      }
  }

  // checks that ct has type t
  def cType(ii: Int, named: NameEnv[Value], bound: NameEnv[Value], ct: CTerm, t: Type): Result[Unit] = (ct, t) match {
    case (Inf(e), _) =>
      iType(ii, named, bound, e).right.flatMap(ty1 =>
        if (quote0(ty1) == quote0(t))
          Right()
        else
          Left(s"type mismatch. inferred: ${pretty(cPrint(0, 0, quote0(ty1)))}. expected: ${pretty(cPrint(0, 0, quote0(t)))}. for expression ${pretty(iPrint(0, 0, e))}")
      )
    case (Lam(e), VPi(ty, ty1)) =>
      cType(ii + 1, named, (Local(ii), ty) :: bound , cSubst(0, Free(Local(ii)), e), ty1(vfree(Local(ii))))
    case _ => Left(s"type mismatch: $ct")
  }
  def iSubst(i: Int, r: ITerm, it: ITerm): ITerm = it match {
    case Ann(c, c1) => Ann(cSubst(i, r, c), cSubst(i, r, c1))
    case Star => Star
    case Pi(ty, ty1) => Pi(cSubst(i, r, ty), cSubst(i + 1, r, ty1))
    case Bound(j) => if (i == j) r else Bound(j)
    case Free(y) => Free(y)
    case (e1 :@: e2) => iSubst(i, r, e1) @@ cSubst(i, r, e2)
  }
  def cSubst(ii: Int, r: ITerm, ct: CTerm): CTerm = ct match {
    case Inf(e) => Inf(iSubst(ii, r, e))
    case Lam(e) => Lam(cSubst(ii + 1, r, e))
  }
}
