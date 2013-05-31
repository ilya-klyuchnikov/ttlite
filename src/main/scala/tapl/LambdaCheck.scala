package tapl

trait LambdaCheck extends LambdaAST {
   def cKind(g: Context, t: Type, k: Kind): Result[Unit] = (t, k) match {
     case (TFree(x), Star) => lookup(x, g) match {
       case Some(HasKind(Star)) => Right()
       case Some(_) => Left("wrong type")
       case None => Left("unknown id")
     }
     case (Fun(kk, kk1), Star) => {
       // TODO: chain
       cKind(g, kk, Star)
       cKind(g, kk1, Star)
     }
   }
}
