package tapl

trait Common {
  trait Name
  case class Global(n: String) extends Name
  case class Local(i: Int) extends Name
  case class Quote(i: Int) extends Name

  trait Type
  case class TFree(n: Name) extends Type
  case class Fun(t1: Type, t2: Type) extends Type

  trait Kind
  case object Star extends Kind

  trait Info
  case class HasKind(k: Kind) extends Info
  case class HasType(t: Type) extends Info

  type Context = List[(Name, Info)]
  type Result[A] = Either[String, A]
  type NameEnv[V] = List[(Name, V)]

  trait Stmt[+I, +TInf]
  case class Let[I](n: String, i: I) extends Stmt[I, Nothing]
  case class Assume[TInf](ns: List[(String, TInf)]) extends Stmt[Nothing, TInf]
  case class Eval[I](e: I) extends Stmt[I, Nothing]
  case class PutStrLm(s: String) extends Stmt[Nothing, Nothing]
  case class Out(s: String) extends Stmt[Nothing, Nothing]

  // TODO
  val vars: Stream[String] = null
}