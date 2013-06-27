package superspec

import org.kiama.output.PrettyPrinter

trait Common extends PrettyPrinter {
  trait Name
  case class Global(n: String) extends Name
  case class Local(i: Int) extends Name
  case class Quote(i: Int) extends Name

  type Result[A] = Either[String, A]
  type NameEnv[V] = List[(Name, V)]

  trait Stmt[+I, +TInf]
  case class Let[I](n: String, i: I) extends Stmt[I, Nothing]
  case class Assume[TInf](ns: List[(String, TInf)]) extends Stmt[Nothing, TInf]
  case class Eval[I](e: I) extends Stmt[I, Nothing]
  case class Import(s: String) extends Stmt[Nothing, Nothing]
  case class Supercompile[I](e: I) extends Stmt[I, Nothing]

  val ids = "abcdefghijklmnopqrstuvwxyz"
  val suffs = List("", "1")
  val vars = for {j <- suffs; i <- ids} yield s"$i$j"

  // utility
  def lookup[A, B](k: A, kvs: List[(A, B)]): Option[B] =
    kvs.find(_._1 == k).map(_._2)

  def parensIf(b: Boolean, d: Doc) =
    if (b) parens(d) else d
}