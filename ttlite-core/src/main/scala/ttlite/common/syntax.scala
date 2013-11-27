package ttlite.common

import scala.collection.immutable.Queue
import scala.annotation.tailrec

object Path {
  sealed trait PathElem
  object L extends PathElem
  object R extends PathElem
  def norm(i : Int, n : Int) : List[PathElem] = (i, n) match {
    case (1, 2) => List(L)
    case (2, 2) => List(R)
    case (i, n) if i == n => List(R)
    case (i, n) => L :: norm(i, n - 1)
  }
  @tailrec
  private def subterm0(elems : List[PathElem], rest : Queue[(Int, Int)], mt : MTerm) : MTerm = elems match {
    case Nil if rest.isEmpty =>
      mt
    case Nil =>
      val (seg, rest1) = rest.dequeue
      val elems1 = norm(seg._1, seg._2)
      subterm0(elems1, rest1, mt)
    case elem :: elems1 => (mt, elem) match {
      case (t1 @@ t2, L) =>
        subterm0(elems1, rest, t1)
      case (t1 @@ t2, R) =>
        subterm0(elems1, rest, t2)
      case (MAnn(t1, t2), L) =>
        subterm0(elems1, rest, t1)
      case (MAnn(t1, t2), R) =>
        subterm0(elems1, rest, t2)
      case (MBind(_, t1, t2), L) =>
        subterm0(elems1, rest, t1)
      case (MBind(_, t1, t2), R) =>
        subterm0(elems1, rest, t2)
      case _ => sys.error("??")
    }
  }
  def subterm(mt : MTerm, path : Path) : MTerm =
    subterm0(Nil, path.rawElems, mt)
  val empty = Path(Queue())
}

case class Path private (rawElems : Queue[(Int, Int)]) {
  def /(i : Int, from : Int) : Path =
    Path(rawElems.enqueue((i, from)))
}

// NAMES
sealed class Name (s : String) {
  override def toString = s
}
case class Global(n: String) extends Name(n)
case class Assumed(n: String) extends Name(n)
case class Local(i: Int) extends Name(s"<$i>")
case class Quote(i: Int) extends Name(s"[$i]")
// META-SYNTAX
// TODO it is better to name it *shallow term* and *shallow syntax*
sealed trait MTerm extends RichPositional {
  def ~(t1: MTerm) = @@(this, t1)
}
case class MVar(n: Name) extends MTerm
case class @@(t1: MTerm, t2: MTerm) extends MTerm
case class MAnn(t1: MTerm, t2: MTerm) extends MTerm
case class MBind(id: String, tp: MTerm, body: MTerm) extends MTerm

trait Stmt[+I]
case class Let[I](n: String, i: I) extends Stmt[I]
case class TypedLet[I](n: String, i: I, t: I) extends Stmt[I]
case class Assume[I](n: String, i: I) extends Stmt[I]
case class Eval[I](e: I) extends Stmt[I]
case class Import(s: String) extends Stmt[Nothing]
case class ExportToAgda(s: String) extends Stmt[Nothing]
case class Reload(s: String) extends Stmt[Nothing]
case object Quit extends Stmt[Nothing]
