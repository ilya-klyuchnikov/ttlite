package ttlite.common

// NAMES
sealed class Name (s : String) {
  override def toString = s
}
case class Global(n: String) extends Name(n)
case class Assumed(n: String) extends Name(n)
case class Local(i: Int) extends Name(s"<$i>")
case class Quote(i: Int) extends Name(s"[$i]")
// META-SYNTAX
sealed trait MTerm extends RichPositional {
  def ~(t1: MTerm) = @@(this, t1)
  def subTerm(path : Path) : MTerm
}
case class MVar(n: Name) extends MTerm {
  def subTerm(path : Path) : MTerm = path match {
    case Nil => this
    case _ => sys.error("??")
  }
}
case class @@(t1: MTerm, t2: MTerm) extends MTerm {
  override def toString = s"$t1 ~ $t2"
  def subTerm(path : Path) : MTerm = path match {
    case Nil => this
    case L :: p => t1.subTerm(p)
    case R :: p => t2.subTerm(p)
  }
}
case class MAnn(t1: MTerm, t2: MTerm) extends MTerm {
  def subTerm(path : Path) : MTerm = path match {
    case Nil => this
    case L :: p => t1.subTerm(p)
    case R :: p => t2.subTerm(p)
  }
}
case class MBind(id: String, tp: MTerm, body: MTerm) extends MTerm {
  def subTerm(path : Path) : MTerm = path match {
    case Nil => this
    case L :: p => tp.subTerm(p)
    case R :: p => body.subTerm(p)
  }
}

trait Stmt[+I]
case class Let[I](n: String, i: I) extends Stmt[I]
case class TypedLet[I](n: String, i: I, t: I) extends Stmt[I]
case class Assume[I](n: String, i: I) extends Stmt[I]
case class Eval[I](e: I) extends Stmt[I]
case class Import(s: String) extends Stmt[Nothing]
case class ExportToAgda(s: String) extends Stmt[Nothing]
case class Reload(s: String) extends Stmt[Nothing]
case object Quit extends Stmt[Nothing]
