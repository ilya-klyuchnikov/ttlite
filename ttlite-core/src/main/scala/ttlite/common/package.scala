package ttlite

package object common {
  // this should be extracted into MPath class or something similar
  sealed trait PathElem
  object L extends PathElem
  object R extends PathElem
  type Path = List[PathElem]
  // should be lazy??
  def p(i : Int, n : Int) : Path = (i, n) match {
    case (1, 2) => List(L)
    case (2, 2) => List(R)
    case (i, n) if i == n => List(R)
    case (i, n) => L :: p(i, n - 1)
  }
  implicit class PathWrapper(path : Path) {
    def /(i: Int, n: Int) = path ++ p(i, n)
  }

  // this should be extracted into context
  type NameEnv[V] = Map[Name, V]
  // todo: helper methods: bindVal, bindType
  case class Context[V](vals: NameEnv[V], types: NameEnv[V], ids: List[Name])

  def emptyEnv[V] = Map[Name, V]()
  def emptyContext[V] = Context(emptyEnv[V], emptyEnv[V], Nil)

  // this should be extracted into IO
  val ids = "abcdefghijklmnopqrstuvwxyz"
  val suffs = List("", "1")
  val vars = for {j <- suffs; i <- ids} yield s"$i$j"
}
