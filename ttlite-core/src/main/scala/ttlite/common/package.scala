package ttlite

package object common {
  // this should be extracted into context
  type NameEnv[V] = Map[Name, V]
  // todo: helper methods: bindVal, bindType
  case class Context[V](vals: NameEnv[V], types: NameEnv[V], ids: List[Name])

  def emptyEnv[V] = Map[Name, V]()
  def emptyContext[V] = Context(emptyEnv[V], emptyEnv[V], Nil)

  val vars = {
    // this should be extracted into IO
    val ids = "abcdefghijklmnopqrstuvwxyz"
    val suffs = List("", "1")
    for {j <- suffs; i <- ids} yield s"$i$j"
  }
}
