package ttlite

package object common {
  // this should be extracted into context
  type NameEnv[V] = Map[Name, V]

  val vars = {
    // this should be extracted into IO
    val ids = "abcdefghijklmnopqrstuvwxyz"
    val suffs = List("", "1")
    for {j <- suffs; i <- ids} yield s"$i$j"
  }
}
