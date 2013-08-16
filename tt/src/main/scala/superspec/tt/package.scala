package superspec

package object tt {
  type NameEnv[V] = Map[Name, V]
  val ids = "abcdefghijklmnopqrstuvwxyz"
  val suffs = List("", "1")
  val vars = for {j <- suffs; i <- ids} yield s"$i$j"
}
