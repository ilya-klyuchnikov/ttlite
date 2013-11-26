package ttlite.common

object Context {
  def empty[V] =
    new Context[V](Map(), Map(), Nil)
  def fromVals[V](vals : NameEnv[V]) =
    new Context(vals, Map(), Nil)
}
// right now ids handles assumed variables only. This is wrong - it should have all variables
class Context[V] private (val vals: NameEnv[V], val types: NameEnv[V], val ids: List[Name]) {
  def addGlobal(s : String, v : V, tp : V): Context[V] = {
    val n = Global(s)
    new Context(vals + (n -> v), types + (n -> tp), ids)
  }

  def addLocal(i : Int, v : V, tp : V) : Context[V] = {
    val n = Local(i)
    new Context(vals + (n -> v), types + (n -> tp), ids)
  }

  def addAssumed(s : String, tp : V) : Context[V] = {
    val n = Assumed(s)
    new Context(vals, types + (n -> tp), n :: ids)
  }

  def addTyped(n : Name, tp : V) : Context[V] = {
    new Context(vals, types + (n -> tp), ids)
  }

  def addTypes(tps : NameEnv[V]) : Context[V] =
    new Context(vals, types ++ tps, ids)
}
