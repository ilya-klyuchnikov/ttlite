package ttlite.common

import scala.collection.immutable.Queue

object Context {
  def empty[V] =
    new Context[V](Map(), Map(), Queue())
  def fromVals[V](vals : Map[Name, V]) =
    new Context(vals, Map(), Queue())
}
// right now ids handles assumed variables only. This is wrong - it should have all variables
class Context[V] private (val vals: Map[Name, V], val types: Map[Name, V], val ids: Queue[Name]) {

  def addVal(n : Name, v : V, tp : V) : Context[V] =
    new Context(vals + (n -> v), types + (n -> tp), ids.enqueue(n))

  def addType(n : Name, tp : V) : Context[V] =
    new Context(vals, types + (n -> tp), ids.enqueue(n))

  // todo add to ids as well
  def addTypes(tps : Map[Name, V]) : Context[V] =
    new Context(vals, types ++ tps, ids)
}
