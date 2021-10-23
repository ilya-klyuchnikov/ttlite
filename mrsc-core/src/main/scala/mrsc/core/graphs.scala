package mrsc.core

import scala.annotation.tailrec

case class SNode[C, D](conf: C, in: SEdge[C, D], base: Option[SPath], sPath: SPath) {

  lazy val tPath: List[Int] = sPath.reverse

  val ancestors: List[SNode[C, D]] =
    if (in == null) List() else in.node :: in.node.ancestors

  override def toString: String = conf.toString
}

case class SEdge[C, D](node: SNode[C, D], driveInfo: D)

case class SGraph[C, D](
    incompleteLeaves: List[SNode[C, D]],
    completeLeaves: List[SNode[C, D]],
    completeNodes: List[SNode[C, D]],
) {

  val isComplete: Boolean = incompleteLeaves.isEmpty
  val current: SNode[C, D] = if (isComplete) null else incompleteLeaves.head
  lazy val size: Int = completeNodes.size + incompleteLeaves.size
  lazy val depth: Int = current.ancestors.size + 1
}

case class TNode[C, D](conf: C, outs: List[TEdge[C, D]], base: Option[TPath], tPath: TPath) {

  lazy val sPath: List[Int] = tPath.reverse

  @tailrec
  final def get(relTPath: TPath): TNode[C, D] = relTPath match {
    case Nil     => this
    case i :: rp => outs(i).node.get(rp)
  }
}

case class TEdge[C, D](node: TNode[C, D], driveInfo: D)

case class TGraph[C, D](root: TNode[C, D], leaves: List[TNode[C, D]], focus: Option[TPath] = None) {
  def get(tPath: TPath): TNode[C, D] = root.get(tPath)
}

case class Tmp[C, D](node: TNode[C, D], in: SEdge[C, D])

object Transformations {
  def transpose[C, D, E](g: SGraph[C, D]): TGraph[C, D] = {
    val allLeaves = g.completeLeaves ++ g.incompleteLeaves
    val allNodes = g.completeNodes ++ g.incompleteLeaves
    val orderedNodes = allNodes.sortBy(_.sPath)(PathOrdering)
    val rootNode = orderedNodes.head

    val leafPathes = allLeaves.map(_.sPath)
    val levels = orderedNodes.groupBy(_.sPath.length).toList.sortBy(_._1).map(_._2)
    val sortedLevels = levels.map(_.sortBy(_.tPath)(PathOrdering))
    val (tNodes, tLeaves) = subTranspose(sortedLevels, leafPathes)
    val nodes = tNodes map { _.node }
    val leaves = tLeaves map { _.node }
    TGraph(nodes.head, leaves, Option(g.current).map(_.tPath))
  }

  private def subTranspose[C, D](
      nodes: List[List[SNode[C, D]]],
      leaves: List[TPath],
  ): (List[Tmp[C, D]], List[Tmp[C, D]]) =
    nodes match {
      case Nil =>
        (Nil, Nil)

      case ns1 :: Nil =>
        val tmpNodes: List[Tmp[C, D]] = ns1 map { n =>
          val node = TNode[C, D](n.conf, Nil, n.base.map(_.reverse), n.tPath)
          Tmp(node, n.in)
        }
        val tmpLeaves = tmpNodes.filter { tmp =>
          leaves.contains(tmp.node.sPath)
        }
        (tmpNodes, tmpLeaves)

      case ns1 :: ns =>
        val (allCh, leaves1) = subTranspose(ns, leaves)
        val allchildren = allCh.groupBy { _.node.sPath.tail }
        val tmpNodes = ns1 map { n =>
          val children: List[Tmp[C, D]] = allchildren.getOrElse(n.sPath, Nil)
          val edges = children map { tmp => TEdge(tmp.node, tmp.in.driveInfo) }
          val node = TNode(n.conf, edges, n.base.map(_.reverse), n.tPath)
          Tmp(node, n.in)
        }
        val tmpLeaves = tmpNodes.filter { tmp => leaves.contains(tmp.node.sPath) }
        (tmpNodes, tmpLeaves ++ leaves1)
    }
}

object PathOrdering extends Ordering[TPath] {
  @tailrec
  final def compare(p1: TPath, p2: TPath): Int =
    if (p1.length < p2.length) -1
    else if (p1.length > p2.length) +1
    else {
      val result = p1.head compare p2.head
      if (result == 0) {
        compare(p1.tail, p2.tail)
      } else {
        result
      }
    }
}
