package mrsc.core

import scala.annotation.tailrec
import scala.collection.mutable
import scala.collection.mutable.ListBuffer

trait GraphRewriteRules[C, D] {
  type N = SNode[C, D]
  type G = SGraph[C, D]
  type S = GraphRewriteStep[C, D]
  def steps(g: G): List[S]
}

enum GraphRewriteStep[C, D] {
  case CompleteCurrentNodeStep() extends GraphRewriteStep[C, D]
  case AddChildNodesStep[C, D](ns: List[(C, D)]) extends GraphRewriteStep[C, D]
  case FoldStep[C, D](to: SPath) extends GraphRewriteStep[C, D]
  case RebuildStep[C, D](c: C) extends GraphRewriteStep[C, D]
  case RollbackStep[C, D](to: SPath, c: C) extends GraphRewriteStep[C, D]
}

case class GraphGenerator[C, D](rules: GraphRewriteRules[C, D], conf: C) extends Iterator[SGraph[C, D]] {

  private val completeGs: mutable.Queue[SGraph[C, D]] = mutable.Queue()
  private var pendingGs: List[SGraph[C, D]] = List(initial(conf))

  private def initial(c: C): SGraph[C, D] = {
    val initialNode = SNode[C, D](c, null, None, Nil)
    SGraph(List(initialNode), Nil, Nil)
  }

  private def normalize(): Unit =
    while (completeGs.isEmpty && pendingGs.nonEmpty) {
      val pendingDelta = ListBuffer[SGraph[C, D]]()
      val g = pendingGs.head
      val rewrittenGs = rules.steps(g) map { GraphGenerator.executeStep(_, g) }
      for (g1 <- rewrittenGs)
        if (g1.isComplete) {
          completeGs.enqueue(g1)
        } else {
          pendingDelta += g1
        }
      pendingGs = pendingDelta ++: pendingGs.tail
    }

  override def hasNext: Boolean = {
    normalize()
    completeGs.nonEmpty
  }

  override def next(): SGraph[C, D] = {
    if (!hasNext) throw new NoSuchElementException("no graph")
    completeGs.dequeue()
  }
}

object GraphGenerator {
  @tailrec
  def executeStep[C, D](step: GraphRewriteStep[C, D], g: SGraph[C, D]): SGraph[C, D] = {
    import GraphRewriteStep._
    step match {
      case AddChildNodesStep(List()) =>
        executeStep(CompleteCurrentNodeStep(), g)
      case CompleteCurrentNodeStep() =>
        SGraph(g.incompleteLeaves.tail, g.current :: g.completeLeaves, g.current :: g.completeNodes)
      case AddChildNodesStep(ns) =>
        val deltaLeaves: List[SNode[C, D]] = ns.zipWithIndex map { case ((conf, dInfo), i) =>
          val in = SEdge(g.current, dInfo)
          SNode(conf, in, None, i :: g.current.sPath)
        }
        SGraph(deltaLeaves ++ g.incompleteLeaves.tail, g.completeLeaves, g.current :: g.completeNodes)
      case FoldStep(basePath) =>
        val node = g.current.copy(base = Some(basePath))
        SGraph(g.incompleteLeaves.tail, node :: g.completeLeaves, node :: g.completeNodes)
      case RebuildStep(c) =>
        val node = g.current.copy(conf = c)
        SGraph(node :: g.incompleteLeaves.tail, g.completeLeaves, g.completeNodes)
      case RollbackStep(sPath, c) =>
        val to = g.current.ancestors.find(_.sPath == sPath).get
        def prune_?(n: SNode[C, D]) = n.tPath.startsWith(to.tPath)
        val node = to.copy(conf = c)
        val completeNodes1 = g.completeNodes.filterNot(prune_?)
        val completeLeaves1 = g.completeLeaves.filterNot(prune_?)
        val incompleteLeaves1 = g.incompleteLeaves.tail.filterNot(prune_?)
        SGraph(node :: incompleteLeaves1, completeLeaves1, completeNodes1)
    }
  }
}
