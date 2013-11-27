package ttlite.sc

import mrsc.core._
import ttlite.core.CoreREPL

trait GraphPrettyPrinter2 extends CoreREPL with TTSc {

  def tgToString(tg: TGraph[Conf, Label]): String = {
    val focus = tg.focus
    toString(tg.root, focus)
  }

  // kiama pretty printer is not able to produce single string, so here is a hack
  def toString(c: Conf): String = {
    val s = pretty(pretty(c.term), 1000) + " |||| " + pretty(pretty(c.tp), 1000)
    s.replace('\n', ' ').replaceAll("\\s+", " ")
  }

  def labelToString(l: Label): String =
    l.toString

  def toString(node: TNode[Conf, Label], focus: Option[TPath], indent: String = ""): String = {
    val sb = new StringBuilder()
    sb.append(indent + "|__" + toString(node.conf))
    if (node.base.isDefined) {
      sb.append("*")
    }
    if (focus == Some(node.tPath)) {
      sb.append(" <===")
    }
    for (edge <- node.outs) {
      sb.append("\n  " + indent + "|" + labelToString(edge.driveInfo))
      sb.append("\n" + toString(edge.node, focus, indent + "  "))
    }
    sb.toString
  }

}
