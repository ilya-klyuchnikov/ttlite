package superspec

import mrsc.core._
import superspec.lambdapi.CoreREPL

trait PiGraphPrettyPrinter extends CoreREPL with SuperSpec {

  def tgToString(tg: TGraph[Conf, Label]): String = {
    val focus = tg.focus
    toString(tg.root, focus)
  }

  def toString(c: CTerm): String = {
    val s = pretty(int.icprint(c), 1000)
    s.replace('\n', ' ').replaceAll("\\s+", " ")
  }

  def labelToString(l: Label): String =
    l.toString

  def toString(node: TNode[Conf, Label], focus: Option[TPath], indent: String = ""): String = {
    val sb = new StringBuilder()
    val (c1, c2) = node.conf
    println("***")
    sb.append(indent + "|__" + toString(c1) + ", " + toString(c2))
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

