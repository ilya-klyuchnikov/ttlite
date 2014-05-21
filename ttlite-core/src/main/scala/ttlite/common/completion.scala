package ttlite.common

class ImportCompleter extends jline.console.completer.FileNameCompleter {
  val importFileRE = """(\s*)(reload|import)(\s+)(\")(.*)""".r
  override def complete(buf : String, cursor : Int, candidates : java.util.List[CharSequence]): Int = {
    buf match {
      case importFileRE(s1, s2, s3, s4, file) =>
        super.complete(file, cursor, candidates) match {
          case -1 => -1
          case i =>
            correctFileImport(candidates.asInstanceOf[java.util.List[String]])
            i + s1.size + s2.size + s3.size + s4.size
        }
      case _ =>
        -1
    }
  }
  // FileNameCompletor adds a space to the file and '/' to a dir
  val fileRE = """(.*) """.r
  private def correctFileImport(candidates : java.util.List[String]) {
    if (candidates.size == 1) {
      // if there is a simple file, we complete
      val origin = candidates.get(0)
      origin match {
        case fileRE(file) =>
          candidates.remove(0)
          candidates.add(0, file + "\";")
        case _ =>
      }

    } else {

      for (i <- 0 until candidates.size) {
        val origin = candidates.get(i)
        origin match {
          case fileRE(file) =>
            candidates.remove(i)
            candidates.add(i, file)
          case _ =>
        }
      }

    }
  }
}
