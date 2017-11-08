package ttlite

import ttlite.core._

class TTREPL
  extends CoreREPL
  with FunREPL
  with DPairREPL
  with NatREPL
  with VecREPL
  with IdREPL
  with FinREPL
  with ListREPL
  with PairREPL
  with SumREPL
  with WREPL {
  override val name = "TT"
}

object TTREPL {
  def main(args: Array[String]): Unit = {
    new TTREPL().mainRepl(args)
  }
}
