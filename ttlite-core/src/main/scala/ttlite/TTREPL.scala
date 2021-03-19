package ttlite

import ttlite.core._

class TTREPL
    extends CoreREPL
    with PiREPL
    with SigmaREPL
    with NatREPL
    with VecREPL
    with IdREPL
    with EnumREPL
    with ListREPL
    with ProductREPL
    with SumREPL
    with WREPL {
  override val name = "TT"
}

object TTREPL {
  def main(args: Array[String]): Unit = {
    new TTREPL().mainRepl(args)
  }
}
