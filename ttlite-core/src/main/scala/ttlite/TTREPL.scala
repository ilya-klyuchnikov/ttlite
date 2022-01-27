package ttlite

import ttlite.core._

class TTREPL
    extends CoreREPL,
      PiREPL,
      SigmaREPL,
      NatREPL,
      VecREPL,
      IdREPL,
      EnumREPL,
      ListREPL,
      ProductREPL,
      SumREPL,
      WREPL {
  override val name = "TT"
}

object TTREPL {
  def main(args: Array[String]): Unit = {
    new TTREPL().mainRepl(args)
  }
}
