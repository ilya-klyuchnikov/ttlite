package ttlite

import ttlite.core._

object TTREPL
  extends CoreREPL
  with FunREPL
  with DPairREPL
  with NatREPL
  with VectorREPL
  with IdREPL
  with FinREPL
  with ListREPL
  with PairREPL
  with SumREPL
  with WREPL {
  override val name = "TT"
}