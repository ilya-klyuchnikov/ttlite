package ttlite.core.test

import ttlite.core.TTREPL

object Errors extends App {
  Console.println("==05.hs==")
  TTREPL.main(Array("-t", "examples/test/05.hs"))


  Console.println("==01.hs==")
  TTREPL.main(Array("-t", "examples/test/01.hs"))

  Console.println("==07.hs==")
  TTREPL.main(Array("-t", "examples/test/07.hs"))

  Console.println("==02.hs==")
  TTREPL.main(Array("-t", "examples/test/02.hs"))

  Console.println("==03.hs==")
  TTREPL.main(Array("-t", "examples/test/03.hs"))

  /*
  Console.println("==06.hs==")
  TTREPL.main(Array("-t", "examples/test/06.hs"))
  */
}
