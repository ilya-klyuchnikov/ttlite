package mrsc.core

trait MRSCRules[C, D] extends GraphRewriteRules[C, D] {
  type Signal
  def inspect(g: G): Signal

  def fold(signal: Signal, g: G): List[S]
  def drive(signal: Signal, g: G): List[S]
  def rebuild(signal: Signal, g: G): List[S]

  override def steps(g: G): List[S] = {
    val signal = inspect(g)
    fold(signal, g) ++ drive(signal, g) ++ rebuild(signal, g)
  }
}
