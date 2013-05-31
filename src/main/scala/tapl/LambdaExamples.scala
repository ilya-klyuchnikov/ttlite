package tapl

object LambdaExamples extends scala.App with LambdaAST with LambdaEval with LambdaCheck with LambdaQuote {
  // \x -> x
  val id: CTerm = Lam(Inf(Bound(0)))
  val const: CTerm = Lam(Lam(Inf(Bound(1))))

  def tfree(a: String) = TFree(Global(a))
  def free(x: String) = Inf(Free(Global(x)))

  val term1 = Ann(id, Fun(tfree("a"), tfree("a"))) :@: free("y")
  val term2 =
    (Ann(const, Fun(Fun(tfree("b"), tfree("b")), Fun(tfree("a"), Fun(tfree("b"), tfree("b"))))) :@: id) :@: free("y")

  val env1: Context = List(
    (Global("y"), HasType(tfree("a"))),
    (Global("a"), HasKind(Star))
  )
  val env2: Context = List((Global("b"), HasKind(Star))) ++ env1

  println(quote0(iEval(term1, (Nil, Nil))))
  println(quote0(iEval(term2, (Nil, Nil))))

  println(iType0(env1, term1))
  println(iType0(env2, term2))

  assert(quote0(iEval(term1, (Nil, Nil))) == Inf(Free(Global("y"))))
  assert(quote0(iEval(term2, (Nil, Nil))) == Lam(Inf(Bound(0))))

  assert(iType0(env1, term1) == Right(TFree(Global("a"))))
  assert(iType0(env2, term2) == Right(Fun(TFree(Global("b")),TFree(Global("b")))))
}
