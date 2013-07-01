package superspec.tt

trait CoreSubst extends CoreEval with CoreQuote {
  type Subst = Map[Name, Term]

  def findRenaming(from: Term, to: Term): Option[Subst] =
    for (s <- findSubst(from, to) if findSubst(to, from).isDefined) yield  s

  def findSubst(from: Term, to: Term): Option[Subst] =
    for (sub <- findSubst0(from, to))
    yield sub.filter { case (k, v) => v != Free(k) }

  def findSubst0(from: Term, to: Term): Option[Subst] = (from, to) match {
    case (Lam(t1, e1), Lam(t2, e2)) =>
      mergeOptSubst(
        findSubst0(t1, t2),
        findSubst0(e1, e2)
      )
    case (Free(n@Local(_)), _) =>
      if (isFreeSubTerm(to, 0)) Some(Map(n -> to)) else None
    case (Free(Global(n)), Free(Global(m))) =>
      if (n == m) Some(Map()) else None
    case (Free(Global(n)), _) =>
      None
    case (Bound(i), Bound(j)) =>
      if (i == j) Some(Map()) else None
    case (f@Free(Quote(_)), _) =>
      sys.error("Hey, I do note expect quoted variables here!")
    case (Ann(e1, t1), Ann(e2, t2)) =>
      val s1 = findSubst0(e1, e2)
      val s2 = findSubst0(t1, t2)
      mergeOptSubst(s1, s2)
    case (Star, Star) =>
      Some(Map())
    case (Pi(t1, e1), Pi(t2, e2)) =>
      val s1 = findSubst0(e1, e2)
      val s2 = findSubst0(t1, t2)
      mergeOptSubst(s1, s2)
    case (e1 :@: t1, e2 :@: t2 ) =>
      val s1 = findSubst0(e1, e2)
      val s2 = findSubst0(t1, t2)
      mergeOptSubst(s1, s2)
    case _ =>
      None
  }

  def mergeSubst(sub1: Subst, sub2: Subst): Option[Subst] = {
    val merged1 = sub1 ++ sub2
    val merged2 = sub2 ++ sub1
    if (merged1 == merged2)
      Some(merged1)
    else
      None
  }

  def mergeOptSubst(subs: Option[Subst]*): Option[Subst] = {
    var res = Map():Subst
    for (sub <- subs) {
      sub match {
        case None =>
          return None
        case Some(s) =>
          mergeSubst(res, s) match {
            case None =>
              return None
            case Some(s) =>
              res = s
          }
      }
    }
    Some(res)
  }


  def applySubst(t: Term, subst: Subst): Term = {
    val env: NameEnv[Value] = subst.map {case (n, t) => (n, eval(t, emptyNEnv, Nil))}
    quote0(eval(t, env, Nil))
  }

  def isFreeSubTerm(t: Term, depth: Int): Boolean = t match {
    case Lam(t, e) =>
      isFreeSubTerm(t, depth) && isFreeSubTerm(e, depth + 1)
    case Ann(c1, c2) =>
      isFreeSubTerm(c1, depth) && isFreeSubTerm(c2, depth)
    case Star =>
      true
    case Pi(c1, c2) =>
      isFreeSubTerm(c1, depth) && isFreeSubTerm(c2, depth + 1)
    case Bound(i) =>
      i < depth
    case Free(_) =>
      true
    case (c1 :@: c2) =>
      isFreeSubTerm(c1, depth) && isFreeSubTerm(c2, depth)
  }

}
