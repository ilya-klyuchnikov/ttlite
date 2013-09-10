package superspec.tt

trait FinFunEval extends FunEval with FinEval with DPairEval {

  override def eval(t: Term, ctx: Context[Value], bound: Env): Value = t match {

    case Lam(t, e) =>
      val tp = eval(t, ctx, bound)
      VLam(tp, x => eval(e, ctx, ext(tp, x) :: bound))
    case Pi(ty, ty1) =>
      val tp = eval(ty, ctx, bound)
      VPi(tp, x => eval(ty1, ctx, ext(tp, x) :: bound))
    case Sigma(ty, ty1) =>
      val tp = eval(ty, ctx, bound)
      VSigma(tp, x => eval(ty1, ctx, ext(tp, x) :: bound))
    case Free(x) =>
      ctx.types.get(x) match {
        case Some(VPi(VFalsity, f)) =>
          VLam(VFalsity, x => voidElim(VLam(VFalsity, f), x))

        case _ =>
          super.eval(t, ctx, bound)
      }
    case _ =>
      super.eval(t, ctx, bound)
  }

  def ext(tp: Value, default: Value): Value = tp match {
    case VPi(VFalsity, f) =>
      VLam(VFalsity, x => voidElim(VLam(VFalsity, f), x))
    case _ =>
      default
  }

}
