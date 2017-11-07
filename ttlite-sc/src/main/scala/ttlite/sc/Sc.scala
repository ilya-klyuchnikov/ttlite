package ttlite.sc

import mrsc.core._
import ttlite.core._
import ttlite.common._

trait SC extends Eval with Quoting with Check {
  import scala.language.implicitConversions

  var v = 0
  def freshName(): Name = {
    v += 1
    ScLocal(v)
  }

  implicit def name2Term(n: Name) = Free(n)
  type Subst = Map[Name, Term]

  implicit class TermSubst(t: Term) {
    def /(subst: Subst) = {
      val env: NameEnv[Value] = subst.map {case (n, t) => (n, eval(t, Map[Name, Value](), Nil))}
      quote0(eval(t, env, Nil))
    }
  }

  case class Conf(term: Term, ctx: Context[Value]) {
    val tpVal = iType0(ctx, term)
    val tp = quote0(tpVal)
  }

  trait Label
  case class ElimLabel(sel: Name, ptr: Term, sub: Subst, types: NameEnv[Value]) extends Label {
    override def toString = s"$sel = $ptr"
  }

  // drive steps are very high level
  sealed trait DriveStep {
    def step(t: Conf): Step
  }
  case class ElimDStep(cases: ElimLabel*) extends DriveStep {
    override def step(t: Conf) =
      VariantsStep(
        cases.toList.map { lbl: ElimLabel =>
          lbl -> Conf(
            t.term / Map(lbl.sel -> lbl.ptr),
            lbl.types.foldLeft(t.ctx)((ctx, nt) => ctx.addType(nt._1, nt._2)))})
  }
  case class DecomposeDStep(label: Label, args: Conf*) extends DriveStep {
    override def step(t: Conf) = DecomposeStep(label, args.toList)
  }
  case object StopDStep extends DriveStep {
    override def step(t: Conf) = StopStep
  }

  // just steps are more low-level
  sealed trait Step {
    val graphStep: GraphRewriteStep[Conf, Label]
  }
  case class VariantsStep(cases: List[(ElimLabel, Conf)]) extends Step {
    override val graphStep: GraphRewriteStep[Conf, Label] =
      AddChildNodesStep[Conf, Label](cases.map(v => (v._2, v._1)))
  }
  case class DecomposeStep(label: Label, args: List[Conf]) extends Step {
    override val graphStep: GraphRewriteStep[Conf, Label] =
      AddChildNodesStep[Conf, Label](args.map(_ -> label))
  }
  case object StopStep extends Step {
    override val graphStep: GraphRewriteStep[Conf, Label] =
      CompleteCurrentNodeStep[Conf, Label]()
  }

  def singleDrive(c: Conf): DriveStep
}

trait Driver extends SC {
  // logic
  override def singleDrive(c: Conf): DriveStep = eval0(c.term) match {
    case VNeutral(n) =>
      nv(n) match {
        case Some(n) =>
          elimVar(n, iType0(c.ctx, Free(n)))
        case None =>
          StopDStep
      }
    case _ => decompose(c)
  }

  // neutral variable of a value
  def nv(n: Neutral): Option[Name] =
    None

  def elimVar(n: Name, nt: Value): DriveStep = nt match {
    case _ => StopDStep
  }

  def decompose(c: Conf): DriveStep = StopDStep
}

trait Residuator extends SC {
  type TG = TGraph[Conf, Label]
  type N = TNode[Conf, Label]

  def residuate(g: TG, nEnv: NameEnv[Value]): Value = {
    fold(g.root, nEnv.withDefault(vfree), Nil, Map())
  }

  def fold(node: N, env: NameEnv[Value], bound: Env, recM: Map[TPath, Value]): Value =
    node.base match {
      case Some(tPath) => recM(tPath)
      case None => node.outs match {
        case Nil => eval(node.conf.term, env, bound)
        case outs => sys.error(s"Do not know how to fold $outs")
      }
    }
}

trait ProofResiduator extends Residuator { self: FunAST with IdAST =>
  import scala.language.implicitConversions
  implicit def sym2appV(s: Symbol): VApplicable =
    VNeutral(NFree(Global(s.name)))

  def proofResiduate(g: TG, nEnv: NameEnv[Value]): Value = {
    val env = nEnv.withDefault(vfree)
    proofFold(g.root, env, Nil, Map(), env, Nil, Map())
  }

  def proofFold(node: N,
                env1: NameEnv[Value], bound1: Env, recM1: Map[TPath, Value],
                env2: NameEnv[Value], bound2: Env, recM2: Map[TPath, Value]): Value =
    node.base match {
      case Some(tPath) =>
        recM2(tPath)
      case None =>
        node.outs match {
          case Nil => eval(Refl(node.conf.tp, node.conf.term), env1, bound1)
          case outs => sys.error(s"Do not know how to fold $outs")
        }
    }
}
