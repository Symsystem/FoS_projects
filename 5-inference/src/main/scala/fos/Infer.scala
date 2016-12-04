package fos

object Infer {

  case class TypeScheme(params: List[TypeVar], tp: Type)

  type Env = List[(String, TypeScheme)]
  type Constraint = (Type, Type)

  case class TypeError(msg: String) extends Exception(msg)

  var counter = 0

  def collect(env: Env, t: Term): (Type, List[Constraint]) = t match {
    case True() | False() => (BoolType, List())
    case Zero() => (NatType, List())
    case Pred(t1) => val (tp1, constraint) = collect(env, t1); (NatType, List((tp1, NatType)) ++ constraint)
    case Succ(t1) => val (tp1, constraint) = collect(env, t1); (NatType, List((tp1, NatType)) ++ constraint)
    case IsZero(t1) => val (tp1, constraint) = collect(env, t1); (BoolType, List((tp1, NatType)) ++ constraint)
    case If(t1, t2, t3) =>
      val (tp1, constraint1) = collect(env, t1)
      val (tp2, constraint2) = collect(env, t2)
      val (tp3, constraint3) = collect(env, t3)
      (tp2, List((tp1, BoolType), (tp2, tp3)) ++ constraint1 ++ constraint2 ++ constraint3)
    case Var(x) =>
      try {
        val tpx = env.find(_._1 == x).get._2.tp
        (tpx, List())
      }
      catch {
        case _ => throw TypeError(x + " has not type")
      }
    case Abs(x, tp, t1) =>
      if (tp == EmptyTypeTree()) {
        counter += 1
        val fresh_x = TypeVar(x + counter)
        val (tp2, constraint) = collect(List((x, TypeScheme(List(fresh_x), fresh_x))) ++ env, t1)
        (FunType(fresh_x, tp2), constraint)
      } else {
        val (tp2, constraint) = collect(List((x, TypeScheme(List(), tp.tpe))) ++ env, t1)
        (FunType(tp.tpe, tp2), constraint)
      }
    case App(t1, t2) =>
      val (tp1, constraint1) = collect(env, t1)
      val (tp2, constraint2) = collect(env, t2)
      counter += 1
      val fresh_x = TypeVar("X" + counter)
      (fresh_x, List((tp1, FunType(tp2, fresh_x))) ++ constraint1 ++ constraint2)

    case Let(x, tp, t1, t2) => tp match {
      case EmptyTypeTree() =>
        var (tp1, c1) = collect(env, t1)
        def unifyC1 = unify(c1)
        tp1 = unifyC1(tp1)
        var new_env = env map {case (x, ts: TypeScheme) => (x, TypeScheme(ts.params, unifyC1(ts.tp)))}
        new_env ++= List((x, generalize(tp1, new_env)))
        collect(new_env, t1)
      case _ => collect(env, App(Abs(x, tp, t2), t1))
    }
    case _ => throw TypeError("Term is stuck !")
  }

  def unify(c: List[Constraint]): Type => Type = c match {
    case (t1@TypeVar(x), t2@TypeVar(y)) :: xs if t1 == t2 => unify(xs)
    case (NatType, NatType) :: xs => unify(xs)
    case (BoolType, BoolType) :: xs => unify(xs)
    case (tp1@TypeVar(x), tp2) :: xs =>
      if (isInType(tp1, tp2))
        throw TypeError("Error : infinite loop")
      else
        unify(xs map { case (subT1: Type, subT2: Type) => (sub(tp1)(tp2)(subT1), sub(tp1)(tp2)(subT2)) }).compose(sub(tp1)(tp2))
    case (tp1, tp2@TypeVar(x)) :: xs => unify((tp2, tp1) :: xs)
    case (FunType(t11, t12), FunType(t21, t22)) :: xs => unify(List((t11, t21), (t12, t22)) ++ xs)
    case Nil => x => x
    case _ => throw TypeError("Type error")
  }

  def isInType(t: TypeVar, tree: Type): Boolean = tree match {
    case TypeVar(x) => t == tree
    case FunType(tp1, tp2) => isInType(t, tp1) || isInType(t, tp2)
    case _ => false
  }

  def isInEnv(t: TypeVar, env: Env): Boolean = env match {
    case (str, tpScheme)::xs => if (tpScheme.tp == t) true else isInEnv(t, xs)
    case _ => false
   }

  /**
    * @param s
    * @param t1
    * @param t2
    * @return
    */
  def sub(s: TypeVar)(t1: Type)(t2: Type): Type = t2 match {
    case t@TypeVar(x) => if (t == s) t1 else t2
    case FunType(subT1, subT2) => FunType(sub(s)(t1)(subT1), sub(s)(t1)(subT2))
    case _ => t2
  }

  def generalize(tp: Type, env: Env) : TypeScheme = {
    val typeVars = getTypeVars(tp) filter((tpVar) => isInEnv(tpVar, env))
    TypeScheme(typeVars, tp)
  }

  def getTypeVars(tp: Type): List[TypeVar] = tp match {
    case TypeVar(x) => List(TypeVar(x))
    case FunType(t1, t2) => getTypeVars(t1) ++ getTypeVars(t2)
    case _ => Nil
  }

  def instantiateTypeScheme(tpScheme: TypeScheme): Type = tpScheme.params match {
      case Nil => tpScheme.tp
      case x::xs =>
        counter += 1
        val temp = instantiateTypeScheme(TypeScheme(xs, tpScheme.tp))
        sub(x)(TypeVar("X" + counter))(temp)
  }
}
