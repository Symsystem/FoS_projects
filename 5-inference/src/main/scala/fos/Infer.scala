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
        val tps = env.find(_._1 == x).get._2
        (instantiate(tps), List())
      } catch {
        case _ : Throwable => throw TypeError("x does not have a type")
      }

    case Abs(x, tp, t1) =>
      if (tp == EmptyTypeTree()) {
        val fresh_x = freshTypeVar(x)
        val (tp1, constraint) = collect((x, TypeScheme(List(), fresh_x)) :: env, t1)
        (FunType(fresh_x, tp1), constraint)
      } else {
        val (tp1, constraint) = collect((x, TypeScheme(List(), tp.tpe)) :: env, t1)
        (FunType(tp.tpe, tp1), constraint)
      }

    case App(t1, t2) =>
      val (tp1, constraint1) = collect(env, t1)
      val (tp2, constraint2) = collect(env, t2)
      val fresh_x = freshTypeVar
      (fresh_x, List((tp1, FunType(tp2, fresh_x))) ++ constraint1 ++ constraint2)

    /*case Let(x, tp, t1, t2) =>
      var (tp1, c1) = collect(env, t1)
      if (tp != EmptyTypeTree()) {
        c1 = (tp1, tp.tpe) :: c1
        tp1 = tp.tpe
      }
      val unifyC1 = unify(c1)
      tp1 = unifyC1(tp1)
      var new_env = env map {case (v, ts: TypeScheme) =>
        val tsUnified = unifyC1(ts.tp)
        (v, TypeScheme(ts.params filter {tpv => isInType(tpv, tsUnified)}, tsUnified))}
      new_env = (x, generalize(tp1, new_env)) :: new_env
      val (tp2, c2) = collect(new_env, t2)
      (tp2, c2 ++ c1)*/

    case Let(x, tp, t1, t2) => tp match {
      case EmptyTypeTree() =>
        var (tp1, c1) = collect(env, t1)
        def unifyC1 = unify(c1)
        tp1 = unifyC1(tp1)
        var new_env = env map {case (v, ts: TypeScheme) =>
          val tsUnified = unifyC1(ts.tp)
          (v, TypeScheme(ts.params filter {tpv => isInType(tpv, tsUnified)}, tsUnified))}
        new_env = (x, generalize(tp1, new_env)) :: new_env
        val (tp2, c2) = collect(new_env, t2)
        (tp2, c2 ++ c1)
      case _ => collect(env, App(Abs(x, tp, t2), t1))
    }
      
    case _ => throw TypeError("Term is stuck !")
  }

  def unify(c: List[Constraint]): Type => Type = c match {
    case (t1@TypeVar(_), t2@TypeVar(_)) :: xs if t1 == t2 => unify(xs)
    case (NatType, NatType) :: xs => unify(xs)
    case (BoolType, BoolType) :: xs => unify(xs)
    case (tp1@TypeVar(_), tp2) :: xs =>
      if (isInType(tp1, tp2))
        throw TypeError("Error : infinite loop")
      else
        unify(xs map { case (subT1: Type, subT2: Type) => (sub(tp1)(tp2)(subT1), sub(tp1)(tp2)(subT2)) }).compose(sub(tp1)(tp2))
    case (tp1, tp2@TypeVar(x)) :: xs => unify((tp2, tp1) :: xs)
    case (FunType(t11, t12), FunType(t21, t22)) :: xs => unify(List((t11, t21), (t12, t22)) ++ xs)
    case Nil => x => x
    case _ => throw TypeError("Type error")
  }

  /**
    * @return a fresh TypeVar with the unique name "Xi" (i = counter)
    */
  def freshTypeVar: TypeVar = {
    counter += 1
    TypeVar("X" + counter)
  }

  /**
    * @return a fresh TypeVar with the unique name "namei" (i = counter)
    */
  def freshTypeVar(name: String): TypeVar = {
    counter += 1
    TypeVar(name + counter)
  }

  def instantiate(tps: TypeScheme) : Type = {
    val constraints = tps.params map { tpv => (tpv, freshTypeVar)}
    unify(constraints)(tps.tp)
  }

  /**
    * @param t the TypeVar we want to find in type tp
    * @param tp the type which contains or not t
    * @return if tp contains t
    */
  def isInType(t: TypeVar, tp: Type): Boolean = tp match {
    case TypeVar(_) => t == tp
    case FunType(tp1, tp2) => isInType(t, tp1) || isInType(t, tp2)
    case _ => false
  }

  /**
    * @param s is the TypeVar that will be replaced
    * @param t1 is the type that will replace every instance of s
    * @param t2 is the type in which we replace all instances of s.
    * @return [s -> t1] t2
    */
  def sub(s: TypeVar)(t1: Type)(t2: Type): Type = t2 match {
    case t@TypeVar(_) => if (t == s) t1 else t2
    case FunType(subT1, subT2) => FunType(sub(s)(t1)(subT1), sub(s)(t1)(subT2))
    case _ => t2
  }

  def generalize(tp: Type, env: Env) : TypeScheme = {
    val typeVars = getTypeVars(tp) filter((tpVar) => !isInEnv(tpVar, env))
    TypeScheme(typeVars, tp)
  }

  def getTypeVars(tp: Type): List[TypeVar] = tp match {
    case tpv@TypeVar(_) => List(tpv)
    case FunType(t1, t2) => getTypeVars(t1) ++ getTypeVars(t2)
    case _ => Nil
  }

  def isInEnv(t: TypeVar, env: Env): Boolean = env match {
    case (_, tpScheme)::xs => tpScheme.tp match {
      case tpv@TypeVar(_) if tpv == t => true
      case _ => isInEnv(t, xs)
    }
    case Nil => false
  }
}
