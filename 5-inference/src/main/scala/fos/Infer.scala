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
    case Pred(t1) => val (tp1, constraint) = collect(env, t1); (NatType, constraint ++ List((tp1, NatType)))
    case Succ(t1) => val (tp1, constraint) = collect(env, t1); (NatType, constraint ++ List((tp1, NatType)))
    case IsZero(t1) => val (tp1, constraint) = collect(env, t1); (BoolType, constraint ++ List((tp1, NatType)))
    case If(t1, t2, t3) =>
      val (tp1, constraint1) = collect(env, t1)
      val (tp2, constraint2) = collect(env, t2)
      val (tp3, constraint3) = collect(env, t3)
      (tp2, constraint1 ++ constraint2 ++ constraint3 ++ List((tp1, BoolType), (tp2, tp3)))
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
        counter += 1; val fresh_x = TypeVar(x + counter)
        val (tp2, constraint) = collect(env ++ List((x, TypeScheme(List(fresh_x), fresh_x))), t1)
        (FunType(fresh_x, tp2), constraint)
      } else {
        val (tp2, constraint) = collect(env ++ List((x, TypeScheme(List(), tp.tpe))), t1)
        (FunType(tp.tpe, tp2), constraint)
      }
    case App(t1, t2) =>
      val (tp1, constraint1) = collect(env, t1)
      val (tp2, constraint2) = collect(env, t2)
      counter += 1; val fresh_x = TypeVar("X" + counter)
      (fresh_x, constraint1 ++ constraint2 ++ List((tp1, FunType(tp2, fresh_x))))
    case _ => throw TypeError("Term is stuck !")
  }

  def unify(c: List[Constraint]): Type => Type = c match {
    case (TypeVar(x), TypeVar(y)) :: xs if x == y => unify(xs)
    case (NatType, NatType) :: xs => unify(xs)
    case (BoolType, BoolType) :: xs => unify(xs)
    case (tp1 @ TypeVar(x), tp2) :: xs =>
      if (isIn(tp1, tp2))
        throw TypeError("Error : infinite loop")
      else
        unify(xs map {case (subT1: Type, subT2: Type) => (sub(tp1)(tp2)(subT1), sub(tp1)(tp2)(subT2))}).compose(sub(tp1)(tp2))
    case (tp1, tp2 @ TypeVar(x)) :: xs => unify((tp2, tp1)::xs)
    case (FunType(t11, t12), FunType(t21, t22)) :: xs => unify(List((t11, t21), (t12, t22)) ++ xs)
    case Nil => sub(TypeVar("LOL"))(TypeVar("LOLO"))
    case _ => throw TypeError("Type error")
  }

  def isIn(t: TypeVar, tree: Type): Boolean = tree match {
    case TypeVar(x) => if (t == tree) true else false
    case FunType(tp1, tp2) => isIn(t, tp1) || isIn(t, tp2)
    case _ => false
  }

  /**
    * @param s
    * @param t1
    * @param t2
    * @return
    */
  def sub(s: TypeVar)(t1: Type)(t2: Type): Type = t2 match {
    case t @ TypeVar(x) => if (t == s) t1 else t2
    case FunType(subT1, subT2) => FunType(sub(s)(t1)(subT1), sub(s)(t1)(subT2))
    case _ => t2
  }
}
