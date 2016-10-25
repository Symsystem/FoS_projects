package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  simply typed lambda calculus found in Chapter 9 of
 *  the TAPL book.
 */
object SimplyTyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".", ":", "=", "->", "{", "}", ",", "*")
  lexical.reserved   ++= List("Bool", "Nat", "true", "false", "if", "then", "else", "succ",
                              "pred", "iszero", "let", "in", "fst", "snd")

  /** Term     ::= SimpleTerm { SimpleTerm }
   */
  def Term: Parser[Term] = subterm ~ rep(subterm) ^^ reduceTerm

  def subterm: Parser[Term] = (
      "true" ^^ (_ => True())
      | "false" ^^ (_ => False())
      | "if" ~ Term ~ "then" ~ Term ~ "else" ~ Term ^^ {case _ ~ t1 ~_ ~ t2 ~ _ ~ t3 => If(t1, t2, t3)}
      | numericLit ^^ {x => numTerm(x.toInt)}
      | "pred" ~> Term ^^ Pred
      | "succ" ~> Term ^^ Succ
      | "iszero" ~> Term ^^ IsZero
      | ident ^^ Var
      | "\\" ~ ident ~ ":" ~ typ ~ "." ~ Term ^^ {case _ ~ v ~ _ ~ tp ~ _ ~ t => Abs(v, tp, t)}
      | "(" ~ Term ~ ")" ^^ {case _ ~ t ~ _ => t}
      | "let" ~ ident ~ ":" ~ typ ~ "=" ~ Term ~ "in" ~ Term ^^ {case _ ~ x ~ _ ~ tp ~ _ ~ t1 ~ _ ~ t2 => App(Abs(x, tp, t2), t1)}
      | "{" ~ Term ~ "," ~ Term ~ "}" ^^ {case _ ~ t1 ~ _ ~ t2 ~ _ => TermPair(t1, t2)}
      | "fst" ~> Term ^^ First
      | "snd" ~> Term ^^ Second
    )

  val reduceTerm : Term ~ List[Term] => Term = {
    case i ~ ps => ps.fold(i)((t1, t2) => App(t1, t2))
  }

  def numTerm(n: Int): Term =
    if (n == 0) Zero()
    else
      Succ(numTerm(n-1))

  def typ: Parser[Type] = rep(typPair ~ "->") ~ typPair ^^ reduceType

  def typPair: Parser[Type] = rep(subtyp ~ "*") ~ subtyp ^^ reduceType

  def subtyp: Parser[Type] = (
      "Bool" ^^^ TypeBool
      | "Nat" ^^^ TypeNat
      | "(" ~ typ ~ ")" ^^ {case _ ~ t ~ _ => t}
    )

  val reduceType : List[Type ~ String] ~ Type => Type = {
    case xs ~ x => xs.foldRight(x){
      case (t1 ~ "->", t2) => TypeFun(t1, t2)
      case (t1 ~ "*", t2) => TypePair(t1, t2)
    }
  }

  /** Thrown when no reduction rule applies to the given term. */
  case class NoRuleApplies(t: Term) extends Exception(t.toString)

  /** Print an error message, together with the position where it occured. */
  case class TypeError(t: Term, msg: String) extends Exception(msg) {
    override def toString =
      msg + "\n" + t
  }

  /** The context is a list of variable names paired with their type. */
  type Context = List[(String, Type)]

  var counter = 0

  def alpha(t: Term): Term = t match {
    case Abs(s, tp, t1) => Abs(s + counter, tp, rename(s, t1))
    case _ => t
  }

  def rename(s: String, t: Term): Term = t match {
    case Var(x) => if (s == x) Var(x + counter) else Var(x)
    case Abs(s2, tp, t2) => if (s == s2) Abs(s2, tp, t2) else Abs(s2, tp, rename(s, t2))
    case App(t1, t2) => App(rename(s, t1), rename(s, t2))
    case Succ(t1) => Succ(rename(s, t1))
    case Pred(t1) => Pred(rename(s, t1))
    case IsZero(t1) => IsZero(rename(s, t1))
    case If(cond, t1, t2) => If(rename(s, cond), rename(s, t1), rename(s, t2))
    case TermPair(t1, t2) => TermPair(rename(s, t1), rename(s, t2))
    case First(t1) => First(rename(s, t1))
    case Second(t1) => Second(rename(s, t1))
    case t1 if isValue(t1) => t1
  }

  /** Straight forward substitution method
    *  (see definition 5.3.5 in TAPL book).
    *  [x -> s]t
    *
    *  @param t the term in which we perform substitution
    *  @param x the variable name
    *  @param s the term we replace x with
    *  @return  ...
    */
  def subst(t: Term, x: String, s: Term): Term = t match {
    case Var(y) => if (y == x) s else Var(y)
    case Abs(y, tp, t1) => if (y == x)
      Abs(y, tp, t1)
    else
      counter += 1
      alpha(Abs(y, tp, t1)) match {
        case Abs(z, typ, t2) => Abs(z, typ, subst(t2, x, s))
        case _ => Abs(y, tp, t1)
      }
    case App(t1, t2) => App(subst(t1, x, s), subst(t2, x , s))
    case Succ(t1) => Succ(subst(t1, x, s))
    case Pred(t1) => Pred(subst(t1, x, s))
    case IsZero(t1) => IsZero(subst(t1, x, s))
    case If(cond, t1, t2) => If(subst(cond, x, s), subst(t1, x, s), subst(t2, x, s))
    case TermPair(t1, t2) => TermPair(subst(t1, x, s), subst(t2, x, s))
    case First(t1) => First(subst(t1, x, s))
    case Second(t1) => Second(subst(t1, x, s))
    case t1 if isValue(t1) => t1
    case _ => throw NoRuleApplies(t)
  }

  /** Call by value reducer. */
  def reduce(t: Term): Term = t match {
    case If(cond, t1, t2) => cond match {
      case True() => t1
      case False() => t2
      case _ => If(reduce(cond), t1, t2)
    }
    case IsZero(t1) => t1 match {
      case Zero() => True()
      case Succ(nv) if isNumericValue(nv) => False()
      case _ => IsZero(reduce(t1))
    }
    case Pred(t1) => t1 match {
      case Zero() => Zero()
      case Succ(nv) if isNumericValue(nv) => nv
      case _ => Pred(reduce(t1))
    }
    case Succ(t1) if !isValue(t1) => Succ(reduce(t1))
    case App(Abs(x, tp, t1), t2) if isValue(t2) => subst(t1, x, t2)
    case App(t1, t2) => if (isValue(t1)) App(t1, reduce(t2)) else App(reduce(t1), t2)
    case First(t1) => t1 match {
      case TermPair(ta, tb) if isValue(t1) => ta
      case _ => First(reduce(t1))
    }
    case Second(t1) => t1 match {
      case TermPair(ta, tb) if isValue(t1) => tb
      case _ => Second(reduce(t1))
    }
    case TermPair(t1, t2) => if (isValue(t1))
                                TermPair(t1, reduce(t2))
                              else
                                TermPair(reduce(t1), t2)
    case _ => throw NoRuleApplies(t)
  }

  def isNumericValue(t: Term): Boolean = t match {
    case Zero() => true
    case Succ(t1) => isNumericValue(t1)
    case _ => false
  }

  def isValue(t: Term): Boolean = t match {
    case t1 if isNumericValue(t1) => true
    case True() | False() => true
    case Abs(x, tp, t1) => true
    case TermPair(t1, t2) => isValue(t1) && isValue(t2)
    case _ => false
  }


  /** Returns the type of the given term <code>t</code>.
   *
   *  @param ctx the initial context
   *  @param t   the given term
   *  @return    the computed type
   */
  def typeof(ctx: Context, t: Term): Type = t match {
    case True() | False() => TypeBool
    case Zero() => TypeNat
    case Pred(t1) => if (typeof(ctx, t1) == TypeNat) TypeNat else throw TypeError(t, "Should be a typeNat")
    case Succ(t1) => if (typeof(ctx, t1) == TypeNat) TypeNat else throw TypeError(t, "Should be a typeNat")
    case IsZero(t1) => if (typeof(ctx, t1) == TypeNat) TypeBool else throw TypeError(t, "Should be a typeNat")
    case If(cond, t1, t2) => val ctx0 = forceCtx(ctx, cond, TypeBool)
                             var tp1 = Nil
                             Type tp2
                             try {
                               tp1 = typeof(ctx0, t1)
                             } catch {
                               case TypeError(_, "Couldn't assign a type") => tp1 = None
                             }
                             try {
                               val tp2 = typeof(ctx0, t2)
                             } catch {
                               case TypeError(_, "Couldn't assign a type") => val tp2 = None
                             }
                             if (tp1 != None){
                               if (tp2 != None){
                                 if (tp1 == tp2){
                                   tp1
                                 } else {
                                   throw TypeError(t, "Should be the same type as the else part")
                                 }
                               } else {
                                 val ctx2 = forceCtx(ctx0, t2, tp1)
                                 tp1
                               }
                             }
      
      
      typeof(ctx, cond) match {
      case TypeBool => val tp1 = typeof(ctx, t1)
                       if (tp1 == typeof(ctx, t2))
                         tp1
                       else
                         throw TypeError(t, "Should be the same type as the else part")
      case _ => throw TypeError(t, "Should be a Boolean type")
    }
    case Var(x) => val tp = getVarType(ctx, x)
                   if (tp != None) tp else throw TypeError(t, "Couldn't assign a type")

    case Abs(x, tp, t1) => TypeFun(tp, typeof(ctx, t1))
    case App(t1, t2) => typeof(ctx, t1) match {
      case TypeFun(t11, t12)  => if (typeof(ctx, t2) == t11)
                                   t12
                                 else
                                   throw TypeError(t, "Types do not match with the function")
      case _ => throw TypeError(t1, "Should be a function type")
    }
    case _ => throw TypeError(t, "term is stuck !")
  }
  
  def forceCtx(ctx: Context, t: Term, tp: Type): Context = t match {
    case True() | False() => if (tp == TypeBool) ctx else throw TypeError(t, "Should be forced to typeBool")
    case Zero() => if (tp == TypeNat) ctx else throw TypeError(t, "Should be forced to typeNat")
    case Pred(t1) => if (tp == TypeNat) forceCtx(ctx, t1, TypeNat) else throw TypeError(t, "Should be forced to typeNat")
    case Succ(t1) => if (tp == TypeNat) forceCtx(ctx, t1, TypeNat) else throw TypeError(t, "Should be forced to typeNat")
    case IsZero(t1) => if (tp == TypeBool) forceCtx(ctx, t1, TypeNat) else throw TypeError(t, "Should be forced to typeBool")
    case If(cond, t1, t2) => val ctx0 = forceCtx(ctx, cond, TypeBool)
                             val ctx1 = forceCtx(ctx0, t1, tp) 
                             forceCtx(ctx1, t2, tp)
    case Var(x) => val tp1 = getVarType(ctx, x)
                   if (tp1 == None) ctx :+ (x, tp)
                   else
                     tp1 match {
                       case tp => ctx
                       case _ => throw TypeError(t, "Should be of type" + tp)
                     }
    case Abs(x, tp0, t1) => tp match {
                              case TypeFun(tp1, tp2) => if (tp1 == tp0) {
                                                          val ctx0 = forceCtx(ctx, Var(x), tp1)
                                                          forceCtx(ctx0, t1, tp2)
                                                        } else throw TypeError(t, "Should be forced to " + tp)
                              case _ => throw TypeError(t, "Incorrect Abs type")
                            }
    // TODO complete other cases
    case _ => throw TypeError(t, "Not implemented for now")
  }

  def getVarType(ctx: Context, x: String): Type = ctx.find(_._1 == x).get._2


  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the evaluation strategy used for reduction.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoRuleApplies(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(Term)(tokens) match {
      case Success(trees, _) =>
        try {
          println("typed: " + typeof(Nil, trees))
          for (t <- path(trees, reduce))
            println(t)
        } catch {
          case tperror: Exception => println(tperror.toString)
        }
      case e =>
        println(e)
    }
  }
}
