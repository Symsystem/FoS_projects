package fos

import sun.font.TrueTypeFont

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the
 *  untyped lambda calculus found in Chapter 5 of
 *  the TAPL book.
 */
object Untyped extends StandardTokenParsers {
  lexical.delimiters ++= List("(", ")", "\\", ".")
  import lexical.Identifier

  /** t ::= x
          | '\' x '.' t
          | t t
          | '(' t ')'
   */

  def term: Parser[Term] = subterm ~ rep(subterm) ^^ reduceList

  def subterm: Parser[Term] =
    ( ident ^^ Var
      | "\\" ~ ident ~ "." ~ term ^^ {case _ ~ v ~ _ ~ t => Abs(v, t)}
      | "(" ~ term ~ ")" ^^ {case _ ~ t ~ _ => t}
    )

  val reduceList : Term ~ List[Term] => Term = {
    case i ~ ps => ps.fold(i)((t1, t2) => App(t1, t2))
  }

  var counter = 0

  /** <p>
   *    Alpha conversion: term <code>t</code> should be a lambda abstraction
   *    <code>\x. t</code>.
   *  </p>
   *  <p>
   *    All free occurences of <code>x</code> inside term <code>t/code>
   *    will be renamed to a unique name.
   *  </p>
   *
   *  @param t the given lambda abstraction.
   *  @return  the transformed term with bound variables renamed.
   */

  def alpha(t: Term): Term = t match {
    case Abs(s, t1) => Abs(s + counter, rename(s, t1))
    case _ => t
  }

  def rename(s: String, t: Term): Term = t match {
    case Var(x) => if (s == x) Var(x + counter) else Var(x)
    case Abs(s2, t2) => if (s == s2) Abs(s2, t2) else Abs(s2, rename(s, t2))
    case App(t1, t2) => App(rename(s, t1), rename(s, t2))
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
    case Abs(y, t1) => if (y == x)
                        Abs(y, t1)
                      else
                        counter += 1
                        alpha(Abs(y, t1)) match {
                          case Abs(z , t2) => Abs(z, subst(t2, x, s))
                          case _ => Abs(y, t1)
                        }
    case App(t1, t2) => App(subst(t1, x, s), subst(t2, x , s))
    case _ => throw NoReductionPossible(t)
  }

  /** Term 't' does not match any reduction rule. */
  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Normal order (leftmost, outermost redex first).
   *
   *  @param t the initial term
   *  @return  the reduced term
   */
  def reduceNormalOrder(t: Term): Term = t match {
    case App(Abs(x, t1), t2) => subst(t1, x, t2)
    case App(t1, t2) => if (!isNormalForm(t1))
                          App(reduceNormalOrder(t1), t2)
                        else
                          App(t1, reduceNormalOrder(t2))
    case Abs(x, t1) => Abs(x, reduceNormalOrder(t1))
    case _ => throw NoReductionPossible(t)
  }

  /**
    * @param t the term to test
    * @return true if t is a normal form, otherwise false.
    */
  def isNormalForm(t: Term): Boolean = t match {
    case Var(x) => true
    case App(t1, t2) => isNormalForm(t1)
    case _ => false
  }

  /** Call by value reducer. */
  def reduceCallByValue(t: Term): Term = t match {
    case App(Abs(x, t1), Abs(y, t2)) => subst(t1, x, Abs(y, t2))
    case App(Abs(x, t1), t2) => App(Abs(x, t1), reduceCallByValue(t2))
    case App(App(t1, t2), t3) => App(reduceCallByValue(App(t1, t2)), t3)
    case _ => throw NoReductionPossible(t)
  }

  /** Returns a stream of terms, each being one step of reduction.
   *
   *  @param t      the initial term
   *  @param reduce the method that reduces a term by one step.
   *  @return       the stream of terms representing the big reduction.
   */
  def path(t: Term, reduce: Term => Term): Stream[Term] =
    try {
      var t1 = reduce(t)
      Stream.cons(t, path(t1, reduce))
    } catch {
      case NoReductionPossible(_) =>
        Stream.cons(t, Stream.empty)
    }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        println("normal order: ")
        for (t <- path(trees, reduceNormalOrder))
          println(t)
        println("call-by-value: ")
        for (t <- path(trees, reduceCallByValue))
          println(t)

      case e =>
        println(e)
    }
  }
}
