package fos

import scala.util.parsing.combinator.syntactical.StandardTokenParsers
import scala.util.parsing.input._

/** This object implements a parser and evaluator for the NB
 *  language of booleans and numbers found in Chapter 3 of
 *  the TAPL book.
 */
object Arithmetic extends StandardTokenParsers {
  lexical.reserved ++= List("true", "false", "0", "if", "then", "else", "succ", "pred", "iszero")

  import lexical.NumericLit

  /** term ::= 'true'
             | 'false'
             | 'if' term 'then' term 'else' term
             | '0'
             | 'succ' term
             | 'pred' term
             | 'iszero' term
   */
  def term: Parser[Term] = (
        "true" ^^^ True
      | "false" ^^^ False
      | "if" ~ term ~ "then" ~ term ~ "else" ~ term ^^ { case _ ~ a ~ _ ~ b ~ _ ~ c => If(a, b, c) }
      | numericLit ^^ { x => numTerm(x.toInt) }
      | "succ" ~> term ^^ Succ
      | "pred" ~> term ^^ Pred
      | "iszero" ~> term ^^ IsZero
    )

  def numTerm(n: Int): Term =
    if (n == 0) Zero
    else
      Succ(numTerm(n-1))

  case class NoReductionPossible(t: Term) extends Exception(t.toString)

  /** Return a list of at most n terms, each being one step of reduction. */
  def path(t: Term, n: Int = 64): List[Term] =
    if (n <= 0) Nil
    else
      t :: {
        try {
          path(reduce(t), n - 1)
        } catch {
          case NoReductionPossible(t1) =>
            Nil
        }
      }

  /** Perform one step of reduction, when possible.
   *  If reduction is not possible NoReductionPossible exception
   *  with corresponding irreducible term should be thrown.
   */
  def reduce(t: Term): Term = t match {
      case If(True, t1, _) => t1
      case If(False, _, t2) => t2
      case IsZero(Zero) => True
      case IsZero(Succ(_)) => False
      case Pred(Zero) => Zero
      case Pred(Succ(nv)) if isNumericValue(nv) => nv
      case If(term, t1, t2) => If(reduce(term), t1, t2)
      case IsZero(term) => IsZero(reduce(term))
      case Pred(term) => Pred(reduce(term))
      case Succ(term) => Succ(reduce(term))
      case _ => throw NoReductionPossible(t)
  }

  def isNumericValue(t: Term): Boolean = t match {
    case Zero => true
    case Succ(t1) => isNumericValue(t1)
    case _ => false
  }

  case class TermIsStuck(t: Term) extends Exception(t.toString)

  /** Perform big step evaluation (result is always a value.)
   *  If evaluation is not possible TermIsStuck exception with
   *  corresponding inner irreducible term should be thrown.
   */
  def eval(t: Term): Term = t match {
    case True => True
    case False => False
    case Zero => Zero
    case If(cond, t1, t2) => eval(cond) match {
      case True => eval(t1)
      case False => eval(t2)
      case _ => throw TermIsStuck(t)
    }
    case Succ(term) if isNumericValue(term) => Succ(eval(term))
    case Pred(term) => eval(term) match {
      case Zero => Zero
      case Succ(t1) if isNumericValue(t1) => eval(t1)
      case _ => throw TermIsStuck(t)
    }
    case IsZero(term) => if (eval(term) == Zero) True else False
    case _ => throw TermIsStuck(t)
  }

  def main(args: Array[String]): Unit = {
    val stdin = new java.io.BufferedReader(new java.io.InputStreamReader(System.in))
    val tokens = new lexical.Scanner(stdin.readLine())
    phrase(term)(tokens) match {
      case Success(trees, _) =>
        for (t <- path(trees))
          println(t)
        try {
          print("Big step: ")
          println(eval(trees))
        } catch {
          case TermIsStuck(t) => println("Stuck term: " + t)
        }
      case e =>
        println(e)
    }
  }
}
