package definitions

object UnreachableCaseException extends Exception()

sealed trait ProofStep

/**
  * 
  * ----------- Hyp
  *  ϕ^L, ϕ^R
  */
case class Hypothesis(phi: Formula) extends ProofStep
/**
  *      Π
  * ----------- Weaken
  *    Π, Δ
  */
case class Weaken(delta: Option[AnnotatedFormula], premise: ProofStep) extends ProofStep
/**
  *    Π, ϕ^L
  * ----------- LeftAnd1
  * Π, ϕ /\ ψ^L
  */
case class LeftAnd1(phi: Formula, psi: Formula, premise1: ProofStep) extends ProofStep
/**
  *    Π, ϕ^L
  * ----------- LeftAnd2
  * Π, ψ /\ ϕ^L
  */
case class LeftAnd2(phi: Formula, psi: Formula, premise1: ProofStep) extends ProofStep
/**
  *    Π, ϕ^R   Π, ψ^R
  * ------------------- RightAnd
  *     Π, ϕ /\ ψ^R
  */
case class RightAnd(phi: Formula, psi: Formula, premise1: ProofStep, premise2: ProofStep) extends ProofStep
/**
  *    Π, ϕ^L   Π, ψ^L
  * ------------------- LeftOr
  *     Π, ϕ \/ ψ^L
  */
case class LeftOr(phi: Formula, psi: Formula, premise1: ProofStep, premise2: ProofStep) extends ProofStep
/**
  *    Π, ϕ^R
  * ----------- RightOr1
  * Π, ϕ \/ ψ^R
  */
case class RightOr1(phi: Formula, psi: Formula, premise1: ProofStep) extends ProofStep
/**
  *    Π, ϕ^R
  * ----------- RightOr2
  * Π, ψ \/ ϕ^R
  */
case class RightOr2(phi: Formula, psi: Formula, premise1: ProofStep) extends ProofStep
/**
  *    Π, ϕ^R
  * ----------- LeftNot
  *   Π, ~ϕ^L
  */
case class LeftNot(phi: Formula, premise: ProofStep) extends ProofStep
/**
  *    Π, ϕ^L
  * ----------- LeftNot
  *   Π, ~ϕ^R
  */
case class RightNot(phi: Formula, premise: ProofStep) extends ProofStep
/**
  *    Π, Π
  * ----------- LeftNot
  *     Π
  */
case class Deduplicate(premise: ProofStep) extends ProofStep


/**
  * Representation of an OL sequent, only used internally for printing.
  *
  * @param el initial set of elements, all but 2 discarded.
  */
class Sequent(el: List[AnnotatedFormula]) {
    val maxSize = 2
    val elems: List[AnnotatedFormula] = el.take(maxSize)

    infix def +(f: AnnotatedFormula): Sequent =
        val newElems = f :: elems
        if newElems.size > maxSize then this else Sequent(newElems)
    infix def -(f: AnnotatedFormula): Sequent =
        elems match
          case `f` :: next => Sequent(next)
          case other :: `f` :: Nil => Sequent(other :: Nil)
          case _ => Sequent(elems)
        

    override def toString: String = 
        elems match {
            case Nil => "∅"
            case f :: Nil => f.toString
            case f1 :: f2 :: Nil => s"$f1, $f2"
            case _ => throw UnreachableCaseException
        }
    def toLatex: String = 
        elems match {
            case Nil => "\\emptyset"
            case f :: Nil => f.toLatex
            case f1 :: f2 :: Nil => s"${f1.toLatex}, ${f2.toLatex}"
            case _ => throw UnreachableCaseException
        }
}

val dollar = "$"

extension (p: ProofStep) {
    /**
      * Produces a compilable Latex document around the `bussproof` from
      * [[toLatexRaw]].
      */
    def toLatex: String = s"""
    \\documentclass{standalone}
    \\usepackage{bussproofs}
    \\usepackage{amsmath}

    \\begin{document}
    ${p.toLatexRaw}
    \\DisplayProof
    \\end{document}
    """
    /**
      * Produces a latex `bussproof` from the proof object.
      */
    def toLatexRaw: String = print._1
    def print: (String, Sequent) =
        p match
            case Hypothesis(phi) =>
                val st = s"""
                \\AxiomC{}
                \\RightLabel{\\text{Hyp}}
                \\UnaryInfC{$dollar${Left(phi).toLatex}, ${Right(phi).toLatex}$dollar}
                """
                (st, Sequent(List(Left(phi), Right(phi))))
            case Weaken(delta, premise) =>
                val inner = premise.print
                val seq = delta match {
                    case None => inner._2
                    case Some(v) => inner._2 + v
                }
                val st = s"""
                \\RightLabel{\\text{Weaken}}
                \\UnaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner._1 + st, seq)
            case LeftAnd1(phi, psi, premise1) =>
                val inner = premise1.print
                val seq = inner._2 - Left(phi) + Left(phi /\ psi)
                val st = s"""
                \\RightLabel{\\text{LeftAnd1}}
                \\UnaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner._1 + st, seq)
            case LeftAnd2(phi, psi, premise1) =>
                val inner = premise1.print
                val seq = inner._2 - Left(phi) + Left(psi /\ phi)
                val st = s"""
                \\RightLabel{\\text{LeftAnd2}}
                \\UnaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner._1 + st, seq)
            case RightAnd(phi, psi, premise1, premise2) =>
                val inner1 = premise1.print
                val inner2 = premise2.print
                val seq = inner1._2 - Right(phi) + Right(phi /\ psi)
                val st = s"""
                \\RightLabel{\\text{RightAnd}}
                \\BinaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner1._1 + inner2._1 + st, seq)
            case LeftOr(phi, psi, premise1, premise2) =>
                val inner1 = premise1.print
                val inner2 = premise2.print
                val seq = inner1._2 - Left(phi) + Left(phi \/ psi)
                val st = s"""
                \\RightLabel{\\text{LeftOr}}
                \\BinaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner1._1 + inner2._1 + st, seq)
            case RightOr1(phi, psi, premise1) =>
                val inner = premise1.print
                val seq = inner._2 - Right(phi) + Right(phi \/ psi)
                val st = s"""
                \\RightLabel{\\text{RightOr1}}
                \\UnaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner._1 + st, seq)
            case RightOr2(phi, psi, premise1) =>
                val inner = premise1.print
                val seq = inner._2 - Right(phi) + Right(psi \/ phi)
                val st = s"""
                \\RightLabel{\\text{RightOr2}}
                \\UnaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner._1 + st, seq)
            case LeftNot(phi, premise) =>
                val inner = premise.print
                val seq = inner._2 - Right(phi) + Left(!phi)
                val st = s"""
                \\RightLabel{\\text{LeftNot}}
                \\UnaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner._1 + st, seq)
            case RightNot(phi, premise) =>
                val inner = premise.print
                val seq = inner._2 - Left(phi) + Right(!phi)
                val st = s"""
                \\RightLabel{\\text{RightNot}}
                \\UnaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner._1 + st, seq)
            case Deduplicate(premise) =>
                val inner = premise.print
                val pi = inner._2.elems.head
                val seq = inner._2 - pi
                val st = s"""
                \\RightLabel{\\text{Deduplicate}}
                \\UnaryInfC{$dollar${seq.toLatex}$dollar}
                """
                (inner._1 + st, seq)
}
