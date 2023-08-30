package interpolation

import definitions.*
import proving.*

given toOption[A]: Conversion[A, Option[A]] = Option(_)

/**
  * Given an ordered pair of (possibly empty) annotated formulas `(gamma1,
  * gamma2)` and an orthologic proof of the sequent `gamma1, gamma2`, `p`.
  * Produces an interpolant `I` containing only the common variables of `gamma1`
  * and `gamma2` such that `gamma1` proves `I` and `I` proves `gamma2` in
  * orthologic.
  *
  * The behaviour is undefined if `p` is not a proof of `gamma1, gamma2`.
  *
  * @param gamma1 first annotated formula
  * @param gamma2 second annotated formula
  * @param p proof of `gamma1, gamma2`
  * @return an interpolant of `(gamma1, gamma2)`
  */
def interpOLate(
    gamma1: Option[AnnotatedFormula], 
    gamma2: Option[AnnotatedFormula],
    p: ProofStep): Formula = 
    p match
        case Hypothesis(phi) =>
            gamma1 match
                case Some(Left(`phi`)) => phi
                case Some(Right(`phi`)) => !phi
                case _ => throw UnreachableCaseException
        case Weaken(delta, premise) =>
            gamma1 match
                case `delta` => interpOLate(None, gamma2, premise)
                case _ => interpOLate(gamma1, None, premise)
        case LeftAnd1(phi, psi, premise1) =>
            gamma1 match
                case Some(Left(And(`phi`, `psi`))) => interpOLate(Left(phi), gamma2, premise1)
                case _ => interpOLate(gamma1, Left(phi), premise1)
        case LeftAnd2(phi, psi, premise1) =>
            gamma1 match
                case Some(Left(And(`psi`, `phi`))) => interpOLate(Left(phi), gamma2, premise1)
                case _ => interpOLate(gamma1, Left(phi), premise1)
        case RightAnd(phi, psi, premise1, premise2) =>
            gamma1 match
                case Some(Right(And(`phi`, `psi`))) => 
                    interpOLate(Right(phi), gamma2, premise1) \/ interpOLate(Right(psi), gamma2, premise2)
                case _ => 
                    interpOLate(gamma1, Right(phi), premise1) /\ interpOLate(gamma1, Right(psi), premise2)
        case LeftOr(phi, psi, premise1, premise2) =>
            gamma1 match
                case Some(Left(Or(`phi`, `psi`))) => 
                    interpOLate(Left(phi), gamma2, premise1) \/ interpOLate(Left(psi), gamma2, premise2)
                case _ => 
                    interpOLate(gamma1, Left(phi), premise1) /\ interpOLate(gamma1, Left(psi), premise2)
        case RightOr1(phi, psi, premise1) =>
            gamma1 match
                case Some(Right(Or(`phi`, `psi`))) => interpOLate(Right(phi), gamma2, premise1)
                case _ => interpOLate(gamma1, Right(phi), premise1)
        case RightOr2(phi, psi, premise1) =>
            gamma1 match
                case Some(Right(Or(`psi`, `phi`))) => interpOLate(Right(phi), gamma2, premise1)
                case _ => interpOLate(gamma1, Right(phi), premise1)
        case LeftNot(phi, premise) =>
            gamma1 match
                case Some(Left(Not(`phi`))) => interpOLate(Right(phi), gamma2, premise)
                case _ => interpOLate(gamma1, Right(phi), premise)
        case RightNot(phi, premise) =>
            gamma1 match
                case Some(Right(Not(`phi`))) => interpOLate(Left(phi), gamma2, premise)
                case _ => interpOLate(gamma1, Left(phi), premise)


/**
  * Given two terms `a` and `b` in the theory of ortholattices, computes their
  * interpolant `c` such that `a <= c <= b` (assuming `a <= b` can be proved).
  *
  * @param a
  * @param b
  * @return their interpolant
  */
def interpolateLeq(a: Formula, b: Formula): Option[Formula] = 
    proveLeq(a, b).map(interpOLate(Left(a), Right(b), _))
