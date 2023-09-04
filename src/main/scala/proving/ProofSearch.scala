package proving

import definitions.*

given toOption[A]: Conversion[A, Option[A]] = Option(_)

/**
  * Given a sequent as two possibly empty annotated formulas, produces a proof
  * (without axioms) if one exists. Naive proof search based on case analysis.
  */
def prove(
    left: Option[AnnotatedFormula], 
    right: Option[AnnotatedFormula]
) : Option[ProofStep] = memoisedProve(left, right)

val memoisedProve = memoised(proveInner)

private def proveInner(
    left: Option[AnnotatedFormula], 
    right: Option[AnnotatedFormula]
) : Option[ProofStep] = {
    right match
        case None => 
            left match
                case None => None
                case _ => prove(right, left)
        case Some(value) => 
            value match
                case Left(f) => 
                    f match
                        case v @ Variable(name) => 
                            // if left is also a variable, done, else reduce it first
                            left match
                                case None => None
                                case Some(Right(`v`)) => Hypothesis(v)
                                case Some(Left(Variable(name2))) => None
                                case Some(Right(Variable(name2))) if name != name2 => None
                                case _ => prove(right, left)
                        case And(l, r) =>
                            val p1 = prove(left, Left(l))
                            lazy val p2 = prove(left, Left(r))
                            p1.map(
                                LeftAnd1(l, r, _)
                            ).orElse(
                                p2.map(
                                    LeftAnd2(r, l, _)
                                )
                            )
                        case Or(l, r) =>
                            val p1 = prove(left, Left(l))
                            val p2 = prove(left, Left(r))
                            p1.flatMap(fs => p2.map(sd => LeftOr(l, r, fs, sd)))
                        case Not(l) =>
                            val inner = prove(left, Right(l))
                            inner.map(LeftNot(l, _))
                        case Exists(v, inner) => None
                        case Forall(v, inner) => None
                case Right(f) =>
                    f match
                        case v @ Variable(name) => 
                            // if left is also a variable, done, else reduce it first
                            left match
                                case None => None
                                case Some(Left(`v`)) => Hypothesis(v)
                                case Some(Right(Variable(name2))) => None
                                case Some(Left(Variable(name2))) if name != name2 => None
                                case _ => prove(right, left)
                        case And(l, r) =>
                            val p1 = prove(left, Right(l))
                            val p2 = prove(left, Right(r))
                            p1.flatMap(fs => p2.map(sd => RightAnd(l, r, fs, sd)))
                        case Or(l, r) =>
                            val p1 = prove(left, Right(l))
                            lazy val p2 = prove(left, Right(r))
                            p1.map(
                                RightOr1(l, r, _)
                            ).orElse(
                                p2.map(
                                    RightOr2(r, l, _)
                                )
                            )
                        case Not(l) =>
                            val inner = prove(left, Left(l))
                            inner.map(RightNot(l, _))
                        case Exists(v, inner) => None
                        case Forall(v, inner) => None
}

/**
  * Given two terms in the theory of ortholattice, returns a proof of `f1` <=
  * `f2` by converting to the sequent `f1^L, f2^R`.
  */
def proveLeq(
    f1: Formula,
    f2: Formula
): Option[ProofStep] =
    prove(Left(f1), Right(f2))


// memoization utilities

def memoised[A, B](f: (A, A) => B): (A, A) => B = 
    (l, r) => memoised((inp: Tuple2[A, A]) => f(inp._1, inp._2))((l, r))

/**
  * Memoises a function on a pair in an order-agnostic manner
  */
def memoised[A, B](f: Tuple2[A, A] => B): (Tuple2[A, A] => B) = 
    val hasher = scala.util.hashing.ByteswapHashing[A]()
    val hash = hasher.hash(_)
    val memory = scala.collection.mutable.Map.empty[Int, B]
    val fun: (Tuple2[A, A] => B) = 
        inp => 
            inline def l = hash(inp._1)
            inline def r = hash(inp._2)
            val key = l * r
            val stored = memory.get(key)
            if stored.isEmpty then
                memory.update(key, f(inp))
            memory(key)
    fun
