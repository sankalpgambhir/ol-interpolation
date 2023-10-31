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
) : Option[ProofStep] =
    val p1 = memoisedProve(left, right)
    lazy val p2 = memoisedProve(right, left)
    p1.orElse(p2)
    

val memoisedProve = memoised(proveInner, None)

private def proveInner(
    left: Option[AnnotatedFormula], 
    right: Option[AnnotatedFormula]
) : Option[ProofStep] = {
    (left, right) match
        case (None, None) => None
        case (None, Some(_)) =>
            // single formula, duplicate
            prove(right, right).map(Deduplicate(_))
        case (Some(_), None) =>
            // single formula, duplicate
            prove(left, left).map(Deduplicate(_))
        case (Some(_), Some(r)) =>
            r match
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

case class MemoizationStats(hits: Int, miss: Int, faulted: Int):
    def withHit = MemoizationStats(hits + 1, miss, faulted)
    def withMiss = MemoizationStats(hits, miss + 1, faulted)
    def withFault = MemoizationStats(hits, miss, faulted + 1)

class Memoised[A, B](f: Tuple2[A, A] => B, default: B) extends Function1[Tuple2[A, A], B]:
    val hasher = scala.util.hashing.ByteswapHashing[A]()
    val hash = hasher.hash(_)
    val visited = scala.collection.mutable.Set.empty[Int]
    val memory = scala.collection.mutable.Map.empty[Int, B]
    var stats = MemoizationStats(0, 0, 0)

    def this(f: (A, A) => B, default: B) = this(f.tupled, default)

    val fun: (Tuple2[A, A] => B) = 
        inp => 
            inline def l = hash(inp._1)
            inline def r = hash(inp._2)
            val key = l * 3 + r * 5
            val seen = visited.contains(key)
            val stored = memory.get(key)
            if stored.isEmpty then
                visited.add(key)
                if seen then
                    stats = stats.withFault
                    memory.update(key, default)
                else 
                    stats = stats.withMiss
                    memory.update(key, f(inp))
            else
                stats = stats.withHit
                    
            memory(key)

    def apply(v1: (A, A)): B = fun(v1)

def memoised[A, B](f: (A, A) => B, default: B): Memoised[A, B] = 
    Memoised(f, default)

/**
  * Memoises a function on a pair
  */
def memoised[A, B](f: Tuple2[A, A] => B, default: B): Memoised[A, B] = 
    Memoised(f, default)
