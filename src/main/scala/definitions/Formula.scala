package definitions

sealed trait Formula {
    override def toString(): String = 
        this match
            case Variable(name) => name
            case And(l, r) => s"($l ∧ $r)"
            case Or(l, r) => s"($l ∨ $r)"
            case Not(l) => s"¬$l"
            case Forall(v, inner) => s"⋀$v. $inner"
            case Exists(v, inner) => s"⋁$v. $inner"
        
    def toLatex: String =
        this match
            case Variable(name) => name
            case And(l, r) => s"(${l.toLatex} \\land ${r.toLatex})" 
            case Or(l, r) => s"(${l.toLatex} \\lor ${r.toLatex})" 
            case Not(l) => s"\\neg${l.toLatex}" 
            case Forall(v, inner) => s"\bigwedge ${v.toLatex}. ${inner.toLatex}"
            case Exists(v, inner) => s"\bigvee ${v.toLatex}. ${inner.toLatex}"
}

case class Variable(name: String) extends Formula
case class And(l: Formula, r: Formula) extends Formula
case class Or(l: Formula, r: Formula) extends Formula
case class Not(l: Formula) extends Formula
case class Forall(v: Variable, inner: Formula) extends Formula
case class Exists(v: Variable, inner: Formula) extends Formula

extension (f1: Formula) {
    def unary_! = Not(f1)
    infix def `/\\`(f2: Formula) = And(f1, f2) 
    infix def `\\/`(f2: Formula) = Or(f1, f2) 
}

sealed trait AnnotatedFormula {
    override def toString(): String = // maybe a cleaner way to write?
        this match {
            case Left(f) =>  s"${f}^L"
            case Right(f) =>  s"${f}^R"
        } 
    def toLatex = 
        this match {
            case Left(f) =>  s"${f.toLatex}^L"
            case Right(f) =>  s"${f.toLatex}^R"
        }
}

case class Left(f: Formula) extends AnnotatedFormula
case class Right(f: Formula) extends AnnotatedFormula
