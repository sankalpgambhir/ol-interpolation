import interpolation.*
import definitions.*
import proving.*

object Tester:
  def createFile(fileName: String): Unit =
    val file = java.io.File(fileName)
    file.getParentFile().mkdirs()

  @main def test = {
    // define some variables
    val a = Variable("a")
    val b = Variable("b")
    val c = Variable("c")
    val d = Variable("d")
    val e = Variable("e")
    val f = Variable("f")
    val g = Variable("g")
    val h = Variable("\\phi") // latex names will print during latex output

    // we have two formulas
    val A = a \/ (!a)
    val B =  b \/ a

    // and a proof that A <= B
    // val proof = proveLeq(A, B)
    val proof = prove(None, Some(Right(A)))

    // we can see the interpolant of A and B, if one exists
    println(interpolateLeq(A, B))

    // output latex file
    val file = "out/test.tex"

    // or print the proof that A <= B
    proof.foreach { // if proof is not None
      p => {
        createFile(file)
        val writer = new java.io.PrintWriter(file)
        writer.write(p.toLatex)
        writer.close
        println(s"Printed proof to $file")
      }
    }
    println(proving.memoisedProve.stats)
  }
end Tester