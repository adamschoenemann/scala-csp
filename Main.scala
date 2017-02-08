
import csp._
import Constraint._
import Shifts._

object Main extends App {

  // here are a bunch of scenario tests
  def test() = {
    testNC()
    testAC1()
    testAC2()
    sudoku2csp(List.fill(81) (0))
    val s = simpleSudoku
    testSudokuAC(s)
    testSudokuBT(s)
    testExam15();
  }

  // converts a Sudoku represtend as a flat list of ints (9 * 9 = 81) into
  // a CSP
  def sudoku2csp(s:List[Int]):CSP[Int] = {
    import Constraint._

    val domain = List.range(1,10)
    val letters = List.range('A', 'J')
    val ids =
      List.range(0,81).map { i =>
        val r = i / 9
        val c = 1 + i - r * 9
        letters(r) + c.toString
      }

    val assigned =
      s.zip(ids).foldLeft[List[UnaryCon[Int]]] (Nil) {
        case (a, (x:Int,id:String)) =>
          if (x == 0)
            a
          else
            unary[Int] (id, _ == x) :: a
      }

    val vars = ids.map(Var[Int] (_, domain))

    val allDiffRows = List.range('A', 'J').flatMap {r =>
      allDiff[Int](
        List.range(1,10).map(r + _.toString)
      )
    }

    val allDiffCols = List.range(1, 10).flatMap {c =>
      allDiff[Int](
        List.range('A', 'J').map(_ + c.toString)
      )
    }

    val allDiffBoxes =
      List.range('A', 'J').grouped(3).flatMap(rs =>
        List.range(1,10).grouped(3).flatMap(cs =>
          allDiff[Int](
            for {
              r <- rs
              c <- cs
            } yield (r + c.toString)
          )
        )
      ).toList

    val constraints = allDiffRows ++ allDiffCols ++ allDiffBoxes ++ assigned
    CSP(vars.map(x => (x.id, x)).toMap, constraints)
  }

  def simpleSudoku = {

    val simple = List(
      0,0,3,0,2,0,6,0,0,
      9,0,0,3,0,5,0,0,1,
      0,0,1,8,0,6,4,0,0,
      0,0,8,1,0,2,9,0,0,
      7,0,0,0,0,0,0,0,8,
      0,0,6,7,0,8,2,0,0,
      0,0,2,6,0,9,5,0,0,
      8,0,0,2,0,3,0,0,9,
      0,0,5,0,1,0,3,0,0
    )

    sudoku2csp(simple)
  }

  def showSudoku(s:Seq[Int]):String = s
    .grouped(9).toList
    .map(
      _.grouped(3).toList.map(
        "|" + _.map(" " + _ + " ").mkString
      ).flatten.mkString + "|\n"
    )
    .grouped(3).map((List.fill (3 * 10) ('-').mkString + "-\n") :: _)
    .flatten
    .toList.tail
    .mkString

  def testSudokuBT(s:CSP[Int]) = {

    val CompleteAssignment(solution) = s.backtrack().get
    val solString = showSudoku(solution.map(_.value).reverse)



    println(solString)
  }

  def testSudokuAC(s:CSP[Int]) = {

    val csp = s.nodeConsistent.arcConsistent().get

    // solution found!
    // assert(csp.vars.map(_.domain.length).sum == 9 * 9)

    // println(showSudoku(csp.vars.map(_.domain.head)))

  }

  def testNC() = {
    import Constraint.{unary}
    val domain = List.range(0,21)
    val c1 = CSP(
      List("x","y","z").map(x => (x, Var(x, domain))).toMap,
      List(
        unary[Int]("x", _ % 2 == 0),
        unary[Int]("y", _ % 2 == 1),
        unary[Int]("z", _ < 10),
        unary[Int]("z", _ > 4)
      )
    )

    val c1nc = c1.nodeConsistent
    c1nc.vars match {
      case List(Var("x", xd), Var("y", yd), Var("z", zd)) =>
        assert(
          xd == List.range(0, 11).map(_ * 2) &&
          yd == List.range(0, 10).map(_ * 2 + 1) &&
          zd == List.range(5, 10)
        )
    }
  }

  def testAC1() = {
    val digits = List.range(0,10)
    val x = Var("x", digits)
    val y = Var("y", digits)
    val c1 = CSP(
      Map("x" -> x, "y" -> y),
      List(
        BinCon[Int](("x","y"), (x,y) => y == x * x)
      )
    )
    val c1ac = c1.arcConsistent().get

    assert(c1ac.vars ==
      List(Var("x", List(0,1,2,3)), Var("y", List(0,1,4,9)))
    )
  }

  def testAC2() = {
    import Constraint._
    val domain = List.range(1,7)
    val c1 = CSP(
      List("c1", "c2", "c3", "c4").map(x => (x, Var(x, domain))).toMap,
      List(
        unary[Int]("c1", _ != 1), unary[Int]("c2", _ != 2),
        unary[Int]("c3", _ != 3), unary[Int]("c4", _ != 4),
        binary[Int](("c4", "c3"), _ - _ > 2),
        binary[Int](("c3", "c1"), _ + _ >= 5),
        binary[Int](("c1", "c2"), _ * _ >= 6),
        binary[Int](("c1", "c2"), _ + _ <= 7),
        unary[Int]("c3", _ <= 5),
        unary[Int]("c4", _ > 4)
      )
    )

    val consistent = c1.nodeConsistent.arcConsistent().get
  }

  implicit def implvar[A](tup:(String, Domain[A])):Var[A] =
    Var(tup._1, tup._2)
  implicit def implvars[A](vs:List[(String,Domain[A])]):List[Var[A]] =
    vs.map(implvar)

  implicit def implbin[A](tup:(String,String,BinRel[A])):BinCon[A] =
    tup match {
      case (a,b,c) => binary[A]((a,b),c)
    }
  implicit def implbins[A](bs:List[(String,String,BinRel[A])]):List[BinCon[A]] =
    bs.map(implbin)

  def testExam15() = {
    val domain = List(1,2,3,4)
    val exam = CSP(
      List("a","b","c","d","e","f").map(x => (x, Var(x, domain))).toMap,
      List[BinCon[Int]](
        ("a","b", (_:Int) + (_:Int) == 5),
        ("b","d", (_:Int) + (_:Int) == 6),
        ("d","c", (_:Int) + (_:Int) == 5),
        ("c","f", (_:Int) + (_:Int) == 4),
        ("f","e", (_:Int) + (_:Int) == 5),
        ("e","a", (_:Int) + (_:Int) == 5)
      )
    )

    val acexam = exam.arcConsistent().get

    println(acexam)

    println("Solution")
    val sol = acexam.backtrack(inferencer = CSP.MCInference)
    println(sol.get.assigned)

  }

  def testCombinations() {
    println(CSP.combinations(List(List(1,2))))
    println(CSP.combinations(List(List(1,2), List(3,4,5))))
    println(CSP.combinations(List(List(1,2), List(3,4), List(5,6))))
    println(CSP.combinations(List(List(0,1), List(0,1), List(0,1), List(0,1))))
  }

  def testReviseNAry() {
    val bdomain = List(true,false)
    val ids = List("x", "y")
    val vars1 = ids.map(x => Var(x, bdomain))
    val c1 = NAryCon[Boolean]("c1", ids, _.forall(_ == true))
    assert ((CSP.revise(vars1, c1)) == List(List(true,true)))

    val c2 = NAryCon[Boolean]("c2", ids, _.exists(_ == true))
    assert ((CSP.revise(vars1, c2)) == List(List(true,true), List(true,false), List(false, true)))

    {
      val domain = List(0,1)
      val ids = List("x","y","z")
      val vars = ids.map(x => Var(x, domain))
      val c1 = NAryCon[Int]("c1", ids, _.filter(_ == 1).length == 1)
      assert (CSP.revise(vars, c1) == List(List(0, 0, 1), List(0, 1, 0), List(1, 0, 0)))
    }
    {
      val domain = List(3,5,2,0)
      val ids = List("x","y","z")
      val vars = ids.map(x => Var(x, domain))
      val c1 = NAryCon[Int]("c1", ids, _.sum == 8)
      assert (CSP.revise(vars, c1) ==
        List(List(3, 3, 2), List(3, 5, 0), List(3, 2, 3), List(3, 0, 5),
             List(5, 3, 0), List(5, 0, 3), List(2, 3, 3), List(0, 3, 5), List(0, 5, 3)
        )
      )
    }
  }

  def testDuality() {
    val domain = List(true,false)
    val ids = List.range(1,7).map(n => s"x_$n")
    val clause1 = NAryCon[Boolean]("y_1", Seq("x_1","x_2","x_6"), _.exists(_ == true))
    val clause2 = NAryCon[Boolean]("y_2", Seq("x_1","x_3","x_4"),
                    c => !c(0) || c(1) || c(2))
    val clause3 = NAryCon[Boolean]("y_3", Seq("x_4","x_5","x_6"),
                    c => !c(0) || !c(1) || c(2))
    val clause4 = NAryCon[Boolean]("y_4", Seq("x_2","x_5","x_6"),
                    c => c(0) || c(1) || !c(2))

    val clauses = List(clause1, clause2, clause3, clause4)
    val domainMap = ids.map((_, domain)).toMap
    val dual = clauses.map(_.toBinary(domainMap))

    dual.map(x => println(x._2))

  }

  testDuality()
  // testReviseNAry()
  // test()
  // testShiftAssignment()

 }
