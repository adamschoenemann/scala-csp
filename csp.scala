
object csp {

  // some aliases
  type VarID = String

  // A Var has an ID (string) and a domain of legal values
  case class Var[A](id:VarID, domain:Domain[A])

  type Vars[A] = List[Var[A]]

  type Domain[A] = List[A]
  type Domains[A] = List[Domain[A]]

  type BinRel[A] = (A,A) => Boolean
  type UnaryRel[A] = A => Boolean

  // not used right now
  type NAryRel[A] = List[A] => Boolean

  sealed trait Constraint[+A]

  // unary constraint
  case class UnaryCon[A](variable: VarID, rel:UnaryRel[A]) extends Constraint[A] {

    // unsafe!
    def variable(csp:CSP[A]):Var[A] =
      csp.vars.find(_.id == variable).get
  }

  // binary constraint
  case class BinCon[A](vars: (VarID,VarID), rel: BinRel[A]) extends Constraint[A] {

    // unsafe!
    def vars(csp:CSP[A]):(Var[A],Var[A]) = {
      val o = for {
        a <- csp.vars.find(_.id == vars._1)
        b <- csp.vars.find(_.id == vars._2)
      } yield (a,b)
      o.get
    }

    def reflect:BinCon[A] =  {
      val (a,b) = vars
      BinCon[A]((b,a), (x,y) => rel(y,x))
    }
  }

  // not used right now
  case class NAryCon[A](vars: List[A], rel: NAryRel[A]) extends Constraint[A]

  object Constraint {
    // "smart" constructor - just slightly more handy that writing the normal
    // constructor
    def binary[A](vars: (VarID,VarID), rel: BinRel[A]):BinCon[A] =
      BinCon[A](vars, rel)

    // "smart" constructor - just slightly more handy that writing the normal
    // constructor
    def unary[A](v:VarID, rel:UnaryRel[A]):UnaryCon[A] =
      UnaryCon[A](v,rel)

    // represent an AllDiff constraint as a list of binary constraints
    def allDiff[A](vars:List[VarID]):List[BinCon[A]] =
      for {
        v <- vars
        v2 <- vars if v != v2
      } yield binary[A]((v, v2), _ != _)
  }

  type Constraints[A] = List[Constraint[A]]

  object CSP {

    // revise two variables with a binary constraint
    def revise[A](x:Var[A], y:Var[A], c:BinCon[A]):Domain[A] =
      x.domain.filter(a =>
      y.domain.exists(b =>
      c.rel(a,b)
    ))

    // type aliases used to customize backtracking
    type VarSelecter[A] = (List[VarID], CSP[A]) => (VarID, List[VarID])
    type DomainOrderer[A] = Domain[A] => Domain[A]
    type Inferencer[A] = (CSP[A], VarID, Assignment[A]) => Option[CSP[A]]

    // Maintain Arc Consistence inference (MAC)
    // Basically, just AC, except we start with a queue containing only neighbours
    // of the constrained variable
    def MCInference[A]:Inferencer[A] = (csp, vid, ass) => {
      val neighbours = csp.dependents(vid).filter {(c:BinCon[A]) =>
        ass.unassigned.contains (c.vars._1)
      }
      csp.arcConsistent(neighbours)
    }


    // default variable selecter.
    // Just returns (head, tail)
    // Fails on empty lists
    def defVarSelecter[A]:VarSelecter[A] = (ids, csp) => ids match {
      case id :: ids => (id, ids)
      case _ => sys.error("should not happen")
    }

    // default domain orderer - performs no ordering
    def defDomainOrderer[A]:DomainOrderer[A] = identity _

    // Forward-Checking inference (FC)
    // This inference algorithm just performs arc-consistency on the neighbours
    // of the constrained variable, and does not recurse out to its neighbours
    def FCInference[A]:Inferencer[A] = (csp, vid, ass) => {
      val neighbours = csp.dependents(vid).filter {(c:BinCon[A]) =>
        ass.unassigned.contains (c.vars._1)
      }

      neighbours.foldLeft[Option[CSP[A]]] (Some(csp)) {
        case (None, _) => None
        case (Some(acc), c) => acStep(c, acc).map(_._2)
      }
      // val x = csp.getVar(vid)
      // this is basically just arcConsistent without maintaining a queue
      // to update
      // val csp2 = neighbours.foldLeft[Option[CSP[A]]] (Some(csp)) ((a,b) => (a,b) match {
      //   case (None, _) => None
      //   case (Some(acc), c) => {
      //     val y = acc.getVar(c.vars._1)
      //     val domain = CSP.revise(y, x, c)
      //     if (domain.isEmpty)
      //       None
      //     else Some(acc.updateDomain(y.id, domain))
      //   }
      // })

      // csp2
    }

    def acStep[A](c:BinCon[A], csp:CSP[A]):Option[(Boolean, CSP[A])] = {
      val (x, y) = c.vars(csp)

      // get a revised domain for X
      val domain2 = CSP.revise(x,y,c)

      // no change, so just continue with queue
      if (x.domain == domain2)
        Some((false, csp))
        // ac(cs, csp)
      else if (domain2.isEmpty) // empty domain, so inconsistent assignment
        None
      else { // the new domain != old domain
        // update domain of variable
        val csp2 = csp.updateDomain(
            x.copy(domain = domain2)
          )
        Some((true, csp2))
      }
    }
  }

  // CSP case class!
  // Represents a Constraint Satisfaction Problem
  // The "D" component in the book that contains domains for variables
  // have been eliminated - instead, each variable keeps track of its own
  // domain
  case class CSP[A](vars:Vars[A], constraints:Constraints[A]) {

    import CSP._

    // unsafe!
    def domain(vid:VarID):Domain[A] =
      getVar(vid).domain

    // unsafe
    def getVar(vid:VarID):Var[A] =
      vars.find(_.id == vid).get

    def updateDomain(v:Var[A]):CSP[A] =
      updateDomain(v.id, v.domain)

    // update the domain of variable with id == vid
    def updateDomain(vid:VarID, domain:Domain[A]):CSP[A] =
      copy(vars = vars.map(x =>
        if (vid == x.id) Var(vid, domain) else x
      ))

    // get variables that is the left hand side in a constraint with
    // vid as the right hand side.
    // Could also be called "neighbours"
    def dependents(vid:VarID):List[BinCon[A]] =
      binaryConstraints.filter(_.vars._2 == vid)

    // get a list of all unary constraints in the CSP
    def unaryConstraints:List[UnaryCon[A]] =
      constraints.flatMap {
        case c@UnaryCon(_,_) => List(c)
        case _             => Nil
      }

    // get a list of all binary constraints in the CSP
    def binaryConstraints:List[BinCon[A]] =
      constraints.flatMap {
        case c@BinCon(_,_) => List(c)
        case _             => Nil
      }

    // represent all binary constraints as two directed arcs in a graph
    def arcs:List[BinCon[A]] = {
      val as = binaryConstraints
      as ++ as.map (_.reflect)
    }

    // return a new CSP that is node consistent
    def nodeConsistent:CSP[A] = {
      val cs = unaryConstraints
      cs.foldLeft[CSP[A]] (this) {(csp,c) =>
        val v = c.variable(csp)
        val domain = v.domain.filter(c.rel(_))
        csp.updateDomain(v.copy(domain = domain))
      }
    }

    /**
     * Returns an Option of arc-consistent CSP
     * @param queue List[BinCon[A]] A queue of binary constraint arcs that
     * need to be made arc-consistent. default: this.arcs
     * @type Option[CSP[A]]
     */
    def arcConsistent(queue:List[BinCon[A]] = this.arcs):Option[CSP[A]] = {

      def getPropagated(x:Var[A], y:Var[A], csp:CSP[A]):List[BinCon[A]] = {
        csp.arcs.filter(_.vars._1 != y.id).filter(_.vars._2 == x.id)
      }

      @annotation.tailrec
      def ac(queue:List[BinCon[A]], csp:CSP[A]):Option[CSP[A]] = queue match {
        case Nil => Some(csp)
        case c :: cs => {
          // we cannot flatmap this, because then we lose tail recursion
          acStep(c, csp) match {
            case None => None
            case Some((t, csp2)) => {
              val (x,y) = c.vars(csp)
              val addToQueue = if (t) {
                  getPropagated(x,y,csp)
                } else {
                  Nil
                }
              ac(cs ++ addToQueue, csp2)
            }
          }
        }
      }

      ac(queue, this)
    }

    def canAssign(ass:VarAss[A]):Boolean = {
      val v = getVar(ass.varID)
      val ds = "{" + v.domain.mkString(",") + "}"
      println(s"assigning ${ass.varID} to ${ass.value}. legal values are $ds")
      v.domain.contains(ass.value)
    }

    // Create a new CSP from an assignment.
    // Basically, to assign a variable in a CSP, just constrain its domain
    // to a single value, i.e. List(value)
    def assign(ass:Assignment[A]):CSP[A] = {
      def as(ass:List[VarAss[A]]):CSP[A] = {
        ass.foldLeft (this) {(c, a) =>
          c.updateDomain(a.varID, List(a.value))
        }
      }
      as(ass.assigned)
    }

    def assign(ass:VarAss[A]):CSP[A] = {
      this.updateDomain(ass.varID, List(ass.value))
    }

    def isConsistent(ass:CompleteAssignment[A]):Boolean = {
      unaryConstraints.forall(c => c.rel(ass.getValue(c.variable))) &&
        binaryConstraints.forall(c => {
          val x = ass.getValue(c.vars._1)
          val y = ass.getValue(c.vars._2)
          c.rel(x,y)
        })
    }



    /**
     * Backtrack!
     * Searches for a consistent and complete assignment.
     * It takes three Higher-Order Functions that parameterizes its behaviour.
     * However, they all have default parameters
     * @param varSelecter VarSelecter[A] Selects a variable
     * @param domainOrderer DomainOrderer[A] Orders the domain of a variable
     * before assigning a value from the domain
     * @param inferencer Inferencer[A] performs inference on the CSP after
     * a variable has been assigned
     * @type {Option[Assignment[A]]}
     */
    def backtrack(varSelecter: VarSelecter[A] = defVarSelecter,
                  domainOrderer: DomainOrderer[A] = defDomainOrderer,
                  inferencer:Inferencer[A] = FCInference)
                  :Option[Assignment[A]] = {


      def bc(ass:Assignment[A], csp:CSP[A]):Option[Assignment[A]] = ass match {

        case c@CompleteAssignment(_) =>
          if (csp.isConsistent(c))
            Some(c)
          else None

        case c@PartialAssignment(assigned, Nil) =>
          bc(CompleteAssignment(assigned), csp)

        case PartialAssignment(assigned, unassigned) => {
          val (u, us) = varSelecter(unassigned, csp)
          // for each value in domain of u
          // assign, check if valid if yes, move on on, if no, try next
          // value
          val domain = domainOrderer(csp.domain(u))
          domain.foldLeft[Option[Assignment[A]]] (None) ((a,d) => {
            if (a.isEmpty == false) a // solution already found
            else {
              val varAss = VarAss(u, d)
              val ass2 = PartialAssignment(varAss :: assigned, us)
              if (csp.canAssign(varAss))
                inferencer(csp.assign(varAss), u, ass2).flatMap(csp2 =>
                  bc(ass2, csp2)
                )
              else None
            }
          })
        }

      }

      bc(PartialAssignment(Nil, vars.map(_.id)), this.nodeConsistent)

    }

  }



  // A single variable assignment
  case class VarAss[+A](varID:VarID, value:A)

  // base class for a CSP assignment (i.e. multiple variables assigned)
  sealed trait Assignment[+A] {
    def assigned:List[VarAss[A]]
    def unassigned:List[VarID]
  }

  // a partial assignment
  case class PartialAssignment[A]
            (assigned:List[VarAss[A]], unassigned:List[VarID])
             extends Assignment[A]

  // a compelte assignment
  case class CompleteAssignment[A]
            (assigned:List[VarAss[A]])
            extends Assignment[A] {

    def unassigned = Nil

    def getValue(id:String):A = assigned.find(_.varID == id).get.value
  }



}

object Main extends App {

  import csp._
  import Constraint._

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
    CSP(vars, constraints)
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

  def showSudoku(s:List[Int]):String = s
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
      List(Var("x", domain), Var("y",domain), Var("z",domain)),
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
      List(x, y),
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
      List(
        Var("c1", domain), Var("c2", domain), Var("c3", domain), Var("c4", domain)
      ),
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

  def testExam15() = {
    val domain = List(1,2,3,4)
    val exam = CSP(
      List(
        Var("a", domain), Var("b", domain), Var("c", domain), Var("d", domain),
        Var("e", domain), Var("f", domain)
      ),
      List(
        binary[Int](("a","b"), (_) + (_) == 5),
        binary[Int](("b","d"), (_) + (_) == 6),
        binary[Int](("d","c"), (_) + (_) == 5),
        binary[Int](("c","f"), (_) + (_) == 4),
        binary[Int](("f","e"), (_) + (_) == 5),
        binary[Int](("e","a"), (_) + (_) == 5)
      )
    )

    val acexam = exam.arcConsistent().get

    println(acexam)

    println("Solution")
    val sol = acexam.backtrack(inferencer = CSP.MCInference)
    println(sol.get.assigned)

  }

  test()

}

