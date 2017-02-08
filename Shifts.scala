
import csp._
import Constraint._

object Shifts {

  /*
  2M: all users must have at least two shifts each month. And at least two
      must also be on weekdays (ie. not in weekend)
  10H: if a user has a shift of >= 10 hours they cannot take the shift the day after
  1D: a user can only take one shift per day
  LIMIT: a user must have hours more than (-5 their limit) and less than (+5) their limit
         unless it is zero. In that case, they can take no shifts.
  ASS: every shift must be assigned

    let T = {a,b,c} be the types of shifts on each day
    let D = all days of the month (four whole weeks)
    let W = the fours weeks of a month, s.t. ∀d ∈ D. W₀ <= week(d) <= W₃
    let ∀w ∈ W. days(w) = the days of the week w
    let U = all the users that can take shifts
    let ∀u ∈ U, w ∈ W. L(w, u) = the limit of hours a user u can work in week w
    let ∀t ∈ T. H(t) = the duration of a shift in hours (Double)
    let ∀t ∈ T, d ∈ D, u ∈ U.
          utd = true iff user u has taken shift t on day d

    constraint 1D: ∀u ∈ U, d ∈ D. size ({ utd | t ∈ T, utd = true}) = 1
    constraint 2M: size( {utd | ∀u ∈ U, d ∈ D, t ∈ T, utd = true} ) >= 2
    constraint LIMIT:
        ∀u ∈ U. ∀w ∈ W. ∀d ∈ days(w).
          if L(w,u) != 0
          then L(w,u) - 5 <= sum({H(t) | t ∈ T, utd = true}) <= L(w,u) + 5
          else sum({H(t) | t ∈ T, utd = true}) = 0
    constraint 10H:
      ∀u ∈ U, dᵢ ∈ D. ((∃utd ∧ H(t) >= 10) ⇒ ¬(∃utdⱼ))
      where j = i+1
  */

  def testShiftAssignment() = {
    val nweeks = 1
    val diw = 1 // days in week
    case class Day(week:Int, day:Int)
    val weeks = List.range(0,nweeks)
    val days = weeks.flatMap(w =>
      for (d <- w*diw until w*diw+diw) yield
        Day(w, d)
    )
    def daysInWeek(w:Int) = days.filter(_.week == w)
    def shiftTypes = Map[String,Double](
      "x" -> 5.5,
      "a" -> 6.5,
      "b" -> 8.5
      // "c" -> 6.5,
      // "d" -> 5
    )

    case class User(name:String, limits: Seq[Int])

    val names = Seq("Jonas", "Emma", "Adam", "Sara", "Andreas", "Andrea",
                    "Trump", "Anders", "Cecilie", "Jeanette", "Jesper",
                    "Greve", "Ditte", "Siri", "Oscar", "Martin", "Soeren"
                   )

    import scala.util.Random
    val r = new Random(17)
    def mkLimits() = Seq.range(0,4).map(_ => r.nextInt(4) * 10)

    val users = for (i <- 0 until 3) yield {
      val nm = names(r.nextInt(names.length)) + i.toString
      User(nm, mkLimits())
    }

    implicit class BooleanImp(a:Boolean) {
      def ==>(b:Boolean):Boolean = if (a) b else true
    }

    def sdv(u:User, t:String, d:Day) = s"${u.name}_${t}_${d.day}"

    val dayShiftVars =
      for {
        u <- users; t <- shiftTypes.keys; d <- days
      } yield (Var(sdv(u,t,d), List(0,1)))

    val d1 = for {
      u <- users
      d <- days
      t1 <- shiftTypes.keys
      t2 <- shiftTypes.keys if t1 != t2
    } yield {
      binary[Int]((sdv(u,t1,d), sdv(u,t2,d)), (x,y) => (x == 1) ==> (y == 0))
    }

    // val ass =
    //   for {
    //     d <- days
    //     t <- shiftTypes.keys
    //   } yield {
    //     val vn = s"ass_$d_$t"
    //     val cv = Var(vn, Seq(1))
    //     users.map(u =>
    //       binary[Int](sdv())
    //     )
    //     NAryCon[Int](users.map(sdv(_,t,d)), l => l.forall(_ == 1))
    //   }
    val ass =
      for {
        d <- days
        t <- shiftTypes.keys
        u1 <- users
        u2 <- users if u1 != u2
      } yield {
        binary[Int]((sdv(u1,t,d), sdv(u2,t,d)), (x,y) => (x == 1) || (y == 1))
      }
    // ass.map(println)

    // same shift cannot be taken by two users
    val one_shift =
      for {
        d <- days
        t <- shiftTypes.keys
        u1 <- users
        u2 <- users if u1 != u2
      } yield {
        binary[Int]((sdv(u1,t,d), sdv(u2,t,d)), (x,y) => (x == 1) ==> (y == 0))
      }

    // println(d1)
    val csp = CSP(dayShiftVars.map(x => (x.id, x)).toMap, (d1 ++ ass).toList)
    val Some(sol) = csp.backtrack(inferencer = CSP.MCInference)
    // println(sol)

    sol.assigned.filter(_.value == 1).map(x =>
      x.varID.split("_") match {
        case Array(n,s,d) => (n,s,d)
      }
    ).sortBy(_._3).map({case (n,s,d) => s"$n\t takes the $s shift on day $d."})
     .map(println)
  }

  // def proccessSolution(sol:CompleteAssignment[Int]):List[(String,Int)] = {
  //   val
  // }
}