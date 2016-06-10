# Constraint Satisfaction Programming
This is a small library and example implementation of a CSP solver in Scala.
I wrote this in order to understand CSP for my Intelligent Systems Programming
class at ITU in Copenhagen.

## Features
- Node Consistency
- Arc Consistency
- Backtracking with inferences
    - Forward Checking
    - MAC (Maintain Arc Consistency)
    - Write your own!
    - Write your own variable selection and domain ordering heuristics!
- Methods to convert Sudoku problems to CSV

## Example
This example performs Arc Consistency on two variables with domains from 0 to 9
and constraints (y == x^2)
```scala
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
```

## Example
The following example solves the following simple CSP problem.


    ||===========||
    || a |   | b || 5
    ||   | c | d || 5
    || e | f |   || 5
    ||===========||
       5   4   6    

In the grade school puzzle above, the students must assign values to the variables
a,b,...,f such that the row and column sums are correct (i.e., a+b = 5, b+d = 6
etc.). The domain of each variable is {1,2,3,4}

```scala
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
```

This example uses MacInference, but Forward Checking could also be used