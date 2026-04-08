import Smt

-- Trust mode: Z3 solves, proof admitted
example (p q : Prop) (h1 : p) (h2 : p → q) : q := by
  smt (solver := .z3) +trust [h1, h2]

example (x y : Int) (h1 : x < y) (h2 : y < x + 1) : x + 1 = y := by
  smt (solver := .z3) +trust [h1, h2]
