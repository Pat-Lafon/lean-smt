import Smt

-- Test: sat result (goal is false) — should show solver name and "sat"
theorem z3_sat_error (x : Int) : x > 0 := by
  smt (solver := .z3)

-- Test: cvc5 sat for comparison
theorem cvc5_sat_error (x : Int) : x > 0 := by
  smt
