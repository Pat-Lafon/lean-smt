import Smt

-- === Quantifier tests ===

-- Simple universal (already closed by smt preprocessing)
theorem z3_forall_trivial : ∀ (x : Int), x = x := by
  smt (solver := .z3)

-- Universal with hypothesis
theorem z3_forall_hyp (f : Int → Int) (h : ∀ x, f x = x) : f 0 = 0 := by
  smt (solver := .z3) [h]

-- Universal with two variables
theorem z3_forall_two (f : Int → Int → Int) (h : ∀ x y, f x y = f y x) :
    f 1 2 = f 2 1 := by
  smt (solver := .z3) [h]

-- Verify all proofs are sorry-free
#print axioms z3_forall_trivial
#print axioms z3_forall_hyp
#print axioms z3_forall_two
