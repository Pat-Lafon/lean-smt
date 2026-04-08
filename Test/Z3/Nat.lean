import Smt

-- === Natural Number Arithmetic (embedded to Int) ===

theorem z3_nat_triv : Nat.zero + Nat.succ Nat.zero = Nat.succ Nat.zero := by
  smt (solver := .z3)

theorem z3_nat_triv' : (0 : Nat) + 1 = 1 := by
  smt (solver := .z3)

theorem z3_nat_cong (f : Nat → Nat) (x y : Nat) (h : x = y) : f x = f y := by
  smt (solver := .z3) [h]

theorem z3_nat_forall : ∀ x : Nat, x ≥ 0 := by
  smt (solver := .z3)

theorem z3_nat_neq_zero (x : Nat) : x + 1 ≠ 0 := by
  smt (solver := .z3)

theorem z3_nat_zero_sub (x : Nat) : 0 - x = 0 := by
  smt (solver := .z3)

theorem z3_nat_exists : ∃ x : Nat, x = 1 := by
  smt (solver := .z3)

theorem z3_nat_exists' : ∃ x : Nat, x ≥ 0 := by
  smt (solver := .z3)

-- Verify all proofs are sorry-free
#print axioms z3_nat_triv
#print axioms z3_nat_triv'
#print axioms z3_nat_cong
#print axioms z3_nat_forall
#print axioms z3_nat_neq_zero
#print axioms z3_nat_zero_sub
#print axioms z3_nat_exists
#print axioms z3_nat_exists'
