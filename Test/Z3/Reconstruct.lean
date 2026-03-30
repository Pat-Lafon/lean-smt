import Smt

-- === Propositional ===

-- Modus ponens
theorem z3_prop (p q : Prop) (h1 : p) (h2 : p → q) : q := by
  smt (solver := .z3) [h1, h2]

-- Resolution (self-contained, no hints needed)
theorem z3_resolution : ∀ (p q r : Prop), p ∨ q → ¬p ∨ r → q ∨ r := by
  smt (solver := .z3)

-- Disjunctive syllogism
theorem z3_disj_syll : ∀ (p q : Prop), p ∨ q → ¬p → q := by
  smt (solver := .z3)

-- Disjunction elimination with implication
theorem z3_disj (p q r : Prop) (h1 : p ∨ q) (h2 : ¬p) (h3 : q → r) : r := by
  smt (solver := .z3) [h1, h2, h3]

-- === Integer Arithmetic ===

-- Negation
theorem z3_int_neg (x : Int) : - -x = x := by
  smt (solver := .z3)

-- Positive sum
theorem z3_int_arith (x : Int) (h : 0 < x) : 0 < x + x := by
  smt (solver := .z3) [h]

-- Contradictory bounds
theorem z3_lia_false (x y : Int) (h1 : x < y) (h2 : y < x) : False := by
  smt (solver := .z3) [h1, h2]

-- Equality from bounds
theorem z3_lia_eq (x y : Int) (h1 : x < y) (h2 : y < x + 2) : y = x + 1 := by
  smt (solver := .z3) [h1, h2]

-- === EUF (Uninterpreted Functions) ===

-- Congruence
theorem z3_euf_cong (f : Int → Int) (x y : Int) (h : x = y) : f x = f y := by
  smt (solver := .z3) [h]

-- === Nat (embedded to Int) ===

-- Simple nat arithmetic
theorem z3_nat_triv : Nat.zero + Nat.succ Nat.zero = Nat.succ Nat.zero := by
  smt (solver := .z3)

-- Nat congruence
theorem z3_nat_cong (f : Nat → Nat) (x y : Nat) (h : x = y) : f x = f y := by
  smt (solver := .z3) [h]

-- Verify all proofs are sorry-free
#print axioms z3_prop
#print axioms z3_resolution
#print axioms z3_disj_syll
#print axioms z3_disj
#print axioms z3_int_neg
#print axioms z3_int_arith
#print axioms z3_lia_false
#print axioms z3_lia_eq
#print axioms z3_euf_cong
#print axioms z3_nat_triv
#print axioms z3_nat_cong
