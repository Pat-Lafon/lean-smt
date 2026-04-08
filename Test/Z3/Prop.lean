import Smt

-- === Propositional Logic ===

theorem z3_verum : True := by
  smt (solver := .z3)

theorem z3_triv (p : Prop) : p → p := by
  smt (solver := .z3)

theorem z3_addition (p q : Prop) : p → p ∨ q := by
  smt (solver := .z3)

theorem z3_conjunction (p q : Prop) : p → q → p ∧ q := by
  smt (solver := .z3)

theorem z3_simplification (p q : Prop) : p ∧ q → p := by
  smt (solver := .z3)

theorem z3_modus_ponens (p q : Prop) (h1 : p) (h2 : p → q) : q := by
  smt (solver := .z3) [h1, h2]

theorem z3_modus_tollens (p q : Prop) (h1 : p → q) (h2 : ¬q) : ¬p := by
  smt (solver := .z3) [h1, h2]

theorem z3_hypothetical_syllogism (p q r : Prop) : (p → q) → (q → r) → p → r := by
  smt (solver := .z3)

theorem z3_disjunctive_syllogism (p q : Prop) : p ∨ q → ¬p → q := by
  smt (solver := .z3)

theorem z3_resolution (p q r : Prop) : p ∨ q → ¬p ∨ r → q ∨ r := by
  smt (solver := .z3)

theorem z3_falsum (p : Prop) : p → ¬p → False := by
  smt (solver := .z3)

theorem z3_prop_ext (p q : Prop) : p = q → (p ↔ q) := by
  smt (solver := .z3)

theorem z3_and_assoc (p q r : Prop) : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  smt (solver := .z3)

theorem z3_or_comm (p q : Prop) : p ∨ q ↔ q ∨ p := by
  smt (solver := .z3)

theorem z3_iff (p q : Prop) : (p → q) → (q → p) → (p ↔ q) := by
  smt (solver := .z3)

theorem z3_cong (p q : Prop) (f : Prop → Prop) (h : p = q) : f p = f q := by
  smt (solver := .z3) [h]

-- Verify all proofs are sorry-free
#print axioms z3_verum
#print axioms z3_triv
#print axioms z3_addition
#print axioms z3_conjunction
#print axioms z3_simplification
#print axioms z3_modus_ponens
#print axioms z3_modus_tollens
#print axioms z3_hypothetical_syllogism
#print axioms z3_disjunctive_syllogism
#print axioms z3_resolution
#print axioms z3_falsum
#print axioms z3_prop_ext
#print axioms z3_and_assoc
#print axioms z3_or_comm
#print axioms z3_iff
#print axioms z3_cong
