import Smt

-- === Equality and Uninterpreted Functions ===

-- Basic congruence
theorem z3_euf_cong (f : Int → Int) (x y : Int) (h : x = y) : f x = f y := by
  smt (solver := .z3) [h]

-- Binary function congruence
theorem z3_euf_cong2 (f : Int → Int → Int) (a b c d : Int) (h1 : a = b) (h2 : c = d) :
    f a c = f b d := by
  smt (solver := .z3) [h1, h2]

-- Transitivity through functions
theorem z3_euf_trans (f : Int → Int) (a b c : Int) (h1 : a = b) (h2 : f b = c) :
    f a = c := by
  smt (solver := .z3) [h1, h2]

-- Complex EUF with propositions
theorem z3_euf_complex [Nonempty U] {f : U → U → U} {a b c d : U}
    (h0 : a = b) (h1 : c = d) (h2 : p1 ∧ True) (h3 : (¬ p1) ∨ (p2 ∧ p3))
    (h4 : (¬ p3) ∨ (¬ (f a c = f b d))) : False := by
  smt (solver := .z3) [*]

-- Verify all proofs are sorry-free
#print axioms z3_euf_cong
#print axioms z3_euf_cong2
#print axioms z3_euf_trans
#print axioms z3_euf_complex
