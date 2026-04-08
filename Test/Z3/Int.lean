import Smt

-- === Integer Arithmetic ===

theorem z3_int_neg (x : Int) : - -x = x := by
  smt (solver := .z3)

theorem z3_int_add_comm (x y : Int) : x + y = y + x := by
  smt (solver := .z3)

theorem z3_int_sub (n m k l : Int) : (n - m) * k + l = n*k - m*k + l := by
  smt (solver := .z3)

theorem z3_int_sum_le (n m k l : Int) (hN : n ≤ m) (hK : k ≤ l) : n + k ≤ m + l := by
  smt (solver := .z3) [hN, hK]

theorem z3_int_pos_sum (x : Int) (h : 0 < x) : 0 < x + x := by
  smt (solver := .z3) [h]

theorem z3_int_contra_bounds (x y : Int) (h1 : x < y) (h2 : y < x) : False := by
  smt (solver := .z3) [h1, h2]

theorem z3_int_eq_from_bounds (x y : Int) (h1 : x < y) (h2 : y < x + 2) : y = x + 1 := by
  smt (solver := .z3) [h1, h2]

-- Linear arithmetic with multiple variables
theorem z3_linarith1 (x y z : Int) (h1 : 2*x < 3*y) (h2 : -4*x + 2*z < 0) (h3 : 12*y - 4*z < 0) : False := by
  smt (solver := .z3) [h1, h2, h3]

theorem z3_linarith2 (c v0 v1 : Int)
    (h3 : v0 + v1 + c = 10) : v0 + 5 + (v1 - 3) + (c - 2) = 10 := by
  smt (solver := .z3) [h3]

-- Equality + function congruence
theorem z3_int_eq_fun {x y : Int} {f : Int → Int} : ¬(x ≤ y ∧ y ≤ x ∧ ¬f x = f y) := by
  smt (solver := .z3)

-- Mixed prop + int
theorem z3_int_mixed {p q r : Prop} (hp : ¬p) (hq : ¬q) (hr : r) : ¬(p ∨ q ∨ ¬r) := by
  smt (solver := .z3) [hp, hq, hr]

-- Modular arithmetic
theorem z3_int_mod (a : Int) : a % 2 = 0 ∨ a % 2 = 1 := by
  smt (solver := .z3)

-- Division/modulo properties (requires omega with div/mod lemmas)
theorem z3_int_div_mod (a b : Int) (h : b ≠ 0) : a = b * (a / b) + a % b := by
  smt (solver := .z3) [h]

theorem z3_int_mod_nonneg (a b : Int) (h : b ≠ 0) : a % b ≥ 0 := by
  smt (solver := .z3) [h]

theorem z3_int_mod_bound (a b : Int) (h : b > 0) : a % b < b := by
  smt (solver := .z3) [h]

-- Verify all proofs are sorry-free
#print axioms z3_int_neg
#print axioms z3_int_add_comm
#print axioms z3_int_sub
#print axioms z3_int_sum_le
#print axioms z3_int_pos_sum
#print axioms z3_int_contra_bounds
#print axioms z3_int_eq_from_bounds
#print axioms z3_linarith1
#print axioms z3_linarith2
#print axioms z3_int_eq_fun
#print axioms z3_int_mixed
#print axioms z3_int_mod
#print axioms z3_int_div_mod
#print axioms z3_int_mod_nonneg
#print axioms z3_int_mod_bound
