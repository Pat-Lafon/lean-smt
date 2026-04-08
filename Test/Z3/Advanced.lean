import Smt

-- ============================================================
-- 1. Multi-hypothesis EUF chains (inspired by the tree axioms)
-- ============================================================

-- Chain of function equalities requiring transitive EUF reasoning
theorem euf_chain (U : Type) [Nonempty U] (f g h : U → U) (a b c d : U)
    (h1 : f a = g b) (h2 : g b = h c) (h3 : h c = d) :
    f a = d := by
  smt (solver := .z3) [h1, h2, h3]

-- EUF with arithmetic predicates (like depth/value functions on trees)
theorem euf_arith_mix (f g : Int → Int) (a b : Int)
    (h3 : f a = g b) (h4 : g b > 5) :
    f a > 5 := by
  smt (solver := .z3) [h3, h4]

-- Multiple uninterpreted functions with inequality chains
theorem euf_inequality_chain (f g h : Int → Int) (x : Int)
    (h1 : f x ≥ 0) (h2 : g (f x) ≥ f x + 1)
    (h3 : h (g (f x)) ≥ g (f x) + 1) :
    h (g (f x)) ≥ 2 := by
  smt (solver := .z3) [h1, h2, h3]

-- ============================================================
-- 2. Quantifier-heavy reasoning (inspired by ∀∀∀ axiom patterns)
-- ============================================================

-- Quantified hypothesis with multiple instantiations needed
theorem quant_multi_inst (P : Int → Prop) (a b : Int)
    (h : ∀ x : Int, P x → x ≥ 0)
    (ha : P a) (hb : P b) :
    a + b ≥ 0 := by
  smt (solver := .z3) [h, ha, hb]

-- Nested quantifiers with function application
theorem quant_func (f : Int → Int) (a : Int)
    (h1 : ∀ x : Int, f x ≥ x)
    (h2 : a ≥ 5) :
    f a ≥ 5 := by
  smt (solver := .z3) [h1, h2]

-- Quantified with two variables (like the tree axiom patterns)
theorem quant_two_var (R : Int → Int → Prop) (a b : Int)
    (h1 : ∀ x y : Int, R x y → x ≤ y)
    (h2 : R a b) :
    a ≤ b := by
  smt (solver := .z3) [h1, h2]

-- ============================================================
-- 3. Complex formula structure (like the subtyping queries)
-- ============================================================

-- Conjunction of many conditions (like is_node ∧ value = v ∧ left = l ∧ right = r)
theorem many_conjuncts (a b c d e : Int)
    (h : a > 0 ∧ b > 0 ∧ c > 0 ∧ d > 0 ∧ e > 0) :
    a + b + c + d + e > 0 := by
  smt (solver := .z3) [h]

-- Disjunction with arithmetic (like the case splits in tree proofs)
theorem disj_arith (x y : Int) (h : x > 10 ∨ y > 10) (h2 : x ≤ 5) : y > 10 := by
  smt (solver := .z3) [h, h2]

-- Implication chain (like hypothesis → conclusion patterns in axioms)
theorem impl_chain (P Q R : Prop) (a : Int)
    (h1 : P → a > 0) (h2 : a > 0 → Q) (h3 : Q → R) (hp : P) :
    R := by
  smt (solver := .z3) [h1, h2, h3, hp]

-- ============================================================
-- 4. Uninterpreted predicates combined with datatypes
-- ============================================================

inductive Color where | red | green | blue
deriving DecidableEq

structure Point where
  x : Int
  y : Int

-- Predicate on struct (like is_leaf/is_node on tree)
theorem pred_on_struct (valid : Point → Prop) (p : Point)
    (h1 : valid p → p.x ≥ 0) (h2 : valid p → p.y ≥ 0)
    (hv : valid p) :
    p.x + p.y ≥ 0 := by
  smt (solver := .z3) [h1, h2, hv]

-- Function results depend on enum (like depth depends on leaf/node)
theorem enum_func_cases (f : Color → Int → Int) (c : Color) (x : Int)
    (hr : c = .red → f c x > x)
    (hg : c = .green → f c x > x)
    (hb : c = .blue → f c x > x) :
    f c x > x := by
  smt (solver := .z3) [hr, hg, hb]

-- ============================================================
-- 5. Multi-step reasoning (inspired by failed_subtyping proof chains)
-- ============================================================

-- Requires combining 5+ hypotheses
theorem multi_step (a b c d : Int)
    (h1 : a ≤ b) (h2 : b ≤ c) (h3 : c ≤ d)
    (h4 : d ≤ a + 10) (h5 : a ≥ 0) :
    d - a ≤ 10 ∧ d ≥ 0 := by
  smt (solver := .z3) [h1, h2, h3, h4, h5]

-- Combining function monotonicity with arithmetic bounds
theorem mono_chain (f : Int → Int) (a b : Int)
    (hmono : ∀ x y : Int, x ≤ y → f x ≤ f y)
    (hab : a ≤ b) (hfa : f a ≥ 0) :
    f b ≥ 0 := by
  smt (solver := .z3) [hmono, hab, hfa]

-- ============================================================
-- 6. Struct + quantifier + arithmetic (approaching tree-depth style)
-- ============================================================

-- A "measure" function on points (like depth on trees)
theorem measure_bounds (measure : Point → Int) (p q : Point)
    (h_nonneg : ∀ pt : Point, measure pt ≥ 0)
    (h_bound : measure p ≤ 5) :
    measure q ≥ 0 ∧ measure p ≤ 5 := by
  smt (solver := .z3) [h_nonneg, h_bound]

-- Functional determinism (like ax_11: depth t res → depth t res2 → res2 = res)
theorem func_deterministic (f : Point → Int) (p : Point) (r1 r2 : Int)
    (h1 : f p = r1) (h2 : f p = r2) :
    r1 = r2 := by
  smt (solver := .z3) [h1, h2]

-- ============================================================
-- 7. Boolean-valued functions (like the x_0 : Bool patterns)
-- ============================================================

theorem bool_iff_arith (b : Bool) (s : Int)
    (h2 : b = false ↔ s > 0)
    (h3 : s > 0) :
    b = false := by
  smt (solver := .z3) [h2, h3]

-- Multiple boolean guards (like the nested x_0, x_1 patterns)
theorem multi_bool_guard (b1 b2 : Bool) (x : Int)
    (h1 : b1 = true → x ≥ 0)
    (h2 : b1 = false → b2 = true → x ≥ 0)
    (h3 : b1 = false → b2 = false → x ≥ 0) :
    x ≥ 0 := by
  smt (solver := .z3) [h1, h2, h3]

-- ============================================================
-- 8. Axiom-heavy reasoning (inspired by tree subtyping proofs)
--    Simulating a "measure" system with multiple axioms
-- ============================================================

-- Axiom system for a "size" measure (analogous to depth axioms on trees)
-- Uses concrete Int domain to avoid abstract type reconstruction issues
theorem axiom_system
    (size : Int → Int) (combine : Int → Int → Int)
    (compound : Int → Prop)
    -- Axiom: size is non-negative
    (ax_nonneg : ∀ u : Int, size u ≥ 0)
    -- Axiom: compound elements have positive size
    (ax_compound : ∀ u : Int, compound u → size u > 0)
    -- Axiom: combine increases size
    (ax_combine : ∀ u v : Int, size (combine u v) ≥ size u + size v)
    -- Given: specific elements
    (a b : Int) (ha : compound a) (hb : compound b) :
    size (combine a b) ≥ 2 := by
  smt (solver := .z3) [ax_nonneg, ax_compound, ax_combine, ha, hb]

-- Reasoning with many hypotheses about the same function
-- (like ax_0 through ax_14 all about depth)
theorem multi_axiom_func (f : Int → Int → Int) (a b c : Int)
    (h3 : f a b + f b c ≤ 10)
    (h4 : ∀ x y : Int, f x y = f y x)
    (h5 : f a c ≤ f a b + f b c) :
    f a c ≤ 10 ∧ f c a ≤ 10 := by
  smt (solver := .z3) [h3, h4, h5]

-- ============================================================
-- 9. Nested implications and conjunctions
--    (like the (is_node t) ∧ (value t = v) ∧ (left t = l) ∧ (right t = r) → ... patterns)
-- ============================================================

-- Deep implication nesting
theorem deep_impl (P Q R S T : Prop) (x : Int)
    (h1 : P → Q) (h2 : Q → R) (h3 : R → S)
    (h4 : S → x > 0) (h5 : x > 0 → T) (hp : P) :
    T ∧ x > 0 := by
  smt (solver := .z3) [h1, h2, h3, h4, h5, hp]

-- Conjunction unpacking with function application
theorem conj_unpack (f g : Int → Int) (a b : Int)
    (h : f a = 3 ∧ g b = 7 ∧ a > 0 ∧ b > 0 ∧ f a + g b = 10) :
    f a + g b = 10 ∧ f a > 0 := by
  smt (solver := .z3) [h]

-- ============================================================
-- 10. Quantifier + datatype + arithmetic (most complex)
-- ============================================================

-- Color-indexed bounds with quantified property
theorem color_quant_bounds (f : Color → Int → Int) (c : Color) (x : Int)
    (h_bound : ∀ col : Color, ∀ y : Int, y ≥ 0 → f col y ≥ y)
    (hx : x ≥ 5) :
    f c x ≥ 5 := by
  smt (solver := .z3) [h_bound, hx]

-- Multiple struct values with quantified monotonicity
theorem struct_quant_mono (f : Point → Int) (p q : Point)
    (h_mono_x : ∀ a b : Point, a.x ≤ b.x → a.y = b.y → f a ≤ f b)
    (hx : p.x ≤ q.x) (hy : p.y = q.y)
    (hfp : f p ≥ 10) :
    f q ≥ 10 := by
  smt (solver := .z3) [h_mono_x, hx, hy, hfp]

-- Combining enum exhaustion + quantified property + arithmetic
theorem combined_theories (f g : Color → Int) (c : Color)
    (h1 : ∀ col : Color, f col + g col = 100)
    (h2 : f .red = 30) (h3 : f .green = 50) (h4 : f .blue = 70)
    (h5 : c = .red ∨ c = .green ∨ c = .blue) :
    g c ≥ 30 := by
  smt (solver := .z3) [h1, h2, h3, h4, h5]

#print axioms euf_chain
#print axioms euf_arith_mix
#print axioms euf_inequality_chain
#print axioms quant_multi_inst
#print axioms quant_func
#print axioms quant_two_var
#print axioms many_conjuncts
#print axioms disj_arith
#print axioms impl_chain
#print axioms pred_on_struct
#print axioms enum_func_cases
#print axioms multi_step
#print axioms mono_chain
#print axioms measure_bounds
#print axioms func_deterministic
#print axioms bool_iff_arith
#print axioms multi_bool_guard
#print axioms axiom_system
#print axioms multi_axiom_func
#print axioms deep_impl
#print axioms conj_unpack
#print axioms color_quant_bounds
#print axioms struct_quant_mono
#print axioms combined_theories
