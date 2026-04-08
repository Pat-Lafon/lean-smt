import Smt

inductive Color where | red | green | blue
deriving DecidableEq

inductive Tree where
  | leaf : Tree
  | node : Tree → Nat → Tree → Tree

structure Point where
  x : Int
  y : Int

-- ============================================================
-- Pure datatype reasoning (grind could handle alone with cases,
-- but Z3 hints provide the proof certificates)
-- ============================================================

theorem color_exhaust (c : Color) : c = .red ∨ c = .green ∨ c = .blue := by
  smt (solver := .z3)

theorem color_red_ne_green : Color.red ≠ Color.green := by
  smt (solver := .z3)

theorem tree_leaf_ne_node (l r : Tree) (n : Nat) : Tree.leaf ≠ Tree.node l n r := by
  smt (solver := .z3)

theorem point_mk_eq (a b c d : Int) (h1 : a = c) (h2 : b = d) :
    Point.mk a b = Point.mk c d := by
  smt (solver := .z3) [h1, h2]

theorem color_not_red_or (c : Color) : c ≠ .red → c = .green ∨ c = .blue := by
  smt (solver := .z3)

theorem two_color_pigeonhole (c1 c2 : Color)
    (h1 : c1 ≠ .red) (h2 : c1 ≠ .green) (h3 : c2 ≠ .red) (h4 : c2 ≠ .green) :
    c1 = c2 := by
  smt (solver := .z3) [h1, h2, h3, h4]

theorem color_eq_or_ne (c1 c2 : Color) : c1 = c2 ∨ c1 ≠ c2 := by
  smt (solver := .z3)

-- ============================================================
-- Datatype + arithmetic: Z3's theory lemmas do real work here
-- combining EUF congruence with linear arithmetic
-- ============================================================

-- Per-constructor function bounds → universal bound
-- Z3 contributes: congruence (c = .red → f c = f .red), arithmetic bounds
theorem color_function (f : Color → Int) (c : Color)
    (hr : f .red > 0) (hg : f .green > 0) (hb : f .blue > 0) :
    f c > 0 := by
  smt (solver := .z3) [hr, hg, hb]

-- Pointwise function equality via exhaustion
theorem color_func_eq (f g : Color → Int)
    (hr : f .red = g .red) (hg : f .green = g .green) (hb : f .blue = g .blue)
    (c : Color) : f c = g c := by
  smt (solver := .z3) [hr, hg, hb]

-- Datatype case split + linear arithmetic
-- Z3 provides both the case analysis AND the arithmetic reasoning
theorem color_arith (f : Color → Int) (c : Color)
    (hr : f .red = 3) (hg : f .green = 7) (hb : f .blue = 11) :
    f c * 2 > 5 := by
  smt (solver := .z3) [hr, hg, hb]

-- Multi-variable datatype + arithmetic interaction
theorem color_two_func (f g : Color → Int) (c : Color)
    (hfr : f .red ≥ 10) (hfg : f .green ≥ 10) (hfb : f .blue ≥ 10)
    (hgr : g .red ≤ 5)  (hgg : g .green ≤ 5)  (hgb : g .blue ≤ 5) :
    f c > g c := by
  smt (solver := .z3) [hfr, hfg, hfb, hgr, hgg, hgb]

-- ============================================================
-- Structure field accessors: Z3 uses selectors from
-- declare-datatypes, mapped back to Lean projections
-- ============================================================

theorem point_compare (p q : Point)
    (h1 : p.x < q.x) : p ≠ q := by
  smt (solver := .z3) [h1]

theorem point_eq_ext (p q : Point) (hx : p.x = q.x) (hy : p.y = q.y) : p = q := by
  smt (solver := .z3) [hx, hy]

theorem point_field_sum (p : Point) (h1 : p.x > 0) (h2 : p.y > 0) : p.x + p.y > 0 := by
  smt (solver := .z3) [h1, h2]

-- Constructor/accessor round-trip (eta)
theorem point_eta (p : Point) : Point.mk p.x p.y = p := by
  smt (solver := .z3)

-- Constructor then project
theorem point_mk_proj (a b : Int) : (Point.mk a b).x = a := by
  smt (solver := .z3)

-- Extensionality with arithmetic in hypotheses
theorem point_ext_arith (p q : Point)
    (hx : p.x + 1 = q.x + 1) (hy : 2 * p.y = 2 * q.y) : p = q := by
  smt (solver := .z3) [hx, hy]

-- Two structs, field arithmetic across both
theorem point_two_struct (p q : Point)
    (h1 : p.x = q.x + 1) (h2 : p.y = q.y - 1) :
    p.x + p.y = q.x + q.y := by
  smt (solver := .z3) [h1, h2]

-- Disjointness from field inequality
theorem point_ne_from_field (p q : Point) (h : p.x ≠ q.x) : p ≠ q := by
  smt (solver := .z3) [h]

-- Enum + struct combination: case split on enum, each case gives struct info
theorem color_point (c : Color) (p : Point)
    (hr : c = .red → p.x > 0) (hg : c = .green → p.x > 0) (hb : c = .blue → p.x > 0) :
    p.x > 0 := by
  smt (solver := .z3) [hr, hg, hb]

-- ============================================================
-- Cross-datatype: struct with enum fields
-- ============================================================

structure Pair where
  fst : Color
  snd : Color

-- Both fields match → pairs equal (requires transitive datatype discovery)
theorem pair_ext (p q : Pair) (h1 : p.fst = q.fst) (h2 : p.snd = q.snd) : p = q := by
  smt (solver := .z3) [h1, h2]

-- ============================================================
-- Relational constraints across two structs
-- ============================================================

structure Interval where
  lo : Int
  hi : Int

theorem interval_overlap_symm (a b : Interval)
    (h1 : a.lo ≤ b.hi) (h2 : b.lo ≤ a.hi) :
    b.lo ≤ a.hi ∧ a.lo ≤ b.hi := by
  smt (solver := .z3) [h1, h2]

theorem interval_disjoint (a b : Interval)
    (h1 : a.lo ≤ a.hi) (h2 : b.lo ≤ b.hi)
    (h3 : a.hi < b.lo) :
    a.lo < b.hi := by
  smt (solver := .z3) [h1, h2, h3]

-- Verify key proofs are sorry-free
#print axioms color_exhaust
#print axioms color_function
#print axioms color_arith
#print axioms color_two_func
#print axioms point_compare
#print axioms point_eq_ext
#print axioms point_field_sum
#print axioms point_eta
#print axioms point_mk_proj
#print axioms point_ext_arith
#print axioms point_two_struct
#print axioms point_ne_from_field
#print axioms color_point
#print axioms pair_ext
#print axioms interval_overlap_symm
#print axioms interval_disjoint
