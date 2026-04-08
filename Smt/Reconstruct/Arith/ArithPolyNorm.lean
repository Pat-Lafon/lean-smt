/-
Copyright (c) 2021-2024 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Mathlib.Tactic.Ring.RingNF
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic

namespace Smt.Arith

theorem lt_eq_sub_lt_zero [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} : (a < b) = (a - b < 0) := by
  simp only [sub_neg]

theorem le_eq_sub_le_zero [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} : (a ≤ b) = (a - b ≤ 0) := by
  simp only [sub_nonpos]

theorem eq_eq_sub_eq_zero [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} : (a = b) = (a - b = 0) := by
  simp only [sub_eq_zero]

theorem ge_eq_sub_ge_zero [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} : (a ≥ b) = (a - b ≥ 0) := by
  simp only [ge_iff_le, sub_nonneg]

theorem gt_eq_sub_gt_zero [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {a b : α} : (a > b) = (a - b > 0) := by
  simp only [gt_iff_lt, sub_pos]

theorem lt_of_sub_eq [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ < a₂) = (b₁ < b₂) := by
  have aux {c x y : α} (hc : c > 0) : (c * (x - y) < 0) = (x - y < 0) :=
    propext ⟨fun h => by_contra fun hle => by push_neg at hle; exact not_lt.mpr (mul_nonneg (le_of_lt hc) hle) h,
             fun h => mul_neg_of_pos_of_neg hc h⟩
  rw [lt_eq_sub_lt_zero, @lt_eq_sub_lt_zero _ _ _ _ b₁, ← aux hc₁, ← aux hc₂, h]

theorem le_of_sub_eq [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≤ a₂) = (b₁ ≤ b₂) := by
  have aux {c x y : α} (hc : c > 0) : (c * (x - y) ≤ 0) = (x - y ≤ 0) :=
    propext ⟨fun h => by_contra fun hle => by push_neg at hle; exact not_le.mpr (mul_pos hc hle) h,
             fun h => mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) h⟩
  rw [le_eq_sub_le_zero, @le_eq_sub_le_zero _ _ _ _ b₁, ← aux hc₁, ← aux hc₂, h]

theorem eq_of_sub_eq [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ = a₂) = (b₁ = b₂) := by
  have aux {c x y : α} (hc : c > 0) : (c * (x - y) = 0) = (x - y = 0) :=
    propext ⟨fun h => (mul_eq_zero.mp h).resolve_left (ne_of_gt hc),
             fun h => by rw [h, mul_zero]⟩
  rw [@eq_eq_sub_eq_zero _ _ _ _ a₁, @eq_eq_sub_eq_zero _ _ _ _ b₁, ← aux hc₁, ← aux hc₂, h]

theorem ge_of_sub_eq [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ ≥ a₂) = (b₁ ≥ b₂) := by
  have aux {c x y : α} (hc : c > 0) : (c * (x - y) ≥ 0) = (x - y ≥ 0) :=
    propext ⟨fun h => by_contra fun hlt => by push_neg at hlt; exact not_le.mpr (mul_neg_of_pos_of_neg hc hlt) h,
             fun h => mul_nonneg (le_of_lt hc) h⟩
  rw [ge_eq_sub_ge_zero, @ge_eq_sub_ge_zero _ _ _ _ b₁, ← aux hc₁, ← aux hc₂, h]

theorem gt_of_sub_eq [Ring α] [LinearOrder α] [IsStrictOrderedRing α] {c₁ c₂ a₁ a₂ b₁ b₂ : α} (hc₁ : c₁ > 0) (hc₂ : c₂ > 0) (h : c₁ * (a₁ - a₂) = c₂ * (b₁ - b₂)) : (a₁ > a₂) = (b₁ > b₂) := by
  have aux {c x y : α} (hc : c > 0) : (c * (x - y) > 0) = (x - y > 0) :=
    propext ⟨fun h => by_contra fun hle => by push_neg at hle; exact not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (le_of_lt hc) hle) h,
             fun h => mul_pos hc h⟩
  rw [gt_eq_sub_gt_zero, @gt_eq_sub_gt_zero _ _ _ _ b₁, ← aux hc₁, ← aux hc₂, h]

open Lean

open Lean Mathlib.Tactic.RingNF Mathlib.Tactic.AtomM in
/-- Use `arithPolyNormCore` to rewrite the main goal. -/
def arithPolyNormCore (mv : MVarId) : MetaM (Option MVarId) := mv.withContext do
  let tgt ← instantiateMVars (← mv.getType)
  let s ← IO.mkRef {}
  let cfg : Config := {}
  let m := recurse s cfg.toConfig (wellBehavedDischarge := true) evalExpr (cleanup cfg)
  let r ← m tgt
  if r.expr.consumeMData.isConstOf ``True then
    mv.assign (← Meta.mkOfEqTrue (← r.getProof))
    return none
  else
    Meta.applySimpResultToTarget mv tgt r

def traceArithPolyNorm (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

/-- Use `arithPolyNorm` to rewrite the main goal. -/
def arithPolyNorm (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.arithPolyNorm traceArithPolyNorm do
  mv.withContext do
  if let .some mv ← arithPolyNormCore mv then
    throwError "[arithPolyNorm]: could not prove {← mv.getType}"

def traceArithNormNum (r : Except Exception Unit) : MetaM MessageData :=
  return match r with
  | .ok _ => m!"{checkEmoji}"
  | _     => m!"{bombEmoji}"

open Mathlib.Meta.NormNum in
def normNum (mv : MVarId) : MetaM Unit := withTraceNode `smt.reconstruct.normNum traceArithNormNum do
  mv.withContext do
  let tgt ← instantiateMVars (← mv.getType)
  let ctx ← Lean.Meta.Simp.mkContext {}
  let r ← deriveSimp ctx true tgt
  if r.expr.consumeMData.isConstOf ``True then
    mv.assign (← Meta.mkOfEqTrue (← r.getProof))
  else
    let mv' ← Meta.applySimpResultToTarget mv tgt r
    throwError "[norm_num]: could not prove {← mv'.getType}"

open Qq in
partial def findConst (α : Q(Type)) (hα : Q(Ring $α)) (hOrd : Q(LinearOrder $α)) (e : Q($α)) : MetaM Expr := do
  match e with
  | ~q($a * $b) => findConst α hα hOrd b
  | ~q($a + $b) => findConst α hα hOrd b
  | ~q($a - $b) => findConst α hα hOrd b
  | ~q(-$a)     => findConst α hα hOrd a
  | _           =>
    if e.hasFVar || e.hasLooseBVars then
      return q(1 : $α)
    else if e.getUsedConstants.contains ``Neg.neg then
      let e : Q(Real) := e
      match e with
      | ~q((-$a) / $b) => return q($a / $b)
      | _              => return e
    else
      return e

end Smt.Arith
