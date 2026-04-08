/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomaz Gomes Mascarenhas
-/

import Mathlib.Algebra.Order.Ring.Defs

namespace Smt.Reconstruct.Arith

open Function

variable {α : Type} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]

variable {a b c d : α}

theorem sumBounds₁ : a < b → c < d → a + c < b + d := add_lt_add
theorem sumBounds₂ : a < b → c ≤ d → a + c < b + d := add_lt_add_of_lt_of_le
theorem sumBounds₃ (h₁ : a < b) (h₂ : c = d) : a + c < b + d := by subst h₂; exact add_lt_add_of_lt_of_le h₁ le_rfl
theorem sumBounds₄ : a ≤ b → c < d → a + c < b + d := add_lt_add_of_le_of_lt
theorem sumBounds₅ : a ≤ b → c ≤ d → a + c ≤ b + d := add_le_add
theorem sumBounds₆ (h₁ : a ≤ b) (h₂ : c = d) : a + c ≤ b + d := by subst h₂; exact add_le_add h₁ le_rfl
theorem sumBounds₇ (h₁ : a = b) (h₂ : c < d) : a + c < b + d := by subst h₁; exact add_lt_add_of_le_of_lt le_rfl h₂
theorem sumBounds₈ (h₁ : a = b) (h₂ : c ≤ d) : a + c ≤ b + d := by subst h₁; exact add_le_add le_rfl h₂
theorem sumBounds₉ (h₁ : a = b) (h₂ : c = d) : a + c ≤ b + d := by subst h₁; subst h₂; exact le_rfl

end Smt.Reconstruct.Arith
