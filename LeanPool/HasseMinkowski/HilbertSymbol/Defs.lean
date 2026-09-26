/-
Copyright (c) 2026 jayyswan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: jayyswan
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Int.Basic
public import Mathlib.Tactic

/-!
# The Hilbert symbol

Defines the Hilbert symbol `(a,b)_k`, valued in `{0, ±1}`, for a field `k`, together with its
basic vanishing, symmetry and value-set properties, and the class `HasBilinHilbertSym`
recording multiplicativity in the first argument.
-/

public section

namespace HasseMinkowski

attribute [local instance] Classical.propDecidable

/-- The Hilbert symbol `(a,b)_k`, valued in `{0, ±1}`. -/
noncomputable def hilbertSym {k : Type*} [Field k] (a b : k) : ℤ :=
  if a = 0 ∨ b = 0 then 0
  else if ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    then 1 else -1

-- Theorem: the Hilbert symbol vanishes if either argument is zero.
theorem hilbertSym_zero_left {k : Type*} [Field k] (a : k) : hilbertSym 0 a = 0 := by
  simp [hilbertSym]

-- Theorem: the Hilbert symbol vanishes if either argument is zero.
theorem hilbertSym_zero_right {k : Type*} [Field k] (a : k) : hilbertSym a 0 = 0 := by
  simp [hilbertSym]

-- Theorem: `hilbertSym a b = 0` exactly when one of the arguments is zero.
theorem hilbertSym_eq_zero_iff {k : Type*} [Field k] (a b : k) :
    hilbertSym a b = 0 ↔ a = 0 ∨ b = 0 := by
  by_cases h : a = 0 ∨ b = 0
  · unfold hilbertSym
    rw [ite_eq_left h]
    exact ⟨fun _ => h, fun _ => rfl⟩
  · unfold hilbertSym
    rw [ite_eq_right h]
    refine ⟨fun hz => ?_, fun hz => absurd hz h⟩
    by_cases hs : ∃ z x y : k,
        (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    · rw [ite_eq_left hs] at hz
      norm_num at hz
    · rw [ite_eq_right hs] at hz
      norm_num at hz

-- Theorem: the Hilbert symbol only takes values among `1`, `0`, `-1`.
theorem hilbertSym_eq_one_or {k : Type*} [Field k] (a b : k) :
    hilbertSym a b = 1 ∨ hilbertSym a b = 0 ∨ hilbertSym a b = -1 := by
  by_cases h : a = 0 ∨ b = 0
  · right; left
    unfold hilbertSym
    rw [ite_eq_left h]
  · by_cases hs : ∃ z x y : k,
        (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    · left
      unfold hilbertSym
      rw [ite_eq_right h, ite_eq_left hs]
    · right; right
      unfold hilbertSym
      rw [ite_eq_right h, ite_eq_right hs]

-- Theorem: the Hilbert symbol only takes values among `-1`, `0`, `1`.
theorem hilbertSym_eq_neg_one_or {k : Type*} [Field k] (a b : k) :
    hilbertSym a b = -1 ∨ hilbertSym a b = 0 ∨ hilbertSym a b = 1 := by
  rcases hilbertSym_eq_one_or a b with h1 | h0 | hm1
  · exact Or.inr (Or.inr h1)
  · exact Or.inr (Or.inl h0)
  · exact Or.inl hm1

-- Theorem: the Hilbert symbol is symmetric in its two arguments.
theorem hilbertSym_comm {k : Type*} [Field k] (a b : k) :
    hilbertSym a b = hilbertSym b a := by
  by_cases h : a = 0 ∨ b = 0
  · rcases h with ha | hb
    · rw [ha, hilbertSym_zero_left, hilbertSym_zero_right]
    · rw [hb, hilbertSym_zero_right, hilbertSym_zero_left]
  · have h' : ¬ (b = 0 ∨ a = 0) := by tauto
    unfold hilbertSym
    rw [ite_eq_right h, ite_eq_right h']
    by_cases hs : ∃ z x y : k,
        (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0
    · have hs' : ∃ z x y : k,
          (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - b * x ^ 2 - a * y ^ 2 = 0 := by
        obtain ⟨z, x, y, hne, heq⟩ := hs
        refine ⟨z, y, x, ?_, ?_⟩
        · intro hc; exact hne (by simp_all)
        · rw [← heq]; ring
      rw [ite_eq_left hs, ite_eq_left hs']
    · have hs' : ¬ ∃ z x y : k,
          (z, x, y) ≠ (0, 0, 0) ∧ z ^ 2 - b * x ^ 2 - a * y ^ 2 = 0 := by
        rintro ⟨z, x, y, hne, heq⟩
        exact hs ⟨z, y, x, by intro hc; exact hne (by simp_all), by rw [← heq]; ring⟩
      rw [ite_eq_right hs, ite_eq_right hs']

/-- A field carries a bilinear Hilbert symbol if the symbol is multiplicative in its first
argument. -/
class HasBilinHilbertSym (k : Type*) [Field k] : Prop where
  mul_left_eq {a a' b : k} : hilbertSym (a * a') b = hilbertSym a b * hilbertSym a' b

namespace HasBilinHilbertSym

variable {k : Type*} [Field k] [HasBilinHilbertSym k]

-- Theorem: bilinearity in the second argument, derived from `mul_left_eq` and symmetry.
theorem mul_right_eq {a b b' : k} :
    hilbertSym a (b * b') = hilbertSym a b * hilbertSym a b' := by
  rw [hilbertSym_comm a (b * b'), mul_left_eq, hilbertSym_comm b a, hilbertSym_comm b' a]

end HasBilinHilbertSym

end HasseMinkowski
