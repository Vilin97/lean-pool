/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import Mathlib.Algebra.GroupWithZero.Action.Units
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Module.NatInt
public import Mathlib.Data.Real.Basic

/-! # Finite Average -/

@[expose] public section

namespace Homogenization

open scoped BigOperators

/-!
# Nonempty finite averages

This module provides the source-facing average of a function over a nonempty
finite set.  Unlike legacy totalized averages, the definition has no value on
the empty set.
-/

/-- The average of `F` over a nonempty finite set. -/
noncomputable def finiteAverage {α E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Finset α) (_hs : s.Nonempty) (F : α → E) : E :=
  (s.card : ℝ)⁻¹ • ∑ a ∈ s, F a

/-- The defining formula for `finiteAverage`. -/
theorem finiteAverage_def {α E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Finset α) (hs : s.Nonempty) (F : α → E) :
    finiteAverage s hs F = (s.card : ℝ)⁻¹ • ∑ a ∈ s, F a :=
  rfl

@[simp]
theorem finiteAverage_singleton {α E : Type*} [AddCommMonoid E] [Module ℝ E]
    (a : α) (F : α → E) :
    finiteAverage ({a} : Finset α) (by simp) F = F a := by
  classical
  simp [finiteAverage]

@[simp]
theorem finiteAverage_const {α E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Finset α) (hs : s.Nonempty) (x : E) :
    finiteAverage s hs (fun _ => x) = x := by
  rw [finiteAverage, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ,
    inv_smul_smul₀ (by exact_mod_cast hs.card_ne_zero)]

theorem finiteAverage_add {α E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Finset α) (hs : s.Nonempty) (F G : α → E) :
    finiteAverage s hs (fun a => F a + G a) =
      finiteAverage s hs F + finiteAverage s hs G := by
  simp only [finiteAverage, Finset.sum_add_distrib, smul_add]

theorem finiteAverage_smul {α E : Type*} [AddCommMonoid E] [Module ℝ E]
    (s : Finset α) (hs : s.Nonempty) (c : ℝ) (F : α → E) :
    finiteAverage s hs (fun a => c • F a) = c • finiteAverage s hs F := by
  unfold finiteAverage
  rw [← Finset.smul_sum, smul_smul, smul_smul, mul_comm]

end Homogenization
