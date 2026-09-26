/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.RingTheory.DiscreteValuationRing.Basic
/-!
# Normalized additive valuations on discrete valuation rings

This file supplies general-purpose facts about Mathlib's normalized additive
valuation on a discrete valuation ring which are independent of any chosen
valued-field presentation.
-/

@[expose] public section

noncomputable
section

universe u

namespace IsDiscreteValuationRing

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- Membership in a power of the maximal ideal is detected by the normalized
additive valuation. -/
theorem mem_maximalIdeal_pow_iff_addVal_ge (a : R) (n : ℕ) :
    a ∈ IsLocalRing.maximalIdeal R ^ n ↔ (n : ℕ∞) ≤ addVal R a := by
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow,
    Ideal.mem_span_singleton, ← addVal_le_iff_dvd, hϖ.addVal_pow]

/-- A ring automorphism of a discrete valuation ring preserves its normalized
additive valuation. -/
@[simp] theorem addVal_ringEquiv (e : R ≃+* R) (a : R) :
    addVal R (e a) = addVal R a := by
  by_cases ha : a = 0
  · subst a
    simp
  obtain ⟨ϖ, hϖ⟩ := exists_irreducible R
  obtain ⟨n, u, ha_decomp⟩ := eq_unit_mul_pow_irreducible ha hϖ
  have hmapϖ : Irreducible (e ϖ) := hϖ.map e
  have hmap_decomp :
      e a = (Units.map e.toMonoidHom u : R) * (e ϖ) ^ n := by
    rw [ha_decomp, map_mul, map_pow]
    rfl
  rw [addVal_def (e a) (Units.map e.toMonoidHom u) hmapϖ n hmap_decomp,
    addVal_def a u hϖ n ha_decomp]

end IsDiscreteValuationRing

end
