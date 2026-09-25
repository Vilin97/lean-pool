/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.SchurTheory.PowerSurj

/-!
# Constructive simplicity of endomorphism algebras

Every nonzero endomorphism of a finite-dimensional complex vector space
generates the full endomorphism algebra in the sense that it can be
"sandwiched" to produce the identity: there exist endomorphisms
`U i`, `W i` such that `∑ i, U i * A * W i = 1`.
-/

@[expose] public section

namespace RS

open Module in
/-- **The sandwich identity**: a nonzero endomorphism generates the
identity as a finite sum of two-sided products. -/
theorem exists_sum_conj_eq_one {V : Type*} [AddCommGroup V]
    [Module ℂ V] [FiniteDimensional ℂ V]
    (A : Module.End ℂ V) (hA : A ≠ 0) :
    ∃ (n : ℕ) (U W : Fin n → Module.End ℂ V),
      ∑ i, U i * A * W i = 1 := by
  -- Since A ≠ 0, pick v with A v ≠ 0
  have hAne : ∃ v, A v ≠ 0 := by
    by_contra h
    push Not at h
    exact hA (LinearMap.ext h)
  obtain ⟨v, hv⟩ := hAne
  -- Get a dual functional φ with φ (A v) = 1
  obtain ⟨φ, hφ⟩ := Projective.exists_dual_eq_one ℂ hv
  -- Get a finite basis
  set d := finrank ℂ V
  set b := Module.finBasis ℂ V
  -- Define W j : y ↦ (b.coord j y) • v  and  U j : y ↦ φ y • b j
  refine ⟨d, fun j => φ.smulRight (b j), fun j => (b.coord j).smulRight v, ?_⟩
  -- Show ∑ j, U j * A * W j = 1
  ext y
  simp only [LinearMap.sum_apply, Module.End.mul_apply,
    LinearMap.smulRight_apply,
    Basis.coord_apply, Module.End.one_apply, map_smul, hφ, smul_smul, mul_one]
  exact b.sum_repr y

end RS
