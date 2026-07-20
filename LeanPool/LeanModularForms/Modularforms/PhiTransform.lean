/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/

module

public import LeanPool.LeanModularForms.Modularforms.Eisenstein
public import LeanPool.LeanModularForms.Modularforms.E2
public import LeanPool.LeanModularForms.Modularforms.Delta

/-! # PhiTransform -/


@[expose] public section

/-!
# Transformation Rules for φ₀

This file proves the transformation properties of φ₀ under the modular group action,
as stated in Blueprint Lemma 7.2:

1. **T-periodicity**: `φ₀(z + 1) = φ₀(z)`
2. **S-transformation**: `φ₀(-1/z) = φ₀(z) - (12i/π)(1/z)φ₋₂(z) - (36/π²)(1/z²)φ₋₄(z)`

Note: The blueprint uses φ₋₂, φ₋₄ but Lean uses φ₂', φ₄' since negative subscripts
are not valid identifiers.

## Main Results

- `φ₀_periodic`: φ₀ is 1-periodic, i.e., `φ₀(z + 1) = φ₀(z)`
- `φ₀_S_transform`: S-transformation formula for φ₀

## Supporting lemmas (in other files)

- `E₂_periodic`, `E₂_S_transform`: in `E2.lean`
- `E₄_periodic`, `E₆_periodic`, `E₄_S_transform`, `E₆_S_transform`: in `Eisenstein.lean`
- `Δ_periodic`, `Δ_S_transform`: in `Delta.lean`

-/

open ModularForm hiding E₄ E₆
open EisensteinSeries UpperHalfPlane TopologicalSpace Set MeasureTheory intervalIntegral
  Metric Filter Function Complex MatrixGroups

open scoped Interval Real NNReal ENNReal Topology BigOperators Nat

noncomputable section

/-! ## Main Theorem: T-periodicity of φ₀ -/

/-- φ₀ is 1-periodic: φ₀(z + 1) = φ₀(z) -/
theorem φ₀_periodic (z : ℍ) : φ₀ ((1 : ℝ) +ᵥ z) = φ₀ z := by
  simp only [φ₀, E₂_periodic, E₄_periodic, E₆_periodic, Δ_periodic]

/-! ## Main Theorem: S-transformation of φ₀ -/

/-- The S-transformation formula for φ₀:
    φ₀(-1/z) = φ₀(z) - (12i/π)(1/z)φ₋₂(z) - (36/π²)(1/z²)φ₋₄(z)

    This is Blueprint Lemma 7.2.
-/
theorem φ₀_S_transform (z : ℍ) :
    φ₀ (ModularGroup.S • z) = φ₀ z - (12 * Complex.I) / (π * z) * φ₂' z
                             - 36 / (π ^ 2 * z ^ 2) * φ₄' z := by
  have hz : (z : ℂ) ≠ 0 := ne_zero z
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hI : Complex.I ≠ 0 := Complex.I_ne_zero
  unfold φ₀ φ₂' φ₄'
  rw [E₂_S_transform, E₄_S_transform, E₆_S_transform, Δ_S_transform]
  set A := E₂ z * E₄ z - E₆ z with hA
  have h_numer : (z : ℂ) ^ 2 * (E₂ z + 6 / (π * Complex.I * z)) * (z ^ 4 * E₄ z) -
                 z ^ 6 * E₆ z = z ^ 6 * (A + 6 * E₄ z / (π * Complex.I * z)) := by
    ring_nf; rw [hA]; ring
  have h_expand : (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 / Δ z =
                  A ^ 2 / Δ z + 12 * A * E₄ z / (π * Complex.I * z * Δ z) +
                  36 * (E₄ z) ^ 2 / (π ^ 2 * Complex.I ^ 2 * z ^ 2 * Δ z) := by
    have hπIz : π * Complex.I * z ≠ 0 := mul_ne_zero (mul_ne_zero hπ hI) hz
    field_simp; ring
  have h_I_factor : (12 : ℂ) / (π * Complex.I * z) = -12 * Complex.I / (π * z) := by
    field_simp [Complex.inv_I]; simp [Complex.I_sq]
  rw [h_numer,
      show (z ^ 6 * (A + 6 * E₄ z / (π * Complex.I * z))) ^ 2 =
        z ^ 12 * (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 by
          rw [mul_pow, sq (z ^ 6 : ℂ), ← pow_add],
      show z ^ 12 * (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 / (z ^ 12 * Δ z) =
        (A + 6 * E₄ z / (π * Complex.I * z)) ^ 2 / Δ z by
          rw [mul_comm (z ^ 12 : ℂ) (Δ z)]; field_simp,
      h_expand, Complex.I_sq,
      show 12 * A * E₄ z / (π * Complex.I * z * Δ z) =
        12 / (π * Complex.I * z) * (E₄ z * A / Δ z) by field_simp,
      h_I_factor]
  ring

end
