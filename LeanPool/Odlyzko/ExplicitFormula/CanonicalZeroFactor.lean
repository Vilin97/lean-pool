/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Analysis.Complex.CanonicalDecomposition
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Canonical Zero Factor

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex ComplexConjugate Filter Metric Set
open scoped Topology

namespace NumberField.Odlyzko

/-- A canonical zero factor used in the Odlyzko-bound argument. -/
noncomputable def canonicalZeroFactor (R : ℝ) (u : ℂ) : ℂ → ℂ :=
  fun z ↦ (canonicalFactor R u z)⁻¹

theorem norm_canonicalZeroFactor_eq_one
    {R : ℝ} {u z : ℂ} (hu : u ∈ ball 0 R) (hz : z ∈ sphere 0 R) :
    ‖canonicalZeroFactor R u z‖ = 1 := by
  rw [canonicalZeroFactor, norm_inv,
    norm_canonicalFactor_eval_circle_eq_one hu hz, inv_one]

theorem canonicalZeroFactor_eq_zero_iff
    {R : ℝ} {u z : ℂ} (hu : u ∈ ball 0 R) (hz : z ∈ ball 0 R) :
    canonicalZeroFactor R u z = 0 ↔ z = u := by
  rw [canonicalZeroFactor, inv_eq_zero,
    canonicalFactor_eq_zero_iff hu hz]

theorem canonicalZeroFactor_apply
    (R : ℝ) (u z : ℂ) :
    canonicalZeroFactor R u z =
      (z - u) * (R : ℂ) / ((-conj u) * z + (R : ℂ) ^ 2) := by
  rw [canonicalZeroFactor, canonicalFactor_apply, inv_div]
  ring

theorem logDeriv_canonicalZeroFactor
    {R : ℝ} {u z : ℂ} (hR : R ≠ 0) (hzu : z ≠ u)
    (hreflect : (R : ℂ) ^ 2 - conj u * z ≠ 0) :
    logDeriv (canonicalZeroFactor R u) z =
      1 / (z - u) + conj u / ((R : ℂ) ^ 2 - conj u * z) := by
  have hreflect' : (-conj u) * z + (R : ℂ) ^ 2 ≠ 0 := by grind
  have hlocal :
      canonicalZeroFactor R u =ᶠ[𝓝 z]
        fun w ↦ (w - u) * (R : ℂ) /
          ((-conj u) * w + (R : ℂ) ^ 2) := by
    filter_upwards with w
    exact canonicalZeroFactor_apply R u w
  rw [logDeriv_apply, hlocal.deriv_eq, hlocal.eq_of_nhds,
    deriv_fun_div
      (c := fun w : ℂ ↦ (w - u) * (R : ℂ))
      (d := fun w : ℂ ↦ (-conj u) * w + (R : ℂ) ^ 2)
      (x := z) (by simp) (by fun_prop) hreflect']
  rw [deriv_mul_const_field, deriv_sub_const, deriv_id'', one_mul,
    deriv_add_const, deriv_const_mul_id]
  have hsub : z - u ≠ 0 := sub_ne_zero.mpr hzu
  have hR' : (R : ℂ) ≠ 0 := ofReal_ne_zero.mpr hR
  let q : ℂ := (-conj u) * z + (R : ℂ) ^ 2
  have hq : (R : ℂ) ^ 2 - conj u * z = q := by grind
  have hqne : q ≠ 0 := hq ▸ hreflect
  rw [hq]
  change
    (((R : ℂ) * q - (z - u) * (R : ℂ) * (-conj u)) / q ^ 2) /
        ((z - u) * (R : ℂ) / q) =
      1 / (z - u) + conj u / q
  have hfactor :
      (z - u) * (R : ℂ) / q ≠ 0 :=
    div_ne_zero (mul_ne_zero hsub hR') hqne
  grind

end NumberField.Odlyzko
