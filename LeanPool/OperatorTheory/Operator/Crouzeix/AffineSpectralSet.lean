/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

import LeanPool.OperatorTheory.Operator.Crouzeix.AffinePolynomial

/-!
# Affine covariance of polynomial spectral sets

An invertible affine change of an operator transports its spectrum and any
polynomial spectral-set estimate by the same affine map, without changing
the spectral-set constant.
-/

open Set
open scoped InnerProductSpace Pointwise Polynomial

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The spectrum commutes with an invertible affine change of an operator. -/
theorem spectrum_smul_add_smul_one
    (A : E →L[ℂ] E) {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    spectrum ℂ (a • A + b • 1) =
      (fun z => a * z + b) '' spectrum ℂ A := by
  calc
    spectrum ℂ (a • A + b • 1) =
        spectrum ℂ (a • A) + {b} := by
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (spectrum.add_singleton_eq (a • A) b).symm
    _ = a • spectrum ℂ A + {b} := by
      have hsmul := spectrum.unit_smul_eq_smul A (Units.mk0 a ha)
      simpa only [Units.smul_def, Units.val_mk0] using
        congrArg (· + {b}) hsmul
    _ = (fun z => a * z + b) '' spectrum ℂ A := by
      ext z
      simp only [Set.mem_add, Set.mem_smul_set, Set.mem_singleton_iff,
        Set.mem_image]
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, _, rfl, rfl⟩
        exact ⟨w, hw, rfl⟩
      · rintro ⟨w, hw, rfl⟩
        exact ⟨a * w, ⟨w, hw, rfl⟩, b, rfl, rfl⟩

/-- A polynomial spectral-set estimate is transported by an invertible
affine change of variables, with the same constant. -/
theorem IsKPolynomialSpectralSet.affine
    {A : E →L[ℂ] E} {K : ℝ} {X : Set ℂ}
    (h : IsKPolynomialSpectralSet A K X)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsKPolynomialSpectralSet (a • A + b • 1) K
      ((fun z => a * z + b) '' X) := by
  constructor
  · rw [spectrum_smul_add_smul_one A ha b]
    exact Set.image_mono h.1
  · intro p
    let q : ℂ[X] := p.affineComposition a b
    have heval : Polynomial.aeval A q =
        Polynomial.aeval (a • A + b • 1) p := by
      exact Polynomial.aeval_affineComposition p a b A
    calc
      ‖Polynomial.aeval (a • A + b • 1) p‖ =
          ‖Polynomial.aeval A q‖ := congrArg norm heval.symm
      _ ≤ K * polynomialSupNorm q X := h.2 q
      _ = K * polynomialSupNorm p ((fun z => a * z + b) '' X) := by
        rw [polynomialSupNorm_affineComposition_image]

/-- Affine transport is an equivalence for nonzero linear coefficient. -/
theorem isKPolynomialSpectralSet_affine_iff
    (A : E →L[ℂ] E) (K : ℝ) (X : Set ℂ)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsKPolynomialSpectralSet (a • A + b • 1) K
        ((fun z => a * z + b) '' X) ↔
      IsKPolynomialSpectralSet A K X := by
  constructor
  · intro h
    have hinv := h.affine (inv_ne_zero ha) (-a⁻¹ * b)
    have hop :
        a⁻¹ • (a • A + b • 1) + (-a⁻¹ * b) • 1 = A := by
      simp only [smul_add, smul_smul, inv_mul_cancel₀ ha, one_smul]
      module
    have hset :
        (fun z => a⁻¹ * z + -a⁻¹ * b) ''
            ((fun z => a * z + b) '' X) = X := by
      ext z
      constructor
      · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
        convert hw using 1
        field_simp [ha]
        ring
      · intro hz
        refine ⟨a * z + b, ⟨z, hz, rfl⟩, ?_⟩
        field_simp [ha]
        ring
    rw [hop, hset] at hinv
    exact hinv
  · exact fun h => h.affine ha b

/-- Invertible affine changes preserve the constant-one polynomial
spectral-set property. -/
theorem IsPolynomialSpectralSet.affine
    {A : E →L[ℂ] E} {X : Set ℂ}
    (h : IsPolynomialSpectralSet A X)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsPolynomialSpectralSet (a • A + b • 1)
      ((fun z => a * z + b) '' X) :=
  IsKPolynomialSpectralSet.affine h ha b

/-- Constant-one polynomial spectral sets are invariant under invertible
affine changes. -/
theorem isPolynomialSpectralSet_affine_iff
    (A : E →L[ℂ] E) (X : Set ℂ)
    {a : ℂ} (ha : a ≠ 0) (b : ℂ) :
    IsPolynomialSpectralSet (a • A + b • 1)
        ((fun z => a * z + b) '' X) ↔
      IsPolynomialSpectralSet A X :=
  isKPolynomialSpectralSet_affine_iff A 1 X ha b

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
