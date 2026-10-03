/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.Transport.Core
public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.Transport.Measure

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Measure transport for directional estimates

This file combines isometric measure transport with fixed-direction scalar estimate sets.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Pull back full-measure scalar directional-line goodness through a linear isometry equivalence.
This is the measure-theoretic companion to
`directionalLineScalarEstimateSet_comp_linearIsometryEquiv`. -/
theorem measure_diff_directionalLineScalarEstimateSet_preimage_linearIsometryEquiv_eq_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {u : F → ℝ} {v : E}
    (hnull : volume (Ω \ directionalLineScalarEstimateSet (e v) u) = 0) :
    volume (e ⁻¹' Ω \ directionalLineScalarEstimateSet v (u ∘ e)) = 0 := by
  rw [directionalLineScalarEstimateSet_comp_linearIsometryEquiv (e := e) u v]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' directionalLineScalarEstimateSet (e v) u =
        e ⁻¹' (Ω \ directionalLineScalarEstimateSet (e v) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_preimage_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_preimage_linearIsometryEquiv_eq_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {u : F → ℝ} {v : E}
    (hnull : volume (Ω \ directionalLineScalarQuotientEstimateSet (e v) u) = 0) :
    volume (e ⁻¹' Ω \ directionalLineScalarQuotientEstimateSet v (u ∘ e)) = 0 := by
  rw [directionalLineScalarQuotientEstimateSet_comp_linearIsometryEquiv (e := e) u v]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' directionalLineScalarQuotientEstimateSet (e v) u =
        e ⁻¹' (Ω \ directionalLineScalarQuotientEstimateSet (e v) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Pull back full-measure scalar directional-line goodness from the image domain of a linear
isometry equivalence. This is the coordinate-change shape used when a problem on `Ω` is transported
to `e '' Ω` with function `u ∘ e.symm`. -/
theorem measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : E}
    (hnull :
      volume (e '' Ω \ directionalLineScalarEstimateSet (e v) (u ∘ e.symm)) = 0) :
    volume (Ω \ directionalLineScalarEstimateSet v u) = 0 := by
  have hpre :=
    measure_diff_directionalLineScalarEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (u := u ∘ e.symm) (v := v) hnull
  have hset :
      e ⁻¹' (e '' Ω) \ directionalLineScalarEstimateSet v ((u ∘ e.symm) ∘ e) =
        Ω \ directionalLineScalarEstimateSet v u := by
    ext x
    simp [directionalLineScalarEstimateSet, Function.comp_def]
  rwa [hset] at hpre

/-- Quotient-estimate version of
`measure_diff_directionalLineScalarEstimateSet_image_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_directionalLineScalarQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ} {v : E}
    (hnull :
      volume (e '' Ω \ directionalLineScalarQuotientEstimateSet (e v) (u ∘ e.symm)) = 0) :
    volume (Ω \ directionalLineScalarQuotientEstimateSet v u) = 0 := by
  have hpre :=
    measure_diff_directionalLineScalarQuotientEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (u := u ∘ e.symm) (v := v) hnull
  have hset :
      e ⁻¹' (e '' Ω) \ directionalLineScalarQuotientEstimateSet v ((u ∘ e.symm) ∘ e) =
        Ω \ directionalLineScalarQuotientEstimateSet v u := by
      ext x
      simp [directionalLineScalarQuotientEstimateSet, Function.comp_def]
  rwa [hset] at hpre

/-- Pull back full-measure finite directional slice-goodness through a linear isometry
equivalence. -/
theorem measure_diff_directionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume (Ω \ directionalSliceEstimateSet D (fun i ↦ e (v i)) u) = 0) :
    volume (e ⁻¹' Ω \ directionalSliceEstimateSet D v (u ∘ e)) = 0 := by
  rw [directionalSliceEstimateSet_comp_linearIsometryEquiv (e := e) D v u]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' directionalSliceEstimateSet D (fun i ↦ e (v i)) u =
        e ⁻¹' (Ω \ directionalSliceEstimateSet D (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Quotient-estimate version of
`measure_diff_directionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_directionalSliceQuotientEstimateSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume (Ω \ directionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u) = 0) :
    volume (e ⁻¹' Ω \ directionalSliceQuotientEstimateSet D v (u ∘ e)) = 0 := by
  rw [directionalSliceQuotientEstimateSet_comp_linearIsometryEquiv (e := e) D v u]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' directionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u =
        e ⁻¹' (Ω \ directionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Pull back full-measure finite directional slice-goodness from the image domain of a linear
isometry equivalence. -/
theorem measure_diff_directionalSliceEstimateSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume (e '' Ω \ directionalSliceEstimateSet D (fun i ↦ e (v i)) (u ∘ e.symm)) =
        0) :
    volume (Ω \ directionalSliceEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_directionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \ directionalSliceEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ directionalSliceEstimateSet D v u := by
    ext x
    simp [directionalSliceEstimateSet, DirectionalSliceEstimateAt, Function.comp_def]
  rwa [hset] at hpre

/-- Quotient-estimate version of
`measure_diff_directionalSliceEstimateSet_image_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_directionalSliceQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume
          (e '' Ω \ directionalSliceQuotientEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    volume (Ω \ directionalSliceQuotientEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_directionalSliceQuotientEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \ directionalSliceQuotientEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ directionalSliceQuotientEstimateSet D v u := by
    ext x
    simp [directionalSliceQuotientEstimateSet, DirectionalSliceQuotientEstimateAt,
      Function.comp_def]
  rwa [hset] at hpre

/-- Pull back full-measure compatible finite directional slice-goodness through a linear isometry
equivalence. -/
theorem measure_diff_compatibleDirectionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume (Ω \ compatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i)) u) = 0) :
    volume (e ⁻¹' Ω \ compatibleDirectionalSliceEstimateSet D v (u ∘ e)) = 0 := by
  rw [compatibleDirectionalSliceEstimateSet_comp_linearIsometryEquiv (e := e) D v u]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' compatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i)) u =
        e ⁻¹' (Ω \ compatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Symmetric-compatible version of
`measure_diff_compatibleDirectionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero`. -/
theorem
    measure_diff_symmetricCompatibleDirectionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume (Ω \ symmetricCompatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i)) u) =
        0) :
    volume (e ⁻¹' Ω \ symmetricCompatibleDirectionalSliceEstimateSet D v (u ∘ e)) = 0 := by
  rw [symmetricCompatibleDirectionalSliceEstimateSet_comp_linearIsometryEquiv (e := e) D v u]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' symmetricCompatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i)) u =
        e ⁻¹' (Ω \ symmetricCompatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Quotient-estimate version of
`measure_diff_compatibleDirectionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero`. -/
theorem
    measure_diff_compatibleDirectionalSliceQuotientEstimateSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume (Ω \ compatibleDirectionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u) =
        0) :
    volume (e ⁻¹' Ω \ compatibleDirectionalSliceQuotientEstimateSet D v (u ∘ e)) =
      0 := by
  rw [compatibleDirectionalSliceQuotientEstimateSet_comp_linearIsometryEquiv (e := e) D v u]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' compatibleDirectionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u =
        e ⁻¹' (Ω \ compatibleDirectionalSliceQuotientEstimateSet D (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Symmetric-compatible quotient-estimate version of
`measure_diff_compatibleDirectionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero`. -/
theorem
    measure_diff_symmetricCompatibleSliceQuotientSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume
          (Ω \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D
            (fun i ↦ e (v i)) u) = 0) :
    volume (e ⁻¹' Ω \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v (u ∘ e)) =
      0 := by
  rw [symmetricCompatibleDirectionalSliceQuotientEstimateSet_comp_linearIsometryEquiv
    (e := e) D v u]
  have hset :
      e ⁻¹' Ω \
          e ⁻¹' symmetricCompatibleDirectionalSliceQuotientEstimateSet D
            (fun i ↦ e (v i)) u =
        e ⁻¹'
          (Ω \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D
            (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Pull back full-measure compatible finite directional slice-goodness from the image domain of
a linear isometry equivalence. -/
theorem measure_diff_compatibleDirectionalSliceEstimateSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume
          (e '' Ω \ compatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    volume (Ω \ compatibleDirectionalSliceEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_compatibleDirectionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \ compatibleDirectionalSliceEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ compatibleDirectionalSliceEstimateSet D v u := by
    ext x
    simp [compatibleDirectionalSliceEstimateSet, CompatibleDirectionalSliceEstimateAt,
      Function.comp_def]
  rwa [hset] at hpre

/-- Symmetric-compatible version of
`measure_diff_compatibleDirectionalSliceEstimateSet_image_linearIsometryEquiv_eq_zero`. -/
theorem
    measure_diff_symmetricCompatibleDirectionalSliceEstimateSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume
          (e '' Ω \ symmetricCompatibleDirectionalSliceEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    volume (Ω \ symmetricCompatibleDirectionalSliceEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_symmetricCompatibleDirectionalSliceEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \
          symmetricCompatibleDirectionalSliceEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ symmetricCompatibleDirectionalSliceEstimateSet D v u := by
    ext x
    simp [symmetricCompatibleDirectionalSliceEstimateSet,
      SymmetricCompatibleDirectionalSliceEstimateAt, Function.comp_def]
  rwa [hset] at hpre

/-- Quotient-estimate version of
`measure_diff_compatibleDirectionalSliceEstimateSet_image_linearIsometryEquiv_eq_zero`. -/
theorem
    measure_diff_compatibleDirectionalSliceQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume
          (e '' Ω \ compatibleDirectionalSliceQuotientEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    volume (Ω \ compatibleDirectionalSliceQuotientEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_compatibleDirectionalSliceQuotientEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \
          compatibleDirectionalSliceQuotientEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ compatibleDirectionalSliceQuotientEstimateSet D v u := by
    ext x
    simp [compatibleDirectionalSliceQuotientEstimateSet,
      CompatibleDirectionalSliceQuotientEstimateAt, Function.comp_def]
  rwa [hset] at hpre

/-- Symmetric-compatible quotient-estimate version of
`measure_diff_compatibleDirectionalSliceEstimateSet_image_linearIsometryEquiv_eq_zero`. -/
theorem
    measure_diff_symmetricCompatibleSliceQuotientSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume
          (e '' Ω \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D
            (fun i ↦ e (v i)) (u ∘ e.symm)) = 0) :
    volume (Ω \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_symmetricCompatibleSliceQuotientSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \
          symmetricCompatibleDirectionalSliceQuotientEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ symmetricCompatibleDirectionalSliceQuotientEstimateSet D v u := by
    ext x
    simp [symmetricCompatibleDirectionalSliceQuotientEstimateSet,
      SymmetricCompatibleDirectionalSliceQuotientEstimateAt, Function.comp_def]
  rwa [hset] at hpre


end AleksandrovDifferentiability
