/-
Copyright (c) 2026 AleksandrovDifferentiability contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William M. Feldman
-/

module

public import LeanPool.ViscositySolutionTheory.AleksandrovDifferentiability.Analysis.Directional.Transport.Quadratic

/-!
Ported for Lean Pool: imports relocated and code adapted to Lean/Mathlib v4.34.0.

# Measure transport under linear isometries

This file records null-set transport lemmas for Lebesgue volume under linear isometry equivalences.
-/

@[expose] public noncomputable section

open MeasureTheory
open scoped MeasureTheory

namespace AleksandrovDifferentiability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- A linear isometry equivalence preserves null preimages for Lebesgue volume. -/
theorem measure_preimage_linearIsometryEquiv_eq_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {s : Set F} (hs : volume s = 0) :
    volume (e ⁻¹' s) = 0 := by
  rw [(LinearIsometryEquiv.measurePreserving e).measure_preimage (NullMeasurableSet.of_null hs)]
  exact hs

/-- Pull back full-measure ambient quadratic estimate goodness through a linear isometry
equivalence. -/
theorem measure_diff_quadraticEstimateSet_preimage_linearIsometryEquiv_eq_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {u : F → ℝ}
    (hnull : volume (Ω \ quadraticEstimateSet u) = 0) :
    volume (e ⁻¹' Ω \ quadraticEstimateSet (u ∘ e)) = 0 := by
  rw [quadraticEstimateSet_comp_linearIsometryEquiv (e := e) u]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' quadraticEstimateSet u =
        e ⁻¹' (Ω \ quadraticEstimateSet u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Quotient-estimate version of
`measure_diff_quadraticEstimateSet_preimage_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_quadraticQuotientEstimateSet_preimage_linearIsometryEquiv_eq_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {u : F → ℝ}
    (hnull : volume (Ω \ quadraticQuotientEstimateSet u) = 0) :
    volume (e ⁻¹' Ω \ quadraticQuotientEstimateSet (u ∘ e)) = 0 := by
  rw [quadraticQuotientEstimateSet_comp_linearIsometryEquiv (e := e) u]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' quadraticQuotientEstimateSet u =
        e ⁻¹' (Ω \ quadraticQuotientEstimateSet u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Pull back full-measure ambient quadratic estimate goodness from the image domain of a linear
isometry equivalence. -/
theorem measure_diff_quadraticEstimateSet_image_linearIsometryEquiv_eq_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (hnull : volume (e '' Ω \ quadraticEstimateSet (u ∘ e.symm)) = 0) :
    volume (Ω \ quadraticEstimateSet u) = 0 := by
  have hpre :=
    measure_diff_quadraticEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (u := u ∘ e.symm) hnull
  have hfun : (u ∘ e.symm) ∘ e = u := by
    funext x
    simp
  have hpreimage : e ⁻¹' (e '' Ω) = Ω := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have hxy' : x = y := by
        have hsymm := congrArg e.symm hxy
        simpa using hsymm.symm
      simpa [hxy'] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  simpa [hfun, hpreimage] using hpre

/-- Quotient-estimate version of
`measure_diff_quadraticEstimateSet_image_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_quadraticQuotientEstimateSet_image_linearIsometryEquiv_eq_zero
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {u : E → ℝ}
    (hnull : volume (e '' Ω \ quadraticQuotientEstimateSet (u ∘ e.symm)) = 0) :
    volume (Ω \ quadraticQuotientEstimateSet u) = 0 := by
  have hpre :=
    measure_diff_quadraticQuotientEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (u := u ∘ e.symm) hnull
  have hfun : (u ∘ e.symm) ∘ e = u := by
    funext x
    simp
  have hpreimage : e ⁻¹' (e '' Ω) = Ω := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hy, hxy⟩
      have hxy' : x = y := by
        have hsymm := congrArg e.symm hxy
        simpa using hsymm.symm
      simpa [hxy'] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  simpa [hfun, hpreimage] using hpre

/-- Pull back full-measure mixed-directional estimate goodness through a linear isometry
equivalence. -/
theorem measure_diff_mixedDirectionalQuadraticEstimateSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume (Ω \ mixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i)) u) = 0) :
    volume (e ⁻¹' Ω \ mixedDirectionalQuadraticEstimateSet D v (u ∘ e)) = 0 := by
  rw [mixedDirectionalQuadraticEstimateSet_comp_linearIsometryEquiv (e := e) D v u]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' mixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i)) u =
        e ⁻¹' (Ω \ mixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Quotient-estimate version of
`measure_diff_mixedDirectionalQuadraticEstimateSet_preimage_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_mixedDirectionalQuadraticQuotientSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume (Ω \ mixedDirectionalQuadraticQuotientEstimateSet D (fun i ↦ e (v i)) u) =
        0) :
    volume (e ⁻¹' Ω \ mixedDirectionalQuadraticQuotientEstimateSet D v (u ∘ e)) = 0 := by
  rw [mixedDirectionalQuadraticQuotientEstimateSet_comp_linearIsometryEquiv (e := e) D v u]
  have hset :
      e ⁻¹' Ω \ e ⁻¹' mixedDirectionalQuadraticQuotientEstimateSet D (fun i ↦ e (v i)) u =
        e ⁻¹' (Ω \ mixedDirectionalQuadraticQuotientEstimateSet D (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Pull back full-measure polarized mixed-directional estimate goodness through a linear
isometry equivalence. -/
theorem measure_diff_polarizedMixedDirectionalQuadraticSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [DecidableEq ι] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume (Ω \ polarizedMixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i)) u) =
        0) :
    volume (e ⁻¹' Ω \ polarizedMixedDirectionalQuadraticEstimateSet D v (u ∘ e)) = 0 := by
  rw [polarizedMixedDirectionalQuadraticEstimateSet_comp_linearIsometryEquiv (e := e) D v u]
  have hset :
      e ⁻¹' Ω \
          e ⁻¹' polarizedMixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i)) u =
        e ⁻¹' (Ω \ polarizedMixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Quotient-estimate version of
`measure_diff_polarizedMixedDirectionalQuadraticSet_preimage_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_polarizedMixedDirectionalQuotientSet_preimage_linearIsometryEquiv_eq_zero
    {ι : Type*} [DecidableEq ι] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set F} {D : Finset ι} {v : ι → E} {u : F → ℝ}
    (hnull :
      volume
          (Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D
            (fun i ↦ e (v i)) u) = 0) :
    volume
        (e ⁻¹' Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v (u ∘ e)) =
      0 := by
  rw [polarizedMixedDirectionalQuadraticQuotientEstimateSet_comp_linearIsometryEquiv
    (e := e) D v u]
  have hset :
      e ⁻¹' Ω \
          e ⁻¹' polarizedMixedDirectionalQuadraticQuotientEstimateSet D
            (fun i ↦ e (v i)) u =
        e ⁻¹'
          (Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D
            (fun i ↦ e (v i)) u) := by
    ext x
    simp
  rw [hset]
  exact measure_preimage_linearIsometryEquiv_eq_zero e hnull

/-- Pull back full-measure mixed-directional estimate goodness from the image domain of a linear
isometry equivalence. -/
theorem measure_diff_mixedDirectionalQuadraticEstimateSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume (e '' Ω \ mixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i))
        (u ∘ e.symm)) = 0) :
    volume (Ω \ mixedDirectionalQuadraticEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_mixedDirectionalQuadraticEstimateSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \ mixedDirectionalQuadraticEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ mixedDirectionalQuadraticEstimateSet D v u := by
    ext x
    simp [mixedDirectionalQuadraticEstimateSet, MixedDirectionalQuadraticEstimateAt,
      Function.comp_def]
  rwa [hset] at hpre

/-- Quotient-estimate version of
`measure_diff_mixedDirectionalQuadraticEstimateSet_image_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_mixedDirectionalQuadraticQuotientSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume
          (e '' Ω \ mixedDirectionalQuadraticQuotientEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    volume (Ω \ mixedDirectionalQuadraticQuotientEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_mixedDirectionalQuadraticQuotientSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \
          mixedDirectionalQuadraticQuotientEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ mixedDirectionalQuadraticQuotientEstimateSet D v u := by
    ext x
    simp [mixedDirectionalQuadraticQuotientEstimateSet,
      MixedDirectionalQuadraticQuotientEstimateAt, Function.comp_def]
  rwa [hset] at hpre

/-- Pull back full-measure polarized mixed-directional estimate goodness from the image domain of
a linear isometry equivalence. -/
theorem measure_diff_polarizedMixedDirectionalQuadraticSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [DecidableEq ι] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume
          (e '' Ω \ polarizedMixedDirectionalQuadraticEstimateSet D (fun i ↦ e (v i))
            (u ∘ e.symm)) = 0) :
    volume (Ω \ polarizedMixedDirectionalQuadraticEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_polarizedMixedDirectionalQuadraticSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \
          polarizedMixedDirectionalQuadraticEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ polarizedMixedDirectionalQuadraticEstimateSet D v u := by
    ext x
    simp [polarizedMixedDirectionalQuadraticEstimateSet,
      PolarizedMixedDirectionalQuadraticEstimateAt, Function.comp_def]
  rwa [hset] at hpre

/-- Quotient-estimate version of
`measure_diff_polarizedMixedDirectionalQuadraticSet_image_linearIsometryEquiv_eq_zero`. -/
theorem measure_diff_polarizedMixedDirectionalQuotientSet_image_linearIsometryEquiv_eq_zero
    {ι : Type*} [DecidableEq ι] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) {Ω : Set E} {D : Finset ι} {v : ι → E} {u : E → ℝ}
    (hnull :
      volume
          (e '' Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D
            (fun i ↦ e (v i)) (u ∘ e.symm)) = 0) :
    volume (Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u) = 0 := by
  have hpre :=
    measure_diff_polarizedMixedDirectionalQuotientSet_preimage_linearIsometryEquiv_eq_zero
      (e := e) (Ω := e '' Ω) (D := D) (v := v) (u := u ∘ e.symm) hnull
  have hset :
      e ⁻¹' (e '' Ω) \
          polarizedMixedDirectionalQuadraticQuotientEstimateSet D v ((u ∘ e.symm) ∘ e) =
        Ω \ polarizedMixedDirectionalQuadraticQuotientEstimateSet D v u := by
    ext x
    simp [polarizedMixedDirectionalQuadraticQuotientEstimateSet,
      PolarizedMixedDirectionalQuadraticQuotientEstimateAt, Function.comp_def]
  rwa [hset] at hpre


end AleksandrovDifferentiability
