/-
Copyright (c) 2026 Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael R. Douglas, Sarah Hoback, Anna Mei, Ron Nissim
-/


import LeanPool.OSforGFF.Spacetime.Basic
import LeanPool.OSforGFF.Spacetime.ProdIntegrable

/-!
# Spacetime Decomposition

This file provides the measure-preserving decomposition of SpaceTime into
time and spatial components: SpaceTime ≃ᵐ ℝ × SpatialCoords.

## Main Definitions

* `piLpMeasurableEquiv` - MeasurableEquiv between PiLp and underlying pi type
* `spacetimeDecomp` - The measurable equivalence SpaceTime ≃ᵐ ℝ × SpatialCoords

## Main Results

* `spacetimeDecomp_measurePreserving` - The decomposition preserves Lebesgue measure
* `spacetimeDecomp_apply` - Explicit formula: spacetimeDecomp k = (k 0, spatialPart k)
* `spacetime_norm_sq_decompose` - Norm decomposition: ‖k‖² = k₀² + ‖k_sp‖²
-/

open MeasureTheory MeasureSpace FiniteDimensional Real

/-! ### Integral Decomposition for SpaceTime

We establish that integrals over SpaceTime can be decomposed into
iterated integrals over ℝ (time component) and SpatialCoords (spatial components).
This uses `MeasurableEquiv.piFinSuccAbove` and `measurePreserving_piFinSuccAbove`.
-/

/-- MeasurableEquiv between PiLp and the underlying pi type. -/
def piLpMeasurableEquiv (n : ℕ) : PiLp 2 (fun _ : Fin n => ℝ) ≃ᵐ (Fin n → ℝ) where
  toEquiv := WithLp.equiv 2 _
  measurable_toFun := WithLp.measurable_ofLp 2 _
  measurable_invFun := WithLp.measurable_toLp 2 _

/-- The measurable equivalence from SpaceTime to ℝ × SpatialCoords.
    Composes three measure-preserving maps:
    1. piLpMeasurableEquiv : EuclideanSpace ℝ (Fin 4) → (Fin 4 → ℝ)
    2. piFinSuccAbove 0 : (Fin 4 → ℝ) → ℝ × (Fin 3 → ℝ)
    3. id × piLpMeasurableEquiv.symm : ℝ × (Fin 3 → ℝ) → ℝ × SpatialCoords
-/
def spacetimeDecomp : SpaceTime ≃ᵐ ℝ × SpatialCoords :=
  (piLpMeasurableEquiv STDimension).trans
  ((MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0).trans
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
    (piLpMeasurableEquiv (STDimension - 1)).symm))

/-- Measure preservation for piLpMeasurableEquiv. -/
lemma piLpMeasurableEquiv_measurePreserving (n : ℕ) :
    MeasurePreserving (piLpMeasurableEquiv n)
      (volume : Measure (PiLp 2 (fun _ : Fin n => ℝ))) volume := by
  simp only [piLpMeasurableEquiv, MeasurableEquiv.coe_mk]
  exact PiLp.volume_preserving_ofLp (ι := Fin n)

/-- The spacetime decomposition preserves measure. -/
theorem spacetimeDecomp_measurePreserving :
    MeasurePreserving spacetimeDecomp (volume : Measure SpaceTime) volume := by
  unfold spacetimeDecomp
  -- Step 1: PiLp → (Fin 4 → ℝ) is measure-preserving
  have h1 : MeasurePreserving (piLpMeasurableEquiv STDimension)
      (volume : Measure SpaceTime) volume :=
    piLpMeasurableEquiv_measurePreserving STDimension
  -- Step 2: piFinSuccAbove 0 is measure-preserving
  have h2 : MeasurePreserving (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) 0)
      (volume : Measure (Fin STDimension → ℝ)) volume :=
    measurePreserving_piFinSuccAbove (fun _ => volume) 0
  -- Step 3: id × piLpMeasurableEquiv.symm is measure-preserving
  have h3 : MeasurePreserving
      (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
        (piLpMeasurableEquiv (STDimension - 1)).symm)
      (volume : Measure (ℝ × (Fin (STDimension - 1) → ℝ))) volume := by
    apply MeasurePreserving.prod
    · exact MeasurePreserving.id volume
    · simp only [piLpMeasurableEquiv, MeasurableEquiv.symm_mk]
      exact PiLp.volume_preserving_toLp (ι := Fin (STDimension - 1))
  exact h1.trans (h2.trans h3)

/-- Spacetime decomposition maps k to (k 0, spatialPart k). -/
theorem spacetimeDecomp_apply (k : SpaceTime) :
    spacetimeDecomp k = (k 0, spatialPart k) := rfl

/-- `spacetimeDecomp.symm` equals `spacetimeOfTimeSpace` (from SchwartzProdIntegrable.lean).
    Both construct a SpaceTime point from time t and spatial coordinates v.
-/
lemma spacetimeDecomp_symm_eq_spacetimeOfTimeSpace (t : ℝ) (v : SpatialCoords) :
    spacetimeDecomp.symm (t, v) = spacetimeOfTimeSpace t v := by
  -- Both definitions construct a point x with x 0 = t and x i = v (i-1) for i > 0
  ext i
  cases i using Fin.cases with
  | zero =>
    -- i = 0: time component
    have h1 : (spacetimeDecomp.symm (t, v)) 0 = t :=
      congr_arg Prod.fst (spacetimeDecomp.apply_symm_apply (t, v))
    rw [h1, spacetimeOfTimeSpace_time]
  | succ j =>
    -- i = j + 1: spatial components
    have h_spatial : spatialPart (spacetimeDecomp.symm (t, v)) = v :=
      congr_arg Prod.snd (spacetimeDecomp.apply_symm_apply (t, v))
    -- spatialPart k j = k j.succ by definition
    have h_spatialPart_def : spatialPart (spacetimeDecomp.symm (t, v)) j =
      (spacetimeDecomp.symm (t, v)) j.succ := rfl
    rw [← h_spatialPart_def, h_spatial]
    exact (spacetimeOfTimeSpace_spatial t v j).symm

/-- The SpaceTime norm decomposes into time and spatial parts: ‖k‖² = k₀² + ‖k_sp‖². -/
lemma spacetime_norm_sq_decompose (k : SpaceTime) :
    ‖k‖^2 = (k 0)^2 + ‖spatialPart k‖^2 := by
  -- Expand SpaceTime norm as sum over 4 components
  have hST : ‖k‖^2 = (k 0)^2 + (k 1)^2 + (k 2)^2 + (k 3)^2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_four]
    simp only [Real.norm_eq_abs, sq_abs]
  -- Expand SpatialCoords norm as sum over 3 components
  have hSp : ‖spatialPart k‖^2 = (k 1)^2 + (k 2)^2 + (k 3)^2 := by
    -- Key component equalities
    have h0 : (spatialPart k : Fin (STDimension - 1) → ℝ) ⟨0, by decide⟩ = k 1 := rfl
    have h1 : (spatialPart k : Fin (STDimension - 1) → ℝ) ⟨1, by decide⟩ = k 2 := rfl
    have h2 : (spatialPart k : Fin (STDimension - 1) → ℝ) ⟨2, by decide⟩ = k 3 := rfl
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
    -- Manually expand the Fin 3 sum
    have hUniv : (Finset.univ : Finset (Fin (STDimension - 1))) =
        {⟨0, by decide⟩, ⟨1, by decide⟩, ⟨2, by decide⟩} := rfl
    rw [hUniv, Finset.sum_insert (by decide : (⟨0, _⟩ : Fin (STDimension - 1)) ∉ _),
        Finset.sum_insert (by decide : (⟨1, _⟩ : Fin (STDimension - 1)) ∉ _),
        Finset.sum_singleton, h0, h1, h2]
    ring
  rw [hST, hSp]; ring

/-- For a product-type integrand f(k₀) × g(k_sp), the integral decomposes as a product. -/
lemma integral_spacetime_prod_split {f : ℝ → ℂ} {g : SpatialCoords → ℂ}
    (_hf : Integrable f) (_hg : Integrable g) :
    ∫ k : SpaceTime, f (k 0) * g (spatialPart k) =
    (∫ k₀ : ℝ, f k₀) * (∫ k_sp : SpatialCoords, g k_sp) := by
  have h := spacetimeDecomp_measurePreserving.integral_comp' (fun p => f p.1 * g p.2)
  simp only [spacetimeDecomp_apply] at h
  rw [h]; exact integral_prod_mul f g
