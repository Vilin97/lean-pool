/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams.
-/
module



public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.PositiveSimplex.Basic

import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import LeanPool.CarlsonFunctions.StdSimplexMeasure.EuclideanCrossSection
import all LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

/-! # Basic integration with the affine-hyperplane coordinate measure -/

open Fintype (card)

public noncomputable section StdSimplexIntegral

namespace MeasureTheory

open Measure MeasureTheory

universe u

variable {ι : Type u} [Fintype ι]

open scoped Classical

/-- Scaling the free coordinates by `c` divides the Bochner integral by
`c ^ (card ι - 1)`. -/
theorem integral_smul_free_coords
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (i : ι) (c : ℝ) (hc : 0 < c)
    (f : ({j : ι // j ≠ i} → ℝ) → E) :
  ∫ x, f (c • x) ∂volume =
    (c ^ (card ι - 1))⁻¹ • ∫ x, f x ∂volume := by
  let e : ({j : ι // j ≠ i} → ℝ) ≃ₜ ({j : ι // j ≠ i} → ℝ) :=
    Homeomorph.smulOfNeZero c hc.ne'
  have hmap : Measure.map e volume =
      ENNReal.ofReal (c ^ (card ι - 1))⁻¹ • volume := by
    simpa [e] using volume_map_smul_free_coords i c hc
  calc
    ∫ x, f (c • x) ∂volume = ∫ x, f x ∂Measure.map e volume := by
      simpa [e] using (e.isClosedEmbedding.integral_map f).symm
    _ = ∫ x, f x ∂(ENNReal.ofReal (c ^ (card ι - 1))⁻¹ • volume) := by rw [hmap]
    _ = (c ^ (card ι - 1))⁻¹ • ∫ x, f x ∂volume := by
      rw [integral_smul_measure]
      simp [(pow_pos hc _).le]

/-- Integration over the standard simplex can be computed in any free-coordinate chart. This is
stated for functions taking values in a normed real vector space. -/
theorem integral_stdSimplex_eq_integral_freeCoords
    [Nonempty ι] (i : ι)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : (ι → ℝ) → E) :
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, f u ∂stdSimplexMeasure =
    ∫ x in stdSimplexFreeCoords i, f (stdSimplexCoordMap i x) := by
  rw [stdSimplexMeasure_restrict_stdSimplex i]
  exact
    (isClosedEmbedding_stdSimplexCoordMap i).integral_map f

/-- A nonnegative integral over the standard simplex can be computed in any free-coordinate
chart. -/
theorem lintegral_stdSimplex_eq_lintegral_freeCoords
    [Nonempty ι] (i : ι) (f : (ι → ℝ) → ENNReal) :
    ∫⁻ u in Convexity.StdSimplex.coordinateSet ℝ ι, f u ∂stdSimplexMeasure =
      ∫⁻ x in stdSimplexFreeCoords i, f (stdSimplexCoordMap i x) := by
  rw [stdSimplexMeasure_restrict_stdSimplex i]
  exact (isClosedEmbedding_stdSimplexCoordMap i).measurableEmbedding.lintegral_map f

/-- The integral of a function over the standard simplex is invariant under coordinate
permutations. -/
theorem integral_stdSimplex_comp_perm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (σ : Equiv.Perm ι) (f : (ι → ℝ) → E) :
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, f (u ∘ σ) ∂stdSimplexMeasure =
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, f u ∂stdSimplexMeasure := by
  have hp := measurePreserving_stdSimplexMeasure_perm σ
  have he : MeasurableEmbedding (fun u : ι → ℝ => u ∘ σ) := by
    apply (continuous_pi (fun j => continuous_apply (σ j))).measurableEmbedding
    intro u v huv
    funext j
    have := congrFun huv (σ.symm j)
    simpa using this
  have hr := hp.restrict_preimage_emb he (Convexity.StdSimplex.coordinateSet ℝ ι)
  rw [preimage_stdSimplex_perm] at hr
  exact hr.integral_comp he f

/-- Continuous functions are integrable on the standard simplex. -/
theorem ContinuousOn.integrableOn_stdSimplex
    [Nonempty ι]
    {E : Type*} [NormedAddCommGroup E]
    {f : (ι → ℝ) → E}
    (hf : ContinuousOn f (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    IntegrableOn f (Convexity.StdSimplex.coordinateSet ℝ ι) stdSimplexMeasure := by
  apply hf.integrableOn_of_subset_isCompact
    (Convexity.StdSimplex.isCompact_coordinateSet ℝ ι)
    (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet
    Set.Subset.rfl
  rw [← Measure.restrict_apply_univ]
  exact measure_ne_top _ _

/-- The integral of `f` over the standard simplex depends only on the values of `f` on
the standard simplex. -/
theorem integral_stdSimplex_congr
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f g : (ι → ℝ) → E}
    (hfg : Set.EqOn f g (Convexity.StdSimplex.coordinateSet ℝ ι)) :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, f u ∂stdSimplexMeasure =
      ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, g u ∂stdSimplexMeasure := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards
    [self_mem_ae_restrict
      (μ := stdSimplexMeasure)
      (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet] with u hu
  exact hfg hu

/-- For a single-point index set, the integral over the simplex reduces to evaluation at the
all-ones vector. (Base case for induction.) -/
theorem integral_stdSimplex_unique
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] [Unique ι] (f : (ι → ℝ) → E) :
  ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι, f u ∂stdSimplexMeasure = f (fun _ ↦ 1) := by
  classical
  rw [stdSimplexMeasure_unique]
  change ∫ u, f u ∂(dirac (fun _ : ι => (1 : ℝ))).restrict (Convexity.StdSimplex.coordinateSet ℝ ι) = _
  rw [MeasureTheory.restrict_dirac' (Convexity.StdSimplex.isClosed_coordinateSet ℝ ι).measurableSet]
  have hmem : (fun _ : ι => (1 : ℝ)) ∈ Convexity.StdSimplex.coordinateSet ℝ ι := by simp [Convexity.StdSimplex.coordinateSet]
  rw [if_pos hmem]
  exact MeasureTheory.integral_dirac f (fun _ : ι => (1 : ℝ))

end MeasureTheory

end StdSimplexIntegral
