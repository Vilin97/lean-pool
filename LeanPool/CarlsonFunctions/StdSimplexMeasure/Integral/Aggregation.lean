/-
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan J Braams
-/
module

public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Integral.Basic

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure
public import LeanPool.CarlsonFunctions.Pochhammer.BetaIntegral
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.PositiveSimplex

public import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.EuclideanCrossSection
public import LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic
import all LeanPool.CarlsonFunctions.StdSimplexMeasure.Measure.Basic

/-! # Coordinate aggregation in standard-simplex integrals -/

open Fintype (card)

@[expose] public noncomputable section StdSimplexIntegral

namespace MeasureTheory

open Measure MeasureTheory

universe u

variable {ι : Type u} [Fintype ι]


/-- Transformation of integrals under coordinate aggregation. The measurability hypothesis is
stated for the weighted target measure, which is exactly the push-forward measure occurring in
the change of variables. -/
theorem integral_stdSimplex_comp_aggregate
    {κ : Type*} [Fintype κ]
    (f : ι → κ) (hf : Function.Surjective f)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : (κ → ℝ) → E)
    (hg : AEStronglyMeasurable g
      (((stdSimplexMeasure (ι := κ)).restrict (Convexity.StdSimplex.coordinateSet ℝ κ)).withDensity
        (stdSimplexAggregateDensity f))) :
    ∫ u in Convexity.StdSimplex.coordinateSet ℝ ι,
        g (stdSimplexAggregate f u) ∂stdSimplexMeasure
      =
    ∫ v in Convexity.StdSimplex.coordinateSet ℝ κ,
        (∏ k,
          v k ^ (stdSimplexAggregateFiberCard f k - 1) /
            Nat.factorial
              (stdSimplexAggregateFiberCard f k - 1)) •
          g v
        ∂stdSimplexMeasure := by
  classical
  let μ := (stdSimplexMeasure (ι := ι)).restrict (Convexity.StdSimplex.coordinateSet ℝ ι)
  let ν := (stdSimplexMeasure (ι := κ)).restrict (Convexity.StdSimplex.coordinateSet ℝ κ)
  let d := stdSimplexAggregateDensity f
  have hagg : Measurable (stdSimplexAggregate (R := ℝ) f) := by
    exact (FunOnFinite.continuous_linearMap ℝ ℝ f).measurable
  have hd : Measurable d := by
    unfold d stdSimplexAggregateDensity
    fun_prop
  have hd_top : ∀ v, d v ≠ ⊤ := by
    intro v
    unfold d stdSimplexAggregateDensity
    apply ENNReal.prod_ne_top
    intro k _
    exact ENNReal.div_ne_top (by simp) (by simp [Nat.factorial_ne_zero])
  have hmeasure : Measure.map (stdSimplexAggregate f) μ = ν.withDensity d := by
    simpa only [μ, ν, d] using
      (map_stdSimplexMeasure_restrict_stdSimplex_aggregate f hf)
  have hgmap : AEStronglyMeasurable g (Measure.map (stdSimplexAggregate f) μ) := by
    rw [hmeasure]
    exact hg
  have hd_lt : ∀ᵐ v ∂ν, d v < ⊤ :=
    Filter.Eventually.of_forall fun v => lt_top_iff_ne_top.mpr (hd_top v)
  calc
    ∫ u, g (stdSimplexAggregate f u) ∂μ =
        ∫ v, g v ∂Measure.map (stdSimplexAggregate f) μ := by
      exact (integral_map hagg.aemeasurable hgmap).symm
    _ = ∫ v, g v ∂ν.withDensity d := by
      rw [hmeasure]
    _ = ∫ v, (d v).toReal • g v ∂ν := by
      rw [integral_withDensity_eq_integral_toReal_smul hd hd_lt]
    _ = ∫ v in Convexity.StdSimplex.coordinateSet ℝ κ,
        (∏ k, v k ^ (stdSimplexAggregateFiberCard f k - 1) /
          Nat.factorial (stdSimplexAggregateFiberCard f k - 1)) • g v
          ∂stdSimplexMeasure := by
      apply integral_congr_ae
      have hmem := self_mem_ae_restrict
        (μ := stdSimplexMeasure) (Convexity.StdSimplex.isClosed_coordinateSet ℝ κ).measurableSet
      filter_upwards [hmem] with v hv
      congr 1
      unfold d stdSimplexAggregateDensity
      rw [ENNReal.toReal_prod]
      apply Finset.prod_congr rfl
      intro k _
      rw [ENNReal.toReal_div, ENNReal.toReal_pow, ENNReal.toReal_ofReal]
      · simp
      · exact hv.1 k

end MeasureTheory

end StdSimplexIntegral
