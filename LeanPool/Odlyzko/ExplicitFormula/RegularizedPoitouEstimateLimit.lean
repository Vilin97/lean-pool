/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import LeanPool.Odlyzko.ExplicitFormula.Assembly
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedInverseGaussLimit
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedRightVerticalIntegral
public import LeanPool.Odlyzko.ExplicitFormula.RegularizedTartarLimit

/-!
# Regularized Poitou Estimate Limit

Supporting definitions and lemmas for the Odlyzko-bound formalization.
-/

@[expose] public section

noncomputable section

open Complex Filter Ideal IsDedekindDomain MeasureTheory Real Set
open NumberField.InfinitePlace
open Module
open scoped Topology

namespace NumberField.Odlyzko

variable (K : Type*) [Field K] [NumberField K] [IsTotallyComplex K]

/-- A regularized right vertical lower bound used in the Odlyzko-bound argument. -/
def RegularizedRightVerticalLowerBound (y σ : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ →
    -(2 * Real.pi) *
        (poitouTransform (regularizedScaledTartar y δ) 1).re ≤
      (∫ t : ℝ,
        poitouTransform (regularizedScaledTartar y δ) (σ + t * I) *
          (logDeriv (poleClearedCompletedDedekindZetaContinuation K) (σ + t * I) -
            completedZetaPoleLogDeriv (σ + t * I))).re

theorem poitouEstimate_of_regularizedRightVerticalLowerBound
    {y σ : ℝ} (hy : 0 < y) (hσ : 1 < σ)
    (hbound : RegularizedRightVerticalLowerBound K y σ) :
    Real.log |(discr K : ℝ)| / finrank ℚ K ≥
      Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
        archimedeanIntegral y -
        12 * Real.pi / (5 * finrank ℚ K * y) := by
  let m : ℝ := nrComplexPlaces K
  let n : ℝ := finrank ℚ K
  have hmn : 2 * m = n := by
    dsimp only [m, n]
    exact_mod_cast two_mul_nrComplexPlaces_eq_finrank K
  have hn : 0 < n := by
    dsimp only [n]
    exact_mod_cast (finrank_pos : 0 < finrank ℚ K)
  have hm : 0 < m := by nlinarith
  let L : ℝ → ℝ := fun δ ↦
    Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
      (∫ x : ℝ in Ioi 0,
        inverseGaussKernel (regularizedScaledTartar y δ) x) -
      (poitouTransform (regularizedScaledTartar y δ) 1).re / m
  have hLle :
      ∀ δ : ℝ, 0 < δ →
        L δ ≤ Real.log |(discr K : ℝ)| / n := by
    intro δ hδ
    have hformula :=
      re_integral_poitouTransform_regularized_mul_logDeriv_sub_poles
        K hδ y hσ
    have hcontour := hbound δ hδ
    rw [hformula] at hcontour
    have hprime :
        0 ≤ ∑' pe : HeightOneSpectrum (𝓞 K) × ℕ,
          regularizedPrimePowerPoitouWeight K y δ pe.1 pe.2 :=
      tsum_regularizedPrimePowerPoitouWeight_nonneg K y δ
    dsimp only [L]
    change
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
          (∫ x : ℝ in Ioi 0,
            inverseGaussKernel (regularizedScaledTartar y δ) x) -
          (poitouTransform (regularizedScaledTartar y δ) 1).re / m ≤
        Real.log |(discr K : ℝ)| / n
    have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    rw [← hmn]
    field_simp [hm.ne']
    nlinarith
  have htransform :
      Tendsto
        (fun δ : ℝ ↦
          (poitouTransform (regularizedScaledTartar y δ) 1).re)
        (𝓝[>] 0)
        (𝓝 (6 * Real.pi / (5 * y))) := by
    have hcomplex :=
      tendsto_poitouTransform_regularizedScaledTartar_nhdsGT_zero
        hy.ne' (s := (1 : ℂ)) (by simp)
    have h := Complex.continuous_re.continuousAt.tendsto.comp hcomplex
    rw [poitouTransform_scaledTartar_one hy] at h
    change
      Tendsto
        (fun δ : ℝ ↦
          (poitouTransform (regularizedScaledTartar y δ) 1).re)
        (𝓝[>] 0)
        (𝓝 (((6 * Real.pi / (5 * y) : ℝ) : ℂ).re)) at h
    simpa only [ofReal_re] using h
  have hinverse :=
    tendsto_integral_inverseGaussKernel_regularizedScaledTartar_nhdsGT_zero y
  have hL :
      Tendsto L (𝓝[>] 0)
        (𝓝
          (Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
            (archimedeanIntegral y - Real.log 2) -
            (6 * Real.pi / (5 * y)) / m)) := by
    dsimp only [L]
    exact
      ((tendsto_const_nhds.add tendsto_const_nhds).sub hinverse).sub
        (htransform.div_const m)
  have hlimit :
      Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
          (archimedeanIntegral y - Real.log 2) -
          (6 * Real.pi / (5 * y)) / m ≤
        Real.log |(discr K : ℝ)| / n :=
    le_of_tendsto hL (by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      simp_all)
  have hlog :
      Real.log (2 * Real.pi) + Real.log 2 =
        Real.log (4 * Real.pi) := by
    rw [← Real.log_mul (by positivity : (2 * Real.pi : ℝ) ≠ 0)
      (by norm_num : (2 : ℝ) ≠ 0)]
    grind
  change
    Real.eulerMascheroniConstant + Real.log (2 * Real.pi) -
          (archimedeanIntegral y - Real.log 2) -
          (6 * Real.pi / (5 * y)) / m ≤
        Real.log |(discr K : ℝ)| / n at hlimit
  change
    Real.eulerMascheroniConstant + Real.log (4 * Real.pi) -
          archimedeanIntegral y -
          12 * Real.pi / (5 * n * y) ≤
        Real.log |(discr K : ℝ)| / n
  rw [← hmn] at hlimit
  have hlimit' :
      Real.eulerMascheroniConstant +
          (Real.log (2 * Real.pi) + Real.log 2) -
          archimedeanIntegral y -
          (6 * Real.pi / (5 * y)) / m ≤
        Real.log |(discr K : ℝ)| / (2 * m) := by
    linarith
  rw [hlog] at hlimit'
  rw [← hmn]
  (convert hlimit' using 1; grind)

theorem totallyComplexPoitouEstimate_of_regularizedRightVerticalLowerBound
    {σ : ℝ} (hσ : 1 < σ)
    (hbound : RegularizedRightVerticalLowerBound K odlyzkoScale σ) :
    TotallyComplexPoitouEstimate K := by
  unfold TotallyComplexPoitouEstimate
  exact poitouEstimate_of_regularizedRightVerticalLowerBound
    K odlyzkoScale_pos hσ hbound

end NumberField.Odlyzko
