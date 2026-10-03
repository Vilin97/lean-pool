/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.ExplicitScales
public import LeanPool.BeyondBethe.BeyondBethe.NumericalNearby
public import Mathlib.Tactic

/-! # Executable Certificate -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

/-!
# The executable structural certificate

The regularized optimizer is represented by a rational doubly stochastic
matrix.  Pair eligibility is decided by directed rational logarithm bounds,
and a deterministic maximal row matching collects the accepted fixed gains.
This file proves the complete positive-matrix dichotomy for that concrete
certificate; no pair-capacity optimizer or maximum-weight matching remains.
-/

/-- The hard-coded rational regularization scale in dimension `n`. -/
def explicitRegularizationScale (n : ℕ) : ℚ :=
  explicitXi / (4 * n)

theorem cast_explicitRegularizationScale (n : ℕ) :
    ((explicitRegularizationScale n : ℚ) : ℝ) =
      (explicitXi : ℝ) / (4 * (n : ℝ)) := by
  simp [explicitRegularizationScale]

theorem explicitRegularizationScale_pos {n : ℕ} (hn : 0 < n) :
    0 < explicitRegularizationScale n := by
  rw [explicitRegularizationScale]
  exact div_pos explicitXi_pos (by positivity)

theorem explicitGamma_pos : 0 < explicitGamma := by
  norm_num [explicitGamma]

theorem explicitRegularizationScale_le_one {n : ℕ} (hn : 1 ≤ n) :
    explicitRegularizationScale n ≤ 1 := by
  have hxi : explicitXi ≤ 1 := by
    norm_num [explicitXi, explicitDelta, explicitEta, explicitRowRatio]
  rw [explicitRegularizationScale, div_le_one (by positivity)]
  have hdenNat : 1 ≤ 4 * n := by omega
  have hden : (1 : ℚ) ≤ 4 * n := by exact_mod_cast hdenNat
  exact hxi.trans hden

/-- The fixed-gain row-pair weights used by the algorithm. -/
def explicitCertifiedRowWeight {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) : RowPair n → ℚ :=
  certifiedConstantRowWeight (explicitRegularizationScale n) X
    explicitKappa explicitGamma (directedPairCostPrecision n)

/-- The rational gain collected by the deterministic greedy matching. -/
def explicitCertifiedMatchingGain {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) : ℚ :=
  greedyCertifiedMatchingGain (explicitCertifiedRowWeight X) explicitGamma

theorem explicitCertifiedMatchingGain_nonneg {n : ℕ}
    (X : Matrix (Fin n) (Fin n) ℚ) :
    0 ≤ explicitCertifiedMatchingGain X := by
  rw [explicitCertifiedMatchingGain, greedyCertifiedMatchingGain]
  exact Finset.sum_nonneg fun q _ ↦
    certifiedConstantRowWeight_nonneg _ _ _ _ _ q explicitGamma_pos.le

/-- The complete structural certificate for a rational exact KKT point.
The structural clean-cycle test uses `0.9 * explicitKappa`; the executable
directed test uses `explicitKappa`, and their gap absorbs all logarithm
rounding error. -/
theorem explicitCertified_certificate_of_logKKT
    (stableCoefficient : AnariOveisGharanStableCoefficient.{0})
    {n : ℕ} (hn : 2 ≤ n)
    {A : Matrix (Fin n) (Fin n) ℝ}
    {Xq : Matrix (Fin n) (Fin n) ℚ}
    (hA : Matrix.Positive A)
    (hX : IsDoublyStochastic (fun i j ↦ ((Xq i j : ℚ) : ℝ)))
    (hXint : ∀ i, IsInteriorProbabilityVector
      (fun j ↦ ((Xq i j : ℚ) : ℝ)))
    {R C : Fin n → ℝ}
    (hKKT : HasLogKKT (explicitRegularizationScale n : ℝ) A
      (fun i j ↦ ((Xq i j : ℚ) : ℝ)) R C) :
    Real.exp (betheObjective A (fun i j ↦ ((Xq i j : ℚ) : ℝ)) +
        (explicitCertifiedMatchingGain Xq : ℝ)) ≤
        Matrix.permanent A ∧
      Real.log (Matrix.permanent A) -
          (betheObjective A (fun i j ↦ ((Xq i j : ℚ) : ℝ)) +
            (explicitCertifiedMatchingGain Xq : ℝ)) ≤
        (Real.log 2 / 2 -
          ((rationalEpsilonPlus explicitCertifiedCompletionScales : ℚ) : ℝ)) * n := by
  let X : Matrix (Fin n) (Fin n) ℝ :=
    fun i j ↦ ((Xq i j : ℚ) : ℝ)
  let τq : ℚ := explicitRegularizationScale n
  let gain : ℝ := (explicitCertifiedMatchingGain Xq : ℝ)
  let η : ℝ := (explicitEta : ℝ)
  let δ : ℝ := (explicitDelta : ℝ)
  let ξ : ℝ := (explicitXi : ℝ)
  have hnpos : 0 < n := by omega
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : Real.log n ≤ (n : ℝ) * Real.log 2 :=
    log_natCast_le_natCast_mul_log_two (show 1 ≤ n by omega)
  have hξ : 0 < ξ := by
    simpa only [ξ] using! (show (0 : ℝ) < (explicitXi : ℝ) by
      exact_mod_cast explicitXi_pos)
  have hτscale : (τq : ℝ) = ξ / (4 * (n : ℝ)) := by
    exact cast_explicitRegularizationScale n
  have hτ0q : 0 ≤ τq := (explicitRegularizationScale_pos hnpos).le
  have hτ1q : τq ≤ 1 :=
    explicitRegularizationScale_le_one (show 1 ≤ n by omega)
  have hmax : ∀ Y, IsDoublyStochastic Y →
      regularizedBetheObjective (τq : ℝ) A Y ≤
        regularizedBetheObjective (τq : ℝ) A X := by
    exact regularizedBetheObjective_le_of_logKKT
      (by simpa only [Fintype.card_fin] using! (show 1 < n by omega))
      (by exact_mod_cast hτ0q) hX hXint hKKT
  have hobjective :
      Real.log (bethePermanent A) - ξ * n ≤ betheObjective A X := by
    have hbudget := regularization_budget_of_paper_scale
      (show (0 : ℝ) < n by positivity) hlogn hξ hτscale
    have hvalue := betheLogValue_le_regularizedMaximizer
      (show 1 < n by omega) (by exact_mod_cast hτ0q) hA hX hmax
    have hmatch := positiveMatrix_hasPerfectMatching hA
    have hlogBethe : Real.log (bethePermanent A) = betheLogValue A := by
      rw [bethePermanent, ite_eq_left hmatch, Real.log_exp]
    rw [hlogBethe]
    linarith
  have hmatch := positiveMatrix_hasPerfectMatching hA
  have hlogBethe : Real.log (bethePermanent A) = betheLogValue A := by
    rw [bethePermanent, ite_eq_left hmatch, Real.log_exp]
  have hupper : Real.log (Matrix.permanent A) ≤
      Real.log (bethePermanent A) + n * (Real.log 2 / 2) := by
    rw [hlogBethe]
    exact log_permanent_le_betheLogValue_add_log_two_half hn A hA
  let w : RowPair n → ℚ := explicitCertifiedRowWeight Xq
  have hlower : ∀ q ∈ greedyThresholdRowMatching w explicitGamma,
      (w q : ℝ) ≤ Real.log (pairGain A X
        (rowPairRow q 0) (rowPairRow q 1)) := by
    intro q hq
    have hmaximal := greedyThresholdRowMatching_isMaximal w explicitGamma
    have hthreshold : explicitGamma ≤ w q := by
      have hmem := hmaximal.subset hq
      simpa only [List.mem_toFinset, mem_thresholdRowPairsList_iff] using! hmem
    have hw : w q = explicitGamma := by
      exact certifiedConstantRowWeight_eq_gamma_of_threshold
        τq Xq explicitKappa explicitGamma (directedPairCostPrecision n) q
          explicitGamma_pos hthreshold
    have heligible : HasCertifiedCorePair τq Xq explicitKappa
        (directedPairCostPrecision n) q := by
      exact (certifiedConstantRowWeight_eq_gamma_iff
        τq Xq explicitKappa explicitGamma (directedPairCostPrecision n) q
          explicitGamma_pos.ne').1 hw
    rw [hw]
    exact certifiedConstantRowWeight_le_log_pairGain
      explicit_cleanPairGain_constants hnreal hlogn hξ
      (by
        have hq := explicitCertifiedCompletionScales.ξ_le_source
        have hr : ((explicitXi : ℚ) : ℝ) ≤
            ((explicitXiSource : ℚ) : ℝ) := by
          exact_mod_cast hq
        simpa only [ξ] using! hr)
      hτscale hA hX hXint hKKT (by norm_num) (by norm_num)
      (directedPairCostPrecision n) q heligible
  have hcertificate : Real.exp (betheObjective A X + gain) ≤
      Matrix.permanent A := by
    exact exp_betheObjective_add_greedyCertifiedMatchingGain_le_permanent
      stableCoefficient w explicitGamma_pos hlower hn hA hX
        (fun i j ↦ (hXint i).2 j |>.1)
  have hnearGain : betheSlack n (Real.log (bethePermanent A))
      (Real.log (Matrix.permanent A)) < δ * n →
      3 * (explicitCertifiedGamma : ℝ) / 8 * n ≤ gain := by
    intro hnear
    rw [hlogBethe] at hnear
    have h := nearCase_greedyCertifiedMatchingGain_ge_threeSixteenths
      anariRezaeiRowInequality hn
      (by exact_mod_cast explicitCertifiedStructuralKappa_pos)
      hnreal hlogn hξ hτscale hτ0q hτ1q explicitGamma_pos.le
      (by exact_mod_cast explicitEta_pos)
      explicitCertifiedCompletionScales.η_le_tenth
      explicitCertifiedCompletionScales.row_small
      explicitCertifiedCompletionScales.cycle_small
      explicitCertifiedCompletionScales.transfer_small
      hA hX hXint hKKT hnear (directedPairCostPrecision n)
      (explicitCertifiedCostMargin n)
    change 3 * (explicitCertifiedGamma : ℝ) / 8 * n ≤
      (explicitCertifiedMatchingGain Xq : ℝ)
    norm_num [explicitCertifiedGamma, explicitGamma] at h ⊢
    exact h
  have hcases := completionCaseDisjunction
    (logPermanent := Real.log (Matrix.permanent A))
    (logBethe := Real.log (bethePermanent A))
    (objective := betheObjective A X) (gain := gain)
    (δ := δ) (ξ := ξ) (γ := (explicitCertifiedGamma : ℝ))
    hobjective (by
      change 0 ≤ (explicitCertifiedMatchingGain Xq : ℝ)
      exact_mod_cast explicitCertifiedMatchingGain_nonneg Xq)
    hupper hnearGain
  have hgap := positiveDichotomy_exponent hcases
  have hεcast := cast_rationalEpsilonPlus explicitCertifiedCompletionScales
  constructor
  · simpa only [X, gain] using! hcertificate
  · simpa only [X, gain, η, δ, ξ, hεcast] using! hgap

end BeyondBethe
