/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/

import LeanPool.BeyondBethe.BeyondBethe.ExplicitBounds
import LeanPool.BeyondBethe.BeyondBethe.CertifiedPairWeights
import LeanPool.BeyondBethe.BeyondBethe.NumericalScales
import Mathlib.Tactic

/-! # Explicit Scales -/

namespace BeyondBethe

/-!
# Hard-coded rational structural scales

This file replaces the remaining density and continuity choices in the
structural proof by one fixed tuple of rationals.
-/

def explicitEta : ℚ := 1 / 10 ^ 12

def explicitRowRatio : ℚ := 1 / 200000

def explicitDelta : ℚ :=
  (explicitEta / 3074) ^ 4 * explicitRowRatio

def explicitXi : ℚ := explicitDelta / 100

/-- The greedy threshold matching retains one quarter of the structural
matching gain: one half from directed thresholding and one half from
maximal-versus-maximum cardinality. -/
def explicitGreedyGamma : ℚ := explicitGamma / 4

/-- The structural clean-cycle threshold leaves a fixed gap below the cost
threshold used by the directed rational certificate. -/
def explicitCertifiedStructuralKappa : ℚ := 9 * explicitKappa / 10

/-- A maximal matching loses only a factor two because every accepted edge
receives the exact same certified gain. -/
def explicitCertifiedGamma : ℚ := explicitGamma / 2

theorem explicitEta_pos : 0 < explicitEta := by
  norm_num [explicitEta]

theorem explicitRowRatio_pos : 0 < explicitRowRatio := by
  norm_num [explicitRowRatio]

theorem explicitDelta_pos : 0 < explicitDelta := by
  rw [explicitDelta]
  exact mul_pos (pow_pos (div_pos explicitEta_pos (by norm_num)) _) explicitRowRatio_pos

theorem explicitXi_pos : 0 < explicitXi := by
  rw [explicitXi]
  exact div_pos explicitDelta_pos (by norm_num)

theorem explicitCertifiedStructuralKappa_pos :
    0 < explicitCertifiedStructuralKappa := by
  norm_num [explicitCertifiedStructuralKappa, explicitKappa]

theorem explicitCertifiedGamma_pos : 0 < explicitCertifiedGamma := by
  norm_num [explicitCertifiedGamma, explicitGamma]

theorem sqrt_explicitEta :
    Real.sqrt ((explicitEta : ℚ) : ℝ) = 1 / 10 ^ 6 := by
  have heq : (((explicitEta : ℚ) : ℝ)) = (1 / 10 ^ 6 : ℝ) ^ 2 := by
    norm_num [explicitEta]
  rw [heq, Real.sqrt_sq (by positivity)]

theorem explicitEta_entropy_bound :
    binaryEntropy ((explicitEta : ℚ) : ℝ) + (explicitEta : ℝ) ≤
      3 / 10 ^ 6 := by
  let η : ℝ := (explicitEta : ℚ)
  have hη0 : 0 ≤ η := by
    change 0 ≤ ((explicitEta : ℚ) : ℝ)
    exact_mod_cast explicitEta_pos.le
  have hη1 : η ≤ 1 := by norm_num [η, explicitEta]
  have hnmlηabs := abs_negMulLog_lt_two_sqrt_abs
    (x := η) (by simpa [abs_of_nonneg hη0] using hη1)
  have hnmlη : Real.negMulLog η ≤ 2 * Real.sqrt η :=
    (le_abs_self _).trans (by simpa [abs_of_nonneg hη0] using hnmlηabs)
  have hnmlone : Real.negMulLog (1 - η) ≤ η := by
    have := Real.negMulLog_le_one_sub_self (sub_nonneg.mpr hη1)
    linarith
  rw [binaryEntropy, Real.negMulLog_def]
  change Real.negMulLog η + Real.negMulLog (1 - η) + η ≤ 3 / 10 ^ 6
  rw [show Real.sqrt η = 1 / 10 ^ 6 by
    simpa only [η] using sqrt_explicitEta] at hnmlη
  norm_num [η, explicitEta] at *
  linarith

theorem explicitOmega_bound :
    goodRowOmega ((explicitEta : ℚ) : ℝ) ≤ 70 / 10 ^ 6 := by
  have h := goodRowOmega_le_seventy_sqrt
    (η := ((explicitEta : ℚ) : ℝ))
    (by exact_mod_cast explicitEta_pos.le) (by norm_num [explicitEta])
  rw [sqrt_explicitEta] at h
  norm_num at h ⊢
  exact h

theorem explicitDelta_ratio :
    ((explicitDelta : ℚ) : ℝ) /
        (((explicitEta : ℚ) : ℝ) / 3074) ^ 4 =
      (explicitRowRatio : ℝ) := by
  have hbase : (((explicitEta : ℚ) : ℝ) / 3074) ^ 4 ≠ 0 := by
    exact pow_ne_zero _ (div_ne_zero (by exact_mod_cast explicitEta_pos.ne') (by norm_num))
  rw [explicitDelta]
  norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]
  exact mul_div_cancel_left₀ _ hbase

theorem explicitDelta_le_rowRatio :
    ((explicitDelta : ℚ) : ℝ) ≤ (explicitRowRatio : ℝ) := by
  have heta : (((explicitEta : ℚ) : ℝ) / 3074) ^ 4 ≤ 1 := by
    have hbase : (0 : ℝ) ≤ ((explicitEta : ℚ) : ℝ) / 3074 := by
      exact div_nonneg (by exact_mod_cast explicitEta_pos.le) (by norm_num)
    have hbase1 : ((explicitEta : ℚ) : ℝ) / 3074 ≤ 1 := by
      norm_num [explicitEta]
    exact pow_le_one₀ hbase hbase1
  rw [explicitDelta]
  norm_num only [Rat.cast_mul, Rat.cast_pow, Rat.cast_div, Rat.cast_ofNat]
  exact mul_le_of_le_one_left (by exact_mod_cast explicitRowRatio_pos.le) heta

def explicit_completionScales :
    RationalCompletionScales explicitKappa explicitXiSource explicitGamma := by
  have hlog0 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hcoef : 6 / Real.log 2 ≤ 10 := by
    rw [div_le_iff₀ hlog0]
    have := Real.log_two_gt_d9
    norm_num at *
    linarith
  have hδr := explicitDelta_le_rowRatio
  have hω := explicitOmega_bound
  have hηH := explicitEta_entropy_bound
  have hr : ((explicitRowRatio : ℚ) : ℝ) = 1 / 200000 := by
    norm_num [explicitRowRatio]
  have hδsmall : ((explicitDelta : ℚ) : ℝ) ≤ 1 / 200000 := by
    rw [← hr]
    exact hδr
  have hξδ : explicitXi < explicitDelta := by
    rw [explicitXi]
    have := explicitDelta_pos
    norm_num at *
    exact div_lt_self this (by norm_num)
  refine {
    η := explicitEta
    δ := explicitDelta
    ξ := explicitXi
    η_pos := explicitEta_pos
    η_le_tenth := by norm_num [explicitEta]
    δ_pos := explicitDelta_pos
    ξ_pos := explicitXi_pos
    ξ_le_source := by
      have hδcast : ((explicitDelta : ℚ) : ℝ) < 1 :=
        hδsmall.trans_lt (by norm_num)
      have hδ : explicitDelta < 1 := by exact_mod_cast hδcast
      rw [explicitXi, explicitXiSource]
      exact (div_lt_div_of_pos_right hδ (by norm_num)).le
    row_small := by
      rw [explicitDelta_ratio]
      norm_num [explicitRowRatio]
    cycle_small := by
      rw [explicitDelta_ratio]
      have hmid : (1 + Real.log 2 / 2) *
          ((explicitRowRatio : ℚ) : ℝ) ≤
          (3 / 2 : ℝ) * (1 / 200000) := by
        rw [hr]
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        linarith
      have hsum :
          ((explicitDelta : ℚ) : ℝ) +
              (1 + Real.log 2 / 2) * (explicitRowRatio : ℝ) +
              goodRowOmega ((explicitEta : ℚ) : ℝ) ≤
            (1 / 200000 : ℝ) + (3 / 2) * (1 / 200000) + 70 / 10 ^ 6 :=
        add_le_add (add_le_add hδsmall hmid) hω
      have hsum0 : 0 ≤
          ((explicitDelta : ℚ) : ℝ) +
            (1 + Real.log 2 / 2) * (explicitRowRatio : ℝ) +
            goodRowOmega ((explicitEta : ℚ) : ℝ) := by
        exact add_nonneg
          (add_nonneg (by exact_mod_cast explicitDelta_pos.le)
            (mul_nonneg (by positivity)
              (by exact_mod_cast explicitRowRatio_pos.le)))
          (goodRowOmega_nonneg _)
      calc
        6 / Real.log 2 *
            (((explicitDelta : ℚ) : ℝ) +
              (1 + Real.log 2 / 2) * (explicitRowRatio : ℝ) +
              goodRowOmega ((explicitEta : ℚ) : ℝ)) ≤
            10 * ((1 / 200000 : ℝ) +
              (3 / 2) * (1 / 200000) + 70 / 10 ^ 6) := by
          exact mul_le_mul hcoef hsum hsum0 (by positivity)
        _ ≤ 1 / 16 := by norm_num
    transfer_small := by
      rw [explicitDelta_ratio]
      have hxi : 2 * ((explicitXi : ℚ) : ℝ) ≤ 1 / 200000 := by
        have hcast : ((explicitXi : ℚ) : ℝ) < ((explicitDelta : ℚ) : ℝ) := by
          exact_mod_cast hξδ
        have hδ0 : 0 ≤ ((explicitDelta : ℚ) : ℝ) := by
          exact_mod_cast explicitDelta_pos.le
        rw [explicitXi]
        norm_num only [Rat.cast_div, Rat.cast_ofNat]
        nlinarith
      have hleft :
          ((explicitDelta : ℚ) : ℝ) + 2 * ((explicitXi : ℚ) : ℝ) +
              binaryEntropy ((explicitEta : ℚ) : ℝ) +
              ((explicitEta : ℚ) : ℝ) +
              (1 + Real.log 2) * ((explicitRowRatio : ℚ) : ℝ) ≤
            23 / 10 ^ 6 := by
        calc
          _ ≤ (1 / 200000 : ℝ) + 1 / 200000 + 3 / 10 ^ 6 +
              2 * (1 / 200000) := by
            have hlast : (1 + Real.log 2) *
                ((explicitRowRatio : ℚ) : ℝ) ≤ 2 * (1 / 200000 : ℝ) := by
              rw [hr]
              gcongr
              linarith
            linarith
          _ = 23 / 10 ^ 6 := by norm_num
      have hright : (1 / 40000 : ℝ) ≤
          (1 / 16) * ((1 / 2 - ((explicitEta : ℚ) : ℝ)) *
            ((explicitKappa : ℚ) : ℝ)) := by
        norm_num [explicitEta, explicitKappa]
      exact (hleft.trans (by norm_num : (23 / 10 ^ 6 : ℝ) ≤ 1 / 40000)).trans hright
    ξ_lt_δ := hξδ
    ξ_lt_gain := by
      have hδsmallQ : explicitDelta ≤ 1 / 200000 := by
        have hcast : ((explicitDelta : ℚ) : ℝ) ≤ (((1 / 200000 : ℚ)) : ℝ) := by
          simpa using hδsmall
        exact_mod_cast hcast
      rw [explicitGamma]
      calc
        explicitXi < explicitDelta := hξδ
        _ ≤ 1 / 200000 := hδsmallQ
        _ < 3 * (1 / 4) / 8 := by norm_num }

/-- Numerical upper bound on the left side of the transfer-smallness
condition.  It is recorded separately so the same analytic estimate can be
used with the slightly smaller structural cost threshold. -/
theorem explicitTransferExpression_le :
    ((explicitDelta : ℚ) : ℝ) + 2 * ((explicitXi : ℚ) : ℝ) +
        binaryEntropy ((explicitEta : ℚ) : ℝ) +
        ((explicitEta : ℚ) : ℝ) +
        (1 + Real.log 2) *
          (((explicitDelta : ℚ) : ℝ) /
            (((explicitEta : ℚ) : ℝ) / 3074) ^ 4) ≤
      23 / 10 ^ 6 := by
  rw [explicitDelta_ratio]
  have hlog1 : Real.log 2 ≤ 1 := Real.log_two_lt_d9.le.trans (by norm_num)
  have hδsmall := explicitDelta_le_rowRatio
  have hηH := explicitEta_entropy_bound
  have hr : ((explicitRowRatio : ℚ) : ℝ) = 1 / 200000 := by
    norm_num [explicitRowRatio]
  have hδ : ((explicitDelta : ℚ) : ℝ) ≤ 1 / 200000 := by
    rw [← hr]
    exact hδsmall
  have hxi : 2 * ((explicitXi : ℚ) : ℝ) ≤ 1 / 200000 := by
    rw [explicitXi]
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hδ0 : 0 ≤ ((explicitDelta : ℚ) : ℝ) := by
      exact_mod_cast explicitDelta_pos.le
    nlinarith
  have hlast : (1 + Real.log 2) *
      ((explicitRowRatio : ℚ) : ℝ) ≤ 2 * (1 / 200000 : ℝ) := by
    rw [hr]
    gcongr
    linarith
  linarith

/-- Completion scales for the actual executable certificate.  The clean
cycle analysis uses `0.9 κ`, the directed test uses `κ`, and the greedy
matching retains half of the uniform gain. -/
def explicitCertifiedCompletionScales :
    RationalCompletionScales explicitCertifiedStructuralKappa
      explicitXiSource explicitCertifiedGamma := by
  refine { explicit_completionScales with
    transfer_small := ?_
    ξ_lt_gain := ?_ }
  · have hleft := explicitTransferExpression_le
    have hright : (23 / 10 ^ 6 : ℝ) ≤
        (1 / 16) *
          ((1 / 2 - ((explicitEta : ℚ) : ℝ)) *
            ((explicitCertifiedStructuralKappa : ℚ) : ℝ)) := by
      norm_num [explicitEta, explicitCertifiedStructuralKappa, explicitKappa]
    exact hleft.trans hright
  · have hδsmall : explicitDelta ≤ 1 / 200000 := by
      have hcast := explicitDelta_le_rowRatio
      have hr : ((explicitRowRatio : ℚ) : ℝ) = 1 / 200000 := by
        norm_num [explicitRowRatio]
      rw [hr] at hcast
      have hcast' : ((explicitDelta : ℚ) : ℝ) ≤
          (((1 / 200000 : ℚ)) : ℝ) := by
        norm_num only [Rat.cast_div, Rat.cast_ofNat]
        exact hcast
      exact Rat.cast_le.mp hcast'
    change explicitXi < 3 * explicitCertifiedGamma / 8
    rw [explicitXi, explicitCertifiedGamma, explicitGamma]
    calc
      explicitDelta / 100 < explicitDelta := by
        exact div_lt_self explicitDelta_pos (by norm_num)
      _ ≤ 1 / 200000 := hδsmall
      _ < 3 * ((1 / 4) / 2) / 8 := by norm_num

theorem explicitCertifiedCostMargin (n : ℕ) :
    4 * (n + 3 : ℝ) *
        ((1 / 2 : ℚ) ^ directedPairCostPrecision n : ℚ) ≤
      (explicitKappa : ℝ) -
        (explicitCertifiedStructuralKappa : ℝ) := by
  have h := directedPairCostPrecision_error_le n
  norm_num [explicitKappa, explicitCertifiedStructuralKappa] at h ⊢
  exact h

/-- The far case is the active branch of the explicit improvement: the
near-case gain margin is vastly larger than the chosen slack scale. -/
theorem explicitCertifiedEpsilon_eq :
    rationalEpsilonPlus explicitCertifiedCompletionScales =
      explicitDelta - explicitXi := by
  rw [rationalEpsilonPlus]
  change min (explicitDelta - explicitXi)
    (3 * explicitCertifiedGamma / 8 - explicitXi) =
      explicitDelta - explicitXi
  rw [min_eq_left]
  have hδsmall : explicitDelta ≤ 1 / 200000 := by
    have hcast := explicitDelta_le_rowRatio
    have hr : ((explicitRowRatio : ℚ) : ℝ) = 1 / 200000 := by
      norm_num [explicitRowRatio]
    rw [hr] at hcast
    have hcast' : ((explicitDelta : ℚ) : ℝ) ≤
        (((1 / 200000 : ℚ)) : ℝ) := by
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      exact hcast
    exact Rat.cast_le.mp hcast'
  have hmain : explicitDelta ≤ 3 * explicitCertifiedGamma / 8 := by
    exact hδsmall.trans (by
      norm_num [explicitCertifiedGamma, explicitGamma])
  linarith

def explicitCertifiedEpsilon : ℚ :=
  rationalEpsilonPlus explicitCertifiedCompletionScales

theorem explicitCertifiedEpsilon_pos : 0 < explicitCertifiedEpsilon := by
  exact rationalEpsilonPlus_pos explicitCertifiedCompletionScales

def explicitStructuralScales : RationalStructuralScales where
  κ₀ := explicitKappa
  ξ₀ := explicitXiSource
  γ₀ := explicitGamma
  κ₀_pos := explicitKappa_pos
  ξ₀_pos := by norm_num [explicitXiSource]
  γ₀_pos := by norm_num [explicitGamma]
  cleanGain := explicit_cleanPairGain_constants
  completion := explicit_completionScales

theorem cleanPairGainGuarantee_mono_gamma
    {κ ξ γ γ' : ℝ} (h : CleanPairGainGuarantee κ ξ γ)
    (hγ : γ' ≤ γ) : CleanPairGainGuarantee κ ξ γ' := by
  intro n ell ξ' τ A X rscale cscale hell hlog hξ hξsource hτ hA hX
    hXint hr hc hKKT r s a b hrs hab hcost
  exact hγ.trans (h hell hlog hξ hξsource hτ hA hX hXint hr hc hKKT
    hrs hab hcost)

theorem explicitGreedyGamma_pos : 0 < explicitGreedyGamma := by
  norm_num [explicitGreedyGamma, explicitGamma]

def explicitGreedyCompletionScales :
    RationalCompletionScales explicitKappa explicitXiSource
      explicitGreedyGamma :=
  { explicit_completionScales with
    ξ_lt_gain := by
      have hδsmall : explicitDelta ≤ 1 / 200000 := by
        have h := explicitDelta_le_rowRatio
        have hr : ((explicitRowRatio : ℚ) : ℝ) = 1 / 200000 := by
          norm_num [explicitRowRatio]
        rw [hr] at h
        have h' : ((explicitDelta : ℚ) : ℝ) ≤ (((1 / 200000 : ℚ)) : ℝ) := by
          simpa using h
        exact_mod_cast h'
      change explicitXi < 3 * explicitGreedyGamma / 8
      rw [explicitXi, explicitGreedyGamma, explicitGamma]
      calc
        explicitDelta / 100 < explicitDelta := by
          exact div_lt_self explicitDelta_pos (by norm_num)
        _ ≤ 1 / 200000 := hδsmall
        _ < 3 * ((1 / 4) / 4) / 8 := by norm_num }

/-- Structural data weakened exactly by the constant-factor loss of the
greedy implementation.  All analytic inequalities and hard-coded scales are
unchanged. -/
def explicitGreedyStructuralScales : RationalStructuralScales where
  κ₀ := explicitKappa
  ξ₀ := explicitXiSource
  γ₀ := explicitGreedyGamma
  κ₀_pos := explicitKappa_pos
  ξ₀_pos := by norm_num [explicitXiSource]
  γ₀_pos := explicitGreedyGamma_pos
  cleanGain := cleanPairGainGuarantee_mono_gamma
    explicit_cleanPairGain_constants (by
      norm_num [explicitGreedyGamma, explicitGamma])
  completion := explicitGreedyCompletionScales

end BeyondBethe
