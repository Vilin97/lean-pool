/-
Copyright (c) 2026 Lior Pachter. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lior Pachter
-/

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.OfFn
import LeanPool.PebblingLean.Concentration
import LeanPool.PebblingLean.UpperBoundDelivery

/-!
# Finite probability setup for the upper bound

This file defines the exact finite sample spaces used in the probabilistic
upper-bound argument.  It also records the interfaces for the Chernoff and
Bernstein inputs.  These are propositions, not axioms: later work must prove
them or replace them with imported theorems.
-/

namespace PebblingLean

namespace Hypercube

open Pebbling
open FiniteProbability

/-- A sample of `N` independent uniform centers in `Q_n`, represented as a
function on `Fin N`. -/
abbrev CenterSample (n N : ℕ) := Fin N → HypercubeVertex n

/-- Convert a center sample into the list used by the deterministic stack
construction. -/
def CenterSample.toList {n N : ℕ} (sample : CenterSample n N) :
    List (HypercubeVertex n) :=
  List.ofFn sample

/-- Total annulus contribution of a sampled `N`-tuple to a fixed target. -/
def sampleTotalContribution {n N : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) (sample : CenterSample n N) : ℕ :=
  ∑ j : Fin N, annulusContribution rIn rOut target (sample j)

theorem annulusTotalContribution_toList {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) (sample : CenterSample n N) :
    annulusTotalContribution rIn rOut target sample.toList =
      sampleTotalContribution rIn rOut target sample := by
  simpa [CenterSample.toList, annulusTotalContribution, sampleTotalContribution,
    List.ofFn_comp'] using
      (Fin.sum_ofFn fun j : Fin N => annulusContribution rIn rOut target (sample j))

theorem card_centerSample (n N : ℕ) :
    Fintype.card (CenterSample n N) = (2 ^ n) ^ N := by
  simp [CenterSample]

/-- Exact expectation of one random annulus contribution. -/
noncomputable def oneCenterContributionExpectation {n : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  uniformExpectation fun center : HypercubeVertex n =>
    annulusContribution rIn rOut target center

/-- Real-valued version of the one-center annulus contribution expectation. -/
noncomputable def oneCenterContributionExpectationReal {n : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℝ :=
  uniformExpectationReal fun center : HypercubeVertex n =>
    (annulusContribution rIn rOut target center : ℝ)

/-- Exact second moment of one random annulus contribution. -/
noncomputable def oneCenterContributionSecondMoment {n : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  uniformExpectation fun center : HypercubeVertex n =>
    (annulusContribution rIn rOut target center) ^ 2

theorem oneCenterContributionExpectation_eq_sum {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionExpectation rIn rOut target =
      (∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℚ)) / (2 ^ n : ℚ) := by
  simp [oneCenterContributionExpectation, uniformExpectation]

theorem oneCenterContributionExpectationReal_eq_sum {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionExpectationReal rIn rOut target =
      (∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℝ)) / (2 ^ n : ℝ) := by
  simp [oneCenterContributionExpectationReal, uniformExpectationReal]

theorem oneCenterContributionSecondMoment_eq_sum {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionSecondMoment rIn rOut target =
      (∑ center : HypercubeVertex n,
          ((annulusContribution rIn rOut target center) ^ 2 : ℚ)) /
        (2 ^ n : ℚ) := by
  simp [oneCenterContributionSecondMoment, uniformExpectation]

/-- Expectation-level version of `Z^2 ≤ B_0 Z` for one random annulus
contribution. -/
theorem oneCenterContributionSecondMoment_le_width_mul_expectation {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionSecondMoment rIn rOut target ≤
      (2 ^ (rOut - rIn) : ℚ) * oneCenterContributionExpectation rIn rOut target := by
  classical
  rw [oneCenterContributionSecondMoment_eq_sum, oneCenterContributionExpectation_eq_sum]
  have hden_pos : 0 < (2 ^ n : ℚ) := by positivity
  have hsum :
      (∑ center : HypercubeVertex n,
          ((annulusContribution rIn rOut target center) ^ 2 : ℚ)) ≤
        (2 ^ (rOut - rIn) : ℚ) *
          ∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℚ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun center _hcenter => by
      exact_mod_cast
        annulusContribution_sq_le_width_mul
          (rIn := rIn) (rOut := rOut) target center
  calc
    (∑ center : HypercubeVertex n,
        ((annulusContribution rIn rOut target center) ^ 2 : ℚ)) / (2 ^ n : ℚ)
        ≤ ((2 ^ (rOut - rIn) : ℚ) *
          ∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℚ)) / (2 ^ n : ℚ) := by
          exact div_le_div_of_nonneg_right hsum hden_pos.le
    _ = (2 ^ (rOut - rIn) : ℚ) *
        ((∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℚ)) / (2 ^ n : ℚ)) := by
          ring

/-- Cardinality of a Hamming sphere, written as a filtered finite sum. -/
theorem card_filter_dist_eq {n i : ℕ} (target : HypercubeVertex n) :
    (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i).card =
      Nat.choose n i := by
  classical
  have hsubtype :
      Fintype.card {center : HypercubeVertex n // dist target center = i} =
        (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i).card := by
    simpa using
      (Fintype.card_subtype fun center : HypercubeVertex n => dist target center = i)
  rw [← hsubtype, card_sphere]

/-- Sum of the annulus contribution over one Hamming sphere. -/
theorem sum_filter_dist_eq_annulusContribution {n rIn rOut i : ℕ}
    (target : HypercubeVertex n) :
    (∑ center ∈
        (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i),
        annulusContribution rIn rOut target center) =
      Nat.choose n i *
        if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 := by
  classical
  let sphere : Finset (HypercubeVertex n) :=
    Finset.univ.filter fun center : HypercubeVertex n => dist target center = i
  let contributionAtDistance : ℕ :=
    if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0
  have hconst :
      ∀ center ∈ sphere,
        annulusContribution rIn rOut target center = contributionAtDistance := by
    intro center hcenter
    have hdist_target : dist target center = i := by
      simpa [sphere] using (Finset.mem_filter.mp hcenter).2
    have hdist_center : dist center target = i := by
      simpa [dist_comm center target] using hdist_target
    by_cases hbounds : rIn ≤ i ∧ i ≤ rOut
    · simp [annulusContribution, contributionAtDistance, hdist_center, hbounds]
    · have hnot_bounds :
          ¬ (rIn ≤ dist center target ∧ dist center target ≤ rOut) := by
        simpa [hdist_center] using hbounds
      simp [annulusContribution, contributionAtDistance, hnot_bounds, hbounds]
  have hcard : sphere.card = Nat.choose n i := by
    simpa [sphere] using card_filter_dist_eq (n := n) (i := i) target
  calc
    (∑ center ∈
        (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i),
        annulusContribution rIn rOut target center)
        = ∑ center ∈ sphere, annulusContribution rIn rOut target center := by
          rfl
    _ = ∑ _center ∈ sphere, contributionAtDistance := by
          exact Finset.sum_congr rfl hconst
    _ = sphere.card * contributionAtDistance := by
          simp [Finset.sum_const]
    _ = Nat.choose n i *
        if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 := by
          simp [hcard, contributionAtDistance]

/-- Exact one-center annulus contribution, grouped by Hamming distance. -/
theorem sum_annulusContribution_eq_sum_range {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    (∑ center : HypercubeVertex n, annulusContribution rIn rOut target center) =
      ∑ i ∈ Finset.range (n + 1),
        Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 := by
  classical
  have hmaps :
      ∀ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
        dist target center ∈ Finset.range (n + 1) := by
    intro center _hcenter
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (dist_le target center))
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (HypercubeVertex n)))
      (t := Finset.range (n + 1))
      (g := fun center : HypercubeVertex n => dist target center)
      hmaps
      (fun center : HypercubeVertex n => annulusContribution rIn rOut target center))
  calc
    (∑ center : HypercubeVertex n, annulusContribution rIn rOut target center)
        = ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
            annulusContribution rIn rOut target center := by
          rfl
    _ = ∑ i ∈ Finset.range (n + 1),
        ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)) with dist target center = i,
          annulusContribution rIn rOut target center := by
          exact hfiber.symm
    _ = ∑ i ∈ Finset.range (n + 1),
        Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simpa using
            sum_filter_dist_eq_annulusContribution
              (n := n) (rIn := rIn) (rOut := rOut) (i := i) target

/-- Exact one-center expectation as a binomial sphere sum. -/
theorem oneCenterContributionExpectation_eq_distance_sum {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionExpectation rIn rOut target =
      ((∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i *
            if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ)) : ℚ) /
        (2 ^ n : ℚ) := by
  rw [oneCenterContributionExpectation_eq_sum]
  have hsum :=
    congrArg (fun x : ℕ => (x : ℚ))
      (sum_annulusContribution_eq_sum_range
        (n := n) (rIn := rIn) (rOut := rOut) target)
  simpa [Nat.cast_sum] using congrArg (fun q : ℚ => q / (2 ^ n : ℚ)) hsum

/-- Numerator of the expected contribution of one random stack.  This is
target-independent by symmetry of the cube. -/
def annulusMeanNumerator (n rIn rOut : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (n + 1),
    Nat.choose n i *
      if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0

/-- Expected contribution of one uniformly random annulus center. -/
noncomputable def annulusMean (n rIn rOut : ℕ) : ℚ :=
  (annulusMeanNumerator n rIn rOut : ℚ) / (2 ^ n : ℚ)

theorem annulusMean_nonneg (n rIn rOut : ℕ) :
    0 ≤ (annulusMean n rIn rOut : ℝ) := by
  unfold annulusMean annulusMeanNumerator
  positivity

/-- Binomial evaluation of the full weighted Hamming-sphere sum. -/
theorem weightedSphereSum_half_eq (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * ((1 : ℝ) / 2) ^ i) =
      ((3 : ℝ) / 2) ^ n := by
  have h := add_pow ((1 : ℝ) / 2) (1 : ℝ) n
  calc
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℝ) * ((1 : ℝ) / 2) ^ i)
        = ∑ i ∈ Finset.range (n + 1),
            ((1 : ℝ) / 2) ^ i * 1 ^ (n - i) * (Nat.choose n i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          ring
    _ = (((1 : ℝ) / 2) + 1) ^ n := h.symm
    _ = ((3 : ℝ) / 2) ^ n := by norm_num

theorem pow_two_sub_eq_mul_half_pow {rOut i : ℕ} (hi : i ≤ rOut) :
    (2 ^ (rOut - i) : ℝ) = (2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i := by
  have hpow : (2 : ℝ) ^ rOut = (2 : ℝ) ^ (rOut - i) * (2 : ℝ) ^ i := by
    rw [← pow_add]
    congr
    omega
  calc
    (2 ^ (rOut - i) : ℝ)
        = ((2 : ℝ) ^ (rOut - i) * ((2 : ℝ) ^ i * ((1 : ℝ) / 2) ^ i)) := by
          rw [← mul_pow]
          norm_num
    _ = (((2 : ℝ) ^ (rOut - i) * (2 : ℝ) ^ i) * ((1 : ℝ) / 2) ^ i) := by ring
    _ = (2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i := by rw [← hpow]

theorem annulusMean_eq_real_sum (n rIn rOut : ℕ) :
    (annulusMean n rIn rOut : ℝ) =
      (∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)) /
        (2 ^ n : ℝ) := by
  unfold annulusMean annulusMeanNumerator
  norm_num
  refine Finset.sum_congr rfl ?_
  intro i _hi
  by_cases h : rIn ≤ i ∧ i ≤ rOut <;> simp [h]

/-- Truncating to an annulus can only decrease the full weighted expectation
`2^rOut (3/4)^n`. -/
theorem annulusMean_le_fullWeightedMean (n rIn rOut : ℕ) :
    (annulusMean n rIn rOut : ℝ) ≤
      (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) := by
  classical
  rw [annulusMean_eq_real_sum]
  have hden_pos : 0 < (2 ^ n : ℝ) := by positivity
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ) ≤
        (Nat.choose n i : ℝ) * ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i) := by
    intro i _hi
    by_cases hbounds : rIn ≤ i ∧ i ≤ rOut
    · have hpow : (2 ^ (rOut - i) : ℝ) =
          (2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i :=
        pow_two_sub_eq_mul_half_pow hbounds.2
      calc
        ((Nat.choose n i *
            if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)
            = (Nat.choose n i : ℝ) * (2 ^ (rOut - i) : ℝ) := by
              simp [hbounds]
        _ ≤ (Nat.choose n i : ℝ) *
              ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i) := by
              rw [hpow]
    · calc
        ((Nat.choose n i *
            if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)
            = 0 := by simp [hbounds]
        _ ≤ (Nat.choose n i : ℝ) *
              ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i) := by
              positivity
  have hsum :
      (∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)) ≤
        ∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) * ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i) := by
    exact Finset.sum_le_sum hterm
  have hdiv := div_le_div_of_nonneg_right hsum hden_pos.le
  calc
    (∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)) /
        (2 ^ n : ℝ)
        ≤ (∑ i ∈ Finset.range (n + 1),
          (Nat.choose n i : ℝ) * ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i)) /
            (2 ^ n : ℝ) := hdiv
    _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) := by
      have hsum_rearr :
          (∑ i ∈ Finset.range (n + 1),
              (Nat.choose n i : ℝ) * ((2 ^ rOut : ℝ) * ((1 : ℝ) / 2) ^ i)) =
            (2 ^ rOut : ℝ) *
              (∑ i ∈ Finset.range (n + 1),
                (Nat.choose n i : ℝ) * ((1 : ℝ) / 2) ^ i) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _hi
        ring
      rw [hsum_rearr, weightedSphereSum_half_eq]
      have hratio : (((3 : ℝ) / 2) ^ n) / ((2 : ℝ) ^ n) =
          ((3 : ℝ) / 4) ^ n := by
        rw [← div_pow]
        norm_num
      calc
        ((2 ^ rOut : ℝ) * ((3 : ℝ) / 2) ^ n) / (2 ^ n : ℝ)
            = (2 ^ rOut : ℝ) * ((((3 : ℝ) / 2) ^ n) / ((2 : ℝ) ^ n)) := by
              ring
        _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) := by rw [hratio]

/-- The probability that a `Binomial(n, 1/3)` random variable lies in the
annulus window `[rIn, rOut]`.  This is the normalized form of the weighted
annulus mean. -/
noncomputable def binomialWindowProbThird (n rIn rOut : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if rIn ≤ i ∧ i ≤ rOut then
      (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) * (((2 : ℝ) / 3) ^ (n - i))
    else
      0

/-- Termwise conversion between the annulus contribution weight and the
`Binomial(1/3)` mass after factoring out the full weighted mean
`2^rOut (3/4)^n`. -/
theorem annulusWeightedTerm_eq_fullFactor_mul_binomialTerm
    {n rOut i : ℕ} (hin : i ≤ n) (hr : i ≤ rOut) :
    (2 ^ (rOut - i) : ℝ) / (2 ^ n : ℝ) =
      (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
        ((((1 : ℝ) / 3) ^ i) * (((2 : ℝ) / 3) ^ (n - i))) := by
  have hpow_r : (2 : ℝ) ^ rOut = (2 : ℝ) ^ (rOut - i) * (2 : ℝ) ^ i := by
    rw [← pow_add]
    congr
    omega
  have hpow_n : (2 : ℝ) ^ n = (2 : ℝ) ^ (n - i) * (2 : ℝ) ^ i := by
    rw [← pow_add]
    congr
    omega
  have hpow3_n : (3 : ℝ) ^ n = (3 : ℝ) ^ (n - i) * (3 : ℝ) ^ i := by
    rw [← pow_add]
    congr
    omega
  have hfour_n :
      (4 : ℝ) ^ n = (2 : ℝ) ^ (i * 2) * (2 : ℝ) ^ ((n - i) * 2) := by
    calc
      (4 : ℝ) ^ n = ((2 : ℝ) ^ 2) ^ n := by norm_num
      _ = (2 : ℝ) ^ (2 * n) := by rw [pow_mul]
      _ = (2 : ℝ) ^ (i * 2 + (n - i) * 2) := by
            congr
            omega
      _ = (2 : ℝ) ^ (i * 2) * (2 : ℝ) ^ ((n - i) * 2) := by rw [pow_add]
  simp only [div_pow]
  field_simp [pow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0),
    pow_ne_zero _ (by norm_num : (3 : ℝ) ≠ 0)]
  rw [hpow_r, hpow_n, hpow3_n]
  rw [hfour_n]
  ring

/-- Exact normalization of the annulus mean: it is the full weighted mean
`2^rOut (3/4)^n` times a `Binomial(n,1/3)` window probability. -/
theorem annulusMean_eq_fullWeightedMean_mul_binomialWindowProbThird
    (n rIn rOut : ℕ) :
    (annulusMean n rIn rOut : ℝ) =
      (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
        binomialWindowProbThird n rIn rOut := by
  classical
  rw [annulusMean_eq_real_sum]
  unfold binomialWindowProbThird
  calc
    (∑ i ∈ Finset.range (n + 1),
        ((Nat.choose n i *
          if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)) /
        (2 ^ n : ℝ)
        = ∑ i ∈ Finset.range (n + 1),
            ((Nat.choose n i *
              if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ) /
              (2 ^ n : ℝ) := by
              rw [Finset.sum_div]
    _ = ∑ i ∈ Finset.range (n + 1),
          (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
            (if rIn ≤ i ∧ i ≤ rOut then
              (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) *
                (((2 : ℝ) / 3) ^ (n - i))
            else
              0) := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
          by_cases hbounds : rIn ≤ i ∧ i ≤ rOut
          · have hterm :=
              annulusWeightedTerm_eq_fullFactor_mul_binomialTerm
                (n := n) (rOut := rOut) (i := i) hin hbounds.2
            calc
              ((Nat.choose n i *
                if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ) /
                  (2 ^ n : ℝ)
                  = (Nat.choose n i : ℝ) *
                      ((2 ^ (rOut - i) : ℝ) / (2 ^ n : ℝ)) := by
                    simp [hbounds]
                    ring
              _ = (Nat.choose n i : ℝ) *
                    ((2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
                      ((((1 : ℝ) / 3) ^ i) * (((2 : ℝ) / 3) ^ (n - i)))) := by
                    rw [hterm]
              _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
                    ((Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) *
                      (((2 : ℝ) / 3) ^ (n - i))) := by ring
              _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
                    (if rIn ≤ i ∧ i ≤ rOut then
                      (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) *
                        (((2 : ℝ) / 3) ^ (n - i))
                    else
                      0) := by simp [hbounds]
          · simp [hbounds]
    _ = (2 ^ rOut : ℝ) * (((3 : ℝ) / 4) ^ n) *
          ∑ i ∈ Finset.range (n + 1),
            (if rIn ≤ i ∧ i ≤ rOut then
              (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) *
                (((2 : ℝ) / 3) ^ (n - i))
            else
              0) := by
          rw [← Finset.mul_sum]

/-- Point mass of a `Binomial(n,1/3)` random variable at `i`. -/
noncomputable def binomialMassThird (n i : ℕ) : ℝ :=
  (Nat.choose n i : ℝ) * (((1 : ℝ) / 3) ^ i) * (((2 : ℝ) / 3) ^ (n - i))

/-- Left tail below the inner annulus radius for `Binomial(n,1/3)`. -/
noncomputable def binomialLeftTailProbThird (n rIn : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if i < rIn then binomialMassThird n i else 0

/-- Right tail above the outer annulus radius for `Binomial(n,1/3)`. -/
noncomputable def binomialRightTailProbThird (n rOut : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (n + 1),
    if rOut < i then binomialMassThird n i else 0

theorem binomialMassThird_nonneg (n i : ℕ) :
    0 ≤ binomialMassThird n i := by
  unfold binomialMassThird
  positivity

theorem binomialTotalProbThird_eq_one (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), binomialMassThird n i) = 1 := by
  have h := add_pow ((1 : ℝ) / 3) ((2 : ℝ) / 3) n
  calc
    (∑ i ∈ Finset.range (n + 1), binomialMassThird n i)
        = ∑ i ∈ Finset.range (n + 1),
            ((1 : ℝ) / 3) ^ i * ((2 : ℝ) / 3) ^ (n - i) *
              (Nat.choose n i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          unfold binomialMassThird
          ring
    _ = (((1 : ℝ) / 3) + ((2 : ℝ) / 3)) ^ n := h.symm
    _ = 1 := by norm_num

/-- For a valid annulus, every binomial mass is either inside the window, in
the left tail, or in the right tail. -/
theorem binomialWindow_tail_partition_term {n rIn rOut i : ℕ}
    (hr : rIn ≤ rOut) :
    (if rIn ≤ i ∧ i ≤ rOut then binomialMassThird n i else 0) +
        (if i < rIn then binomialMassThird n i else 0) +
          (if rOut < i then binomialMassThird n i else 0) =
      binomialMassThird n i := by
  by_cases hleft : i < rIn
  · have hnot_inside : ¬ (rIn ≤ i ∧ i ≤ rOut) := by omega
    have hnot_right : ¬ rOut < i := by omega
    simp [hleft, hnot_inside, hnot_right]
  · by_cases hright : rOut < i
    · have hnot_inside : ¬ (rIn ≤ i ∧ i ≤ rOut) := by omega
      simp [hleft, hright, hnot_inside]
    · have hinside : rIn ≤ i ∧ i ≤ rOut := by omega
      simp [hleft, hright, hinside]

/-- Window probability plus the two outside tails equals one. -/
theorem binomialWindowProbThird_add_tails_eq_one
    (n rIn rOut : ℕ) (hr : rIn ≤ rOut) :
    binomialWindowProbThird n rIn rOut +
        binomialLeftTailProbThird n rIn +
          binomialRightTailProbThird n rOut = 1 := by
  rw [← binomialTotalProbThird_eq_one n]
  unfold binomialWindowProbThird binomialLeftTailProbThird binomialRightTailProbThird
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  unfold binomialMassThird
  have hterm := binomialWindow_tail_partition_term (n := n) (rIn := rIn)
    (rOut := rOut) (i := i) hr
  unfold binomialMassThird at hterm
  exact hterm

/-- If the two binomial tails outside the annulus have total mass at most
`eps`, then the annulus window has mass at least `1-eps`. -/
theorem binomialWindowProbThird_lower_of_tails_le
    {n rIn rOut : ℕ} {eps : ℝ} (hr : rIn ≤ rOut)
    (htails :
      binomialLeftTailProbThird n rIn +
          binomialRightTailProbThird n rOut ≤ eps) :
    1 - eps ≤ binomialWindowProbThird n rIn rOut := by
  have hpartition := binomialWindowProbThird_add_tails_eq_one n rIn rOut hr
  linarith

/-- Exact negative exponential moment of `Binomial(n,1/3)`. -/
theorem binomialExpNegMomentThird_eq (n : ℕ) (lam : ℝ) :
    (∑ i ∈ Finset.range (n + 1),
        binomialMassThird n i * (Real.exp (-lam)) ^ i) =
      (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ^ n := by
  have h := add_pow (((1 : ℝ) / 3) * Real.exp (-lam)) ((2 : ℝ) / 3) n
  calc
    (∑ i ∈ Finset.range (n + 1),
        binomialMassThird n i * (Real.exp (-lam)) ^ i)
        = ∑ i ∈ Finset.range (n + 1),
            (((1 : ℝ) / 3) * Real.exp (-lam)) ^ i *
              (((2 : ℝ) / 3) ^ (n - i)) * (Nat.choose n i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          unfold binomialMassThird
          rw [mul_pow]
          ring
    _ = (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ^ n := h.symm

/-- Exact positive exponential moment of `Binomial(n,1/3)`. -/
theorem binomialExpMomentThird_eq (n : ℕ) (lam : ℝ) :
    (∑ i ∈ Finset.range (n + 1),
        binomialMassThird n i * (Real.exp lam) ^ i) =
      (((1 : ℝ) / 3) * Real.exp lam + ((2 : ℝ) / 3)) ^ n := by
  have h := add_pow (((1 : ℝ) / 3) * Real.exp lam) ((2 : ℝ) / 3) n
  calc
    (∑ i ∈ Finset.range (n + 1),
        binomialMassThird n i * (Real.exp lam) ^ i)
        = ∑ i ∈ Finset.range (n + 1),
            (((1 : ℝ) / 3) * Real.exp lam) ^ i *
              (((2 : ℝ) / 3) ^ (n - i)) * (Nat.choose n i : ℝ) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          unfold binomialMassThird
          rw [mul_pow]
          ring
    _ = (((1 : ℝ) / 3) * Real.exp lam + ((2 : ℝ) / 3)) ^ n := h.symm

/-- Chernoff bound for the left tail of `Binomial(n,1/3)`, with arbitrary
nonnegative parameter `lam`. -/
theorem binomialLeftTailProbThird_le_chernoff (n rIn : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    binomialLeftTailProbThird n rIn ≤
      Real.exp (lam * (rIn : ℝ)) *
        (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ^ n := by
  unfold binomialLeftTailProbThird
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (if i < rIn then binomialMassThird n i else 0) ≤
        Real.exp (lam * (rIn : ℝ)) *
          (binomialMassThird n i * (Real.exp (-lam)) ^ i) := by
    intro i _hi
    by_cases hleft : i < rIn
    · have hmass_nonneg : 0 ≤ binomialMassThird n i := binomialMassThird_nonneg n i
      have hfactor_ge_one :
          1 ≤ Real.exp (lam * (rIn : ℝ)) * (Real.exp (-lam)) ^ i := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        have hle_real : (i : ℝ) ≤ rIn := by exact_mod_cast (Nat.le_of_lt hleft)
        have harg : 0 ≤ lam * ((rIn : ℝ) - i) :=
          mul_nonneg hlam (sub_nonneg.mpr hle_real)
        have heq : lam * (rIn : ℝ) + (i : ℝ) * -lam =
            lam * ((rIn : ℝ) - i) := by ring
        have hexp_le :
            Real.exp 0 ≤ Real.exp (lam * (rIn : ℝ) + (i : ℝ) * -lam) := by
          apply Real.exp_le_exp.mpr
          rw [heq]
          exact harg
        simpa using hexp_le
      calc
        (if i < rIn then binomialMassThird n i else 0)
            = binomialMassThird n i := by simp [hleft]
        _ ≤ binomialMassThird n i *
              (Real.exp (lam * (rIn : ℝ)) * (Real.exp (-lam)) ^ i) :=
            le_mul_of_one_le_right hmass_nonneg hfactor_ge_one
        _ = Real.exp (lam * (rIn : ℝ)) *
              (binomialMassThird n i * (Real.exp (-lam)) ^ i) := by ring
    · have hmass_nonneg : 0 ≤ binomialMassThird n i := binomialMassThird_nonneg n i
      have hpow_nonneg : 0 ≤ (Real.exp (-lam)) ^ i :=
        pow_nonneg (Real.exp_nonneg _) i
      have hrhs_nonneg :
          0 ≤ Real.exp (lam * (rIn : ℝ)) *
            (binomialMassThird n i * (Real.exp (-lam)) ^ i) :=
        mul_nonneg (Real.exp_nonneg _) (mul_nonneg hmass_nonneg hpow_nonneg)
      simpa [hleft] using hrhs_nonneg
  have hsum := Finset.sum_le_sum hterm
  calc
    (∑ i ∈ Finset.range (n + 1),
        if i < rIn then binomialMassThird n i else 0)
        ≤ ∑ i ∈ Finset.range (n + 1),
          Real.exp (lam * (rIn : ℝ)) *
            (binomialMassThird n i * (Real.exp (-lam)) ^ i) := hsum
    _ = Real.exp (lam * (rIn : ℝ)) *
        (∑ i ∈ Finset.range (n + 1),
          binomialMassThird n i * (Real.exp (-lam)) ^ i) := by
          rw [Finset.mul_sum]
    _ = Real.exp (lam * (rIn : ℝ)) *
        (((1 : ℝ) / 3) * Real.exp (-lam) + ((2 : ℝ) / 3)) ^ n := by
          rw [binomialExpNegMomentThird_eq]

/-- Chernoff bound for the right tail of `Binomial(n,1/3)`, with arbitrary
nonnegative parameter `lam`. -/
theorem binomialRightTailProbThird_le_chernoff (n rOut : ℕ) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    binomialRightTailProbThird n rOut ≤
      Real.exp (-(lam * (rOut : ℝ))) *
        (((1 : ℝ) / 3) * Real.exp lam + ((2 : ℝ) / 3)) ^ n := by
  unfold binomialRightTailProbThird
  have hterm : ∀ i ∈ Finset.range (n + 1),
      (if rOut < i then binomialMassThird n i else 0) ≤
        Real.exp (-(lam * (rOut : ℝ))) *
          (binomialMassThird n i * (Real.exp lam) ^ i) := by
    intro i _hi
    by_cases hright : rOut < i
    · have hmass_nonneg : 0 ≤ binomialMassThird n i := binomialMassThird_nonneg n i
      have hfactor_ge_one :
          1 ≤ Real.exp (-(lam * (rOut : ℝ))) * (Real.exp lam) ^ i := by
        rw [← Real.exp_nat_mul, ← Real.exp_add]
        have hle_real : (rOut : ℝ) ≤ i := by exact_mod_cast (Nat.le_of_lt hright)
        have harg : 0 ≤ lam * ((i : ℝ) - rOut) :=
          mul_nonneg hlam (sub_nonneg.mpr hle_real)
        have heq : -(lam * (rOut : ℝ)) + (i : ℝ) * lam =
            lam * ((i : ℝ) - rOut) := by ring
        have hexp_le :
            Real.exp 0 ≤ Real.exp (-(lam * (rOut : ℝ)) + (i : ℝ) * lam) := by
          apply Real.exp_le_exp.mpr
          rw [heq]
          exact harg
        simpa using hexp_le
      calc
        (if rOut < i then binomialMassThird n i else 0)
            = binomialMassThird n i := by simp [hright]
        _ ≤ binomialMassThird n i *
              (Real.exp (-(lam * (rOut : ℝ))) * (Real.exp lam) ^ i) :=
            le_mul_of_one_le_right hmass_nonneg hfactor_ge_one
        _ = Real.exp (-(lam * (rOut : ℝ))) *
              (binomialMassThird n i * (Real.exp lam) ^ i) := by ring
    · have hmass_nonneg : 0 ≤ binomialMassThird n i := binomialMassThird_nonneg n i
      have hpow_nonneg : 0 ≤ (Real.exp lam) ^ i :=
        pow_nonneg (Real.exp_nonneg _) i
      have hrhs_nonneg :
          0 ≤ Real.exp (-(lam * (rOut : ℝ))) *
            (binomialMassThird n i * (Real.exp lam) ^ i) :=
        mul_nonneg (Real.exp_nonneg _) (mul_nonneg hmass_nonneg hpow_nonneg)
      simpa [hright] using hrhs_nonneg
  have hsum := Finset.sum_le_sum hterm
  calc
    (∑ i ∈ Finset.range (n + 1),
        if rOut < i then binomialMassThird n i else 0)
        ≤ ∑ i ∈ Finset.range (n + 1),
          Real.exp (-(lam * (rOut : ℝ))) *
            (binomialMassThird n i * (Real.exp lam) ^ i) := hsum
    _ = Real.exp (-(lam * (rOut : ℝ))) *
        (∑ i ∈ Finset.range (n + 1),
          binomialMassThird n i * (Real.exp lam) ^ i) := by
          rw [Finset.mul_sum]
    _ = Real.exp (-(lam * (rOut : ℝ))) *
        (((1 : ℝ) / 3) * Real.exp lam + ((2 : ℝ) / 3)) ^ n := by
          rw [binomialExpMomentThird_eq]

theorem oneCenterContributionExpectation_eq_annulusMean {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionExpectation rIn rOut target =
      annulusMean n rIn rOut := by
  simpa [annulusMean, annulusMeanNumerator] using
    oneCenterContributionExpectation_eq_distance_sum
      (n := n) (rIn := rIn) (rOut := rOut) target

theorem oneCenterContributionExpectationReal_eq_coe {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionExpectationReal rIn rOut target =
      (oneCenterContributionExpectation rIn rOut target : ℝ) := by
  simp [oneCenterContributionExpectationReal, oneCenterContributionExpectation,
    uniformExpectationReal, uniformExpectation]

theorem oneCenterContributionExpectationReal_eq_annulusMean {n rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    oneCenterContributionExpectationReal rIn rOut target =
      (annulusMean n rIn rOut : ℝ) := by
  rw [oneCenterContributionExpectationReal_eq_coe]
  rw [oneCenterContributionExpectation_eq_annulusMean]

/-- Exact expectation of the total annulus contribution from an `N`-tuple of
uniform centers. -/
noncomputable def sampleContributionExpectation {n N : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  uniformExpectation fun sample : CenterSample n N =>
    sampleTotalContribution rIn rOut target sample

/-- Sum of the second moments of the `N` independent one-center contributions.
This is the variance proxy used by Bernstein; the actual variance is bounded by
this quantity. -/
noncomputable def sampleContributionSecondMomentProxy {n N : ℕ} (rIn rOut : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  (N : ℚ) * oneCenterContributionSecondMoment rIn rOut target

theorem sampleContributionExpectation_eq_sum {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    sampleContributionExpectation (N := N) rIn rOut target =
      (∑ sample : CenterSample n N,
          (sampleTotalContribution rIn rOut target sample : ℚ)) /
        (Fintype.card (CenterSample n N) : ℚ) := by
  rfl

/-- For a fixed coordinate of the random center tuple, summing over all samples
is the one-center sum multiplied by the number of choices for the remaining
coordinates. -/
theorem sum_centerSample_eval {n N : ℕ} (j : Fin N)
    (f : HypercubeVertex n → ℕ) :
    (∑ sample : CenterSample n N, (f (sample j) : ℚ)) =
      ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n, (f center : ℚ) := by
  classical
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (CenterSample n N)))
      (t := (Finset.univ : Finset (HypercubeVertex n)))
      (g := fun sample : CenterSample n N => sample j)
      (fun sample _hsample => Finset.mem_univ (sample j))
      (fun sample : CenterSample n N => (f (sample j) : ℚ)))
  have hinner :
      ∀ center : HypercubeVertex n,
        (∑ sample ∈ (Finset.univ : Finset (CenterSample n N)) with sample j = center,
          (f (sample j) : ℚ)) =
        ((2 ^ n) ^ (N - 1) : ℚ) * (f center : ℚ) := by
    intro center
    let fiber : Finset (CenterSample n N) :=
      (Finset.univ : Finset (CenterSample n N)).filter fun sample => sample j = center
    have hcard : fiber.card = (2 ^ n) ^ (N - 1) := by
      have hpi :=
        Fintype.card_filter_piFinset_const_eq_of_mem
          (s := (Finset.univ : Finset (HypercubeVertex n))) j
          (x := center) (Finset.mem_univ center)
      simpa [fiber, CenterSample, card_vertex] using hpi
    have hconst :
        ∀ sample ∈ fiber, (f (sample j) : ℚ) = (f center : ℚ) := by
      intro sample hsample
      have hsample_eq : sample j = center := by
        simpa [fiber] using (Finset.mem_filter.mp hsample).2
      simp [hsample_eq]
    calc
      (∑ sample ∈ (Finset.univ : Finset (CenterSample n N)) with sample j = center,
          (f (sample j) : ℚ))
          = ∑ sample ∈ fiber, (f (sample j) : ℚ) := by
            rfl
      _ = ∑ _sample ∈ fiber, (f center : ℚ) := by
            exact Finset.sum_congr rfl hconst
      _ = ((2 ^ n) ^ (N - 1) : ℚ) * (f center : ℚ) := by
            simp [Finset.sum_const, hcard, nsmul_eq_mul]
  calc
    (∑ sample : CenterSample n N, (f (sample j) : ℚ))
        = ∑ sample ∈ (Finset.univ : Finset (CenterSample n N)), (f (sample j) : ℚ) := by
          rfl
    _ = ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
        ∑ sample ∈ (Finset.univ : Finset (CenterSample n N)) with sample j = center,
          (f (sample j) : ℚ) := by
          exact hfiber.symm
    _ = ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
        ((2 ^ n) ^ (N - 1) : ℚ) * (f center : ℚ) := by
          exact Finset.sum_congr rfl fun center _hcenter => hinner center
    _ = ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)), (f center : ℚ) := by
          rw [Finset.mul_sum]
    _ = ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n, (f center : ℚ) := by
          rfl

/-- Numerator of the `N`-center expectation, written as `N` copies of the
one-coordinate sum. -/
theorem sum_sampleTotalContribution_eq {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    (∑ sample : CenterSample n N,
        (sampleTotalContribution rIn rOut target sample : ℚ)) =
      (N : ℚ) * ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℚ) := by
  classical
  calc
    (∑ sample : CenterSample n N,
        (sampleTotalContribution rIn rOut target sample : ℚ))
        = ∑ sample : CenterSample n N,
            ∑ j : Fin N,
              (annulusContribution rIn rOut target (sample j) : ℚ) := by
          refine Finset.sum_congr rfl ?_
          intro sample _hsample
          simp [sampleTotalContribution]
    _ = ∑ j : Fin N,
        ∑ sample : CenterSample n N,
          (annulusContribution rIn rOut target (sample j) : ℚ) := by
          rw [Finset.sum_comm]
    _ = ∑ _j : Fin N,
        ((2 ^ n) ^ (N - 1) : ℚ) *
          ∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℚ) := by
          refine Finset.sum_congr rfl ?_
          intro j _hj
          exact sum_centerSample_eval j (annulusContribution rIn rOut target)
    _ = (N : ℚ) * ((2 ^ n) ^ (N - 1) : ℚ) *
        ∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℚ) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

/-- Linearity of expectation for the independent uniform center tuple used
here: the expected total contribution is `N` times the one-center expectation. -/
theorem sampleContributionExpectation_eq_nat_mul_oneCenter {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    sampleContributionExpectation (N := N) rIn rOut target =
      (N : ℚ) * oneCenterContributionExpectation rIn rOut target := by
  classical
  cases N with
  | zero =>
      simp [sampleContributionExpectation, sampleTotalContribution, uniformExpectation]
  | succ M =>
      rw [sampleContributionExpectation_eq_sum, oneCenterContributionExpectation_eq_sum]
      rw [sum_sampleTotalContribution_eq]
      have hpow_ne : (2 ^ n : ℚ) ≠ 0 := by
        positivity
      simp [Nat.cast_pow]
      field_simp [hpow_ne]
      ring

theorem sampleContributionExpectation_eq_nat_mul_annulusMean {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    sampleContributionExpectation (N := N) rIn rOut target =
      (N : ℚ) * annulusMean n rIn rOut := by
  rw [sampleContributionExpectation_eq_nat_mul_oneCenter]
  rw [oneCenterContributionExpectation_eq_annulusMean]

/-- Bernstein variance-proxy bound: the sum of one-center second moments is at
most the annulus width factor times the mean total contribution. -/
theorem sampleContributionSecondMomentProxy_le_width_mul_expectation {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) :
    sampleContributionSecondMomentProxy (N := N) rIn rOut target ≤
      (2 ^ (rOut - rIn) : ℚ) *
        sampleContributionExpectation (N := N) rIn rOut target := by
  rw [sampleContributionSecondMomentProxy,
    sampleContributionExpectation_eq_nat_mul_oneCenter]
  have hN : 0 ≤ (N : ℚ) := by positivity
  have h :=
    mul_le_mul_of_nonneg_left
      (oneCenterContributionSecondMoment_le_width_mul_expectation
        (rIn := rIn) (rOut := rOut) target) hN
  calc
    (N : ℚ) * oneCenterContributionSecondMoment rIn rOut target
        ≤ (N : ℚ) *
          ((2 ^ (rOut - rIn) : ℚ) * oneCenterContributionExpectation rIn rOut target) := h
    _ = (2 ^ (rOut - rIn) : ℚ) *
        ((N : ℚ) * oneCenterContributionExpectation rIn rOut target) := by
          ring

/-- Paper-facing variance-proxy corollary: once the expected total contribution
is at most `2T`, the Bernstein variance proxy is at most `2 B_0 T`. -/
theorem sampleContributionSecondMomentProxy_le_two_width_mul_T
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n)
    (hmean_upper :
      sampleContributionExpectation (N := N) rIn rOut target ≤ 2 * (T : ℚ)) :
    sampleContributionSecondMomentProxy (N := N) rIn rOut target ≤
      2 * (2 ^ (rOut - rIn) : ℚ) * (T : ℚ) := by
  have hwidth_nonneg : 0 ≤ (2 ^ (rOut - rIn) : ℚ) := by positivity
  have h :=
    (sampleContributionSecondMomentProxy_le_width_mul_expectation
      (N := N) (rIn := rIn) (rOut := rOut) target).trans
      (mul_le_mul_of_nonneg_left hmean_upper hwidth_nonneg)
  calc
    sampleContributionSecondMomentProxy (N := N) rIn rOut target
        ≤ (2 ^ (rOut - rIn) : ℚ) * (2 * (T : ℚ)) := h
    _ = 2 * (2 ^ (rOut - rIn) : ℚ) * (T : ℚ) := by
          ring

/-- The event that a particular target receives less than demand `T`. -/
def sampleTargetFails {n N : ℕ} (rIn rOut T : ℕ)
    (target : HypercubeVertex n) (sample : CenterSample n N) : Prop :=
  sampleTotalContribution rIn rOut target sample < T

instance instDecidableSampleTargetFails {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) (sample : CenterSample n N) :
    Decidable (sampleTargetFails rIn rOut T target sample) := by
  unfold sampleTargetFails
  infer_instance

instance instDecidablePredSampleTargetFails {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) :
    DecidablePred (sampleTargetFails (n := n) (N := N) rIn rOut T target) :=
  fun sample => instDecidableSampleTargetFails target sample

/-- The event that some target receives less than demand `T`. -/
def sampleFailsSomeTarget {n N : ℕ} (rIn rOut T : ℕ)
    (sample : CenterSample n N) : Prop :=
  ∃ target : HypercubeVertex n, sampleTargetFails rIn rOut T target sample

instance instDecidableSampleFailsSomeTarget {n N rIn rOut T : ℕ}
    (sample : CenterSample n N) :
    Decidable (sampleFailsSomeTarget rIn rOut T sample) := by
  classical
  unfold sampleFailsSomeTarget
  infer_instance

instance instDecidablePredSampleFailsSomeTarget {n N rIn rOut T : ℕ} :
    DecidablePred (sampleFailsSomeTarget (n := n) (N := N) rIn rOut T) :=
  fun sample => instDecidableSampleFailsSomeTarget sample

/-- Failure probability for one fixed target.  This is the quantity controlled
by Bernstein in the proof. -/
noncomputable def targetFailureProbability {n N : ℕ} (rIn rOut T : ℕ)
    (target : HypercubeVertex n) : ℚ :=
  uniformProbability fun sample : CenterSample n N =>
    sampleTargetFails rIn rOut T target sample

/-- Real-valued form of the fixed-target failure probability, used for
exponential tail estimates. -/
noncomputable def targetFailureProbabilityReal {n N : ℕ} (rIn rOut T : ℕ)
    (target : HypercubeVertex n) : ℝ :=
  uniformProbabilityReal fun sample : CenterSample n N =>
    sampleTargetFails rIn rOut T target sample

theorem targetFailureProbabilityReal_eq_coe {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) :
    targetFailureProbabilityReal (N := N) rIn rOut T target =
      (targetFailureProbability (N := N) rIn rOut T target : ℝ) := by
  classical
  simp [targetFailureProbabilityReal, targetFailureProbability,
    uniformProbabilityReal_eq_coe_uniformProbability]

/-- Exponential moment used by the Chernoff/Markov lower-tail argument for a
fixed target. -/
noncomputable def targetLowerTailExponentialMoment {n N : ℕ}
    (rIn rOut T : ℕ) (target : HypercubeVertex n) (lam : ℝ) : ℝ :=
  uniformExpectationReal fun sample : CenterSample n N =>
    Real.exp (lam * ((T : ℝ) - (sampleTotalContribution rIn rOut target sample : ℝ)))

/-- One-center exponential moment appearing after independence factorization of
the lower-tail Chernoff bound. -/
noncomputable def oneCenterNegativeExponentialMoment {n : ℕ}
    (rIn rOut : ℕ) (target : HypercubeVertex n) (lam : ℝ) : ℝ :=
  uniformExpectationReal fun center : HypercubeVertex n =>
    Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))

theorem oneCenterNegativeExponentialMoment_nonneg {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    0 ≤ oneCenterNegativeExponentialMoment rIn rOut target lam := by
  classical
  unfold oneCenterNegativeExponentialMoment uniformExpectationReal
  exact div_nonneg
    (Finset.sum_nonneg fun center _hcenter => Real.exp_nonneg _)
    (by positivity)

/-- One-center bounded-nonnegative Chernoff estimate: the negative exponential
moment is bounded by the chord estimate in terms of the one-center mean and
the annulus width `B_0 = 2^(rOut-rIn)`. -/
theorem oneCenterNegativeExponentialMoment_le_chord {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    oneCenterNegativeExponentialMoment rIn rOut target lam ≤
      1 - (1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
        (oneCenterContributionExpectationReal rIn rOut target /
          (2 ^ (rOut - rIn) : ℝ)) := by
  classical
  let B : ℝ := (2 ^ (rOut - rIn) : ℝ)
  let q : ℝ := 1 - Real.exp (-(lam * B))
  have hBpos : 0 < B := by positivity
  have hcard_pos : 0 < (2 ^ n : ℝ) := by positivity
  have hcardF_nonneg : 0 ≤ (Fintype.card (HypercubeVertex n) : ℝ) := by positivity
  have hcard_eq : (Fintype.card (HypercubeVertex n) : ℝ) = (2 ^ n : ℝ) := by
    simp
  have hsum :
      (∑ center : HypercubeVertex n,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) ≤
        ∑ center : HypercubeVertex n,
          (1 - q * ((annulusContribution rIn rOut target center : ℝ) / B)) := by
    exact Finset.sum_le_sum fun center _hcenter => by
      have hz0 : 0 ≤ (annulusContribution rIn rOut target center : ℝ) := by positivity
      have hzB :
          (annulusContribution rIn rOut target center : ℝ) ≤ B := by
        simpa [B] using (by
          exact_mod_cast
            annulusContribution_le_width (rIn := rIn) (rOut := rOut) target center)
      simpa [B, q] using
        exp_neg_mul_le_chord (lam := lam) (B := B)
          (z := (annulusContribution rIn rOut target center : ℝ)) hBpos hz0 hzB
  have hsum_chord_eq :
      (∑ center : HypercubeVertex n,
          (1 - q * ((annulusContribution rIn rOut target center : ℝ) / B))) =
        (Fintype.card (HypercubeVertex n) : ℝ) -
          q * ((∑ center : HypercubeVertex n,
            (annulusContribution rIn rOut target center : ℝ)) / B) := by
    rw [Finset.sum_sub_distrib]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    congr 1
    rw [Finset.sum_div]
    rw [Finset.mul_sum]
  rw [oneCenterNegativeExponentialMoment, oneCenterContributionExpectationReal_eq_sum]
  unfold uniformExpectationReal
  calc
    (∑ center : HypercubeVertex n,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) /
        (Fintype.card (HypercubeVertex n) : ℝ)
        ≤ (∑ center : HypercubeVertex n,
          (1 - q * ((annulusContribution rIn rOut target center : ℝ) / B))) /
          (Fintype.card (HypercubeVertex n) : ℝ) := by
          exact div_le_div_of_nonneg_right hsum hcardF_nonneg
    _ = 1 - q *
        (((∑ center : HypercubeVertex n,
          (annulusContribution rIn rOut target center : ℝ)) / (2 ^ n : ℝ)) / B) := by
          rw [hsum_chord_eq]
          rw [hcard_eq]
          field_simp [hBpos.ne', hcard_pos.ne']

/-- Sum of the one-center negative exponential factor over one Hamming sphere. -/
theorem sum_filter_dist_eq_exp_annulusContribution {n rIn rOut i : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ center ∈
        (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i),
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) =
      (Nat.choose n i : ℝ) *
        Real.exp
          (-(lam *
            ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by
  classical
  let sphere : Finset (HypercubeVertex n) :=
    Finset.univ.filter fun center : HypercubeVertex n => dist target center = i
  let contributionAtDistance : ℕ :=
    if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0
  have hconst :
      ∀ center ∈ sphere,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))) =
          Real.exp (-(lam * (contributionAtDistance : ℝ))) := by
    intro center hcenter
    have hdist_target : dist target center = i := by
      simpa [sphere] using (Finset.mem_filter.mp hcenter).2
    have hdist_center : dist center target = i := by
      simpa [dist_comm center target] using hdist_target
    by_cases hbounds : rIn ≤ i ∧ i ≤ rOut
    · simp [annulusContribution, contributionAtDistance, hdist_center, hbounds]
    · have hnot_bounds :
          ¬ (rIn ≤ dist center target ∧ dist center target ≤ rOut) := by
        simpa [hdist_center] using hbounds
      simp [annulusContribution, contributionAtDistance, hnot_bounds, hbounds]
  have hcard : sphere.card = Nat.choose n i := by
    simpa [sphere] using card_filter_dist_eq (n := n) (i := i) target
  calc
    (∑ center ∈
        (Finset.univ.filter fun center : HypercubeVertex n => dist target center = i),
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))))
        = ∑ center ∈ sphere,
            Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))) := by
          rfl
    _ = ∑ _center ∈ sphere,
        Real.exp (-(lam * (contributionAtDistance : ℝ))) := by
          exact Finset.sum_congr rfl hconst
    _ = (sphere.card : ℝ) *
        Real.exp (-(lam * (contributionAtDistance : ℝ))) := by
          simp [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.choose n i : ℝ) *
        Real.exp
          (-(lam *
            ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by
          simp [hcard, contributionAtDistance]

/-- Exact one-center negative exponential moment numerator, grouped by Hamming
distance. -/
theorem sum_exp_annulusContribution_eq_sum_range {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ center : HypercubeVertex n,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))) =
      ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          Real.exp
            (-(lam *
              ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by
  classical
  have hmaps :
      ∀ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
        dist target center ∈ Finset.range (n + 1) := by
    intro center _hcenter
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (dist_le target center))
  have hfiber :=
    (Finset.sum_fiberwise_of_maps_to
      (s := (Finset.univ : Finset (HypercubeVertex n)))
      (t := Finset.range (n + 1))
      (g := fun center : HypercubeVertex n => dist target center)
      hmaps
      (fun center : HypercubeVertex n =>
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))))
  calc
    (∑ center : HypercubeVertex n,
        Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))))
        = ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)),
            Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))) := by
          rfl
    _ = ∑ i ∈ Finset.range (n + 1),
        ∑ center ∈ (Finset.univ : Finset (HypercubeVertex n)) with dist target center = i,
          Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ))) := by
          exact hfiber.symm
    _ = ∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          Real.exp
            (-(lam *
              ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          simpa using
            sum_filter_dist_eq_exp_annulusContribution
              (n := n) (rIn := rIn) (rOut := rOut) (i := i) target lam

/-- Exact one-center negative exponential moment as a binomial Hamming-sphere
sum. -/
theorem oneCenterNegativeExponentialMoment_eq_distance_sum {n rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    oneCenterNegativeExponentialMoment rIn rOut target lam =
      (∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          Real.exp
            (-(lam *
              ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)))) /
        (2 ^ n : ℝ) := by
  rw [oneCenterNegativeExponentialMoment]
  have hsum :=
    sum_exp_annulusContribution_eq_sum_range
      (n := n) (rIn := rIn) (rOut := rOut) target lam
  simp [uniformExpectationReal, hsum]

/-- The one-center exponential moment is independent of the target, by
hypercube symmetry and the Hamming-sphere count. -/
theorem oneCenterNegativeExponentialMoment_eq_of_targets {n rIn rOut : ℕ}
    (target target' : HypercubeVertex n) (lam : ℝ) :
    oneCenterNegativeExponentialMoment rIn rOut target lam =
      oneCenterNegativeExponentialMoment rIn rOut target' lam := by
  rw [oneCenterNegativeExponentialMoment_eq_distance_sum target lam,
    oneCenterNegativeExponentialMoment_eq_distance_sum target' lam]

theorem exp_neg_sampleTotalContribution_eq_prod {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) (sample : CenterSample n N) :
    Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ))) =
      ∏ j : Fin N,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target (sample j) : ℝ))) := by
  have hsum :
      -(lam * (sampleTotalContribution rIn rOut target sample : ℝ)) =
        ∑ j : Fin N,
          -(lam * (annulusContribution rIn rOut target (sample j) : ℝ)) := by
    simp [sampleTotalContribution, Finset.mul_sum]
  calc
    Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ)))
        = Real.exp
          (∑ j : Fin N,
            -(lam * (annulusContribution rIn rOut target (sample j) : ℝ))) := by
          rw [hsum]
    _ = ∏ j : Fin N,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target (sample j) : ℝ))) := by
          simpa using
            (Real.exp_sum Finset.univ
              (fun j : Fin N =>
                -(lam * (annulusContribution rIn rOut target (sample j) : ℝ))))

/-- The product-space sum of independent one-center exponential factors
factors as the `N`th power of the one-center sum. -/
theorem sum_prod_oneCenterNegativeExponentialMoment {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ sample : CenterSample n N,
      ∏ j : Fin N,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target (sample j) : ℝ)))) =
      (∑ center : HypercubeVertex n,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target center : ℝ)))) ^ N := by
  classical
  let f : HypercubeVertex n → ℝ :=
    fun center => Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))
  have hprod :=
    (Fintype.prod_sum (fun _j : Fin N => fun center : HypercubeVertex n => f center)).symm
  simpa [CenterSample, f, Finset.prod_const] using hprod

theorem sum_exp_neg_sampleTotalContribution_eq_pow {n N rIn rOut : ℕ}
    (target : HypercubeVertex n) (lam : ℝ) :
    (∑ sample : CenterSample n N,
      Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ)))) =
      (∑ center : HypercubeVertex n,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target center : ℝ)))) ^ N := by
  classical
  calc
    (∑ sample : CenterSample n N,
      Real.exp (-(lam * (sampleTotalContribution rIn rOut target sample : ℝ))))
        = ∑ sample : CenterSample n N,
          ∏ j : Fin N,
            Real.exp (-(lam *
              (annulusContribution rIn rOut target (sample j) : ℝ))) := by
          refine Finset.sum_congr rfl ?_
          intro sample _hsample
          exact exp_neg_sampleTotalContribution_eq_prod target lam sample
    _ = (∑ center : HypercubeVertex n,
        Real.exp (-(lam *
          (annulusContribution rIn rOut target center : ℝ)))) ^ N := by
          exact sum_prod_oneCenterNegativeExponentialMoment target lam

theorem exp_target_sub_sampleTotalContribution
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n)
    (lam : ℝ) (sample : CenterSample n N) :
    Real.exp (lam * ((T : ℝ) -
        (sampleTotalContribution rIn rOut target sample : ℝ))) =
      Real.exp (lam * (T : ℝ)) *
        Real.exp (-(lam *
          (sampleTotalContribution rIn rOut target sample : ℝ))) := by
  have harg :
      lam * ((T : ℝ) -
          (sampleTotalContribution rIn rOut target sample : ℝ)) =
        lam * (T : ℝ) +
          -(lam * (sampleTotalContribution rIn rOut target sample : ℝ)) := by
    ring
  rw [harg, Real.exp_add]

/-- Independence factorization for the lower-tail exponential moment. -/
theorem targetLowerTailExponentialMoment_eq
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) (lam : ℝ) :
    targetLowerTailExponentialMoment (N := N) rIn rOut T target lam =
      Real.exp (lam * (T : ℝ)) *
        (oneCenterNegativeExponentialMoment rIn rOut target lam) ^ N := by
  classical
  let A : ℝ :=
    ∑ center : HypercubeVertex n,
      Real.exp (-(lam * (annulusContribution rIn rOut target center : ℝ)))
  have hsum :
      (∑ sample : CenterSample n N,
        Real.exp (lam * ((T : ℝ) -
          (sampleTotalContribution rIn rOut target sample : ℝ)))) =
        Real.exp (lam * (T : ℝ)) * A ^ N := by
    calc
      (∑ sample : CenterSample n N,
        Real.exp (lam * ((T : ℝ) -
          (sampleTotalContribution rIn rOut target sample : ℝ))))
          = ∑ sample : CenterSample n N,
            Real.exp (lam * (T : ℝ)) *
              Real.exp (-(lam *
                (sampleTotalContribution rIn rOut target sample : ℝ))) := by
            refine Finset.sum_congr rfl ?_
            intro sample _hsample
            exact exp_target_sub_sampleTotalContribution target lam sample
      _ = Real.exp (lam * (T : ℝ)) *
          ∑ sample : CenterSample n N,
            Real.exp (-(lam *
              (sampleTotalContribution rIn rOut target sample : ℝ))) := by
            rw [Finset.mul_sum]
      _ = Real.exp (lam * (T : ℝ)) * A ^ N := by
            rw [sum_exp_neg_sampleTotalContribution_eq_pow]
  have hcard_ne : (2 ^ n : ℝ) ≠ 0 := by
    positivity
  have hcard_pow_ne : ((2 ^ n : ℝ) ^ N) ≠ 0 := pow_ne_zero N hcard_ne
  simp [targetLowerTailExponentialMoment, oneCenterNegativeExponentialMoment,
    uniformExpectationReal, A, hsum, Nat.cast_pow]
  field_simp [hcard_ne, hcard_pow_ne]
  rw [div_pow]
  field_simp [hcard_pow_ne]

/-- Chord-based lower-tail exponential-moment bound before optimizing the
Chernoff parameter.  Here `B = 2^(rOut-rIn)` and the parenthesized term is the
one-center chord drop. -/
theorem targetLowerTailExponentialMoment_le_exp_chord
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) {lam : ℝ}
    (hlam_nonneg : 0 ≤ lam) :
    targetLowerTailExponentialMoment (N := N) rIn rOut T target lam ≤
      Real.exp
        (lam * (T : ℝ) -
          (N : ℝ) *
            ((1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
              (oneCenterContributionExpectationReal rIn rOut target /
                (2 ^ (rOut - rIn) : ℝ)))) := by
  classical
  let B : ℝ := (2 ^ (rOut - rIn) : ℝ)
  let m : ℝ := oneCenterContributionExpectationReal rIn rOut target
  let u : ℝ := (1 - Real.exp (-(lam * B))) * (m / B)
  have hm_nonneg : 0 ≤ m := by
    unfold m oneCenterContributionExpectationReal uniformExpectationReal
    exact div_nonneg
      (Finset.sum_nonneg fun center _hcenter => by positivity)
      (by positivity)
  have hB_nonneg : 0 ≤ B := by positivity
  have hq_nonneg : 0 ≤ 1 - Real.exp (-(lam * B)) := by
    have harg : -(lam * B) ≤ 0 := by
      nlinarith [mul_nonneg hlam_nonneg hB_nonneg]
    have hexp : Real.exp (-(lam * B)) ≤ Real.exp 0 := Real.exp_le_exp.mpr harg
    simpa using hexp
  have hmoment_chord :
      oneCenterNegativeExponentialMoment rIn rOut target lam ≤ 1 - u := by
    simpa [B, m, u] using
      oneCenterNegativeExponentialMoment_le_chord
        (rIn := rIn) (rOut := rOut) target lam
  have hpow :
      (oneCenterNegativeExponentialMoment rIn rOut target lam) ^ N ≤
        Real.exp (-((N : ℝ) * u)) := by
    exact pow_le_exp_neg_mul_of_le_one_sub N
      (oneCenterNegativeExponentialMoment_nonneg
        (rIn := rIn) (rOut := rOut) target lam)
      hmoment_chord
  rw [targetLowerTailExponentialMoment_eq]
  calc
    Real.exp (lam * (T : ℝ)) *
        (oneCenterNegativeExponentialMoment rIn rOut target lam) ^ N
        ≤ Real.exp (lam * (T : ℝ)) * Real.exp (-((N : ℝ) * u)) := by
          exact mul_le_mul_of_nonneg_left hpow (Real.exp_nonneg _)
    _ = Real.exp
        (lam * (T : ℝ) -
          (N : ℝ) *
            ((1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
              (oneCenterContributionExpectationReal rIn rOut target /
                (2 ^ (rOut - rIn) : ℝ)))) := by
          rw [← Real.exp_add]
          simp [B, m, u]
          ring

/-- Optimized chord-based Chernoff bound for one fixed target.  This is the
analytic gap-closing statement: if the expected annulus contribution `mu`
exceeds the threshold by `gap`, then the optimized exponential moment is
bounded by `exp(-gap^2/(4 B mu))`, where `B = 2^(rOut-rIn)`. -/
theorem targetLowerTailExponentialMoment_le_exp_optimized_chord
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) {gap : ℝ}
    (hgap : 0 ≤ gap)
    (hmu_pos :
      0 < (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)
    (hmean :
      (T : ℝ) + gap ≤
        (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target) :
    targetLowerTailExponentialMoment (N := N) rIn rOut T target
        (gap /
          (2 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target))) ≤
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) := by
  classical
  let B : ℝ := (2 ^ (rOut - rIn) : ℝ)
  let m : ℝ := oneCenterContributionExpectationReal rIn rOut target
  let mu : ℝ := (N : ℝ) * m
  let lam : ℝ := gap / (2 * B * mu)
  have hB_pos : 0 < B := by positivity
  have hB_nonneg : 0 ≤ B := hB_pos.le
  have hmu_pos' : 0 < mu := by simpa [mu, m]
  have hmu_nonneg : 0 ≤ mu := hmu_pos'.le
  have hlam_nonneg : 0 ≤ lam := by
    exact div_nonneg hgap (by positivity)
  have hm_nonneg : 0 ≤ m := by
    unfold m oneCenterContributionExpectationReal uniformExpectationReal
    exact div_nonneg
      (Finset.sum_nonneg fun center _hcenter => by positivity)
      (by positivity)
  have hq_lower :
      lam * B - (lam * B) ^ 2 ≤
        1 - Real.exp (-(lam * B)) := by
    exact one_sub_exp_neg_ge_sub_sq (mul_nonneg hlam_nonneg hB_nonneg)
  have hcoeff_nonneg : 0 ≤ (N : ℝ) * (m / B) := by
    exact mul_nonneg (by positivity) (div_nonneg hm_nonneg hB_nonneg)
  have hdrop_lower :
      (lam - lam ^ 2 * B) * mu ≤
        (N : ℝ) *
          ((1 - Real.exp (-(lam * B))) * (m / B)) := by
    calc
      (lam - lam ^ 2 * B) * mu =
          (lam * B - (lam * B) ^ 2) * ((N : ℝ) * (m / B)) := by
            field_simp [hB_pos.ne']
            ring
      _ ≤ (1 - Real.exp (-(lam * B))) * ((N : ℝ) * (m / B)) := by
            exact mul_le_mul_of_nonneg_right hq_lower hcoeff_nonneg
      _ = (N : ℝ) *
          ((1 - Real.exp (-(lam * B))) * (m / B)) := by
            ring
  have hchord :=
    targetLowerTailExponentialMoment_le_exp_chord
      (N := N) (rIn := rIn) (rOut := rOut) (T := T)
      target (lam := lam) hlam_nonneg
  have hchord_to_quad :
      Real.exp
        (lam * (T : ℝ) -
          (N : ℝ) *
            ((1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
              (oneCenterContributionExpectationReal rIn rOut target /
                (2 ^ (rOut - rIn) : ℝ)))) ≤
        Real.exp (lam * (T : ℝ) - (lam - lam ^ 2 * B) * mu) := by
    apply Real.exp_le_exp.mpr
    simpa [B, m, mu] using sub_le_sub_left hdrop_lower (lam * (T : ℝ))
  have hopt :
      Real.exp (lam * (T : ℝ) - (lam - lam ^ 2 * B) * mu) ≤
        Real.exp (-(gap ^ 2 / (4 * B * mu))) := by
    exact exp_chord_quadratic_optimized
      (T := (T : ℝ)) (gap := gap) (B := B) (mu := mu) (lam := lam)
      hB_pos hmu_pos' hgap (by simpa [mu, m] using hmean) rfl
  calc
    targetLowerTailExponentialMoment (N := N) rIn rOut T target
        (gap /
          (2 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))
        = targetLowerTailExponentialMoment (N := N) rIn rOut T target lam := by
          simp [lam, B, m, mu]
    _ ≤ Real.exp
        (lam * (T : ℝ) -
          (N : ℝ) *
            ((1 - Real.exp (-(lam * (2 ^ (rOut - rIn) : ℝ)))) *
              (oneCenterContributionExpectationReal rIn rOut target /
                (2 ^ (rOut - rIn) : ℝ)))) := hchord
    _ ≤ Real.exp (lam * (T : ℝ) - (lam - lam ^ 2 * B) * mu) :=
          hchord_to_quad
    _ ≤ Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) := by
          simpa [B, m, mu, mul_assoc] using hopt

/-- A target-independent one-center exponential-moment bound for a fixed
Chernoff parameter.  The default target is arbitrary; the preceding
target-independence theorem shows that it represents every target. -/
def OneCenterExponentialMomentBound (n N rIn rOut T : ℕ) (lam eps : ℝ) : Prop :=
  0 < lam ∧
    Real.exp (lam * (T : ℝ)) *
      (oneCenterNegativeExponentialMoment rIn rOut (fun _ : Fin n => false) lam) ^ N ≤ eps

/-- The same one-center exponential-moment bound, with the one-center moment
expanded as the explicit binomial Hamming-sphere sum.  This is the exact
analytic expression that a Bernstein estimate must bound. -/
def OneCenterDistanceSumExponentialMomentBound
    (n N rIn rOut T : ℕ) (lam eps : ℝ) : Prop :=
  0 < lam ∧
    Real.exp (lam * (T : ℝ)) *
      (((∑ i ∈ Finset.range (n + 1),
        (Nat.choose n i : ℝ) *
          Real.exp
            (-(lam *
              ((if rIn ≤ i ∧ i ≤ rOut then 2 ^ (rOut - i) else 0 : ℕ) : ℝ)))) /
        (2 ^ n : ℝ)) ^ N) ≤ eps

theorem oneCenterExponentialMomentBound_of_distanceSum
    {n N rIn rOut T : ℕ} {lam eps : ℝ}
    (hbound : OneCenterDistanceSumExponentialMomentBound n N rIn rOut T lam eps) :
    OneCenterExponentialMomentBound n N rIn rOut T lam eps := by
  rcases hbound with ⟨hlam, hmoment⟩
  refine ⟨hlam, ?_⟩
  simpa [oneCenterNegativeExponentialMoment_eq_distance_sum] using hmoment

theorem targetFailureProbabilityReal_le_exponentialMoment {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) {lam : ℝ} (hlam : 0 < lam) :
    targetFailureProbabilityReal (N := N) rIn rOut T target ≤
      targetLowerTailExponentialMoment (N := N) rIn rOut T target lam := by
  classical
  have hmarkov :=
    uniformProbabilityReal_le_expect_div_of_event_le
      (P := fun sample : CenterSample n N => sampleTargetFails rIn rOut T target sample)
      (X := fun sample : CenterSample n N =>
        Real.exp (lam * ((T : ℝ) -
          (sampleTotalContribution rIn rOut target sample : ℝ))))
      (a := 1)
      (by norm_num)
      (fun sample => Real.exp_nonneg _)
      (fun sample hfail => by
        have hlt :
            (sampleTotalContribution rIn rOut target sample : ℝ) < (T : ℝ) := by
          exact_mod_cast hfail
        have hdiff :
            0 < (T : ℝ) - (sampleTotalContribution rIn rOut target sample : ℝ) :=
          sub_pos.mpr hlt
        have harg :
            0 < lam * ((T : ℝ) -
              (sampleTotalContribution rIn rOut target sample : ℝ)) :=
          mul_pos hlam hdiff
        have hexp :
            Real.exp 0 <
              Real.exp (lam * ((T : ℝ) -
                (sampleTotalContribution rIn rOut target sample : ℝ))) :=
          Real.exp_lt_exp.mpr harg
        simpa using hexp.le)
  simpa [targetFailureProbabilityReal, targetLowerTailExponentialMoment] using hmarkov

theorem targetFailureProbability_le_of_exponentialMoment_le {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) {lam : ℝ} {eps : ℚ}
    (hlam : 0 < lam)
    (hmoment :
      targetLowerTailExponentialMoment (N := N) rIn rOut T target lam ≤ (eps : ℝ)) :
    targetFailureProbability (N := N) rIn rOut T target ≤ eps := by
  have hreal :
      targetFailureProbabilityReal (N := N) rIn rOut T target ≤ (eps : ℝ) :=
    (targetFailureProbabilityReal_le_exponentialMoment target hlam).trans hmoment
  have hcast :
      ((targetFailureProbability (N := N) rIn rOut T target : ℚ) : ℝ) ≤
        (eps : ℝ) := by
    simpa [targetFailureProbabilityReal_eq_coe] using hreal
  exact_mod_cast hcast

theorem targetFailureProbability_le_exp_neg_of_exponentialMoment_le {n N rIn rOut T : ℕ}
    (target : HypercubeVertex n) {lam exponent : ℝ} {eps : ℚ}
    (hlam : 0 < lam)
    (hmoment :
      targetLowerTailExponentialMoment (N := N) rIn rOut T target lam ≤
        Real.exp (-exponent))
    (hexp : Real.exp (-exponent) ≤ (eps : ℝ)) :
    targetFailureProbability (N := N) rIn rOut T target ≤ eps :=
  targetFailureProbability_le_of_exponentialMoment_le target hlam (hmoment.trans hexp)

/-- Fixed-target failure bound obtained from the optimized chord Chernoff
estimate. -/
theorem targetFailureProbability_le_exp_optimized_chord
    {n N rIn rOut T : ℕ} (target : HypercubeVertex n) {gap : ℝ} {eps : ℚ}
    (hgap_pos : 0 < gap)
    (hmu_pos :
      0 < (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)
    (hmean :
      (T : ℝ) + gap ≤
        (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) ≤
        (eps : ℝ)) :
    targetFailureProbability (N := N) rIn rOut T target ≤ eps := by
  let mu : ℝ := (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target
  let B : ℝ := (2 ^ (rOut - rIn) : ℝ)
  let lam : ℝ := gap / (2 * B * mu)
  have hmu_pos' : 0 < mu := by simpa [mu] using hmu_pos
  have hlam_pos : 0 < lam := by
    have hden_pos : 0 < 2 * B * mu := by
      have hB_pos : 0 < B := by positivity
      positivity
    exact div_pos hgap_pos hden_pos
  have hmoment :=
    targetLowerTailExponentialMoment_le_exp_optimized_chord
      (N := N) (rIn := rIn) (rOut := rOut) (T := T)
      target (gap := gap) hgap_pos.le hmu_pos hmean
  have hmoment' :
      targetLowerTailExponentialMoment (N := N) rIn rOut T target lam ≤
        Real.exp
          (-(gap ^ 2 /
            (4 * (2 ^ (rOut - rIn) : ℝ) *
              ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) := by
    simpa [lam, B, mu] using hmoment
  exact targetFailureProbability_le_of_exponentialMoment_le
    target hlam_pos (hmoment'.trans hexp)

/-- Probability that some target fails. -/
noncomputable def globalFailureProbability {n N : ℕ} (rIn rOut T : ℕ) : ℚ :=
  uniformProbability fun sample : CenterSample n N =>
    sampleFailsSomeTarget rIn rOut T sample

/-- Union bound over all targets. -/
theorem globalFailureProbability_le_sum_targetFailureProbability {n N rIn rOut T : ℕ} :
    globalFailureProbability (n := n) (N := N) rIn rOut T ≤
      ∑ target : HypercubeVertex n,
        targetFailureProbability (N := N) rIn rOut T target := by
  classical
  change
    uniformProbability
        (fun sample : CenterSample n N =>
          ∃ target : HypercubeVertex n,
            sampleTotalContribution rIn rOut target sample < T) ≤
      ∑ target : HypercubeVertex n,
        uniformProbability
          (fun sample : CenterSample n N =>
            sampleTotalContribution rIn rOut target sample < T)
  exact
      (uniformProbability_exists_le_sum
        (Ω := CenterSample n N) (ι := HypercubeVertex n)
        (fun target sample => sampleTotalContribution rIn rOut target sample < T))

/-- Probabilistic-method extraction: if the probability that some target fails
is less than one, then a good center sample exists. -/
theorem exists_goodCenterSample_of_globalFailureProbability_lt_one {n N rIn rOut T : ℕ}
    (hprob : globalFailureProbability (n := n) (N := N) rIn rOut T < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by
  classical
  rcases exists_not_of_uniformProbability_lt_one
      (Ω := CenterSample n N)
      (P := fun sample : CenterSample n N =>
        sampleFailsSomeTarget rIn rOut T sample)
      (by simpa [globalFailureProbability] using hprob) with
    ⟨sample, hnot_fail⟩
  refine ⟨sample, ?_⟩
  intro target
  have hnot_lt :
      ¬ sampleTotalContribution rIn rOut target sample < T := by
    intro hlt
    exact hnot_fail ⟨target, hlt⟩
  have hle : T ≤ sampleTotalContribution rIn rOut target sample :=
    Nat.le_of_not_gt hnot_lt
  simpa [annulusTotalContribution_toList] using hle

/-- Costed high-demand conclusion from a global failure-probability bound. -/
theorem hasSolvableAtMostSize_of_globalFailureProbability_lt_one {n N rIn rOut T : ℕ}
    (hprob : globalFailureProbability (n := n) (N := N) rIn rOut T < 1) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by
  classical
  rcases exists_goodCenterSample_of_globalFailureProbability_lt_one hprob with
    ⟨sample, hgood⟩
  have h := hasSolvableAtMostSize_of_goodCenterList hgood
  simpa [CenterSample.toList] using h

/-- High-demand version of the probabilistic-method extraction.  The selected
stack-list distribution has occupied piles of size at least `2^rOut`. -/
theorem hasHighDemandDistribution_of_globalFailureProbability_lt_one
    {n N rIn rOut T : ℕ}
    (hprob : globalFailureProbability (n := n) (N := N) rIn rOut T < 1) :
    HasHighDemandDistribution n T (N * 2 ^ rOut) (2 ^ rOut) := by
  classical
  rcases exists_goodCenterSample_of_globalFailureProbability_lt_one hprob with
    ⟨sample, hgood⟩
  have h := hasHighDemandDistribution_of_goodCenterList hgood
  simpa [CenterSample.toList] using h

/-- The Chernoff input used in this project: the annulus captures enough
expected contribution for every target. -/
def ChernoffMeanLowerBound (n N rIn rOut T : ℕ) : Prop :=
  ∀ target : HypercubeVertex n,
    (T : ℚ) ≤ sampleContributionExpectation (n := n) (N := N) rIn rOut target

theorem chernoffMeanLowerBound_iff_annulusMean {n N rIn rOut T : ℕ} :
    ChernoffMeanLowerBound n N rIn rOut T ↔
      (T : ℚ) ≤ (N : ℚ) * annulusMean n rIn rOut := by
  constructor
  · intro hmean
    have htarget := hmean (fun _ : Fin n => false)
    simpa [sampleContributionExpectation_eq_nat_mul_annulusMean] using htarget
  · intro hmean target
    simpa [sampleContributionExpectation_eq_nat_mul_annulusMean] using hmean

theorem chernoffMeanLowerBound_of_annulusMean {n N rIn rOut T : ℕ}
    (hmean : (T : ℚ) ≤ (N : ℚ) * annulusMean n rIn rOut) :
    ChernoffMeanLowerBound n N rIn rOut T :=
  chernoffMeanLowerBound_iff_annulusMean.mpr hmean

/-- The Bernstein input used in this project: every fixed target has small lower
tail probability. -/
def BernsteinTargetFailureBound (n N rIn rOut T : ℕ) (eps : ℚ) : Prop :=
  ∀ target : HypercubeVertex n,
    targetFailureProbability (n := n) (N := N) rIn rOut T target ≤ eps

/-- Target-failure bound with the target-independent real annulus mean
substituted for the fixed-target mean. -/
theorem bernsteinTargetFailureBound_of_optimized_chord_annulusMean
    {n N rIn rOut T : ℕ} {gap : ℝ} {eps : ℚ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ))))) ≤
        (eps : ℝ)) :
    BernsteinTargetFailureBound n N rIn rOut T eps := by
  intro target
  have hmu_pos_target :
      0 < (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target := by
    simpa [oneCenterContributionExpectationReal_eq_annulusMean]
      using hmu_pos
  have hmean_target :
      (T : ℝ) + gap ≤
        (N : ℝ) * oneCenterContributionExpectationReal rIn rOut target := by
    simpa [oneCenterContributionExpectationReal_eq_annulusMean]
      using hmean
  have hexp_target :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * oneCenterContributionExpectationReal rIn rOut target)))) ≤
        (eps : ℝ) := by
    simpa [oneCenterContributionExpectationReal_eq_annulusMean]
      using hexp
  exact targetFailureProbability_le_exp_optimized_chord
    target hgap_pos hmu_pos_target hmean_target hexp_target

/-- Chernoff-style exponential moment input: for each fixed target, there is a
positive exponential parameter whose lower-tail moment is at most `eps`. -/
def ChernoffExponentialMomentBound (n N rIn rOut T : ℕ) (eps : ℝ) : Prop :=
  ∀ target : HypercubeVertex n,
    ∃ lam : ℝ,
      0 < lam ∧
        targetLowerTailExponentialMoment (n := n) (N := N) rIn rOut T target lam ≤ eps

theorem chernoffExponentialMomentBound_of_oneCenterExponentialMomentBound
    {n N rIn rOut T : ℕ} {lam eps : ℝ}
    (hbound : OneCenterExponentialMomentBound n N rIn rOut T lam eps) :
    ChernoffExponentialMomentBound n N rIn rOut T eps := by
  intro target
  rcases hbound with ⟨hlam, hmoment⟩
  refine ⟨lam, hlam, ?_⟩
  rw [targetLowerTailExponentialMoment_eq]
  rw [oneCenterNegativeExponentialMoment_eq_of_targets
    target (fun _ : Fin n => false) lam]
  exact hmoment

theorem bernsteinTargetFailureBound_of_chernoffExponentialMomentBound
    {n N rIn rOut T : ℕ} {epsReal : ℝ} {eps : ℚ}
    (hmoment : ChernoffExponentialMomentBound n N rIn rOut T epsReal)
    (heps : epsReal ≤ (eps : ℝ)) :
    BernsteinTargetFailureBound n N rIn rOut T eps := by
  intro target
  rcases hmoment target with ⟨lam, hlam, hmoment_target⟩
  exact targetFailureProbability_le_of_exponentialMoment_le target hlam
    (hmoment_target.trans heps)

/-- The usual Bernstein lower-tail exponent, parameterized by a variance proxy,
a per-summand scale, and the gap between the mean and threshold. -/
noncomputable def bernsteinExponent (variance scale gap : ℝ) : ℝ :=
  gap ^ 2 / (2 * (variance + scale * gap / 3))

/-- The constant calculation used in the paper after Bernstein is applied with
variance proxy `2 * B * T`, scale `B`, and gap `delta*T/4`. -/
theorem bernsteinExponent_two_width_mul_T_ge
    {delta T B : ℝ} (hdelta_nonneg : 0 ≤ delta) (hdelta_le : delta ≤ 1 / 2)
    (hT_pos : 0 < T) (hB_pos : 0 < B) :
    (delta ^ 2 * T) / (96 * B) ≤
      bernsteinExponent (2 * B * T) B (delta * T / 4) := by
  have hT_nonneg : 0 ≤ T := hT_pos.le
  have hden_pos : 0 < 2 * (2 * B * T + B * (delta * T / 4) / 3) := by
    have hBT_pos : 0 < B * T := mul_pos hB_pos hT_pos
    have hfactor_pos : 0 < 2 + delta / 12 := by nlinarith
    have hprod : 0 < 2 * (B * T) * (2 + delta / 12) := by positivity
    convert hprod using 1
    ring
  have hden_le : 2 * (2 * B * T + B * (delta * T / 4) / 3) ≤
      5 * B * T := by
    have hBT_nonneg : 0 ≤ B * T := (mul_pos hB_pos hT_pos).le
    have hdelta_div : delta / 6 ≤ 1 := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hdelta_div hBT_nonneg
    nlinarith
  have hnum_nonneg : 0 ≤ (delta * T / 4) ^ 2 := sq_nonneg _
  have hmain :
      (delta * T / 4) ^ 2 / (5 * B * T) ≤
        (delta * T / 4) ^ 2 /
          (2 * (2 * B * T + B * (delta * T / 4) / 3)) := by
    exact div_le_div_of_nonneg_left hnum_nonneg hden_pos hden_le
  have hcoarse :
      (delta ^ 2 * T) / (96 * B) ≤ (delta * T / 4) ^ 2 / (5 * B * T) := by
    have hB_ne : B ≠ 0 := ne_of_gt hB_pos
    have hT_ne : T ≠ 0 := ne_of_gt hT_pos
    field_simp [hB_ne, hT_ne]
    nlinarith [sq_nonneg delta, hT_pos, hB_pos]
  exact hcoarse.trans (by simpa [bernsteinExponent] using hmain)

/-- Bernstein-style exponential moment input.  The analytic Bernstein argument
must prove this proposition for the parameters chosen in the upper-bound proof. -/
def BernsteinExponentialMomentBound (n N rIn rOut T : ℕ)
    (variance scale gap : ℝ) : Prop :=
  ChernoffExponentialMomentBound n N rIn rOut T
    (Real.exp (-(bernsteinExponent variance scale gap)))

theorem bernsteinExponentialMomentBound_of_oneCenterDistanceSum
    {n N rIn rOut T : ℕ} {lam variance scale gap : ℝ}
    (hbound :
      OneCenterDistanceSumExponentialMomentBound n N rIn rOut T lam
        (Real.exp (-(bernsteinExponent variance scale gap)))) :
    BernsteinExponentialMomentBound n N rIn rOut T variance scale gap :=
  chernoffExponentialMomentBound_of_oneCenterExponentialMomentBound
    (oneCenterExponentialMomentBound_of_distanceSum hbound)

theorem bernsteinTargetFailureBound_of_bernsteinExponentialMomentBound
    {n N rIn rOut T : ℕ} {variance scale gap : ℝ} {eps : ℚ}
    (hmoment : BernsteinExponentialMomentBound n N rIn rOut T variance scale gap)
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ)) :
    BernsteinTargetFailureBound n N rIn rOut T eps :=
  bernsteinTargetFailureBound_of_chernoffExponentialMomentBound hmoment hexp

/-- The usual union-bound finish from a Bernstein fixed-target estimate. -/
theorem exists_goodCenterSample_of_bernstein_bound {n N rIn rOut T : ℕ} {eps : ℚ}
    (hbernstein : BernsteinTargetFailureBound n N rIn rOut T eps)
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by
  classical
  have hglobal_le := globalFailureProbability_le_sum_targetFailureProbability
    (n := n) (N := N) (rIn := rIn) (rOut := rOut) (T := T)
  have hsum_le :
      (∑ target : HypercubeVertex n,
        targetFailureProbability (N := N) rIn rOut T target) ≤
        ∑ _target : HypercubeVertex n, eps := by
    exact Finset.sum_le_sum fun target _ => hbernstein target
  have hsum_eps :
      (∑ _target : HypercubeVertex n, eps) =
        (Fintype.card (HypercubeVertex n) : ℚ) * eps := by
    simp
  have hprob :
      globalFailureProbability (n := n) (N := N) rIn rOut T < 1 := by
    exact lt_of_le_of_lt (hglobal_le.trans hsum_le) (by simpa [hsum_eps] using hunion)
  exact exists_goodCenterSample_of_globalFailureProbability_lt_one hprob

/-- Costed high-demand conclusion from the Bernstein fixed-target estimate. -/
theorem hasSolvableAtMostSize_of_bernstein_bound {n N rIn rOut T : ℕ} {eps : ℚ}
    (hbernstein : BernsteinTargetFailureBound n N rIn rOut T eps)
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by
  classical
  rcases exists_goodCenterSample_of_bernstein_bound hbernstein hunion with
    ⟨sample, hgood⟩
  have h := hasSolvableAtMostSize_of_goodCenterList hgood
  simpa [CenterSample.toList] using h

theorem hypercube_card_mul_inv_two_pow_succ_lt_one (n : ℕ) :
    (Fintype.card (HypercubeVertex n) : ℚ) *
        ((1 : ℚ) / (2 ^ (n + 1) : ℚ)) < 1 := by
  have hpow_succ_ne : (2 ^ (n + 1) : ℚ) ≠ 0 := by positivity
  simp only [card_vertex, Nat.cast_pow, Nat.cast_ofNat]
  field_simp [hpow_succ_ne]
  exact pow_lt_pow_right₀ (by norm_num : (1 : ℚ) < 2) (Nat.lt_succ_self n)

/-- Probabilistic-method finish from the optimized chord Chernoff estimate,
using the target-independent annulus mean. -/
theorem exists_goodCenterSample_of_optimized_chord_annulusMean
    {n N rIn rOut T : ℕ} {gap : ℝ} {eps : ℚ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ))))) ≤
        (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList :=
  exists_goodCenterSample_of_bernstein_bound
    (bernsteinTargetFailureBound_of_optimized_chord_annulusMean
      hgap_pos hmu_pos hmean hexp)
    hunion

/-- Costed high-demand conclusion from the optimized chord Chernoff estimate. -/
theorem hasSolvableAtMostSize_of_optimized_chord_annulusMean
    {n N rIn rOut T : ℕ} {gap : ℝ} {eps : ℚ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ))))) ≤
        (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) :=
  hasSolvableAtMostSize_of_bernstein_bound
    (bernsteinTargetFailureBound_of_optimized_chord_annulusMean
      hgap_pos hmu_pos hmean hexp)
    hunion

/-- Optimized chord Chernoff finish with the standard fixed-target failure
budget `2^-(n+1)`, which is strong enough for the union bound over `Q_n`. -/
theorem exists_goodCenterSample_of_optimized_chord_annulusMean_inv_two
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ))))) ≤
        (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ)) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by
  exact exists_goodCenterSample_of_optimized_chord_annulusMean
    (eps := (1 : ℚ) / (2 ^ (n + 1) : ℚ))
    hgap_pos hmu_pos hmean (by simpa using hexp)
    (hypercube_card_mul_inv_two_pow_succ_lt_one n)

/-- Costed high-demand conclusion with fixed-target failure budget
`2^-(n+1)`. -/
theorem hasSolvableAtMostSize_of_optimized_chord_annulusMean_inv_two
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hexp :
      Real.exp
        (-(gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ))))) ≤
        (((1 : ℚ) / (2 ^ (n + 1) : ℚ) : ℚ) : ℝ)) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by
  exact hasSolvableAtMostSize_of_optimized_chord_annulusMean
    (eps := (1 : ℚ) / (2 ^ (n + 1) : ℚ))
    hgap_pos hmu_pos hmean (by simpa using hexp)
    (hypercube_card_mul_inv_two_pow_succ_lt_one n)

/-- Version of the optimized chord finish where the union-bound comparison is
discharged by the exponent inequality `exponent ≥ (n+1) log 2`. -/
theorem exists_goodCenterSample_of_optimized_chord_annulusMean_log
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList :=
  exists_goodCenterSample_of_optimized_chord_annulusMean_inv_two
    hgap_pos hmu_pos hmean
    (exp_neg_le_inv_two_pow_succ_of_log_le n hlog)

/-- Costed high-demand conclusion from the optimized chord estimate and the
exponent condition `gap^2/(4 B_0 mu) ≥ (n+1) log 2`. -/
theorem hasSolvableAtMostSize_of_optimized_chord_annulusMean_log
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) :=
  hasSolvableAtMostSize_of_optimized_chord_annulusMean_inv_two
    hgap_pos hmu_pos hmean
    (exp_neg_le_inv_two_pow_succ_of_log_le n hlog)

/-- The same log-threshold finish, deriving positivity of the mean from the
positive gap and the inequality `T + gap ≤ mean`. -/
theorem exists_goodCenterSample_of_optimized_chord_annulusMean_log_of_mean_gap
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList := by
  have hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ) := by
    have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
    nlinarith
  exact exists_goodCenterSample_of_optimized_chord_annulusMean_log
    hgap_pos hmu_pos hmean hlog

/-- Costed high-demand conclusion with positivity of the mean derived from the
mean-gap hypothesis. -/
theorem hasSolvableAtMostSize_of_optimized_chord_annulusMean_log_of_mean_gap
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) := by
  have hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ) := by
    have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
    nlinarith
  exact hasSolvableAtMostSize_of_optimized_chord_annulusMean_log
    hgap_pos hmu_pos hmean hlog

/-- High-demand conclusion from the optimized chord estimate and logarithmic
union-bound criterion. -/
theorem hasHighDemandDistribution_of_optimized_chord_annulusMean_log_of_mean_gap
    {n N rIn rOut T : ℕ} {gap : ℝ}
    (hgap_pos : 0 < gap)
    (hmean : (T : ℝ) + gap ≤ (N : ℝ) * (annulusMean n rIn rOut : ℝ))
    (hlog :
      ((n + 1 : ℕ) : ℝ) * Real.log 2 ≤
        gap ^ 2 /
          (4 * (2 ^ (rOut - rIn) : ℝ) *
            ((N : ℝ) * (annulusMean n rIn rOut : ℝ)))) :
    HasHighDemandDistribution n T (N * 2 ^ rOut) (2 ^ rOut) := by
  have hmu_pos : 0 < (N : ℝ) * (annulusMean n rIn rOut : ℝ) := by
    have hT_nonneg : 0 ≤ (T : ℝ) := by positivity
    nlinarith
  have hfailure :
      globalFailureProbability (n := n) (N := N) rIn rOut T < 1 := by
    have hbernstein :=
      bernsteinTargetFailureBound_of_optimized_chord_annulusMean
        (eps := (1 : ℚ) / (2 ^ (n + 1) : ℚ))
        hgap_pos hmu_pos hmean
        (by
          simpa using exp_neg_le_inv_two_pow_succ_of_log_le n hlog)
    have hglobal_le := globalFailureProbability_le_sum_targetFailureProbability
      (n := n) (N := N) (rIn := rIn) (rOut := rOut) (T := T)
    have hsum_le :
        (∑ target : HypercubeVertex n,
          targetFailureProbability (N := N) rIn rOut T target) ≤
          ∑ _target : HypercubeVertex n,
            ((1 : ℚ) / (2 ^ (n + 1) : ℚ)) := by
      exact Finset.sum_le_sum fun target _ => hbernstein target
    have hsum_eps :
        (∑ _target : HypercubeVertex n,
            ((1 : ℚ) / (2 ^ (n + 1) : ℚ))) =
          (Fintype.card (HypercubeVertex n) : ℚ) *
            ((1 : ℚ) / (2 ^ (n + 1) : ℚ)) := by
      simp
    exact lt_of_le_of_lt (hglobal_le.trans hsum_le)
      (by
        simpa [hsum_eps] using
          hypercube_card_mul_inv_two_pow_succ_lt_one n)
  exact hasHighDemandDistribution_of_globalFailureProbability_lt_one hfailure

theorem exists_goodCenterSample_of_bernsteinExponentialMomentBound
    {n N rIn rOut T : ℕ} {variance scale gap : ℝ} {eps : ℚ}
    (hmoment : BernsteinExponentialMomentBound n N rIn rOut T variance scale gap)
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList :=
  exists_goodCenterSample_of_bernstein_bound
    (bernsteinTargetFailureBound_of_bernsteinExponentialMomentBound hmoment hexp) hunion

theorem hasSolvableAtMostSize_of_bernsteinExponentialMomentBound
    {n N rIn rOut T : ℕ} {variance scale gap : ℝ} {eps : ℚ}
    (hmoment : BernsteinExponentialMomentBound n N rIn rOut T variance scale gap)
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) :=
  hasSolvableAtMostSize_of_bernstein_bound
    (bernsteinTargetFailureBound_of_bernsteinExponentialMomentBound hmoment hexp) hunion

theorem exists_goodCenterSample_of_oneCenterDistanceSum
    {n N rIn rOut T : ℕ} {lam variance scale gap : ℝ} {eps : ℚ}
    (hbound :
      OneCenterDistanceSumExponentialMomentBound n N rIn rOut T lam
        (Real.exp (-(bernsteinExponent variance scale gap))))
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    ∃ sample : CenterSample n N,
      IsGoodCenterList n rIn rOut T sample.toList :=
  exists_goodCenterSample_of_bernsteinExponentialMomentBound
    (bernsteinExponentialMomentBound_of_oneCenterDistanceSum hbound) hexp hunion

theorem hasSolvableAtMostSize_of_oneCenterDistanceSum
    {n N rIn rOut T : ℕ} {lam variance scale gap : ℝ} {eps : ℚ}
    (hbound :
      OneCenterDistanceSumExponentialMomentBound n N rIn rOut T lam
        (Real.exp (-(bernsteinExponent variance scale gap))))
    (hexp : Real.exp (-(bernsteinExponent variance scale gap)) ≤ (eps : ℝ))
    (hunion : (Fintype.card (HypercubeVertex n) : ℚ) * eps < 1) :
    HasSolvableAtMostSize (graph n) T (N * 2 ^ rOut) :=
  hasSolvableAtMostSize_of_bernsteinExponentialMomentBound
    (bernsteinExponentialMomentBound_of_oneCenterDistanceSum hbound) hexp hunion

end Hypercube

end PebblingLean
