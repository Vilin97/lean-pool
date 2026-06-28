/-
Copyright (c) 2026 Nelson Spence. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nelson Spence
-/

import Mathlib.Data.Nat.Choose.Basic
import LeanPool.OrdvecFormalization.ExponentialTilt

/-!
# Fisher noncentral hypergeometric feasible support

This file instantiates the exponential-tilt theorem for the feasible overlap
range of a Fisher noncentral hypergeometric model.

The formal support is shifted to `0, ..., hi - lo`, where the actual overlap is
`lo + i`. Tilting by `i` is normalization-equivalent to tilting by the actual
overlap, since the missing `exp (θ * lo)` factor is common to every support
point.
-/

open scoped NNReal

namespace OrdvecFormalization

/-- Parameters for a feasible overlap problem. -/
structure FNCHParams where
  /-- Universe size. -/
  N : ℕ
  /-- Number of marked items in the universe. -/
  k : ℕ
  /-- Number of draws. -/
  draws : ℕ
  /-- The marked count is feasible. -/
  k_le_N : k ≤ N
  /-- The draw count is feasible. -/
  draws_le_N : draws ≤ N

namespace FNCHParams

/-- Lower feasible overlap count: `max(0, k + draws - N)`, via truncated subtraction. -/
def lo (p : FNCHParams) : ℕ :=
  p.k + p.draws - p.N

/-- Upper feasible overlap count: `min(k, draws)`. -/
def hi (p : FNCHParams) : ℕ :=
  min p.k p.draws

theorem lo_le_k (p : FNCHParams) : p.lo ≤ p.k := by
  unfold lo
  have hdraws : p.draws ≤ p.N := p.draws_le_N
  omega

theorem lo_le_draws (p : FNCHParams) : p.lo ≤ p.draws := by
  unfold lo
  have hk : p.k ≤ p.N := p.k_le_N
  omega

theorem lo_le_hi (p : FNCHParams) : p.lo ≤ p.hi := by
  unfold hi
  exact le_min (p.lo_le_k) (p.lo_le_draws)

/-- The shifted feasible support. -/
abbrev support (p : FNCHParams) := Support (p.hi - p.lo)

/-- The actual overlap count represented by a shifted support point. -/
def overlap (p : FNCHParams) (x : p.support) : ℕ :=
  p.lo + x.val

theorem lo_le_overlap (p : FNCHParams) (x : p.support) : p.lo ≤ p.overlap x := by
  unfold overlap
  exact Nat.le_add_right p.lo x.val

theorem overlap_le_hi (p : FNCHParams) (x : p.support) : p.overlap x ≤ p.hi := by
  unfold overlap
  have hx : x.val ≤ p.hi - p.lo := Nat.lt_succ_iff.mp x.isLt
  have hlo : p.lo ≤ p.hi := p.lo_le_hi
  omega

theorem overlap_le_k (p : FNCHParams) (x : p.support) : p.overlap x ≤ p.k := by
  exact (p.overlap_le_hi x).trans (min_le_left p.k p.draws)

theorem overlap_le_draws (p : FNCHParams) (x : p.support) :
    p.overlap x ≤ p.draws := by
  exact (p.overlap_le_hi x).trans (min_le_right p.k p.draws)

theorem draws_sub_overlap_le_N_sub_k (p : FNCHParams) (x : p.support) :
    p.draws - p.overlap x ≤ p.N - p.k := by
  have hk : p.k ≤ p.N := p.k_le_N
  have hlo : p.k + p.draws - p.N ≤ p.overlap x := by
    simpa [lo] using p.lo_le_overlap x
  omega

end FNCHParams

/-- The feasible-support binomial base weight for FNCH. -/
noncomputable def fnchBaseWeight (p : FNCHParams) (x : p.support) : ℝ≥0 :=
  (p.k.choose (p.overlap x) : ℝ≥0) *
    ((p.N - p.k).choose (p.draws - p.overlap x) : ℝ≥0)

/-- FNCH base weights are strictly positive on the feasible support. -/
theorem fnchBaseWeight_pos (p : FNCHParams) (x : p.support) :
    0 < fnchBaseWeight p x := by
  have h₁Nat : 0 < p.k.choose (p.overlap x) :=
    Nat.choose_pos (p.overlap_le_k x)
  have h₂Nat : 0 < (p.N - p.k).choose (p.draws - p.overlap x) :=
    Nat.choose_pos (p.draws_sub_overlap_le_N_sub_k x)
  have h₁ : 0 < (p.k.choose (p.overlap x) : ℝ≥0) := by
    exact (Nat.cast_pos' (α := ℝ≥0)).mpr h₁Nat
  have h₂ : 0 < ((p.N - p.k).choose (p.draws - p.overlap x) : ℝ≥0) := by
    exact (Nat.cast_pos' (α := ℝ≥0)).mpr h₂Nat
  exact mul_pos h₁ h₂

/-- Positive base weights for the feasible FNCH support. -/
noncomputable def fnchBase (p : FNCHParams) : PosWeights (p.hi - p.lo) where
  weight x := fnchBaseWeight p x
  pos x := fnchBaseWeight_pos p x

/-- The finite FNCH family as an exponential tilt of feasible binomial base weights. -/
noncomputable def fnchPMF (p : FNCHParams) (θ : ℝ) : PosPMF (p.hi - p.lo) :=
  exponentialTilt (fnchBase p) θ

/-- FNCH PMFs have MLR as the noncentrality parameter increases. -/
theorem fnch_hasMLR (p : FNCHParams) {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) :
    HasMLR (fnchPMF p θ₀) (fnchPMF p θ₁) :=
  exponentialTilt_hasMLR (fnchBase p) hθ

/-- Strict-parameter corollary for FNCH PMFs. -/
theorem fnch_hasMLR_of_lt (p : FNCHParams) {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) :
    HasMLR (fnchPMF p θ₀) (fnchPMF p θ₁) :=
  fnch_hasMLR p hθ.le

/-- FNCH Bayes admit sets are thresholds on the feasible support. -/
theorem fnch_bayesAdmit_isThreshold (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      bayesAdmit (fnchPMF p θ₀) (fnchPMF p θ₁) prior x ↔
        x ∈ thresholdSet (p.hi - p.lo) cut :=
  exponentialTilt_bayesAdmit_isThreshold (fnchBase p) hθ prior

/-- FNCH Bayes risk is minimized by a threshold on the feasible support. -/
theorem fnch_threshold_bayesRisk_optimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      bayesRisk (fnchPMF p θ₀) (fnchPMF p θ₁) prior
          (thresholdSet (p.hi - p.lo) cut) ≤
        bayesRisk (fnchPMF p θ₀) (fnchPMF p θ₁) prior R :=
  exponentialTilt_threshold_bayesRisk_optimal (fnchBase p) hθ prior

/-- Cost-sensitive FNCH Bayes admit sets are thresholds on the feasible support. -/
theorem fnch_costedBayesAdmit_isThreshold (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      costedBayesAdmit (fnchPMF p θ₀) (fnchPMF p θ₁) prior costs x ↔
        x ∈ thresholdSet (p.hi - p.lo) cut :=
  exponentialTilt_costedBayesAdmit_isThreshold (fnchBase p) hθ prior costs

/-- Cost-sensitive FNCH Bayes risk is minimized by a threshold on the feasible support. -/
theorem fnch_costed_threshold_bayesRisk_optimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      costedBayesRisk (fnchPMF p θ₀) (fnchPMF p θ₁) prior costs
          (thresholdSet (p.hi - p.lo) cut) ≤
        costedBayesRisk (fnchPMF p θ₀) (fnchPMF p θ₁) prior costs R :=
  exponentialTilt_costed_threshold_bayesRisk_optimal (fnchBase p) hθ prior costs

/--
The threshold set written in actual overlap coordinates.

For `cut : Fin (hi - lo + 2)`, the actual-overlap boundary is `lo + cut`.
-/
def actualOverlapThresholdSet (p : FNCHParams) (cut : Fin (p.hi - p.lo + 2)) :
    Set p.support :=
  {x | p.lo + cut.val ≤ p.overlap x}

/-- Actual-overlap thresholds and shifted-support thresholds define the same set. -/
theorem mem_actualOverlapThresholdSet_iff (p : FNCHParams)
    (cut : Fin (p.hi - p.lo + 2)) (x : p.support) :
    x ∈ actualOverlapThresholdSet p cut ↔
      x ∈ thresholdSet (p.hi - p.lo) cut := by
  unfold actualOverlapThresholdSet thresholdSet FNCHParams.overlap
  exact Nat.add_le_add_iff_left

/-- Actual-overlap threshold sets are the same as the shifted threshold sets. -/
theorem actualOverlapThresholdSet_eq_thresholdSet (p : FNCHParams)
    (cut : Fin (p.hi - p.lo + 2)) :
    actualOverlapThresholdSet p cut = thresholdSet (p.hi - p.lo) cut := by
  ext x
  exact mem_actualOverlapThresholdSet_iff p cut x

/-- FNCH Bayes admit sets are thresholds in actual overlap coordinates. -/
theorem fnch_bayesAdmit_isActualOverlapThreshold (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      bayesAdmit (fnchPMF p θ₀) (fnchPMF p θ₁) prior x ↔
        x ∈ actualOverlapThresholdSet p cut := by
  rcases fnch_bayesAdmit_isThreshold p hθ prior with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro x
  exact (hcut x).trans (mem_actualOverlapThresholdSet_iff p cut x).symm

/-- FNCH Bayes risk is minimized by a threshold in actual overlap coordinates. -/
theorem fnch_actualOverlapThreshold_bayesRisk_optimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      bayesRisk (fnchPMF p θ₀) (fnchPMF p θ₁) prior
          (actualOverlapThresholdSet p cut) ≤
        bayesRisk (fnchPMF p θ₀) (fnchPMF p θ₁) prior R := by
  rcases fnch_threshold_bayesRisk_optimal p hθ prior with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro R
  simpa [actualOverlapThresholdSet_eq_thresholdSet p cut] using hcut R

/-- Cost-sensitive FNCH Bayes admit sets are thresholds in actual overlap coordinates. -/
theorem fnch_costedBayesAdmit_isActualOverlapThreshold (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      costedBayesAdmit (fnchPMF p θ₀) (fnchPMF p θ₁) prior costs x ↔
        x ∈ actualOverlapThresholdSet p cut := by
  rcases fnch_costedBayesAdmit_isThreshold p hθ prior costs with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro x
  exact (hcut x).trans (mem_actualOverlapThresholdSet_iff p cut x).symm

/-- Cost-sensitive FNCH Bayes risk is minimized by an actual-overlap threshold. -/
theorem fnch_costed_actualOverlapThreshold_bayesRisk_optimal (p : FNCHParams)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      costedBayesRisk (fnchPMF p θ₀) (fnchPMF p θ₁) prior costs
          (actualOverlapThresholdSet p cut) ≤
        costedBayesRisk (fnchPMF p θ₀) (fnchPMF p θ₁) prior costs R := by
  rcases fnch_costed_threshold_bayesRisk_optimal p hθ prior costs with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro R
  simpa [actualOverlapThresholdSet_eq_thresholdSet p cut] using hcut R

/-- Literal FNCH weight using the actual overlap count in the exponential tilt. -/
noncomputable def fnchActualWeight (p : FNCHParams) (θ : ℝ) (x : p.support) : ℝ≥0 :=
  fnchBaseWeight p x * nnexp (θ * p.overlap x)

/-- Literal FNCH weights are positive on the feasible support. -/
theorem fnchActualWeight_pos (p : FNCHParams) (θ : ℝ) (x : p.support) :
    0 < fnchActualWeight p θ x := by
  exact mul_pos (fnchBaseWeight_pos p x) (nnexp_pos (θ * p.overlap x))

/-- The actual-overlap exponential factor differs from the shifted one by a common factor. -/
theorem nnexp_actualOverlap_eq_common_mul (p : FNCHParams) (θ : ℝ) (x : p.support) :
    nnexp (θ * p.overlap x) = nnexp (θ * p.lo) * nnexp (θ * x.val) := by
  have harg : θ * (p.overlap x : ℝ) = θ * (p.lo : ℝ) + θ * (x.val : ℝ) := by
    have hoverlap : (p.overlap x : ℝ) = (p.lo : ℝ) + (x.val : ℝ) := by
      rw [FNCHParams.overlap, Nat.cast_add]
    calc
      θ * (p.overlap x : ℝ) = θ * ((p.lo : ℝ) + (x.val : ℝ)) := by
        rw [hoverlap]
      _ = θ * (p.lo : ℝ) + θ * (x.val : ℝ) := by
        rw [mul_add]
  calc
    nnexp (θ * p.overlap x) = nnexp (θ * (p.lo : ℝ) + θ * (x.val : ℝ)) := by
      rw [harg]
    _ = nnexp (θ * p.lo) * nnexp (θ * x.val) := by
      exact (nnexp_mul (θ * p.lo) (θ * x.val)).symm

/-- Literal FNCH weights are common-factor multiples of shifted FNCH tilt weights. -/
theorem fnchActualWeight_eq_common_mul (p : FNCHParams) (θ : ℝ) (x : p.support) :
    fnchActualWeight p θ x = nnexp (θ * p.lo) * tiltWeight (fnchBase p) θ x := by
  simp [fnchActualWeight, tiltWeight, fnchBase, nnexp_actualOverlap_eq_common_mul,
    mul_comm, mul_assoc]

/-- Normalizing constant for literal actual-overlap FNCH weights. -/
noncomputable def fnchActualNormalizer (p : FNCHParams) (θ : ℝ) : ℝ≥0 :=
  Finset.univ.sum fun x : p.support => fnchActualWeight p θ x

/-- The literal actual-overlap normalizer is positive. -/
theorem fnchActualNormalizer_pos (p : FNCHParams) (θ : ℝ) :
    0 < fnchActualNormalizer p θ := by
  unfold fnchActualNormalizer
  refine Finset.sum_pos (fun x _hx => fnchActualWeight_pos p θ x) ?_
  exact ⟨⟨0, Nat.succ_pos (p.hi - p.lo)⟩, by simp⟩

/-- The literal normalizer differs from the shifted normalizer by the same common factor. -/
theorem fnchActualNormalizer_eq_common_mul (p : FNCHParams) (θ : ℝ) :
    fnchActualNormalizer p θ =
      nnexp (θ * p.lo) * tiltNormalizer (fnchBase p) θ := by
  calc
    fnchActualNormalizer p θ =
        Finset.univ.sum fun x : p.support =>
          nnexp (θ * p.lo) * tiltWeight (fnchBase p) θ x := by
      unfold fnchActualNormalizer
      exact Finset.sum_congr rfl fun x _hx => fnchActualWeight_eq_common_mul p θ x
    _ = nnexp (θ * p.lo) * tiltNormalizer (fnchBase p) θ := by
      simp [tiltNormalizer, Finset.mul_sum]

/-- Literal actual-overlap FNCH PMF. -/
noncomputable def fnchActualPMF (p : FNCHParams) (θ : ℝ) : PosPMF (p.hi - p.lo) where
  mass x := fnchActualWeight p θ x / fnchActualNormalizer p θ
  pos x := div_pos (fnchActualWeight_pos p θ x) (fnchActualNormalizer_pos p θ)
  sum_one := by
    rw [← Finset.sum_div]
    change fnchActualNormalizer p θ / fnchActualNormalizer p θ = 1
    exact div_self (ne_of_gt (fnchActualNormalizer_pos p θ))

/-- Literal actual-overlap FNCH masses equal the shifted-coordinate FNCH masses. -/
theorem fnchActualPMF_mass_eq_fnchPMF_mass (p : FNCHParams) (θ : ℝ) (x : p.support) :
    (fnchActualPMF p θ).mass x = (fnchPMF p θ).mass x := by
  have hc : nnexp (θ * p.lo) ≠ 0 := ne_of_gt (nnexp_pos (θ * p.lo))
  calc
    (fnchActualPMF p θ).mass x =
        (nnexp (θ * p.lo) * tiltWeight (fnchBase p) θ x) /
          (nnexp (θ * p.lo) * tiltNormalizer (fnchBase p) θ) := by
      simp [fnchActualPMF, fnchActualWeight_eq_common_mul,
        fnchActualNormalizer_eq_common_mul]
    _ = tiltWeight (fnchBase p) θ x / tiltNormalizer (fnchBase p) θ := by
      simpa using
        (mul_div_mul_left (tiltWeight (fnchBase p) θ x)
          (tiltNormalizer (fnchBase p) θ) hc)
    _ = (fnchPMF p θ).mass x := by
      simp [fnchPMF, exponentialTilt]

/-- Literal actual-overlap FNCH PMFs have MLR as the noncentrality parameter increases. -/
theorem fnchActual_hasMLR (p : FNCHParams) {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) :
    HasMLR (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) := by
  intro x y hxy
  simpa [fnchActualPMF_mass_eq_fnchPMF_mass] using fnch_hasMLR p hθ x y hxy

/-- Strict-parameter corollary for literal actual-overlap FNCH PMFs. -/
theorem fnchActual_hasMLR_of_lt (p : FNCHParams) {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) :
    HasMLR (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) :=
  fnchActual_hasMLR p hθ.le

/-- Literal actual-overlap FNCH Bayes admit sets are actual-overlap thresholds. -/
theorem fnchActual_bayesAdmit_isActualOverlapThreshold (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      bayesAdmit (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior x ↔
        x ∈ actualOverlapThresholdSet p cut := by
  rcases bayesAdmit_isThreshold (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior
      (fnchActual_hasMLR p hθ) with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro x
  exact (hcut x).trans (mem_actualOverlapThresholdSet_iff p cut x).symm

/-- Literal actual-overlap FNCH Bayes risk is minimized by an actual-overlap threshold. -/
theorem fnchActual_actualOverlapThreshold_bayesRisk_optimal (p : FNCHParams) {θ₀ θ₁ : ℝ}
    (hθ : θ₀ ≤ θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior
          (actualOverlapThresholdSet p cut) ≤
        bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior R := by
  rcases threshold_bayesRisk_optimal (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior
      (fnchActual_hasMLR p hθ) with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro R
  simpa [actualOverlapThresholdSet_eq_thresholdSet p cut] using hcut R

/-- Literal actual-overlap FNCH cost-sensitive Bayes admit sets are actual-overlap thresholds. -/
theorem fnchActual_costedBayesAdmit_isActualOverlapThreshold (p : FNCHParams)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      costedBayesAdmit (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs x ↔
        x ∈ actualOverlapThresholdSet p cut := by
  rcases costedBayesAdmit_isThreshold (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior
      costs (fnchActual_hasMLR p hθ) with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro x
  exact (hcut x).trans (mem_actualOverlapThresholdSet_iff p cut x).symm

/-- Literal actual-overlap FNCH cost-sensitive Bayes risk is minimized by a threshold. -/
theorem fnchActual_costed_actualOverlapThreshold_bayesRisk_optimal (p : FNCHParams)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ ≤ θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs
          (actualOverlapThresholdSet p cut) ≤
        costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs R := by
  rcases costed_threshold_bayesRisk_optimal (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior
      costs (fnchActual_hasMLR p hθ) with ⟨cut, hcut⟩
  refine ⟨cut, ?_⟩
  intro R
  simpa [actualOverlapThresholdSet_eq_thresholdSet p cut] using hcut R

/-- Strict-parameter Bayes threshold corollary for literal actual-overlap FNCH PMFs. -/
theorem fnchActual_bayesAdmit_isActualOverlapThreshold_of_lt (p : FNCHParams)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      bayesAdmit (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior x ↔
        x ∈ actualOverlapThresholdSet p cut :=
  fnchActual_bayesAdmit_isActualOverlapThreshold p hθ.le prior

/-- Strict-parameter Bayes-risk optimality corollary for literal actual-overlap FNCH PMFs. -/
theorem fnchActual_actualOverlapThreshold_bayesRisk_optimal_of_lt (p : FNCHParams)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior
          (actualOverlapThresholdSet p cut) ≤
        bayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior R :=
  fnchActual_actualOverlapThreshold_bayesRisk_optimal p hθ.le prior

/-- Strict-parameter cost-sensitive threshold corollary for literal actual-overlap FNCH PMFs. -/
theorem fnchActual_costedBayesAdmit_isActualOverlapThreshold_of_lt (p : FNCHParams)
    {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior) (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ x : p.support,
      costedBayesAdmit (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs x ↔
        x ∈ actualOverlapThresholdSet p cut :=
  fnchActual_costedBayesAdmit_isActualOverlapThreshold p hθ.le prior costs

/-- Strict-parameter cost-sensitive Bayes-risk corollary for literal actual-overlap FNCH PMFs. -/
theorem fnchActual_costed_actualOverlapThreshold_bayesRisk_optimal_of_lt
    (p : FNCHParams) {θ₀ θ₁ : ℝ} (hθ : θ₀ < θ₁) (prior : Prior)
    (costs : DecisionCosts) :
    ∃ cut : Fin (p.hi - p.lo + 2), ∀ R : Set p.support,
      costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs
          (actualOverlapThresholdSet p cut) ≤
        costedBayesRisk (fnchActualPMF p θ₀) (fnchActualPMF p θ₁) prior costs R :=
  fnchActual_costed_actualOverlapThreshold_bayesRisk_optimal p hθ.le prior costs

end OrdvecFormalization
