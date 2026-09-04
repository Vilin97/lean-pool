/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

import LeanPool.MetricCodes.Binary
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Orthogonality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Probability.Distributions.Beta

/-!
# Strict rate improvements

The MRRW comparison and the first spherical hierarchy and numerical bounds.
-/

noncomputable section MetricCodesNoncomputable

namespace MetricCodes

namespace MRRW

section


open Filter Topology
open scoped Topology

theorem hasDerivAt_mul_continuous_zero
    (g : ℝ → ℝ) (hg : ContinuousAt g 0) (hgzero : g 0 = 0) :
    HasDerivAt (fun r : ℝ => r * g r) 0 0 := by
  apply (hasDerivAt_iff_tendsto_slope_zero).2
  have htend : Tendsto g (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    simpa only [hgzero] using hg.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[≠] (0 : ℝ) ≤ 𝓝 (0 : ℝ))
  have hquotient :
      Tendsto (fun r : ℝ => r⁻¹ * (r * g r))
        (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
    refine (tendsto_congr' ?_).2 htend
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrzero : r ≠ 0 := by simpa only [ne_eq, Set.mem_compl_iff, Set.mem_singleton_iff] using hr
    field_simp [hrzero]
  simpa only [zero_add, zero_mul, sub_zero, smul_eq_mul] using hquotient

private def inverseDegree (r : ℝ) : ℝ :=
  (1 - Real.sqrt (1 - r ^ 2)) / 2

private def inverseVarianceFactor (r : ℝ) : ℝ :=
  (2 * (1 + Real.sqrt (1 - r ^ 2)))⁻¹

theorem inverseVarianceFactor_continuous :
    Continuous inverseVarianceFactor := by
  unfold inverseVarianceFactor
  apply Continuous.inv₀
  · fun_prop
  · intro r
    have hroot : 0 ≤ Real.sqrt (1 - r ^ 2) :=
      Real.sqrt_nonneg _
    positivity

theorem inverseDegree_eq_sq_mul_factor
    {r : ℝ} (hr : r ^ 2 ≤ 1) :
    inverseDegree r = r * (r * inverseVarianceFactor r) := by
  have hradical : 0 ≤ 1 - r ^ 2 := by linarith
  have hsquare := Real.sq_sqrt hradical
  have hroot : 0 ≤ Real.sqrt (1 - r ^ 2) :=
    Real.sqrt_nonneg _
  have hdenominator :
      1 + Real.sqrt (1 - r ^ 2) ≠ 0 := by
    positivity
  unfold inverseDegree inverseVarianceFactor
  field_simp [hdenominator]
  nlinarith

private def inverseEntropyFactor (r : ℝ) : ℝ :=
  inverseVarianceFactor r * Real.negMulLog r +
    Real.negMulLog (r * inverseVarianceFactor r)

theorem inverseEntropyFactor_continuous :
    Continuous inverseEntropyFactor := by
  unfold inverseEntropyFactor
  exact
    (inverseVarianceFactor_continuous.mul
      Real.continuous_negMulLog).add
      (Real.continuous_negMulLog.comp
        (continuous_id.mul inverseVarianceFactor_continuous))

@[simp] theorem inverseEntropyFactor_zero :
    inverseEntropyFactor 0 = 0 := by
  simp only [inverseEntropyFactor, inverseVarianceFactor, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, sub_zero, Real.sqrt_one, mul_inv_rev, Real.negMulLog_zero,
    mul_zero, zero_mul, add_zero]

theorem negMulLog_inverseDegree_eventually :
    (fun r : ℝ => Real.negMulLog (inverseDegree r)) =ᶠ[𝓝 (0 : ℝ)]
      (fun r : ℝ => r * inverseEntropyFactor r) := by
  have hsmall : ∀ᶠ r : ℝ in 𝓝 0, r ^ 2 < 1 :=
    (continuousAt_id.pow 2).tendsto
      (gt_mem_nhds (by norm_num : (0 : ℝ) ^ 2 < 1))
  filter_upwards [hsmall] with r hr
  rw [inverseDegree_eq_sq_mul_factor hr.le,
    Real.negMulLog_mul]
  unfold inverseEntropyFactor
  ring

theorem hasDerivAt_negMulLog_inverseDegree_zero :
    HasDerivAt (fun r : ℝ => Real.negMulLog (inverseDegree r)) 0 0 := by
  exact
    (hasDerivAt_mul_continuous_zero inverseEntropyFactor
      inverseEntropyFactor_continuous.continuousAt
      inverseEntropyFactor_zero).congr_of_eventuallyEq
      negMulLog_inverseDegree_eventually

theorem hasDerivAt_inverseDegree_zero :
    HasDerivAt inverseDegree 0 0 := by
  have hradical :
      HasDerivAt (fun r : ℝ => 1 - r ^ 2) 0 0 := by
    simpa only [Pi.pow_apply, id_eq, Nat.cast_ofNat, Nat.add_one_sub_one, pow_one, mul_zero,
      mul_one, neg_zero] using ((hasDerivAt_id (0 : ℝ)).pow 2).const_sub (1 : ℝ)
  have hroot :
      HasDerivAt (fun r : ℝ => Real.sqrt (1 - r ^ 2)) 0 0 := by
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero, Real.sqrt_one,
      mul_one, zero_div] using hradical.sqrt (by norm_num : (1 : ℝ) - 0 ^ 2 ≠ 0)
  unfold inverseDegree
  simpa only [Pi.sub_apply, sub_self, zero_div] using
    ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hroot).div_const (2 : ℝ)

theorem hasDerivAt_mrrwG_sq_zero :
    HasDerivAt
      (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2)) 0 0 := by
  have hcomplement :
      HasDerivAt
        (fun r : ℝ => Real.negMulLog (1 - inverseDegree r)) 0 0 := by
    have hinner :
        HasDerivAt (fun r : ℝ => 1 - inverseDegree r) 0 0 := by
      change
        HasDerivAt
          ((fun _ : ℝ => (1 : ℝ)) - inverseDegree) 0 0
      simpa only [sub_self] using (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        hasDerivAt_inverseDegree_zero
    have houter :
        HasDerivAt Real.negMulLog (-1) (1 - inverseDegree 0) := by
      simpa only [inverseDegree, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, sub_zero,
        Real.sqrt_one, sub_self, zero_div, Real.log_one, neg_zero,
        zero_sub] using Real.hasDerivAt_negMulLog (by norm_num : (1 : ℝ) ≠ 0)
    simpa only [Function.comp_def, mul_zero] using houter.comp 0 hinner
  have hentropy :
      HasDerivAt
        (fun r : ℝ =>
          (Real.negMulLog (inverseDegree r) +
            Real.negMulLog (1 - inverseDegree r)) / Real.log 2)
        0 0 := by
    simpa only [Pi.add_apply, add_zero, zero_div] using
      (hasDerivAt_negMulLog_inverseDegree_zero.add hcomplement).div_const (Real.log 2)
  have hfunctions :
      (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2)) =
        (fun r : ℝ =>
          (Real.negMulLog (inverseDegree r) +
            Real.negMulLog (1 - inverseDegree r)) / Real.log 2) := by
    funext r
    unfold MetricCodes.Johnson.mrrwG inverseDegree
    rw [MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log,
      Real.binEntropy_eq_negMulLog_add_negMulLog_one_sub]
  rw [hfunctions]
  exact hentropy

private def lowerEndpointRoot (δ : ℝ) : ℝ :=
  Real.sqrt (1 - 2 * δ)

private def lowerEndpointWeight (δ : ℝ) : ℝ :=
  (1 - lowerEndpointRoot δ) / 2

private def lowerEndpointDerivative (δ : ℝ) : ℝ :=
  δ *
    (Real.log (1 - lowerEndpointWeight δ) -
      Real.log (lowerEndpointWeight δ)) /
      (2 * lowerEndpointRoot δ * Real.log 2)

theorem lowerEndpointRoot_pos {δ : ℝ}
    (hhalf : δ < (1 : ℝ) / 2) :
    0 < lowerEndpointRoot δ := by
  unfold lowerEndpointRoot
  apply Real.sqrt_pos.mpr
  linarith

theorem lowerEndpointRoot_lt_one {δ : ℝ}
    (hδ : 0 < δ) :
    lowerEndpointRoot δ < 1 := by
  unfold lowerEndpointRoot
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
  linarith

theorem lowerEndpointWeight_pos {δ : ℝ}
    (hδ : 0 < δ) :
    0 < lowerEndpointWeight δ := by
  unfold lowerEndpointWeight
  linarith [lowerEndpointRoot_lt_one hδ]

theorem lowerEndpointWeight_lt_half {δ : ℝ}
    (hhalf : δ < (1 : ℝ) / 2) :
    lowerEndpointWeight δ < (1 : ℝ) / 2 := by
  unfold lowerEndpointWeight
  linarith [lowerEndpointRoot_pos hhalf]

theorem lowerEndpointDerivative_pos {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    0 < lowerEndpointDerivative δ := by
  have hweight := lowerEndpointWeight_pos hδ
  have hhalfweight := lowerEndpointWeight_lt_half hhalf
  have hlog :
      Real.log (lowerEndpointWeight δ) <
        Real.log (1 - lowerEndpointWeight δ) :=
    Real.log_lt_log hweight (by linarith)
  have hroot := lowerEndpointRoot_pos hhalf
  have hlogtwo : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num)
  unfold lowerEndpointDerivative
  exact div_pos
    (mul_pos hδ (sub_pos.mpr hlog))
    (by positivity)

theorem hasDerivAt_mrrwG_boundary_quadratic_zero
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    HasDerivAt
      (fun r : ℝ =>
        MetricCodes.Johnson.mrrwG (r ^ 2 + 2 * δ * r + 2 * δ))
      (lowerEndpointDerivative δ) 0 := by
  have hquadratic :
      HasDerivAt
        (fun r : ℝ => r ^ 2 + 2 * δ * r + 2 * δ)
        (2 * δ) 0 := by
    simpa only [hasDerivAt_add_const_iff, id_eq, Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat,
      Nat.add_one_sub_one,
      pow_one, mul_zero, mul_one, zero_add] using
      (((hasDerivAt_id (0 : ℝ)).pow 2).add ((hasDerivAt_id (0 : ℝ)).const_mul (2 *
        δ))).add_const (2 * δ)
  have hradical :
      HasDerivAt
        (fun r : ℝ =>
          1 - (r ^ 2 + 2 * δ * r + 2 * δ))
        (-2 * δ) 0 := by
    simpa only [neg_mul] using hquadratic.const_sub (1 : ℝ)
  have hradicalzero :
      1 - ((0 : ℝ) ^ 2 + 2 * δ * 0 + 2 * δ) ≠ 0 := by
    have hpositive : 0 < 1 - 2 * δ := by linarith
    simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, add_zero,
      zero_add] using
      hpositive.ne'
  have hroot :
      HasDerivAt
        (fun r : ℝ =>
          Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)))
        ((-2 * δ) / (2 * lowerEndpointRoot δ)) 0 := by
    simpa only [neg_mul, lowerEndpointRoot, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, add_zero, zero_add] using hradical.sqrt hradicalzero
  have hnumerator :
      HasDerivAt
        ((fun _ : ℝ => (1 : ℝ)) -
          (fun r : ℝ =>
            Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ))))
        (0 - ((-2 * δ) / (2 * lowerEndpointRoot δ))) 0 :=
    (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hroot
  have hprobability :
      HasDerivAt
        (fun r : ℝ =>
          (1 - Real.sqrt
            (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2)
        (δ / (2 * lowerEndpointRoot δ)) 0 := by
    change
      HasDerivAt
        (fun r : ℝ =>
          (((fun _ : ℝ => (1 : ℝ)) -
            (fun s : ℝ =>
              Real.sqrt (1 - (s ^ 2 + 2 * δ * s + 2 * δ)))) r) /
            (2 : ℝ))
        (δ / (2 * lowerEndpointRoot δ)) 0
    exact
      (hnumerator.div_const (2 : ℝ)).congr_deriv (by ring)
  have hweight := lowerEndpointWeight_pos hδ
  have hweightone :
      lowerEndpointWeight δ ≠ 1 := by
    have h := lowerEndpointWeight_lt_half hhalf
    linarith
  have hentropyfun :
      MetricCodes.binaryEntropy =
        (fun a : ℝ => Real.binEntropy a / Real.log 2) :=
    funext MetricCodes.Johnson.binaryEntropy_eq_binEntropy_div_log
  have hbinary :
      HasDerivAt MetricCodes.binaryEntropy
        ((Real.log (1 - lowerEndpointWeight δ) -
          Real.log (lowerEndpointWeight δ)) / Real.log 2)
        (lowerEndpointWeight δ) := by
    rw [hentropyfun]
    exact
      (Real.hasDerivAt_binEntropy hweight.ne'
        hweightone).div_const (Real.log 2)
  have hbinaryzero :
      HasDerivAt MetricCodes.binaryEntropy
        ((Real.log (1 - lowerEndpointWeight δ) -
          Real.log (lowerEndpointWeight δ)) / Real.log 2)
        ((1 - Real.sqrt
          (1 - ((0 : ℝ) ^ 2 + 2 * δ * 0 + 2 * δ))) / 2) := by
    simpa only [lowerEndpointWeight, lowerEndpointRoot, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, add_zero, zero_add] using hbinary
  change
    HasDerivAt
      (fun r : ℝ =>
        MetricCodes.binaryEntropy
          ((1 - Real.sqrt
            (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2))
      (lowerEndpointDerivative δ) 0
  have hcoeff :
      ((Real.log (1 - lowerEndpointWeight δ) -
        Real.log (lowerEndpointWeight δ)) / Real.log 2) *
          (δ / (2 * lowerEndpointRoot δ)) =
        lowerEndpointDerivative δ := by
    unfold lowerEndpointDerivative
    field_simp [(lowerEndpointRoot_pos hhalf).ne',
      (Real.log_pos (by norm_num : (1 : ℝ) < 2)).ne']
  exact (hbinaryzero.comp 0 hprobability).congr_deriv hcoeff

theorem hasDerivAt_mrrwObjective_zero
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    HasDerivAt (MetricCodes.Johnson.mrrwObjective δ)
      (-lowerEndpointDerivative δ) 0 := by
  unfold MetricCodes.Johnson.mrrwObjective
  change
    HasDerivAt
      (((fun _ : ℝ => (1 : ℝ)) +
        (fun r : ℝ => MetricCodes.Johnson.mrrwG (r ^ 2))) -
        (fun r : ℝ =>
          MetricCodes.Johnson.mrrwG (r ^ 2 + 2 * δ * r + 2 * δ)))
      (-lowerEndpointDerivative δ) 0
  simpa only [add_zero, zero_sub] using
    ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).add hasDerivAt_mrrwG_sq_zero).sub
      (hasDerivAt_mrrwG_boundary_quadratic_zero hδ hhalf)

theorem exists_mrrwObjective_lt_zero
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r < 1 - 2 * δ ∧
      MetricCodes.Johnson.mrrwObjective δ r <
        MetricCodes.Johnson.mrrwObjective δ 0 := by
  have hderivative := lowerEndpointDerivative_pos hδ hhalf
  have hslope :=
    (hasDerivAt_mrrwObjective_zero hδ hhalf).tendsto_slope_zero_right
  have hnegative :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        r⁻¹ *
          (MetricCodes.Johnson.mrrwObjective δ r -
            MetricCodes.Johnson.mrrwObjective δ 0) < 0 := by
    have h :=
      hslope.eventually
        (gt_mem_nhds (by linarith :
          -lowerEndpointDerivative δ < 0))
    filter_upwards [h] with r hr
    simpa only [zero_add, smul_eq_mul] using hr
  have hupper :
      ∀ᶠ r : ℝ in 𝓝[>] 0, r < 1 - 2 * δ :=
    nhdsWithin_le_nhds
      (gt_mem_nhds (by linarith : (0 : ℝ) < 1 - 2 * δ))
  have hwitness :
      ∀ᶠ r : ℝ in 𝓝[>] 0,
        0 < r ∧ r < 1 - 2 * δ ∧
          MetricCodes.Johnson.mrrwObjective δ r <
            MetricCodes.Johnson.mrrwObjective δ 0 := by
    filter_upwards [hnegative, hupper, self_mem_nhdsWithin]
      with r hquotient hrupper (hr : 0 < r)
    refine ⟨hr, hrupper, ?_⟩
    apply sub_neg.mp
    calc
      MetricCodes.Johnson.mrrwObjective δ r -
          MetricCodes.Johnson.mrrwObjective δ 0 =
        r *
          (r⁻¹ *
            (MetricCodes.Johnson.mrrwObjective δ r -
              MetricCodes.Johnson.mrrwObjective δ 0)) := by
          field_simp [hr.ne']
      _ < 0 := mul_neg_of_pos_of_neg hr hquotient
  exact hwitness.exists

theorem mrrw_minimizer_pos
    {δ r : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hr : 0 ≤ r) (hupper : r ≤ 1 - 2 * δ)
    (hmin : ∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
      MetricCodes.Johnson.mrrwObjective δ r ≤
        MetricCodes.Johnson.mrrwObjective δ s) :
    0 < r := by
  rcases hr.eq_or_lt with hzero | hpositive
  · have hrzero : r = 0 := hzero.symm
    subst r
    obtain ⟨s, hs, hsupper, hstrict⟩ :=
      exists_mrrwObjective_lt_zero hδ hhalf
    exact False.elim
      ((not_lt_of_ge (hmin s hs.le hsupper.le)) hstrict)
  · exact hpositive

theorem exists_positive_mrrw_minimizer
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 - 2 * δ ∧
      (∀ s : ℝ, 0 ≤ s → s ≤ 1 - 2 * δ →
        MetricCodes.Johnson.mrrwObjective δ r ≤
          MetricCodes.Johnson.mrrwObjective δ s) ∧
      MetricCodes.Johnson.mrrwRate δ =
        MetricCodes.Johnson.mrrwObjective δ r := by
  obtain ⟨r, hr, hupper, hmin⟩ :=
    MetricCodes.Johnson.exists_mrrw_minimizer hhalf.le
  refine ⟨r, mrrw_minimizer_pos hδ hhalf hr hupper hmin,
    hupper, hmin, ?_⟩
  exact MetricCodes.Johnson.mrrwRate_eq_objective_of_minimizer
    hr hupper hmin

private def inverseWeight (δ r : ℝ) : ℝ :=
  (1 - Real.sqrt
    (1 - (r ^ 2 + 2 * δ * r + 2 * δ))) / 2


theorem inverse_zero_fibre_boundary
    {δ r : ℝ}
    (hδ : 0 < δ) (_ : δ < (1 : ℝ) / 2)
    (hr : 0 < r) (hupper : r < 1 - 2 * δ) :
    ∃ a u : ℝ,
      0 < u ∧ u < a ∧ a < (1 : ℝ) / 2 ∧
      δ / 2 < a ∧
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a ∧
      MetricCodes.Johnson.mrrwObjective δ r =
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hrplus : 0 < 1 + r := by linarith
  have hrminus : 0 < 1 - r := by linarith
  have hmargin : 0 < 1 - 2 * δ - r := by linarith
  have hrvariance : 0 < 1 - r ^ 2 := by
    nlinarith only [mul_pos hrminus hrplus]
  have hquadratic :
      0 < 1 - (r ^ 2 + 2 * δ * r + 2 * δ) := by
    nlinarith only [mul_pos hrplus hmargin]
  have hradorder :
      1 - (r ^ 2 + 2 * δ * r + 2 * δ) <
        1 - r ^ 2 := by
    nlinarith only [mul_pos hδ hrplus]
  have hrootorder :
      Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) <
        Real.sqrt (1 - r ^ 2) :=
    Real.sqrt_lt_sqrt hquadratic.le hradorder
  have hrootlt : Real.sqrt (1 - r ^ 2) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).2
    nlinarith only [mul_pos hr hr]
  have hsmallroot :
      0 < Real.sqrt
        (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) :=
    Real.sqrt_pos.mpr hquadratic
  have hdegreesquare :
      Real.sqrt (1 - r ^ 2) ^ 2 = 1 - r ^ 2 :=
    Real.sq_sqrt hrvariance.le
  have hweightsquare :
      Real.sqrt (1 - (r ^ 2 + 2 * δ * r + 2 * δ)) ^ 2 =
        1 - (r ^ 2 + 2 * δ * r + 2 * δ) :=
    Real.sq_sqrt hquadratic.le
  let u : ℝ := inverseDegree r
  let a : ℝ := inverseWeight δ r
  have hu : 0 < u := by
    dsimp [u, inverseDegree]
    linarith
  have hua : u < a := by
    dsimp [u, a, inverseDegree, inverseWeight]
    linarith
  have ha : a < (1 : ℝ) / 2 := by
    dsimp [a, inverseWeight]
    linarith
  have ha0 : 0 < a := lt_trans hu hua
  have haone : 0 < 1 - a := by linarith
  have huone : 0 < 1 - u := by linarith
  have hvarianceu : 4 * u * (1 - u) = r ^ 2 := by
    dsimp [u, inverseDegree]
    nlinarith only [hdegreesquare]
  have hvariancea :
      4 * a * (1 - a) =
        r ^ 2 + 2 * δ * r + 2 * δ := by
    dsimp [a, inverseWeight]
    nlinarith only [hweightsquare]
  have hdistancevariance : 2 * δ < 4 * a * (1 - a) := by
    rw [hvariancea]
    nlinarith only [mul_pos hδ hr, sq_nonneg r]
  have hvarianceweight : 4 * a * (1 - a) < 4 * a := by
    nlinarith only [mul_pos ha0 ha0]
  have hweightdistance : δ / 2 < a := by
    nlinarith only [hdistancevariance, hvarianceweight]
  have husquare := Real.sq_sqrt (mul_pos hu huone).le
  have hrootsquare :
      (2 * Real.sqrt (u * (1 - u))) ^ 2 = r ^ 2 := by
    nlinarith only [husquare, hvarianceu]
  have huradical :
      2 * Real.sqrt (u * (1 - u)) = r := by
    calc
      2 * Real.sqrt (u * (1 - u)) =
          Real.sqrt ((2 * Real.sqrt (u * (1 - u))) ^ 2) :=
        (Real.sqrt_sq (by positivity)).symm
      _ = Real.sqrt (r ^ 2) := by rw [hrootsquare]
      _ = r := Real.sqrt_sq hr.le
  have hplus : 1 + r ≠ 0 := hrplus.ne'
  have hfraction :
      (a * (1 - a) - u * (1 - u)) /
        (a * (1 - a) * (1 + r)) =
        δ / (2 * a * (1 - a)) := by
    field_simp [ha0.ne', haone.ne', hplus];
      nlinarith only [hvariancea, hvarianceu]
  have hspectral :
      1 - MetricCodes.Johnson.spectralLimit a 0 0 u =
        (a * (1 - a) - u * (1 - u)) /
          (a * (1 - a) * (1 + r)) := by
    simpa only [huradical] using
      MetricCodes.Johnson.spectralLimit_zero_fibre_boundary hu hua ha
  have hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a := by
    unfold MetricCodes.Johnson.asymptoticThreshold
    linarith only [hspectral, hfraction]
  have hobjective :
      MetricCodes.Johnson.mrrwObjective δ r =
        MetricCodes.Johnson.shellRate a 0 0 u := by
    simpa only [huradical] using
      MetricCodes.Johnson.mrrwObjective_zero_fibre_boundary
        hu hua ha hboundary
  exact ⟨a, u, hu, hua, ha, hweightdistance,
    hboundary, hobjective⟩

theorem exists_zero_fibre_boundary_of_interior_minimizer
    {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hstrict :
      MetricCodes.Johnson.mrrwRate δ <
        MetricCodes.Hamming.classicalRate δ) :
    ∃ a u : ℝ,
      0 < u ∧ u < a ∧ a < (1 : ℝ) / 2 ∧
      δ / 2 < a ∧
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a ∧
      MetricCodes.Johnson.mrrwRate δ =
        MetricCodes.Johnson.shellRate a 0 0 u := by
  obtain ⟨r, hr, hupper, _hmin, hrate⟩ :=
    exists_positive_mrrw_minimizer hδ hhalf
  have hrstrict : r < 1 - 2 * δ := by
    rcases lt_or_eq_of_le hupper with hlt | heq
    · exact hlt
    · exfalso
      have hendpoint :
          MetricCodes.Johnson.mrrwRate δ =
            MetricCodes.Hamming.classicalRate δ := by
        calc
          MetricCodes.Johnson.mrrwRate δ =
              MetricCodes.Johnson.mrrwObjective δ r := hrate
          _ = MetricCodes.Johnson.mrrwObjective δ (1 - 2 * δ) := by
            rw [heq]
          _ = MetricCodes.Hamming.classicalRate δ :=
            MetricCodes.Johnson.mrrwObjective_endpoint hδ hhalf
      exact (ne_of_lt hstrict) hendpoint
  obtain ⟨a, u, hu, hua, ha, hweightdistance,
      hboundary, hobjective⟩ :=
    inverse_zero_fibre_boundary hδ hhalf hr hrstrict
  exact ⟨a, u, hu, hua, ha, hweightdistance,
    hboundary, hrate.trans hobjective⟩

end

section


open Filter Topology
open scoped Topology

private def interiorSlope (a u : ℝ) : ℝ :=
  (Real.sqrt (u * (1 - u)) * (1 - 2 * a))⁻¹

private def interiorWeight (a u e : ℝ) : ℝ :=
  a - interiorSlope a u * e

private def interiorSupport (a u e : ℝ) : ℝ :=
  interiorWeight a u e * e

private def interiorComplement (a u e : ℝ) : ℝ :=
  (1 - interiorWeight a u e) * e

@[simp] theorem interiorWeight_zero (a u : ℝ) :
    interiorWeight a u 0 = a := by
  simp only [interiorWeight, mul_zero, sub_zero]

@[simp] theorem interiorSupport_zero (a u : ℝ) :
    interiorSupport a u 0 = 0 := by
  simp only [interiorSupport, interiorWeight_zero, mul_zero]

@[simp] theorem interiorComplement_zero (a u : ℝ) :
    interiorComplement a u 0 = 0 := by
  simp only [interiorComplement, interiorWeight_zero, mul_zero]

theorem interiorSupport_add_complement (a u e : ℝ) :
    interiorSupport a u e + interiorComplement a u e = e := by
  unfold interiorSupport interiorComplement
  ring

theorem rankPenalty_interior {a u e : ℝ}
    (hweight : 0 < interiorWeight a u e)
    (hweight' : interiorWeight a u e < 1) :
    MetricCodes.Johnson.rankPenalty
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) =
      MetricCodes.binaryEntropy e := by
  have hsupport :
      interiorSupport a u e / interiorWeight a u e = e := by
    unfold interiorSupport
    exact mul_div_cancel_left₀ e hweight.ne'
  have hcomplement :
      interiorComplement a u e / (1 - interiorWeight a u e) = e := by
    unfold interiorComplement
    exact mul_div_cancel_left₀ e (sub_pos.mpr hweight').ne'
  unfold MetricCodes.Johnson.rankPenalty
  rw [hsupport, hcomplement]
  ring

theorem tendsto_interiorWeight_zero (a u : ℝ) :
    Tendsto (interiorWeight a u) (𝓝[>] 0) (𝓝 a) := by
  have hcontinuous : Continuous (interiorWeight a u) := by
    unfold interiorWeight
    fun_prop
  simpa only [interiorWeight_zero] using
    hcontinuous.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)

theorem eventually_binaryEntropy_inward_improvement
    {a : ℝ} (ha : 0 < a) (ha' : a < 1) (C : ℝ) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) <
        MetricCodes.binaryEntropy e := by
  let f : ℝ → ℝ := fun e =>
    MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e)
  have hinner :
      DifferentiableAt ℝ (fun e : ℝ => a - C * e) 0 := by
    fun_prop
  have houter : DifferentiableAt ℝ MetricCodes.binaryEntropy a :=
    MetricCodes.Hamming.differentiableAt_binaryEntropy ha ha'
  have houter0 :
      DifferentiableAt ℝ MetricCodes.binaryEntropy (a - C * (0 : ℝ)) := by
    simpa only [mul_zero, sub_zero] using houter
  have hf : DifferentiableAt ℝ f 0 := by
    dsimp [f]
    exact (houter0.comp 0 hinner).const_sub (MetricCodes.binaryEntropy a)
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ e : ℝ in 𝓝[>] 0,
        e⁻¹ *
          (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e)) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with e he
    simpa [f, smul_eq_mul] using he
  have hloglim :
      Tendsto (fun e : ℝ => -Real.logb 2 e) (𝓝[>] 0) atTop := by
    simpa only [tendsto_neg_atTop_iff, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog : ∀ᶠ e : ℝ in 𝓝[>] 0, M < -Real.logb 2 e :=
    hloglim.eventually (eventually_gt_atTop M)
  have hsmall : ∀ᶠ e : ℝ in 𝓝[>] 0, e < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hupper, hlog, hsmall, self_mem_nhdsWithin]
    with e hbound hlog' heone (he : 0 < e)
  have houter_bound :
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) <
        e * M := by
    calc
      MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e) =
          e * (e⁻¹ *
            (MetricCodes.binaryEntropy a - MetricCodes.binaryEntropy (a - C * e))) := by
            field_simp [he.ne']
      _ < e * M := mul_lt_mul_of_pos_left hbound he
  have hsingular : e * M < e * (-Real.logb 2 e) :=
    mul_lt_mul_of_pos_left hlog' he
  have hentropy :=
    MetricCodes.Hamming.neg_mul_logb_le_binaryEntropy he.le heone.le
  linarith

theorem eventually_shellRate_interior_improvement
    {a u : ℝ} (ha : 0 < a) (ha' : a < (1 : ℝ) / 2) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.shellRate
          (interiorWeight a u e)
          (interiorSupport a u e)
          (interiorComplement a u e) u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hentropy := eventually_binaryEntropy_inward_improvement
    ha (ha'.trans (by norm_num)) (interiorSlope a u)
  have hweight := tendsto_interiorWeight_zero a u
  have hpositive :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds ha)
  have hless :
      ∀ᶠ e : ℝ in 𝓝[>] 0, interiorWeight a u e < 1 :=
    hweight.eventually
      (gt_mem_nhds (ha'.trans (by norm_num : (1 : ℝ) / 2 < 1)))
  filter_upwards [hentropy, hpositive, hless]
    with e he hpos hlt
  rw [MetricCodes.Johnson.shellRate, rankPenalty_interior hpos hlt,
    MetricCodes.Johnson.shellRate_zero_fibre]
  change
    1 - MetricCodes.binaryEntropy (a - interiorSlope a u * e) +
        MetricCodes.binaryEntropy u - MetricCodes.binaryEntropy e <
      1 - MetricCodes.binaryEntropy a + MetricCodes.binaryEntropy u
  linarith

private def interiorSpectralMargin (δ a u e : ℝ) : ℝ :=
  MetricCodes.Johnson.spectralLimit
      (interiorWeight a u e)
      (interiorSupport a u e)
      (interiorComplement a u e) u -
    MetricCodes.Johnson.asymptoticThreshold δ (interiorWeight a u e)

theorem interiorSpectralMargin_zero {δ a u : ℝ}
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    interiorSpectralMargin δ a u 0 = 0 := by
  simp only [interiorSpectralMargin, interiorWeight_zero, interiorSupport_zero,
    interiorComplement_zero, hboundary, sub_self]

theorem interior_boundary_delta_relation {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    δ * (1 + 2 * Real.sqrt (u * (1 - u))) =
      2 * (a * (1 - a) - u * (1 - u)) := by
  have huone : 0 < 1 - u := by linarith
  have hsquare := Real.sq_sqrt (mul_pos hu huone).le
  have hvariance := MetricCodes.Johnson.zero_fibre_boundary_variance
    hu hua ha hboundary
  nlinarith

theorem interior_boundary_weight_gt_distance {δ a u : ℝ}
    (hδ : 0 < δ)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    δ / 2 < a := by
  have ha0 : 0 < a := lt_trans hu hua
  have huone : 0 < 1 - u := by linarith
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu huone)
  have hvariance := MetricCodes.Johnson.zero_fibre_boundary_variance
    hu hua ha hboundary
  have hcross : 0 < δ * (2 * Real.sqrt (u * (1 - u))) := by
    positivity
  nlinarith [sq_nonneg (2 * Real.sqrt (u * (1 - u))),
    sq_pos_of_pos ha0]

theorem spectralLimit_interior_eq (a u e : ℝ) :
    MetricCodes.Johnson.spectralLimit
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u =
      let z := (1 - 2 * u)
      let m := (1 - 2 * (interiorWeight a u e))
      let t := 1 - 2 * e
      (m * (t ^ 2 - z ^ 2)) ^ 2 /
          (z ^ 2 * (1 - m ^ 2) * (1 - z ^ 2)) +
        ((z ^ 2 - (m * t) ^ 2) * (t ^ 2 - z ^ 2)) /
          (z ^ 2 * (1 - m ^ 2) * Real.sqrt (1 - z ^ 2)) := by
  dsimp [MetricCodes.Johnson.spectralLimit,
    MetricCodes.Johnson.centeredEta,
    interiorSupport, interiorComplement]
  ring

theorem eventually_interior_parameters
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hδa : δ / 2 < a)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.AsymptoticParameters δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u := by
  have hweight := tendsto_interiorWeight_zero a u
  have hweight_distance :
      ∀ᶠ e : ℝ in 𝓝[>] 0, δ / 2 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds hδa)
  have hweight_half :
      ∀ᶠ e : ℝ in 𝓝[>] 0, interiorWeight a u e < (1 : ℝ) / 2 :=
    hweight.eventually (gt_mem_nhds ha)
  have hweight_degree :
      ∀ᶠ e : ℝ in 𝓝[>] 0, u < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds hua)
  have hehalf : ∀ᶠ e : ℝ in 𝓝[>] 0, e < (1 : ℝ) / 2 :=
    nhdsWithin_le_nhds
      (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  have hedegree : ∀ᶠ e : ℝ in 𝓝[>] 0, e < u :=
    nhdsWithin_le_nhds (gt_mem_nhds hu)
  have hleftcontinuous : Continuous
      (fun e : ℝ =>
        interiorWeight a u e - interiorSupport a u e +
          interiorComplement a u e) := by
    unfold interiorSupport interiorComplement interiorWeight
    fun_prop
  have hleftlimit :
      Tendsto
        (fun e : ℝ =>
          interiorWeight a u e - interiorSupport a u e +
            interiorComplement a u e)
        (𝓝[>] 0) (𝓝 a) := by
    simpa only [interiorWeight_zero, interiorSupport_zero, sub_zero, interiorComplement_zero,
      add_zero] using
      hleftcontinuous.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hleft : ∀ᶠ e : ℝ in 𝓝[>] 0,
      u < interiorWeight a u e - interiorSupport a u e +
        interiorComplement a u e :=
    hleftlimit.eventually (lt_mem_nhds hua)
  have hrightcontinuous : Continuous
      (fun e : ℝ =>
        1 - interiorWeight a u e + interiorSupport a u e -
          interiorComplement a u e) := by
    unfold interiorSupport interiorComplement interiorWeight
    fun_prop
  have hrightlimit :
      Tendsto
        (fun e : ℝ =>
          1 - interiorWeight a u e + interiorSupport a u e -
            interiorComplement a u e)
        (𝓝[>] 0) (𝓝 (1 - a)) := by
    simpa only [interiorWeight_zero, interiorSupport_zero, add_zero, interiorComplement_zero,
      sub_zero] using
      hrightcontinuous.continuousAt.tendsto.mono_left (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have huright : u < 1 - a := by linarith
  have hright : ∀ᶠ e : ℝ in 𝓝[>] 0,
      u < 1 - interiorWeight a u e + interiorSupport a u e -
        interiorComplement a u e :=
    hrightlimit.eventually (lt_mem_nhds huright)
  filter_upwards [hweight_distance, hweight_half, hweight_degree,
    hehalf, hedegree, hleft, hright, self_mem_nhdsWithin]
    with e hwd hwh hwu heh heu hel her (he : 0 < e)
  have hwpos : 0 < interiorWeight a u e := by
    nlinarith
  have hwcomplement : 0 < 1 - interiorWeight a u e := by
    linarith
  refine {
    distance_pos := hδ
    distance_lt_half := hδ'
    weight_gt_distance := hwd
    weight_lt_half := hwh
    support_nonneg := ?_
    support_lt_half := ?_
    complement_nonneg := ?_
    complement_lt_half := ?_
    first_lt_degree := ?_
    degree_lt_weight := hwu
    degree_lt_left := hel
    degree_lt_right := her
  }
  · unfold interiorSupport
    exact mul_nonneg hwpos.le he.le
  · unfold interiorSupport
    nlinarith [mul_lt_mul_of_pos_left heh hwpos]
  · unfold interiorComplement
    exact mul_nonneg hwcomplement.le he.le
  · unfold interiorComplement
    nlinarith [mul_lt_mul_of_pos_left heh hwcomplement]
  · rw [interiorSupport_add_complement]
    exact heu

theorem hasDerivAt_interiorSpectralMargin
    {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    HasDerivAt (interiorSpectralMargin δ a u)
      ((1 - 2 * (a * (1 - a))) *
          (1 - 2 * Real.sqrt (u * (1 - u))) /
        (a * (1 - a) * Real.sqrt (u * (1 - u)) *
          (1 + 2 * Real.sqrt (u * (1 - u))))) 0 := by
  have ha0 : 0 < a := lt_trans hu hua
  have ha1 : 0 < 1 - a := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hz0 : 0 < 1 - 2 * u := by linarith
  have hm0 : 0 < 1 - 2 * a := by linarith
  have hrad : 0 < 1 - (1 - 2 * u) ^ 2 := by
    nlinarith [mul_pos hu hu1]
  have hmrad : 0 < 1 - (1 - 2 * a) ^ 2 := by
    nlinarith [mul_pos ha0 ha1]
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu hu1)
  have hsquare := Real.sq_sqrt (mul_pos hu hu1).le
  have hroot :
      Real.sqrt (1 - (1 - 2 * u) ^ 2) =
        2 * Real.sqrt (u * (1 - u)) := by
    exact MetricCodes.Johnson.sqrt_one_sub_centeredDegree_sq hu (lt_trans hua ha)
  have hdelta :=
    interior_boundary_delta_relation hu hua ha hboundary
  let c : ℝ := interiorSlope a u
  let A : ℝ → ℝ := fun e => a - c * e
  let m : ℝ → ℝ := fun e => 1 - 2 * A e
  let t : ℝ → ℝ := fun e => 1 - 2 * e
  let z : ℝ := 1 - 2 * u
  let q : ℝ := Real.sqrt (1 - z ^ 2)
  let p : ℝ → ℝ := fun e => t e ^ 2 - z ^ 2
  let Q : ℝ → ℝ := fun e => 1 - m e ^ 2
  have hA : HasDerivAt A (-c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => a) - (fun e : ℝ => c * e)) (-c) 0
    simpa only [id_eq, mul_one, zero_sub] using
      (hasDerivAt_const (x := (0 : ℝ)) a).sub ((hasDerivAt_id (0 : ℝ)).const_mul c)
  have hm : HasDerivAt m (2 * c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) -
          (fun e : ℝ => 2 * (a - c * e)))
        (2 * c) 0
    simpa only [mul_neg, sub_neg_eq_add, zero_add] using
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub (hA.const_mul 2)
  have ht : HasDerivAt t (-2) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) - (fun e : ℝ => 2 * e))
        (-2) 0
    simpa only [id_eq, mul_one, zero_sub] using
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub ((hasDerivAt_id (0 : ℝ)).const_mul 2)
  have hp : HasDerivAt p (-4) 0 := by
    change
      HasDerivAt
        (((fun e : ℝ => 1 - 2 * e) ^ 2) -
          (fun _ : ℝ => z ^ 2))
        (-4) 0
    exact
      ((ht.pow 2).sub
        (hasDerivAt_const (x := (0 : ℝ)) (z ^ 2))).congr_deriv
        (by norm_num)
  have hQ : HasDerivAt Q (-4 * (1 - 2 * a) * c) 0 := by
    change
      HasDerivAt
        ((fun _ : ℝ => 1) -
          ((fun e : ℝ => 1 - 2 * (a - c * e)) ^ 2))
        (-4 * (1 - 2 * a) * c) 0
    exact
      ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub
        (hm.pow 2)).congr_deriv (by dsimp [m, A]; ring)
  have hden1 : z ^ 2 * Q 0 * (1 - z ^ 2) ≠ 0 := by
    simpa [z, Q, m, A] using
      mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hz0.ne') hmrad.ne')
        hrad.ne'
  have hden2 : z ^ 2 * Q 0 * q ≠ 0 := by
    have hroot_ne : Real.sqrt (1 - (1 - 2 * u) ^ 2) ≠ 0 :=
      (Real.sqrt_pos.mpr hrad).ne'
    simpa [z, Q, m, A, q] using
      mul_ne_zero
        (mul_ne_zero (pow_ne_zero 2 hz0.ne') hmrad.ne')
        hroot_ne
  have hden3 : 2 * A 0 * (1 - A 0) ≠ 0 := by
    simpa [A] using
      mul_ne_zero
        (mul_ne_zero (by norm_num : (2 : ℝ) ≠ 0) ha0.ne')
        ha1.ne'
  have hterm1 :=
    ((hm.mul hp).pow 2).div
      (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).mul hQ).mul
        (hasDerivAt_const (x := (0 : ℝ)) (1 - z ^ 2))) hden1
  have hterm2 :=
    (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).sub
        ((hm.mul ht).pow 2)).mul hp).div
      (((hasDerivAt_const (x := (0 : ℝ)) (z ^ 2)).mul hQ).mul
        (hasDerivAt_const (x := (0 : ℝ)) q)) hden2
  have hthreshold :=
    (hasDerivAt_const (x := (0 : ℝ)) δ).div
      ((hA.const_mul 2).mul
        ((hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ)).sub hA))
      hden3
  have hraw :=
    ((hterm1.add hterm2).sub
      (hasDerivAt_const (x := (0 : ℝ)) (1 : ℝ))).add hthreshold
  have hfun :
      (fun e : ℝ => interiorSpectralMargin δ a u e) =
        (fun e : ℝ =>
          (m e * p e) ^ 2 /
              (z ^ 2 * Q e * (1 - z ^ 2)) +
            ((z ^ 2 - (m e * t e) ^ 2) * p e) /
              (z ^ 2 * Q e * q) - 1 +
            δ / (2 * A e * (1 - A e))) := by
    funext e
    unfold interiorSpectralMargin
    rw [spectralLimit_interior_eq]
    dsimp [MetricCodes.Johnson.asymptoticThreshold,
      A, m, t, z, q, p, Q, c, interiorWeight]
    ring
  change HasDerivAt (fun e : ℝ => interiorSpectralMargin δ a u e) _ 0
  rw [hfun]
  refine hraw.congr_deriv ?_
  simp only [Nat.cast_ofNat, interiorSlope, mul_inv_rev, Pi.mul_apply, mul_zero, sub_zero, one_pow,
    Nat.add_one_sub_one, pow_one, mul_neg, Pi.pow_apply, zero_mul, neg_mul, zero_add, add_zero,
    sub_neg_eq_add, mul_one, zero_sub, Pi.sub_apply, m, A, c, p, t, z, Q, q]
  rw [hroot]
  have hdelta_div :
      δ =
        2 * (a * (1 - a) - u * (1 - u)) /
          (1 + 2 * Real.sqrt (u * (1 - u))) := by
    apply (eq_div_iff (by positivity)).2
    exact hdelta
  rw [hdelta_div]
  field_simp [ha0.ne', ha1.ne', hu.ne', hu1.ne',
    hz0.ne', hm0.ne', hs.ne', hrad.ne', hmrad.ne']
  ring_nf at hsquare ⊢
  linear_combination
    ((-128 * a ^ 3 * (a - 1) ^ 3 * (2 * a - 1) ^ 3 *
        Real.sqrt (u - u ^ 2)) +
      (64 * a ^ 2 * u * (a - 1) ^ 2 * (2 * a - 1) * (u - 1))) *
      hsquare

theorem interiorSpectralMargin_derivative_pos
    {a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2) :
    0 <
      (1 - 2 * (a * (1 - a))) *
          (1 - 2 * Real.sqrt (u * (1 - u))) /
        (a * (1 - a) * Real.sqrt (u * (1 - u)) *
          (1 + 2 * Real.sqrt (u * (1 - u)))) := by
  have ha0 : 0 < a := lt_trans hu hua
  have ha1 : 0 < 1 - a := by linarith
  have hu1 : 0 < 1 - u := by linarith
  have hs : 0 < Real.sqrt (u * (1 - u)) :=
    Real.sqrt_pos.mpr (mul_pos hu hu1)
  have hvariance : u * (1 - u) < (1 : ℝ) / 4 := by
    nlinarith [sq_pos_of_pos (by linarith : 0 < 1 - 2 * u)]
  have hshalf : Real.sqrt (u * (1 - u)) < (1 : ℝ) / 2 := by
    exact (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1 / 2)).mpr
      (by nlinarith)
  have hweight : 0 < 1 - 2 * (a * (1 - a)) := by
    nlinarith [sq_nonneg (a - (1 : ℝ) / 2)]
  exact div_pos
    (mul_pos hweight (by linarith))
    (by positivity)

theorem eventually_interiorSpectralMargin_pos
    {δ a u : ℝ}
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < interiorSpectralMargin δ a u e := by
  have hderiv :=
    hasDerivAt_interiorSpectralMargin hu hua ha hboundary
  have hpositive := interiorSpectralMargin_derivative_pos hu hua ha
  have hslope := hderiv.tendsto_slope_zero_right
  have heventual := hslope.eventually (lt_mem_nhds hpositive)
  filter_upwards [heventual, self_mem_nhdsWithin]
    with e he (hepos : 0 < e)
  have hzero := interiorSpectralMargin_zero hboundary
  have hslopepos : 0 < e⁻¹ * interiorSpectralMargin δ a u e := by
    simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using he
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hepos)).mp hslopepos

theorem eventually_interior_feasible
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∀ᶠ e : ℝ in 𝓝[>] 0,
      MetricCodes.Johnson.Feasible δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u := by
  have hweight := interior_boundary_weight_gt_distance
    hδ hu hua ha hboundary
  have hparameters := eventually_interior_parameters
    hδ hδ' hweight hu hua ha
  have hspectral := eventually_interiorSpectralMargin_pos
    hu hua ha hboundary
  filter_upwards [hparameters, hspectral] with e he hs
  refine ⟨he, ?_⟩
  change
    MetricCodes.Johnson.asymptoticThreshold δ (interiorWeight a u e) <
      MetricCodes.Johnson.spectralLimit
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u
  exact sub_pos.mp hs

theorem interior_shell_improvement
    {δ a u : ℝ}
    (hδ : 0 < δ) (hδ' : δ < (1 : ℝ) / 2)
    (hu : 0 < u) (hua : u < a) (ha : a < (1 : ℝ) / 2)
    (hboundary :
      MetricCodes.Johnson.spectralLimit a 0 0 u =
        MetricCodes.Johnson.asymptoticThreshold δ a) :
    ∃ A b g : ℝ,
      0 < b ∧ 0 < g ∧
      MetricCodes.Johnson.Feasible δ A b g u ∧
      MetricCodes.Johnson.shellRate A b g u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
  have hfeasible := eventually_interior_feasible
    hδ hδ' hu hua ha hboundary
  have himprovement := eventually_shellRate_interior_improvement
    (u := u) (lt_trans hu hua) ha
  have hweight := tendsto_interiorWeight_zero a u
  have hpositive :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < interiorWeight a u e :=
    hweight.eventually (lt_mem_nhds (lt_trans hu hua))
  have hcomplement :
      ∀ᶠ e : ℝ in 𝓝[>] 0, 0 < 1 - interiorWeight a u e := by
    filter_upwards
      [hweight.eventually
        (gt_mem_nhds (show a < (1 : ℝ) by linarith))]
      with e he
    linarith
  have hall : ∀ᶠ e : ℝ in 𝓝[>] 0,
      0 < interiorSupport a u e ∧
      0 < interiorComplement a u e ∧
      MetricCodes.Johnson.Feasible δ
        (interiorWeight a u e)
        (interiorSupport a u e)
        (interiorComplement a u e) u ∧
      MetricCodes.Johnson.shellRate
          (interiorWeight a u e)
          (interiorSupport a u e)
          (interiorComplement a u e) u <
        MetricCodes.Johnson.shellRate a 0 0 u := by
    filter_upwards [hfeasible, himprovement, hpositive, hcomplement,
      self_mem_nhdsWithin] with e hf hi hw hc (he : 0 < e)
    refine ⟨?_, ?_, hf, hi⟩
    · unfold interiorSupport
      exact mul_pos hw he
    · unfold interiorComplement
      exact mul_pos hc he
  obtain ⟨e, he⟩ := hall.exists
  exact ⟨interiorWeight a u e,
    interiorSupport a u e, interiorComplement a u e, he⟩

theorem variationalRate_lt_mrrw_of_interior
    {δ : ℝ}
    (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2)
    (hstrict :
      MetricCodes.Johnson.mrrwRate δ < MetricCodes.Hamming.classicalRate δ) :
    MetricCodes.Johnson.variationalRate δ <
      MetricCodes.Johnson.mrrwRate δ := by
  obtain ⟨a, u, hu, hua, ha, _hweight, hboundary, hrate⟩ :=
    exists_zero_fibre_boundary_of_interior_minimizer
      hδ hhalf hstrict
  obtain ⟨A, b, g, _hb, _hg, hfeasible, himprovement⟩ :=
    interior_shell_improvement hδ hhalf hu hua ha hboundary
  calc
    MetricCodes.Johnson.variationalRate δ ≤
        MetricCodes.Johnson.shellRate A b g u :=
      MetricCodes.Johnson.variationalRate_le_of_feasible hfeasible
    _ < MetricCodes.Johnson.shellRate a 0 0 u := himprovement
    _ = MetricCodes.Johnson.mrrwRate δ := hrate.symm

theorem strict_mrrw2
    {δ : ℝ} (hδ : 0 < δ) (hhalf : δ < (1 : ℝ) / 2) :
    MetricCodes.Johnson.combinedVariationalRate δ <
      MetricCodes.Johnson.mrrwRate δ := by
  rcases MetricCodes.Johnson.mrrw_endpoint_dichotomy hδ hhalf with
    hstrict | hendpoint
  · exact
      (MetricCodes.Johnson.combinedVariationalRate_le_shell δ).trans_lt
        (variationalRate_lt_mrrw_of_interior hδ hhalf hstrict)
  · exact MetricCodes.Johnson.combinedVariationalRate_lt_mrrw_of_endpoint
      hδ hhalf hendpoint

end

end MRRW

namespace Johnson

section


open scoped BigOperators InnerProductSpace Matrix

private def johnsonWindowBasis {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (Q : ShellWindowIndex n p q L) :
    MetricCodes.Boolean.Function n :=
  MetricCodes.Boolean.harmonicBasisFunction n
    (p + q + Q.1.val) (h.window_degree_half Q.1) Q.2

theorem johnsonWindowBasis_isHarmonic {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (Q : ShellWindowIndex n p q L) :
    MetricCodes.Boolean.IsHarmonic (p + q + Q.1.val)
      (johnsonWindowBasis h Q) := by
  exact MetricCodes.Boolean.harmonicBasisFunction_isHarmonic n
    (p + q + Q.1.val) (h.window_degree_half Q.1) Q.2

private def johnsonHarmonicCoordinates {n j : ℕ}
    (hj : 2 * j ≤ n)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f) :
    Fin (MetricCodes.booleanHarmonicDimension n j) → ℝ :=
  fun a =>
    (MetricCodes.Boolean.harmonicOrthonormalBasis n j hj).repr
      (globalHarmonicVector f hf) a

theorem johnsonHarmonicCoordinates_pairing {n j : ℕ}
    (hj : 2 * j ≤ n)
    (f g : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (hg : MetricCodes.Boolean.IsHarmonic j g) :
    (∑ a : Fin (MetricCodes.booleanHarmonicDimension n j),
      johnsonHarmonicCoordinates hj f hf a *
        johnsonHarmonicCoordinates hj g hg a) =
      MetricCodes.Boolean.dot f g := by
  let e := MetricCodes.Boolean.harmonicOrthonormalBasis n j hj
  let A := globalHarmonicVector f hf
  let B := globalHarmonicVector g hg
  calc
    (∑ a : Fin (MetricCodes.booleanHarmonicDimension n j),
      johnsonHarmonicCoordinates hj f hf a *
        johnsonHarmonicCoordinates hj g hg a) =
      @inner ℝ
        (EuclideanSpace ℝ
          (Fin (MetricCodes.booleanHarmonicDimension n j))) _
          (e.repr A) (e.repr B) := by
            change
              (∑ a : Fin (MetricCodes.hammingFibreDimension n j),
                e.repr A a * e.repr B a) =
                @inner ℝ
                  (EuclideanSpace ℝ
                    (Fin (MetricCodes.hammingFibreDimension n j))) _
                    (e.repr A) (e.repr B)
            rw [PiLp.inner_apply]
            simp only [RCLike.inner_apply, Real.ringHom_apply, mul_comm]
    _ = @inner ℝ
        (MetricCodes.Boolean.harmonicEuclideanLayer n j) _ A B :=
      e.repr.inner_map_map A B
    _ = MetricCodes.Boolean.dot f g :=
      globalHarmonicVector_inner f g hf hg

theorem johnsonWindowBasis_dot {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (source : Index p q L)
    (a b : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + source.val))) :
    MetricCodes.Boolean.dot
        (johnsonWindowBasis h ⟨source, a⟩)
        (johnsonWindowBasis h ⟨source, b⟩) =
      if a = b then 1 else 0 := by
  exact MetricCodes.Boolean.harmonicBasisFunction_dot n
    (p + q + source.val) (h.window_degree_half source) a b

theorem globalHarmonicVector_harmonicBasisFunction {n j : ℕ}
    (hj : 2 * j ≤ n)
    (a : Fin (MetricCodes.booleanHarmonicDimension n j)) :
    globalHarmonicVector
        (MetricCodes.Boolean.harmonicBasisFunction n j hj a)
        (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic n j hj a) =
      MetricCodes.Boolean.harmonicOrthonormalBasis n j hj a := by
  apply Subtype.ext
  change
    WithLp.toLp 2
        (MetricCodes.Boolean.layerRestrict j
          (MetricCodes.Boolean.layerExtend
            (WithLp.ofLp
              ((MetricCodes.Boolean.harmonicOrthonormalBasis
                n j hj a).val)))) =
      (MetricCodes.Boolean.harmonicOrthonormalBasis n j hj a).val
  rw [MetricCodes.Boolean.layerRestrict_layerExtend]

theorem johnsonHarmonicCoordinates_eq_basis_dot {n j : ℕ}
    (hj : 2 * j ≤ n)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic j f)
    (a : Fin (MetricCodes.booleanHarmonicDimension n j)) :
    johnsonHarmonicCoordinates hj f hf a =
      MetricCodes.Boolean.dot
        (MetricCodes.Boolean.harmonicBasisFunction n j hj a) f := by
  unfold johnsonHarmonicCoordinates
  rw [OrthonormalBasis.repr_apply_apply]
  rw [← globalHarmonicVector_harmonicBasisFunction hj a]
  exact globalHarmonicVector_inner
    (MetricCodes.Boolean.harmonicBasisFunction n j hj a) f
    (MetricCodes.Boolean.harmonicBasisFunction_isHarmonic n j hj a) hf

theorem johnsonWindowBasis_dot_coupled
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (x : JohnsonSphere n w)
    (source : Index p q L)
    (a : HarmonicFibreIndex n w p q)
    (b : Fin (MetricCodes.booleanHarmonicDimension
      n (p + q + source.val))) :
    MetricCodes.Boolean.dot (johnsonWindowBasis h ⟨source, b⟩)
        (coupledHarmonic x h.support_half h.complement_half
          a source.val) =
      coupledDegreeCoordinates h x source a b := by
  symm
  exact johnsonHarmonicCoordinates_eq_basis_dot
    (h.window_degree_half source)
    (coupledHarmonic x h.support_half h.complement_half
      a source.val)
    (coupledHarmonic_isHarmonic x h.support_half h.complement_half
      (h.supportResidual_bound source)
      (h.complementResidual_bound source) a) b

private def johnsonWindowChannelMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (lam : ℝ) :
    Matrix (Fin n × ShellWindowIndex n p q L)
      (ShellWindowIndex n p q L) ℝ :=
  fun T Q =>
    johnsonAdjacentBlockCoefficient n w p q L v lam T.2.1 Q.1 *
      johnsonHarmonicCoordinates (h.window_degree_half T.2.1)
        (johnsonAdjacentChannel n w p q L T.2.1 Q.1
          (johnsonWindowBasis h Q) T.1)
        (johnsonAdjacentChannel_isHarmonic h hstrict T.2.1 Q.1
          (johnsonWindowBasis h Q)
          (johnsonWindowBasis_isHarmonic h Q) T.1) T.2.2

theorem johnsonWindowChannelMatrix_pairing
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (lam : ℝ)
    (Q R : ShellWindowIndex n p q L) :
    (∑ T : Fin n × ShellWindowIndex n p q L,
      johnsonWindowChannelMatrix h hstrict v lam T Q *
        johnsonWindowChannelMatrix h hstrict v lam T R) =
      ∑ target : Index p q L,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonAdjacentBlockCoefficient n w p q L v lam target R.1) *
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target Q.1
            (johnsonWindowBasis h Q))
          (johnsonAdjacentChannel n w p q L target R.1
            (johnsonWindowBasis h R)) := by
  classical
  unfold johnsonWindowChannelMatrix
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro target _
  calc
    (∑ b : Fin (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val)),
      ∑ a : Fin n,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target Q.1
              (johnsonWindowBasis h Q) a)
            (johnsonAdjacentChannel_isHarmonic h hstrict target Q.1
              (johnsonWindowBasis h Q)
              (johnsonWindowBasis_isHarmonic h Q) a) b) *
        (johnsonAdjacentBlockCoefficient n w p q L v lam target R.1 *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target R.1
              (johnsonWindowBasis h R) a)
            (johnsonAdjacentChannel_isHarmonic h hstrict target R.1
              (johnsonWindowBasis h R)
              (johnsonWindowBasis_isHarmonic h R) a) b)) =
      (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
        johnsonAdjacentBlockCoefficient n w p q L v lam target R.1) *
      (∑ a : Fin n,
        ∑ b : Fin (MetricCodes.booleanHarmonicDimension
          n (p + q + target.val)),
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target Q.1
              (johnsonWindowBasis h Q) a)
            (johnsonAdjacentChannel_isHarmonic h hstrict target Q.1
              (johnsonWindowBasis h Q)
              (johnsonWindowBasis_isHarmonic h Q) a) b *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target R.1
              (johnsonWindowBasis h R) a)
            (johnsonAdjacentChannel_isHarmonic h hstrict target R.1
              (johnsonWindowBasis h R)
              (johnsonWindowBasis_isHarmonic h R) a) b) := by
        rw [Finset.sum_comm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
    _ = _ := by
      unfold MetricCodes.Boolean.coordinateDot
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      exact johnsonHarmonicCoordinates_pairing
        (h.window_degree_half target)
        (johnsonAdjacentChannel n w p q L target Q.1
          (johnsonWindowBasis h Q) a)
        (johnsonAdjacentChannel n w p q L target R.1
          (johnsonWindowBasis h R) a)
        (johnsonAdjacentChannel_isHarmonic h hstrict target Q.1
          (johnsonWindowBasis h Q)
          (johnsonWindowBasis_isHarmonic h Q) a)
        (johnsonAdjacentChannel_isHarmonic h hstrict target R.1
          (johnsonWindowBasis h R)
          (johnsonWindowBasis_isHarmonic h R) a)

theorem johnsonWindowChannelMatrix_transpose_mul
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v) :
    (johnsonWindowChannelMatrix h hstrict v lam)ᵀ *
      johnsonWindowChannelMatrix h hstrict v lam = 1 := by
  classical
  ext Q R
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  rw [johnsonWindowChannelMatrix_pairing h hstrict v lam Q R]
  rcases Q with ⟨source, a⟩
  rcases R with ⟨other, b⟩
  by_cases heq : source = other
  · subst other
    calc
      (∑ target : Index p q L,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target source *
          johnsonAdjacentBlockCoefficient n w p q L v lam target source) *
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source
            (johnsonWindowBasis h ⟨source, a⟩))
          (johnsonAdjacentChannel n w p q L target source
            (johnsonWindowBasis h ⟨source, b⟩))) =
        ∑ target : Index p q L,
          johnsonAdjacentBlockCoefficient n w p q L v lam
            target source ^ 2 *
            MetricCodes.Boolean.dot
              (johnsonWindowBasis h ⟨source, a⟩)
              (johnsonWindowBasis h ⟨source, b⟩) := by
          apply Finset.sum_congr rfl
          intro target _
          by_cases hactive : johnsonChannelActive p q L target source
          · rw [johnsonAdjacentChannel_isometry h hstrict
              target source hactive
              (johnsonWindowBasis h ⟨source, a⟩)
              (johnsonWindowBasis h ⟨source, b⟩)
              (johnsonWindowBasis_isHarmonic h ⟨source, a⟩)
              (johnsonWindowBasis_isHarmonic h ⟨source, b⟩)]
            ring
          · have hzero :=
              johnsonSourceChannelCoefficient_eq_zero_of_not_active
                (n := n) (w := w)
                source target hactive
            have hblock :
                johnsonAdjacentBlockCoefficient
                  n w p q L v lam target source = 0 := by
              simp only [johnsonAdjacentBlockCoefficient, hzero, zero_mul, zero_div, Real.sqrt_zero]
            simp only [hblock, mul_zero, zero_mul, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
              zero_pow]
      _ = (∑ target : Index p q L,
            johnsonAdjacentBlockCoefficient n w p q L v lam
              target source ^ 2) *
          MetricCodes.Boolean.dot
            (johnsonWindowBasis h ⟨source, a⟩)
            (johnsonWindowBasis h ⟨source, b⟩) := by
          rw [Finset.sum_mul]
      _ = if (⟨source, a⟩ : ShellWindowIndex n p q L) =
            (⟨source, b⟩ : ShellWindowIndex n p q L)
          then 1 else 0 := by
          rw [johnsonAdjacentBlockCoefficient_sq_sum
            h hstrict v hv lam hlam heigen source,
            one_mul, johnsonWindowBasis_dot]
          by_cases hab : a = b
          · subst b
            simp only [↓reduceIte]
          · have hsigma :
                (⟨source, a⟩ : ShellWindowIndex n p q L) ≠
                  (⟨source, b⟩ : ShellWindowIndex n p q L) := by
              intro heq
              cases heq
              exact hab rfl
            simp only [hab, ↓reduceIte, hsigma]
  · have hsigma :
        (⟨source, a⟩ : ShellWindowIndex n p q L) ≠
          (⟨other, b⟩ : ShellWindowIndex n p q L) := by
      intro hpair
      exact heq
        (congrArg (fun Z : ShellWindowIndex n p q L => Z.1) hpair)
    rw [ite_eq_right hsigma]
    apply Finset.sum_eq_zero
    intro target _
    rw [johnsonAdjacentChannel_orthogonal h hstrict
      target source other heq
      (johnsonWindowBasis h ⟨source, a⟩)
      (johnsonWindowBasis h ⟨other, b⟩)
      (johnsonWindowBasis_isHarmonic h ⟨source, a⟩)
      (johnsonWindowBasis_isHarmonic h ⟨other, b⟩)]
    ring

private def johnsonChannelMatrix {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L) (lam : ℝ) :
    Matrix
      (Fin n × Fin (MetricCodes.johnsonAmbientDimension n (p + q) L))
      (Fin (MetricCodes.johnsonAmbientDimension n (p + q) L)) ℝ :=
  fun T Q =>
    johnsonWindowChannelMatrix h hstrict v lam
      (T.1, (shellWindowIndexEquiv n p q L h.first_le).symm T.2)
      ((shellWindowIndexEquiv n p q L h.first_le).symm Q)

theorem johnsonChannelMatrix_transpose_mul
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v) :
    (johnsonChannelMatrix h hstrict v lam)ᵀ *
      johnsonChannelMatrix h hstrict v lam = 1 := by
  classical
  let e := shellWindowIndexEquiv n p q L h.first_le
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
  change
    (∑ T : Fin n × Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
      johnsonWindowChannelMatrix h hstrict v lam
          (T.1, e.symm T.2) (e.symm i) *
        johnsonWindowChannelMatrix h hstrict v lam
          (T.1, e.symm T.2) (e.symm j)) =
      if i = j then 1 else 0
  have hwindow := congrArg
    (fun M : Matrix (ShellWindowIndex n p q L)
        (ShellWindowIndex n p q L) ℝ =>
      M (e.symm i) (e.symm j))
    (johnsonWindowChannelMatrix_transpose_mul
      h hstrict v hv lam hlam heigen)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.one_apply] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ a : Fin n,
      ∑ T : Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
        johnsonWindowChannelMatrix h hstrict v lam
            (a, e.symm T) (e.symm i) *
          johnsonWindowChannelMatrix h hstrict v lam
            (a, e.symm T) (e.symm j)) =
      ∑ a : Fin n,
        ∑ T : ShellWindowIndex n p q L,
          johnsonWindowChannelMatrix h hstrict v lam
              (a, T) (e.symm i) *
            johnsonWindowChannelMatrix h hstrict v lam
              (a, T) (e.symm j) := by
          apply Finset.sum_congr rfl
          intro a _
          exact e.symm.sum_comp
            (fun T : ShellWindowIndex n p q L =>
              johnsonWindowChannelMatrix h hstrict v lam
                  (a, T) (e.symm i) *
                johnsonWindowChannelMatrix h hstrict v lam
                  (a, T) (e.symm j))
    _ = if i = j then 1 else 0 := by
      rw [hwindow]
      simp only [EmbeddingLike.apply_eq_iff_eq]

theorem johnsonAdjacentChannel_coordinate_axisDot
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (x : JohnsonSphere n w)
    (target source : Index p q L)
    (f : MetricCodes.Boolean.Function n)
    (hf : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
    (a : HarmonicFibreIndex n w p q) :
    (∑ k : Fin n,
      ∑ b : Fin (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val)),
        geometricAxis x k *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target source f k)
            (johnsonAdjacentChannel_isHarmonic h hstrict
              target source f hf k) b *
          coupledDegreeCoordinates h x target a b) =
      MetricCodes.Boolean.coordinateDot
        (johnsonAdjacentChannel n w p q L target source f)
        (johnsonAxisTensor x
          (coupledHarmonic x h.support_half h.complement_half
            a target.val)) := by
  classical
  unfold MetricCodes.Boolean.coordinateDot johnsonAxisTensor
  apply Finset.sum_congr rfl
  intro k _
  calc
    (∑ b : Fin (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val)),
      geometricAxis x k *
        johnsonHarmonicCoordinates (h.window_degree_half target)
          (johnsonAdjacentChannel n w p q L target source f k)
          (johnsonAdjacentChannel_isHarmonic h hstrict
            target source f hf k) b *
        coupledDegreeCoordinates h x target a b) =
      geometricAxis x k *
        (∑ b : Fin (MetricCodes.booleanHarmonicDimension
          n (p + q + target.val)),
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target source f k)
            (johnsonAdjacentChannel_isHarmonic h hstrict
              target source f hf k) b *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)
            (coupledHarmonic_isHarmonic x h.support_half
              h.complement_half (h.supportResidual_bound target)
              (h.complementResidual_bound target) a) b) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        simp only [coupledDegreeCoordinates,
          johnsonHarmonicCoordinates, coupledDegreeVector]
        ring
    _ = geometricAxis x k *
        MetricCodes.Boolean.dot
          (johnsonAdjacentChannel n w p q L target source f k)
          (coupledHarmonic x h.support_half h.complement_half
            a target.val) := by
      rw [johnsonHarmonicCoordinates_pairing
        (h.window_degree_half target)
        (johnsonAdjacentChannel n w p q L target source f k)
        (coupledHarmonic x h.support_half h.complement_half
          a target.val)
        (johnsonAdjacentChannel_isHarmonic h hstrict
          target source f hf k)
        (coupledHarmonic_isHarmonic x h.support_half
          h.complement_half (h.supportResidual_bound target)
          (h.complementResidual_bound target) a)]
    _ = MetricCodes.Boolean.dot
        (johnsonAdjacentChannel n w p q L target source f k)
        ((geometricAxis x k) •
          coupledHarmonic x h.support_half h.complement_half
            a target.val) := by
      rw [MetricCodes.Boolean.dot_smul_right]

theorem johnsonWindowChannelMatrix_transpose_axis_fibre
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val))
    (x : JohnsonSphere n w) :
    (johnsonWindowChannelMatrix h hstrict v lam)ᵀ *
      MetricCodes.Boolean.matrixAxisLift
        (fun k : Fin n => geometricAxis x k)
        (johnsonWindowFibreMatrix h v x) =
      Real.sqrt lam • johnsonWindowFibreMatrix h v x := by
  classical
  ext Q a
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ T : Fin n × ShellWindowIndex n p q L,
      (johnsonAdjacentBlockCoefficient n w p q L v lam T.2.1 Q.1 *
        johnsonHarmonicCoordinates (h.window_degree_half T.2.1)
          (johnsonAdjacentChannel n w p q L T.2.1 Q.1
            (johnsonWindowBasis h Q) T.1)
          (johnsonAdjacentChannel_isHarmonic h hstrict T.2.1 Q.1
            (johnsonWindowBasis h Q)
            (johnsonWindowBasis_isHarmonic h Q) T.1) T.2.2) *
      (geometricAxis x T.1 *
        (johnsonFibreAmplitude n w p q L v T.2.1 *
          coupledDegreeCoordinates h x T.2.1 a T.2.2))) =
      Real.sqrt lam *
        (johnsonFibreAmplitude n w p q L v Q.1 *
          coupledDegreeCoordinates h x Q.1 a Q.2)
  rw [Fintype.sum_prod_type, Finset.sum_comm, Fintype.sum_sigma]
  calc
    (∑ target : Index p q L,
      ∑ b : Fin (MetricCodes.booleanHarmonicDimension
        n (p + q + target.val)),
      ∑ k : Fin n,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonHarmonicCoordinates (h.window_degree_half target)
            (johnsonAdjacentChannel n w p q L target Q.1
              (johnsonWindowBasis h Q) k)
            (johnsonAdjacentChannel_isHarmonic h hstrict target Q.1
              (johnsonWindowBasis h Q)
              (johnsonWindowBasis_isHarmonic h Q) k) b) *
          (geometricAxis x k *
            (johnsonFibreAmplitude n w p q L v target *
              coupledDegreeCoordinates h x target a b))) =
      ∑ target : Index p q L,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonFibreAmplitude n w p q L v target) *
          (∑ k : Fin n,
            ∑ b : Fin (MetricCodes.booleanHarmonicDimension
              n (p + q + target.val)),
              geometricAxis x k *
                johnsonHarmonicCoordinates
                  (h.window_degree_half target)
                  (johnsonAdjacentChannel n w p q L target Q.1
                    (johnsonWindowBasis h Q) k)
                  (johnsonAdjacentChannel_isHarmonic
                    h hstrict target Q.1 (johnsonWindowBasis h Q)
                    (johnsonWindowBasis_isHarmonic h Q) k) b *
                coupledDegreeCoordinates h x target a b) := by
          apply Finset.sum_congr rfl
          intro target _
          rw [Finset.sum_comm, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro k _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro b _
          ring
    _ = ∑ target : Index p q L,
        (johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
          johnsonFibreAmplitude n w p q L v target) *
          MetricCodes.Boolean.coordinateDot
            (johnsonAdjacentChannel n w p q L target Q.1
              (johnsonWindowBasis h Q))
            (johnsonAxisTensor x
              (coupledHarmonic x h.support_half h.complement_half
                a target.val)) := by
      apply Finset.sum_congr rfl
      intro target _
      rw [johnsonAdjacentChannel_coordinate_axisDot
        h hstrict x target Q.1
        (johnsonWindowBasis h Q)
        (johnsonWindowBasis_isHarmonic h Q) a]
    _ = (∑ target : Index p q L,
          johnsonAdjacentBlockCoefficient n w p q L v lam target Q.1 *
            johnsonFibreAmplitude n w p q L v target *
            Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L Q.1 target)) *
          MetricCodes.Boolean.dot (johnsonWindowBasis h Q)
            (coupledHarmonic x h.support_half h.complement_half
              a Q.1.val) := by
      simp_rw [haxis x _ Q.1
        (johnsonWindowBasis h Q)
        (johnsonWindowBasis_isHarmonic h Q) a]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro target _
      ring
    _ = Real.sqrt lam *
        (johnsonFibreAmplitude n w p q L v Q.1 *
          coupledDegreeCoordinates h x Q.1 a Q.2) := by
      rw [johnsonAdjacentBlockCoefficient_amplitude_sum
        h hstrict v hv lam hlam heigen Q.1,
        johnsonWindowBasis_dot_coupled h x Q.1 a Q.2]
      ring

theorem johnsonChannelMatrix_transpose_axis_fibre
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val))
    (x : JohnsonSphere n w) :
    (johnsonChannelMatrix h hstrict v lam)ᵀ *
      MetricCodes.Boolean.matrixAxisLift
        (fun k : Fin n => geometricAxis x k)
        (johnsonFibreMatrix h v x) =
      Real.sqrt lam • johnsonFibreMatrix h v x := by
  classical
  let e := shellWindowIndexEquiv n p q L h.first_le
  let d := harmonicFibreIndexEquiv n w p q
  ext i a
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul]
  change
    (∑ T : Fin n × Fin (MetricCodes.johnsonAmbientDimension
      n (p + q) L),
      johnsonWindowChannelMatrix h hstrict v lam
          (T.1, e.symm T.2) (e.symm i) *
        (geometricAxis x T.1 *
          johnsonWindowFibreMatrix h v x
            (e.symm T.2) (d.symm a))) =
      Real.sqrt lam *
        johnsonWindowFibreMatrix h v x (e.symm i) (d.symm a)
  have hwindow := congrArg
    (fun M : Matrix (ShellWindowIndex n p q L)
        (HarmonicFibreIndex n w p q) ℝ =>
      M (e.symm i) (d.symm a))
    (johnsonWindowChannelMatrix_transpose_axis_fibre
      h hstrict v hv lam hlam heigen haxis x)
  simp only [Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.smul_apply, smul_eq_mul] at hwindow
  rw [Fintype.sum_prod_type] at hwindow ⊢
  calc
    (∑ k : Fin n,
      ∑ T : Fin (MetricCodes.johnsonAmbientDimension n (p + q) L),
        johnsonWindowChannelMatrix h hstrict v lam
            (k, e.symm T) (e.symm i) *
          (geometricAxis x k *
            johnsonWindowFibreMatrix h v x
              (e.symm T) (d.symm a))) =
      ∑ k : Fin n,
        ∑ T : ShellWindowIndex n p q L,
          johnsonWindowChannelMatrix h hstrict v lam
              (k, T) (e.symm i) *
            (geometricAxis x k *
              johnsonWindowFibreMatrix h v x T (d.symm a)) := by
        apply Finset.sum_congr rfl
        intro k _
        exact e.symm.sum_comp
          (fun T : ShellWindowIndex n p q L =>
            johnsonWindowChannelMatrix h hstrict v lam
                (k, T) (e.symm i) *
              (geometricAxis x k *
                johnsonWindowFibreMatrix h v x T (d.symm a)))
    _ = Real.sqrt lam *
        johnsonWindowFibreMatrix h v x (e.symm i) (d.symm a) :=
      hwindow

theorem johnsonChannelMatrix_transpose_axis_projection
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val))
    (x : JohnsonSphere n w) :
    (johnsonChannelMatrix h hstrict v lam)ᵀ *
      MetricCodes.Boolean.matrixAxisLift
        (fun k : Fin n => geometricAxis x k)
        ((johnsonProjectionFamily h v hv).projection x) =
      Real.sqrt lam •
        ((johnsonProjectionFamily h v hv).projection x) := by
  let A := johnsonFibreMatrix h v x
  change
    (johnsonChannelMatrix h hstrict v lam)ᵀ *
      MetricCodes.Boolean.matrixAxisLift
        (fun k : Fin n => geometricAxis x k)
        (A * Aᵀ) =
      Real.sqrt lam • (A * Aᵀ)
  rw [MetricCodes.Boolean.matrixAxisLift_mul, ← Matrix.mul_assoc,
    johnsonChannelMatrix_transpose_axis_fibre
      h hstrict v hv lam hlam heigen haxis x,
    Matrix.smul_mul]

private def johnsonGramIndexEquiv (n D : ℕ) :
    ((Fin n × Fin D) × Fin D) ≃ Fin (n * D * D) :=
  Fintype.equivOfCardEq (by simp only [Fintype.card_prod, Fintype.card_fin])

private def johnsonProjectionGramFeature
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (x : JohnsonSphere n w) :
    EuclideanSpace ℝ
      (Fin (n * MetricCodes.johnsonAmbientDimension n (p + q) L *
        MetricCodes.johnsonAmbientDimension n (p + q) L)) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (johnsonGramIndexEquiv n
      (MetricCodes.johnsonAmbientDimension n (p + q) L)))
    (MetricCodes.Boolean.matrixAxisGramFeature
      (johnsonProjectionFamily h v hv)
      (fun (y : JohnsonSphere n w) (k : Fin n) =>
        geometricAxis y k)
      (johnsonChannelMatrix h hstrict v lam)
      (Real.sqrt lam) x)

theorem johnsonProjectionGramFeature_inner
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (v : Space p q L)
    (hv : ∀ i : Index p q L, 0 < v i)
    (lam : ℝ) (hlam : 0 < lam)
    (heigen : operator n w p q L v = lam • v)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val))
    (x y : JohnsonSphere n w) :
    @inner ℝ
      (EuclideanSpace ℝ
        (Fin (n * MetricCodes.johnsonAmbientDimension n (p + q) L *
          MetricCodes.johnsonAmbientDimension n (p + q) L))) _
      (johnsonProjectionGramFeature h hstrict v hv lam x)
      (johnsonProjectionGramFeature h hstrict v hv lam y) =
      (correlation x y - lam) *
        (johnsonProjectionFamily h v hv).overlap x y := by
  let P := johnsonProjectionFamily h v hv
  let axis : JohnsonSphere n w → Fin n → ℝ :=
    fun z k => geometricAxis z k
  let B := johnsonChannelMatrix h hstrict v lam
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
    (johnsonGramIndexEquiv n
      (MetricCodes.johnsonAmbientDimension n (p + q) L))
  have hgram := MetricCodes.Boolean.matrixAxisResidual_gram P axis B
    (Real.sqrt lam) lam
    (johnsonChannelMatrix_transpose_mul
      h hstrict v hv lam hlam heigen)
    (fun z => johnsonChannelMatrix_transpose_axis_projection
      h hstrict v hv lam hlam heigen haxis z)
    (Real.sq_sqrt hlam.le) x y
  have haxisinner :
      (∑ k : Fin n,
        geometricAxis x k * geometricAxis y k) =
        correlation x y := by
    have hinner := geometricAxis_inner h.weight_pos h.weight_lt x y
    simpa only [PiLp.inner_apply, RCLike.inner_apply, Real.ringHom_apply, mul_comm] using hinner
  change
    @inner ℝ
      (EuclideanSpace ℝ
        (Fin (n * MetricCodes.johnsonAmbientDimension n (p + q) L *
          MetricCodes.johnsonAmbientDimension n (p + q) L))) _
      (e (MetricCodes.Boolean.matrixAxisGramFeature P axis B
        (Real.sqrt lam) x))
      (e (MetricCodes.Boolean.matrixAxisGramFeature P axis B
        (Real.sqrt lam) y)) =
      (correlation x y - lam) * P.overlap x y
  rw [e.inner_map_map]
  simpa only [axis, haxisinner] using hgram

private def johnsonProjectionGram_of_axis
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hwindow : p + q < L)
    (haxis : ∀ (x : JohnsonSphere n w)
      (target source : Index p q L)
      (f : MetricCodes.Boolean.Function n)
      (_ : MetricCodes.Boolean.IsHarmonic (p + q + source.val) f)
      (a : HarmonicFibreIndex n w p q),
        MetricCodes.Boolean.coordinateDot
          (johnsonAdjacentChannel n w p q L target source f)
          (johnsonAxisTensor x
            (coupledHarmonic x h.support_half h.complement_half
              a target.val)) =
          Real.sqrt
              (johnsonSourceChannelCoefficient
                n w p q L source target) *
            MetricCodes.Boolean.dot f
              (coupledHarmonic x h.support_half h.complement_half
                a source.val)) :
    ProjectionGram n w p q L := by
  classical
  let hperron := exists_positive_unit_topEigenvector h hstrict
  let v : Space p q L := Classical.choose hperron
  have hdata := Classical.choose_spec hperron
  have heigen :
      operator n w p q L v =
        topEigenvalue n w p q L • v := hdata.2.1
  have hv : ∀ i : Index p q L, 0 < v i := hdata.2.2
  have hpositive := topEigenvalue_pos h hstrict hwindow
  exact {
    projections := johnsonProjectionFamily h v hv
    feature := johnsonProjectionGramFeature
      h hstrict v hv (topEigenvalue n w p q L)
    gram := fun x y => johnsonProjectionGramFeature_inner
      h hstrict v hv (topEigenvalue n w p q L)
      hpositive heigen haxis x y
  }

private def johnsonProjectionGram
    {n w p q L : ℕ}
    (h : AdmissibleDegrees n w p q L)
    (hstrict : 2 * w < n)
    (hwindow : p + q < L) :
    ProjectionGram n w p q L :=
  johnsonProjectionGram_of_axis h hstrict hwindow
    (fun x target source f hf a =>
      johnsonAdjacentChannel_axis_inner h hstrict x target source f hf a)

end

namespace SpectralAsymptotics

section


open Filter Topology
open scoped BigOperators Topology
open MetricCodes.Johnson.Asymptotics

private def terminalIndex (u : ℝ) (r n : ℕ) : ℕ :=
  terminalDegree u n - r

theorem tendsto_terminalIndex_ratio
    {u : ℝ} (hu : 0 < u) (r : ℕ) :
    Tendsto
      (fun n : ℕ => (terminalIndex u r n : ℝ) / (n : ℝ))
      atTop (nhds u) := by
  simpa only [terminalIndex,
    terminalDegree] using MetricCodes.Hamming.tendsto_terminal_degree_ratio hu r

theorem tendsto_add_degree_add_fixed_ratio
    {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => (f n : ℝ) / (n : ℝ))
      atTop (nhds a))
    (hg : Tendsto (fun n : ℕ => (g n : ℝ) / (n : ℝ))
      atTop (nhds b))
    (r : ℕ) :
    Tendsto
      (fun n : ℕ => ((f n + g n + r : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (a + b)) := by
  have hsum := tendsto_add_degree_ratio hf hg
  have hoffset :=
    tendsto_const_div_atTop_nhds_zero_nat (r : ℝ)
  have htotal := hsum.add hoffset
  rw [add_zero] at htotal
  refine htotal.congr' (Eventually.of_forall fun n => ?_)
  push_cast
  ring

theorem eventually_terminal_block_fit
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      supportDegree b n + complementDegree g n + r <
        terminalDegree u n := by
  have hfirst := tendsto_add_degree_add_fixed_ratio
    (tendsto_supportDegree_ratio h.support_nonneg)
    (tendsto_complementDegree_ratio h.complement_nonneg) r
  exact eventually_degree_lt_of_ratio hfirst
    (tendsto_terminalDegree_ratio h.degree_pos.le)
    h.first_lt_degree

theorem tendsto_complementWeight_ratio
    {a : ℝ} (ha : 0 ≤ a) (ha' : a ≤ 1) :
    Tendsto
      (fun n : ℕ =>
        ((n - shellWeight a n : ℕ) : ℝ) / (n : ℝ))
      atTop (nhds (1 - a)) := by
  simpa only [shellWeight] using MetricCodes.Hamming.tendsto_complement_longitudinal_ratio ha ha'

theorem tendsto_johnsonJ1_ratio
    {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonJ1 (shellWeight a n) (supportDegree b n) /
          (n : ℝ))
      atTop (nhds (a / 2 - b)) := by
  have hspin :=
    (tendsto_shellWeight_ratio ha).div_const 2
  have hmain := hspin.sub (tendsto_supportDegree_ratio hb)
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonJ1
  ring

theorem tendsto_johnsonJ2_ratio
    {a g : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1) (hg : 0 ≤ g) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonJ2 n (shellWeight a n) (complementDegree g n) /
          (n : ℝ))
      atTop (nhds ((1 - a) / 2 - g)) := by
  have hspin :=
    (tendsto_complementWeight_ratio ha ha').div_const 2
  have hmain := hspin.sub (tendsto_complementDegree_ratio hg)
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonJ2
  ring

theorem tendsto_johnsonJ_ratio
    {u : ℝ} (hu : 0 < u) (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ))
      atTop (nhds ((1 - 2 * u) / 2)) := by
  have hspin := tendsto_dimension_ratio.div_const 2
  have hmain := hspin.sub (tendsto_terminalIndex_ratio hu r)
  have hcenter : (1 : ℝ) / 2 - u =
      (1 - 2 * u) / 2 := by
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonJ
  ring

theorem tendsto_johnsonM_ratio
    {a : ℝ} (ha : 0 ≤ a) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonM n (shellWeight a n) / (n : ℝ))
      atTop (nhds ((1 - 2 * a) / 2)) := by
  have hspin := tendsto_dimension_ratio.div_const 2
  have hmain := hspin.sub (tendsto_shellWeight_ratio ha)
  have hcenter : (1 : ℝ) / 2 - a =
      (1 - 2 * a) / 2 := by
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonM
  ring

theorem tendsto_johnsonSigma_ratio
    {a b g : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hb : 0 ≤ b) (hg : 0 ≤ g) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonSigma n (shellWeight a n)
          (supportDegree b n) (complementDegree g n) /
            (n : ℝ))
      atTop (nhds ((1 - 2 * b - 2 * g) / 2)) := by
  have hmain :=
    (tendsto_johnsonJ1_ratio ha hb).add
      (tendsto_johnsonJ2_ratio ha ha' hg)
  have hcenter :
      (a / 2 - b) + ((1 - a) / 2 - g) =
        (1 - 2 * b - 2 * g) / 2 := by
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonSigma
  ring

theorem tendsto_johnsonDelta_ratio
    {a b g : ℝ}
    (ha : 0 ≤ a) (ha' : a ≤ 1)
    (hb : 0 ≤ b) (hg : 0 ≤ g) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonDelta n (shellWeight a n)
          (supportDegree b n) (complementDegree g n) /
            (n : ℝ))
      atTop (nhds (MetricCodes.Johnson.centeredEta a b g / 2)) := by
  have hmain :=
    (tendsto_johnsonJ2_ratio ha ha' hg).sub
      (tendsto_johnsonJ1_ratio ha hb)
  have hcenter :
      ((1 - a) / 2 - g) - (a / 2 - b) =
        MetricCodes.Johnson.centeredEta a b g / 2 := by
    unfold MetricCodes.Johnson.centeredEta
    ring
  rw [hcenter] at hmain
  refine hmain.congr' (Eventually.of_forall fun n => ?_)
  unfold MetricCodes.johnsonDelta
  ring

private def normalizedMu (j₁ j₂ j m e : ℝ) : ℝ :=
  (m / 2) *
    (j₂ * (j₂ + e) - j₁ * (j₁ + e)) /
      (j * (j + e))

theorem johnsonMu_div_eq_normalized
    (n w p q j : ℕ) (hn : 0 < n)
    (hj : MetricCodes.johnsonJ n j ≠ 0)
    (hj' : MetricCodes.johnsonJ n j + 1 ≠ 0) :
    MetricCodes.johnsonMu n w p q j / (n : ℝ) =
      normalizedMu
        (MetricCodes.johnsonJ1 w p / (n : ℝ))
        (MetricCodes.johnsonJ2 n w q / (n : ℝ))
        (MetricCodes.johnsonJ n j / (n : ℝ))
        (MetricCodes.johnsonM n w / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  unfold MetricCodes.johnsonMu normalizedMu
  field_simp [hnreal.ne', hj, hj']

private def muLimit (a b g u : ℝ) : ℝ :=
  (1 - 2 * a) *
      (1 - 2 * b - 2 * g) *
      MetricCodes.Johnson.centeredEta a b g /
    (4 * (1 - 2 * u) ^ 2)

theorem normalizedMu_zero
    (a b g u : ℝ)
    (hz : (1 - 2 * u) ≠ 0) :
    normalizedMu
        (a / 2 - b)
        ((1 - a) / 2 - g)
        ((1 - 2 * u) / 2)
        ((1 - 2 * a) / 2)
        0 =
      muLimit a b g u := by
  unfold normalizedMu muLimit MetricCodes.Johnson.centeredEta at *
  field_simp [hz]; ring

private theorem tendsto_pointwise_div
    {f g : ℕ → ℝ} {a b : ℝ}
    (hf : Tendsto f atTop (nhds a))
    (hg : Tendsto g atTop (nhds b))
    (hb : b ≠ 0) :
    Tendsto (fun n : ℕ => f n / g n)
      atTop (nhds (a / b)) :=
  (hf.div hg hb).congr'
    (Eventually.of_forall fun _ => rfl)

theorem tendsto_johnsonMu_div
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonMu n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n) / (n : ℝ))
      atTop (nhds (muLimit a b g u)) := by
  have haone : a ≤ 1 := by linarith [h.weight_lt_half]
  have hj₁ := tendsto_johnsonJ1_ratio
    h.weight_pos.le h.support_nonneg
  have hj₂ := tendsto_johnsonJ2_ratio
    h.weight_pos.le haone h.complement_nonneg
  have hj := tendsto_johnsonJ_ratio h.degree_pos r
  have hm := tendsto_johnsonM_ratio h.weight_pos.le
  have he := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have hnum :=
    (hm.div_const 2).mul
      ((hj₂.mul (hj₂.add he)).sub
        (hj₁.mul (hj₁.add he)))
  have hden := hj.mul (hj.add he)
  have hdenne :
      ((1 - 2 * u) / 2) *
          ((1 - 2 * u) / 2 + 0) ≠ 0 := by
    have hz := h.centeredDegree_pos
    positivity
  have hnormalized :
      Tendsto
        (fun n : ℕ =>
          normalizedMu
            (MetricCodes.johnsonJ1 (shellWeight a n)
              (supportDegree b n) / (n : ℝ))
            (MetricCodes.johnsonJ2 n (shellWeight a n)
              (complementDegree g n) / (n : ℝ))
            (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ))
            (MetricCodes.johnsonM n (shellWeight a n) / (n : ℝ))
            ((1 : ℝ) / (n : ℝ)))
        atTop
        (nhds
          (normalizedMu
            (a / 2 - b)
            ((1 - a) / 2 - g)
            ((1 - 2 * u) / 2)
            ((1 - 2 * a) / 2)
            0)) := by
    simpa only [normalizedMu, one_div, add_zero] using tendsto_pointwise_div hnum hden hdenne
  rw [normalizedMu_zero a b g u h.centeredDegree_pos.ne']
    at hnormalized
  have hjpositive :
      ∀ᶠ n : ℕ in atTop,
        0 < MetricCodes.johnsonJ n (terminalIndex u r n) := by
    have hlimit : 0 < (1 - 2 * u) / 2 := by
      exact div_pos h.centeredDegree_pos (by norm_num)
    have hevent := hj.eventually (Ioi_mem_nhds hlimit)
    filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)]
      with n hjn hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hproduct :
        0 <
          (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ)) *
            (n : ℝ) := mul_pos hjn hnreal
    have hidentity :
        (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ)) *
            (n : ℝ) =
          MetricCodes.johnsonJ n (terminalIndex u r n) := by
      field_simp [hnreal.ne']
    rwa [hidentity] at hproduct
  refine hnormalized.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ), hjpositive]
    with n hn hjn
  exact
    (johnsonMu_div_eq_normalized n
      (shellWeight a n) (supportDegree b n)
      (complementDegree g n) (terminalIndex u r n) hn
      hjn.ne' (by positivity)).symm

private def normalizedDiagonal
    (j₁ j₂ j m e x y : ℝ) : ℝ :=
  (normalizedMu j₁ j₂ j m e - m ^ 2) / (x * y)

theorem johnsonDiagonal_eq_normalized
    (n w p q j : ℕ)
    (hn : 0 < n) (hw : 0 < w) (hwn : w < n)
    (hj : 0 < MetricCodes.johnsonJ n j) :
    MetricCodes.johnsonDiagonal n w p q j =
      normalizedDiagonal
        (MetricCodes.johnsonJ1 w p / (n : ℝ))
        (MetricCodes.johnsonJ2 n w q / (n : ℝ))
        (MetricCodes.johnsonJ n j / (n : ℝ))
        (MetricCodes.johnsonM n w / (n : ℝ))
        ((1 : ℝ) / (n : ℝ))
        ((w : ℝ) / (n : ℝ))
        (((n - w : ℕ) : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hwreal : (0 : ℝ) < (w : ℝ) := by exact_mod_cast hw
  have hc : (0 : ℝ) < ((n - w : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - w by omega)
  unfold normalizedDiagonal
  rw [← johnsonMu_div_eq_normalized n w p q j hn
    hj.ne' (by positivity)]
  unfold MetricCodes.johnsonDiagonal
  field_simp [hnreal.ne', hwreal.ne', hc.ne']

private def diagonalLimit (a b g u : ℝ) : ℝ :=
  (1 - 2 * a) *
      ((1 - 2 * b - 2 * g) *
        MetricCodes.Johnson.centeredEta a b g -
        (1 - 2 * a) *
          (1 - 2 * u) ^ 2) /
    ((1 - 2 * u) ^ 2 *
      (1 - (1 - 2 * a) ^ 2))

theorem tendsto_johnsonDiagonal
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (diagonalLimit a b g u)) := by
  have haone : a ≤ 1 := by linarith [h.weight_lt_half]
  have hmu := tendsto_johnsonMu_div h r
  have hm := tendsto_johnsonM_ratio h.weight_pos.le
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hc := tendsto_complementWeight_ratio
    h.weight_pos.le haone
  have hdenne : a * (1 - a) ≠ 0 :=
    (mul_pos h.weight_pos h.weight_complement_pos).ne'
  have hquot := tendsto_pointwise_div
    (hmu.sub (hm.pow 2)) (hw.mul hc) hdenne
  have hlimit :
      (muLimit a b g u -
          ((1 - 2 * a) / 2) ^ 2) /
        (a * (1 - a)) =
      diagonalLimit a b g u := by
    have hcenter :
        1 - (1 - 2 * a) ^ 2 =
          4 * a * (1 - a) := by
      ring
    unfold muLimit diagonalLimit
    exact MetricCodes.Johnson.Asymptotics.centered_diagonal_limit_algebra
      h.centeredDegree_pos.ne'
      h.one_sub_centeredWeight_sq_pos.ne' hcenter
  rw [hlimit] at hquot
  have hjpositive :
      ∀ᶠ n : ℕ in atTop,
        0 < MetricCodes.johnsonJ n (terminalIndex u r n) := by
    have hj := tendsto_johnsonJ_ratio h.degree_pos r
    have hlimit' : 0 < (1 - 2 * u) / 2 := by
      exact div_pos h.centeredDegree_pos (by norm_num)
    filter_upwards [hj.eventually (Ioi_mem_nhds hlimit'),
      eventually_gt_atTop (0 : ℕ)] with n hjn hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hp := mul_pos hjn hnreal
    have heq :
        (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ)) *
            (n : ℝ) =
          MetricCodes.johnsonJ n (terminalIndex u r n) := by
      field_simp [hnreal.ne']
    rwa [heq] at hp
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_admissibleDegrees h, hjpositive]
    with n hn hadmissible hjn
  have hnormalized := johnsonDiagonal_eq_normalized n
    (shellWeight a n) (supportDegree b n)
    (complementDegree g n) (terminalIndex u r n)
    hn hadmissible.weight_pos hadmissible.weight_lt hjn
  have hmuidentity := johnsonMu_div_eq_normalized n
    (shellWeight a n) (supportDegree b n)
    (complementDegree g n) (terminalIndex u r n)
    hn hjn.ne' (by positivity)
  unfold normalizedDiagonal at hnormalized
  rw [← hmuidentity] at hnormalized
  exact hnormalized.symm

private def normalizedNu (j m eta sigma e : ℝ) : ℝ :=
  Real.sqrt
      ((j ^ 2 - m ^ 2) *
        (j ^ 2 - eta ^ 2) *
        ((sigma + e) ^ 2 - j ^ 2)) /
    (2 * j * Real.sqrt ((2 * j - e) * (2 * j + e)))

theorem normalizedNu_scale
    (N J M eta sigma : ℝ)
    (hN : 0 < N) (hstep : 0 < 2 * J - 1) :
    (Real.sqrt
        ((J ^ 2 - M ^ 2) *
          (J ^ 2 - eta ^ 2) *
          ((sigma + 1) ^ 2 - J ^ 2)) /
      (2 * J * Real.sqrt ((2 * J - 1) * (2 * J + 1)))) / N =
      normalizedNu
        (J / N) (M / N) (eta / N) (sigma / N) (1 / N) := by
  have hrad :
      (J ^ 2 - M ^ 2) *
          (J ^ 2 - eta ^ 2) *
          ((sigma + 1) ^ 2 - J ^ 2) =
        (N ^ 3) ^ 2 *
          (((J / N) ^ 2 - (M / N) ^ 2) *
            ((J / N) ^ 2 - (eta / N) ^ 2) *
            (((sigma / N + 1 / N) ^ 2 - (J / N) ^ 2))) := by
    field_simp [hN.ne']
  have hdenrad :
      (2 * J - 1) * (2 * J + 1) =
        N ^ 2 *
          ((2 * (J / N) - 1 / N) *
            (2 * (J / N) + 1 / N)) := by
    field_simp [hN.ne']
  have hJ : 0 < J := by linarith
  have hleft : 0 < 2 * (J / N) - 1 / N := by
    have heq :
        2 * (J / N) - 1 / N = (2 * J - 1) / N := by
      field_simp [hN.ne']
    rw [heq]
    exact div_pos hstep hN
  have hright : 0 < 2 * (J / N) + 1 / N := by
    have heq :
        2 * (J / N) + 1 / N = (2 * J + 1) / N := by
      field_simp [hN.ne']
    rw [heq]
    exact div_pos (by linarith) hN
  have hroot :
      Real.sqrt
        ((2 * (J / N) - 1 / N) *
          (2 * (J / N) + 1 / N)) ≠ 0 :=
    (Real.sqrt_pos.mpr (mul_pos hleft hright)).ne'
  unfold normalizedNu
  rw [hrad, hdenrad,
    Real.sqrt_mul (sq_nonneg (N ^ 3)),
    Real.sqrt_sq (by positivity : 0 ≤ N ^ 3),
    Real.sqrt_mul (sq_nonneg N), Real.sqrt_sq hN.le]
  field_simp [hN.ne', hJ.ne', hroot]

theorem johnsonNu_div_eq_normalized
    (n w p q j : ℕ) (hn : 0 < n)
    (hstep : 0 < 2 * MetricCodes.johnsonJ n j - 1) :
    MetricCodes.johnsonNu n w p q j / (n : ℝ) =
      normalizedNu
        (MetricCodes.johnsonJ n j / (n : ℝ))
        (MetricCodes.johnsonM n w / (n : ℝ))
        (MetricCodes.johnsonDelta n w p q / (n : ℝ))
        (MetricCodes.johnsonSigma n w p q / (n : ℝ))
        ((1 : ℝ) / (n : ℝ)) := by
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simpa only [johnsonNu, one_div] using
    normalizedNu_scale (n : ℝ) (MetricCodes.johnsonJ n j) (MetricCodes.johnsonM n w)
      (MetricCodes.johnsonDelta n w p q)
      (MetricCodes.johnsonSigma n w p q) hnreal hstep

private def nuLimit (a b g u : ℝ) : ℝ :=
  Real.sqrt
      (((1 - 2 * u) ^ 2 -
          (1 - 2 * a) ^ 2) *
        ((1 - 2 * u) ^ 2 -
          MetricCodes.Johnson.centeredEta a b g ^ 2) *
        ((1 - 2 * b - 2 * g) ^ 2 -
          (1 - 2 * u) ^ 2)) /
    (8 * (1 - 2 * u) ^ 2)

theorem normalizedNu_zero
    (a b g u : ℝ)
    (hz : 0 < (1 - 2 * u)) :
    normalizedNu
        ((1 - 2 * u) / 2)
        ((1 - 2 * a) / 2)
        (MetricCodes.Johnson.centeredEta a b g / 2)
        ((1 - 2 * b - 2 * g) / 2)
        0 =
      nuLimit a b g u := by
  have hrad :
      (((1 - 2 * u) / 2) ^ 2 -
          ((1 - 2 * a) / 2) ^ 2) *
        (((1 - 2 * u) / 2) ^ 2 -
          (MetricCodes.Johnson.centeredEta a b g / 2) ^ 2) *
        (((1 - 2 * b - 2 * g) / 2) ^ 2 -
          ((1 - 2 * u) / 2) ^ 2) =
      ((1 / 8 : ℝ) ^ 2) *
        (((1 - 2 * u) ^ 2 -
            (1 - 2 * a) ^ 2) *
          ((1 - 2 * u) ^ 2 -
            MetricCodes.Johnson.centeredEta a b g ^ 2) *
          ((1 - 2 * b - 2 * g) ^ 2 -
            (1 - 2 * u) ^ 2)) := by
    ring
  have hdenrad :
      (2 * ((1 - 2 * u) / 2)) *
          (2 * ((1 - 2 * u) / 2)) =
        (1 - 2 * u) ^ 2 := by
    ring
  unfold normalizedNu
  simp only [add_zero, sub_zero]
  rw [hrad, hdenrad,
    Real.sqrt_mul (sq_nonneg (1 / 8 : ℝ)),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1 / 8),
    Real.sqrt_sq hz.le]
  unfold nuLimit
  field_simp [hz.ne']

theorem tendsto_johnsonNu_div
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonNu n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n) / (n : ℝ))
      atTop (nhds (nuLimit a b g u)) := by
  have haone : a ≤ 1 := by linarith [h.weight_lt_half]
  have hj := tendsto_johnsonJ_ratio h.degree_pos r
  have hm := tendsto_johnsonM_ratio h.weight_pos.le
  have heta := tendsto_johnsonDelta_ratio
    h.weight_pos.le haone h.support_nonneg h.complement_nonneg
  have hsigma := tendsto_johnsonSigma_ratio
    h.weight_pos.le haone h.support_nonneg h.complement_nonneg
  have he := tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ))
      atTop (nhds 2) := tendsto_const_nhds
  have hrad :=
    (((hj.pow 2).sub (hm.pow 2)).mul
      ((hj.pow 2).sub (heta.pow 2))).mul
        (((hsigma.add he).pow 2).sub (hj.pow 2))
  have hdenrad :=
    (((htwo.mul hj).sub he).mul
      ((htwo.mul hj).add he)).sqrt
  have hden := (htwo.mul hj).mul hdenrad
  have hz := h.centeredDegree_pos
  have hdenne :
      2 * ((1 - 2 * u) / 2) *
        Real.sqrt
          ((2 * ((1 - 2 * u) / 2) - 0) *
            (2 * ((1 - 2 * u) / 2) + 0)) ≠ 0 := by
    have hhalf : 0 < (1 - 2 * u) / 2 :=
      div_pos hz (by norm_num)
    have hrad :
        0 <
          (2 * ((1 - 2 * u) / 2) - 0) *
            (2 * ((1 - 2 * u) / 2) + 0) := by
      apply mul_pos <;> linarith
    exact
      (mul_pos (mul_pos (by norm_num) hhalf)
        (Real.sqrt_pos.mpr hrad)).ne'
  have hnormalized :
      Tendsto
        (fun n : ℕ =>
          normalizedNu
            (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ))
            (MetricCodes.johnsonM n (shellWeight a n) / (n : ℝ))
            (MetricCodes.johnsonDelta n (shellWeight a n)
              (supportDegree b n) (complementDegree g n) /
                (n : ℝ))
            (MetricCodes.johnsonSigma n (shellWeight a n)
              (supportDegree b n) (complementDegree g n) /
                (n : ℝ))
            ((1 : ℝ) / (n : ℝ)))
        atTop
        (nhds
          (normalizedNu
            ((1 - 2 * u) / 2)
            ((1 - 2 * a) / 2)
            (MetricCodes.Johnson.centeredEta a b g / 2)
            ((1 - 2 * b - 2 * g) / 2)
            0)) := by
    simpa only [normalizedNu, one_div, add_zero,
      sub_zero] using tendsto_pointwise_div hrad.sqrt hden hdenne
  rw [normalizedNu_zero a b g u h.centeredDegree_pos]
    at hnormalized
  have hstep :
      ∀ᶠ n : ℕ in atTop,
        0 < 2 * MetricCodes.johnsonJ n (terminalIndex u r n) - 1 := by
    have hscaled := (htwo.mul hj).sub he
    have hlimit :
        0 < 2 * ((1 - 2 * u) / 2) - 0 := by
      linarith [h.centeredDegree_pos]
    filter_upwards [hscaled.eventually (Ioi_mem_nhds hlimit),
      eventually_gt_atTop (0 : ℕ)] with n hscaled' hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hproduct := mul_pos hscaled' hnreal
    have hidentity :
        (2 *
            (MetricCodes.johnsonJ n (terminalIndex u r n) / (n : ℝ)) -
          (1 : ℝ) / (n : ℝ)) * (n : ℝ) =
        2 * MetricCodes.johnsonJ n (terminalIndex u r n) - 1 := by
      field_simp [hnreal.ne']
    rwa [hidentity] at hproduct
  refine hnormalized.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ), hstep]
    with n hn hstep'
  exact
    (johnsonNu_div_eq_normalized n
      (shellWeight a n) (supportDegree b n)
      (complementDegree g n) (terminalIndex u r n)
      hn hstep').symm

private def edgeLimit (a b g u : ℝ) : ℝ :=
  Real.sqrt
      (((1 - 2 * u) ^ 2 -
          (1 - 2 * a) ^ 2) *
        ((1 - 2 * u) ^ 2 -
          MetricCodes.Johnson.centeredEta a b g ^ 2) *
        ((1 - 2 * b - 2 * g) ^ 2 -
          (1 - 2 * u) ^ 2)) /
    (2 * (1 - 2 * u) ^ 2 *
      (1 - (1 - 2 * a) ^ 2))

private theorem centered_edge_limit_algebra
    {a m z R : ℝ}
    (hz : z ≠ 0) (ha : a ≠ 0) (hc : 1 - a ≠ 0)
    (hcenter : 1 - m ^ 2 = 4 * a * (1 - a)) :
    (Real.sqrt R / (8 * z ^ 2)) /
        (a * (1 - a)) =
      Real.sqrt R / (2 * z ^ 2 * (1 - m ^ 2)) := by
  rw [hcenter]
  field_simp [hz, ha, hc]; ring

theorem tendsto_johnsonEdge
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (edgeLimit a b g u)) := by
  have haone : a ≤ 1 := by linarith [h.weight_lt_half]
  have hnu := tendsto_johnsonNu_div h r
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hc := tendsto_complementWeight_ratio
    h.weight_pos.le haone
  have hdenne : a * (1 - a) ≠ 0 :=
    (mul_pos h.weight_pos h.weight_complement_pos).ne'
  have hquot := tendsto_pointwise_div hnu (hw.mul hc) hdenne
  have hcenter :
      1 - (1 - 2 * a) ^ 2 =
        4 * a * (1 - a) := by
    ring
  have hlimit :
      nuLimit a b g u / (a * (1 - a)) =
        edgeLimit a b g u := by
    unfold nuLimit edgeLimit
    exact centered_edge_limit_algebra
      h.centeredDegree_pos.ne' h.weight_pos.ne'
      h.weight_complement_pos.ne' hcenter
  rw [hlimit] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    eventually_admissibleDegrees h] with n hn hadmissible
  have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hwreal : (0 : ℝ) < (shellWeight a n : ℝ) := by
    exact_mod_cast hadmissible.weight_pos
  have hcreal :
      (0 : ℝ) < ((n - shellWeight a n : ℕ) : ℝ) := by
    exact_mod_cast
      (Nat.sub_pos_of_lt hadmissible.weight_lt)
  unfold MetricCodes.johnsonEdge
  field_simp [hnreal.ne', hwreal.ne', hcreal.ne']

theorem zeroFibreParameters
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    MetricCodes.Johnson.AsymptoticParameters d a 0 0 u := by
  refine ⟨h.distance_pos, h.distance_lt_half,
    h.weight_gt_distance, h.weight_lt_half,
    le_rfl, ?_, le_rfl, ?_, ?_, h.degree_lt_weight, ?_, ?_⟩
  · linarith [h.weight_pos]
  · linarith [h.weight_complement_pos]
  · simpa only [add_zero] using h.degree_pos
  · simpa only [sub_zero, add_zero] using h.degree_lt_weight
  · nlinarith [h.degree_lt_weight, h.weight_lt_half]

private def hattedDiagonalLimit (a b g u : ℝ) : ℝ :=
  ((1 - 2 * b - 2 * g) *
      MetricCodes.Johnson.centeredEta a b g -
      (1 - 2 * a) *
        (1 - 2 * u) ^ 2) ^ 2 /
    ((1 - 2 * u) ^ 2 *
      (1 - (1 - 2 * a) ^ 2) *
      (1 - (1 - 2 * u) ^ 2))

private def hattedEdgeLimit (a b g u : ℝ) : ℝ :=
  (((1 - 2 * u) ^ 2 -
      MetricCodes.Johnson.centeredEta a b g ^ 2) *
    ((1 - 2 * b - 2 * g) ^ 2 -
      (1 - 2 * u) ^ 2)) /
    (2 * (1 - 2 * u) ^ 2 *
      (1 - (1 - 2 * a) ^ 2) *
      Real.sqrt (1 - (1 - 2 * u) ^ 2))

theorem spectralLimit_eq_hatted
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    MetricCodes.Johnson.spectralLimit a b g u =
      hattedDiagonalLimit a b g u + 2 * hattedEdgeLimit a b g u := by
  unfold MetricCodes.Johnson.spectralLimit hattedDiagonalLimit hattedEdgeLimit
  dsimp
  have hz := h.centeredDegree_pos.ne'
  have hm := h.one_sub_centeredWeight_sq_pos.ne'
  have hu := h.one_sub_centeredDegree_sq_pos.ne'
  have hs := (Real.sqrt_pos.mpr h.one_sub_centeredDegree_sq_pos).ne'
  field_simp [hz, hm, hu, hs]

theorem hattedEdgeLimit_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    0 < hattedEdgeLimit a b g u := by
  unfold hattedEdgeLimit
  have hz := h.centeredDegree_pos
  have hm := h.one_sub_centeredWeight_sq_pos
  have hu := h.one_sub_centeredDegree_sq_pos
  have he := h.degree_sq_sub_eta_sq_pos
  have hs := h.sigma_sq_sub_degree_sq_pos
  positivity

theorem diagonalLimit_zero_eq
    {d a b g u : ℝ}
    (_h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    diagonalLimit a 0 0 u =
      (1 - 2 * a) ^ 2 *
        (1 - (1 - 2 * u) ^ 2) /
        ((1 - 2 * u) ^ 2 *
          (1 - (1 - 2 * a) ^ 2)) := by
  unfold diagonalLimit
    MetricCodes.Johnson.centeredEta
  have heta : 1 - 2 * a + 2 * (0 : ℝ) - 2 * 0 =
      (1 - 2 * a) := by
    ring
  rw [heta]
  norm_num
  ring

theorem diagonalLimit_zero_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    0 < diagonalLimit a 0 0 u := by
  have hz := h.centeredDegree_pos
  have hm := h.centeredWeight_pos
  have hden := h.one_sub_centeredWeight_sq_pos
  have hu := h.one_sub_centeredDegree_sq_pos
  rw [diagonalLimit_zero_eq h]
  exact div_pos (mul_pos (sq_pos_of_pos hm) hu)
    (mul_pos (sq_pos_of_pos hz) hden)

theorem diagonalLimit_sq_div_zero
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    diagonalLimit a b g u ^ 2 / diagonalLimit a 0 0 u =
      hattedDiagonalLimit a b g u := by
  have hz := h.centeredDegree_pos.ne'
  have hm := h.centeredWeight_pos.ne'
  have hd := h.one_sub_centeredWeight_sq_pos.ne'
  have hu := h.one_sub_centeredDegree_sq_pos.ne'
  rw [diagonalLimit_zero_eq h]
  unfold diagonalLimit hattedDiagonalLimit
  field_simp [hz, hm, hd, hu]

theorem edgeLimit_zero_eq
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    edgeLimit a 0 0 u =
      ((1 - 2 * u) ^ 2 -
        (1 - 2 * a) ^ 2) *
        Real.sqrt (1 - (1 - 2 * u) ^ 2) /
        (2 * (1 - 2 * u) ^ 2 *
          (1 - (1 - 2 * a) ^ 2)) := by
  have hzero := zeroFibreParameters h
  have hfactor := hzero.degree_sq_sub_eta_sq_pos
  have hfactor' : 0 < (1 - 2 * u) ^ 2 -
      (1 - 2 * a) ^ 2 := by
    simpa only [sub_pos, centeredEta, mul_zero, add_zero, sub_zero] using hfactor
  unfold edgeLimit
  have heta : MetricCodes.Johnson.centeredEta a 0 0 =
      (1 - 2 * a) := by
    simp only [centeredEta, mul_zero, add_zero, sub_zero]
  have hsigma : (1 - 2 * 0 - 2 * 0 : ℝ) = 1 := by
    norm_num
  rw [heta, hsigma]
  have hrad :
      Real.sqrt
          (((1 - 2 * u) ^ 2 -
              (1 - 2 * a) ^ 2) *
            ((1 - 2 * u) ^ 2 -
              (1 - 2 * a) ^ 2) *
            ((1 : ℝ) ^ 2 - (1 - 2 * u) ^ 2)) =
        ((1 - 2 * u) ^ 2 -
          (1 - 2 * a) ^ 2) *
          Real.sqrt (1 - (1 - 2 * u) ^ 2) := by
    rw [one_pow]
    rw [← pow_two]
    rw [Real.sqrt_mul (sq_nonneg _)]
    rw [Real.sqrt_sq hfactor'.le]
  rw [hrad]

theorem edgeLimit_zero_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    0 < edgeLimit a 0 0 u := by
  rw [edgeLimit_zero_eq h]
  have hzero := zeroFibreParameters h
  have hfactor := hzero.degree_sq_sub_eta_sq_pos
  have hfactor' : 0 < (1 - 2 * u) ^ 2 -
      (1 - 2 * a) ^ 2 := by
    simpa only [sub_pos, centeredEta, mul_zero, add_zero, sub_zero] using hfactor
  have hz := h.centeredDegree_pos
  have hm := h.one_sub_centeredWeight_sq_pos
  have hu := h.one_sub_centeredDegree_sq_pos
  positivity

theorem edgeLimit_sq_div_zero
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    edgeLimit a b g u ^ 2 / edgeLimit a 0 0 u =
      hattedEdgeLimit a b g u := by
  rw [edgeLimit_zero_eq h]
  have hzero := zeroFibreParameters h
  have hfactor := hzero.degree_sq_sub_eta_sq_pos
  have hfactor' : 0 < (1 - 2 * u) ^ 2 -
      (1 - 2 * a) ^ 2 := by
    simpa only [sub_pos, centeredEta, mul_zero, add_zero, sub_zero] using hfactor
  have hrad : 0 ≤
      ((1 - 2 * u) ^ 2 -
          (1 - 2 * a) ^ 2) *
        ((1 - 2 * u) ^ 2 -
          MetricCodes.Johnson.centeredEta a b g ^ 2) *
        ((1 - 2 * b - 2 * g) ^ 2 -
          (1 - 2 * u) ^ 2) := by
    exact (mul_pos (mul_pos hfactor'
      h.degree_sq_sub_eta_sq_pos)
      h.sigma_sq_sub_degree_sq_pos).le
  have hsquare := Real.sq_sqrt hrad
  have hz := h.centeredDegree_pos.ne'
  have hm := h.one_sub_centeredWeight_sq_pos.ne'
  have hu := h.one_sub_centeredDegree_sq_pos
  have hs := (Real.sqrt_pos.mpr hu).ne'
  have hf := hfactor'.ne'
  unfold edgeLimit hattedEdgeLimit
  field_simp [hz, hm, hs, hf]
  nlinarith [hsquare]

theorem tendsto_johnsonHattedDiagonal
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (hattedDiagonalLimit a b g u)) := by
  have hzero := zeroFibreParameters h
  have hnum := (tendsto_johnsonDiagonal h r).pow 2
  have hden := tendsto_johnsonDiagonal hzero r
  have hden' :
      Tendsto
        (fun n : ℕ =>
          MetricCodes.johnsonZonalDiagonal n (shellWeight a n)
            (terminalIndex u r n))
        atTop (nhds (diagonalLimit a 0 0 u)) := by
    simpa only [johnsonZonalDiagonal, supportDegree, Hamming.longitudinalDegree, zero_mul,
      Nat.floor_zero, complementDegree] using hden
  have hquot := hnum.div hden' (diagonalLimit_zero_pos h).ne'
  rw [diagonalLimit_sq_div_zero h] at hquot
  refine hquot.congr' ?_
  filter_upwards [eventually_terminal_block_fit h r] with n hn
  have hpositive : 0 < terminalIndex u r n := by
    unfold terminalIndex
    omega
  simp only [Pi.div_apply, johnsonHattedDiagonal, hpositive.ne', ↓reduceIte]

theorem tendsto_johnsonHattedEdge
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (r : ℕ) :
    Tendsto
      (fun n : ℕ =>
        MetricCodes.johnsonHattedEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u r n))
      atTop (nhds (hattedEdgeLimit a b g u)) := by
  have hzero := zeroFibreParameters h
  have hnum := (tendsto_johnsonEdge h r).pow 2
  have hden := tendsto_johnsonEdge hzero r
  have hden' :
      Tendsto
        (fun n : ℕ =>
          MetricCodes.johnsonZonalEdge n (shellWeight a n)
            (terminalIndex u r n))
        atTop (nhds (edgeLimit a 0 0 u)) := by
    simpa only [johnsonZonalEdge, supportDegree, Hamming.longitudinalDegree, zero_mul,
      Nat.floor_zero, complementDegree] using hden
  have hquot := hnum.div hden' (edgeLimit_zero_pos h).ne'
  rw [edgeLimit_sq_div_zero h] at hquot
  exact hquot.congr' (Eventually.of_forall fun n => by
    rfl)

theorem tridiagonal_quadratic_sum
    (d : ℕ) (b c v : ℕ → ℝ) :
    (∑ i ∈ Finset.range (d + 1),
      ∑ j ∈ Finset.range (d + 1),
        (if i = j then b i
          else if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i) =
      (∑ i ∈ Finset.range (d + 1), b i * v i ^ 2) +
        2 * ∑ i ∈ Finset.range d, c i * v i * v (i + 1) := by
  have hpoint (i j : ℕ) :
      (if i = j then b i
        else if i + 1 = j then c i
        else if j + 1 = i then c j else 0) * v j * v i =
      (if i = j then b i * v i ^ 2 else 0) +
        (if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i := by
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte, Nat.add_eq_left, one_ne_zero, zero_mul, add_zero]
      ring
    · simp only [hij, ↓reduceIte, ite_mul, zero_mul, zero_add]
  calc
    (∑ i ∈ Finset.range (d + 1),
      ∑ j ∈ Finset.range (d + 1),
        (if i = j then b i
          else if i + 1 = j then c i
          else if j + 1 = i then c j else 0) * v j * v i) =
      ∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          ((if i = j then b i * v i ^ 2 else 0) +
            (if i + 1 = j then c i
              else if j + 1 = i then c j else 0) * v j * v i) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply Finset.sum_congr rfl
        intro j hj
        exact hpoint i j
    _ =
      (∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          if i = j then b i * v i ^ 2 else 0) +
      (∑ i ∈ Finset.range (d + 1),
        ∑ j ∈ Finset.range (d + 1),
          (if i + 1 = j then c i
            else if j + 1 = i then c j else 0) * v j * v i) := by
        simp_rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [MetricCodes.Hamming.tridiagonal_quadratic_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Finset.sum_ite_eq, Finset.mem_range, Finset.mem_range.mp hi, ↓reduceIte]

theorem terminal_indicator_diagonal_sum
    (d m : ℕ) (hm : m ≤ d) (b : ℕ → ℝ) :
    (∑ i ∈ Finset.range (d + 1),
      b i * MetricCodes.Hamming.terminalIndicator d m i ^ 2) =
      ∑ r ∈ Finset.range (m + 1), b (d - m + r) := by
  have hsplit : d + 1 = (d - m) + (m + 1) := by omega
  rw [hsplit, Finset.sum_range_add]
  have hfirst :
      (∑ i ∈ Finset.range (d - m),
        b i * MetricCodes.Hamming.terminalIndicator d m i ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' : i < d - m := Finset.mem_range.mp hi
    simp only [Hamming.terminalIndicator, Nat.not_le.mpr hi', ↓reduceIte, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero]
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro r hr
  have hmem : d - m ≤ d - m + r := by omega
  simp only [Hamming.terminalIndicator, hmem, ↓reduceIte, one_pow, mul_one]

/-- The terminal vector used in the Johnson-code argument. -/
def terminalVector (p q L m : ℕ) : MetricCodes.Johnson.Space p q L :=
  MetricCodes.Hamming.terminalVector (p + q) L m

theorem terminalVector_ne_zero (p q L m : ℕ) :
    terminalVector p q L m ≠ 0 := by
  exact MetricCodes.Hamming.terminalVector_ne_zero (p + q) L m

theorem terminalVector_norm_sq
    (p q L m : ℕ) (hm : m ≤ L - (p + q)) :
    ‖terminalVector p q L m‖ ^ 2 = (m : ℝ) + 1 := by
  exact MetricCodes.Hamming.terminalVector_norm_sq (p + q) L m hm

theorem terminalVector_inner
    (n w p q L m : ℕ)
    (hfirst : p + q ≤ L) (hm : m ≤ L - (p + q)) :
    @inner ℝ (MetricCodes.Johnson.Space p q L) _
      (MetricCodes.Johnson.operator n w p q L (terminalVector p q L m))
      (terminalVector p q L m) =
      (∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n w p q (L - m + r) := by
  rw [PiLp.inner_apply]
  simp only [Real.inner_apply]
  change
    (∑ i : Fin (L - (p + q) + 1),
      (∑ j : Fin (L - (p + q) + 1),
        (if i = j then
          MetricCodes.johnsonHattedDiagonal n w p q (p + q + i.val)
        else if i.val + 1 = j.val then
          MetricCodes.johnsonHattedEdge n w p q (p + q + i.val)
        else if j.val + 1 = i.val then
          MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
        else 0) *
          MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val) *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i.val) = _
  simp_rw [Finset.sum_mul]
  let f : ℕ → ℝ := fun i =>
    ∑ j : Fin (L - (p + q) + 1),
      (if i = j.val then
        MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
      else if i + 1 = j.val then
        MetricCodes.johnsonHattedEdge n w p q (p + q + i)
      else if j.val + 1 = i then
        MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
      else 0) *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i
  have hreplace :
      (∑ i : Fin (L - (p + q) + 1),
        ∑ j : Fin (L - (p + q) + 1),
          (if i = j then
            MetricCodes.johnsonHattedDiagonal n w p q (p + q + i.val)
          else if i.val + 1 = j.val then
            MetricCodes.johnsonHattedEdge n w p q (p + q + i.val)
          else if j.val + 1 = i.val then
            MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
          else 0) *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i.val) =
        ∑ i : Fin (L - (p + q) + 1), f i.val := by
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [f]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hij : i = j
    · subst j
      simp only [↓reduceIte]
    · have hval : i.val ≠ j.val := fun heq => hij (Fin.ext heq)
      simp only [hij, ↓reduceIte, ite_mul, zero_mul, hval]
  rw [hreplace, Fin.sum_univ_eq_sum_range f]
  dsimp only [f]
  have hfin (i : ℕ) :
      (∑ j : Fin (L - (p + q) + 1),
        (if i = j.val then
          MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
        else if i + 1 = j.val then
          MetricCodes.johnsonHattedEdge n w p q (p + q + i)
        else if j.val + 1 = i then
          MetricCodes.johnsonHattedEdge n w p q (p + q + j.val)
        else 0) *
          MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j.val *
          MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i) =
        ∑ j ∈ Finset.range (L - (p + q) + 1),
          (if i = j then
            MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
          else if i + 1 = j then
            MetricCodes.johnsonHattedEdge n w p q (p + q + i)
          else if j + 1 = i then
            MetricCodes.johnsonHattedEdge n w p q (p + q + j)
          else 0) *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j *
            MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i := by
    let g : ℕ → ℝ := fun j =>
      (if i = j then
        MetricCodes.johnsonHattedDiagonal n w p q (p + q + i)
      else if i + 1 = j then
        MetricCodes.johnsonHattedEdge n w p q (p + q + i)
      else if j + 1 = i then
        MetricCodes.johnsonHattedEdge n w p q (p + q + j)
      else 0) *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m j *
        MetricCodes.Hamming.terminalIndicator (L - (p + q)) m i
    change (∑ j : Fin (L - (p + q) + 1), g j.val) =
      ∑ j ∈ Finset.range (L - (p + q) + 1), g j
    exact Fin.sum_univ_eq_sum_range g (L - (p + q) + 1)
  simp_rw [hfin]
  rw [tridiagonal_quadratic_sum]
  rw [terminal_indicator_diagonal_sum (L - (p + q)) m hm]
  rw [MetricCodes.Hamming.terminal_indicator_edge_sum (L - (p + q)) m hm]
  congr 1
  · apply Finset.sum_congr rfl
    intro r hr
    congr 1
    omega
  · congr 1
    apply Finset.sum_congr rfl
    intro r hr
    congr 1
    omega

theorem terminalVector_rayleigh
    (n w p q L m : ℕ)
    (hfirst : p + q ≤ L) (hm : m ≤ L - (p + q)) :
    MetricCodes.Johnson.rayleigh n w p q L (terminalVector p q L m) =
      ((∑ r ∈ Finset.range (m + 1),
          MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
        2 * ∑ r ∈ Finset.range m,
          MetricCodes.johnsonHattedEdge n w p q (L - m + r)) /
        ((m : ℝ) + 1) := by
  rw [MetricCodes.Johnson.rayleigh_eq_inner,
    terminalVector_inner n w p q L m hfirst hm,
    terminalVector_norm_sq p q L m hm]

theorem terminal_rayleigh_le_top
    (n w p q L m : ℕ)
    (hfirst : p + q ≤ L) (hm : m ≤ L - (p + q)) :
    ((∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n w p q (L - m + r)) +
      2 * ∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n w p q (L - m + r)) /
      ((m : ℝ) + 1) ≤ MetricCodes.Johnson.topEigenvalue n w p q L := by
  rw [← terminalVector_rayleigh n w p q L m hfirst hm]
  exact MetricCodes.Johnson.rayleigh_le_top n w p q L
    (terminalVector p q L m) (terminalVector_ne_zero p q L m)

private def terminalRayleigh (a b g u : ℝ) (m n : ℕ) : ℝ :=
  ((∑ r ∈ Finset.range (m + 1),
      MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalIndex u (m - r) n)) +
    2 * ∑ r ∈ Finset.range m,
      MetricCodes.johnsonHattedEdge n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalIndex u (m - r) n)) /
    ((m : ℝ) + 1)

theorem tendsto_terminalRayleigh
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (m : ℕ) :
    Tendsto (terminalRayleigh a b g u m) atTop
      (nhds
        ((((m : ℝ) + 1) * hattedDiagonalLimit a b g u +
          2 * (m : ℝ) * hattedEdgeLimit a b g u) /
            ((m : ℝ) + 1))) := by
  have hdiagonal :
      Tendsto
        (fun n : ℕ =>
          ∑ r ∈ Finset.range (m + 1),
            MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalIndex u (m - r) n))
        atTop
        (nhds (∑ _r ∈ Finset.range (m + 1),
          hattedDiagonalLimit a b g u)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_johnsonHattedDiagonal h (m - r)
  have hedge :
      Tendsto
        (fun n : ℕ =>
          ∑ r ∈ Finset.range m,
            MetricCodes.johnsonHattedEdge n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalIndex u (m - r) n))
        atTop
        (nhds (∑ _r ∈ Finset.range m,
          hattedEdgeLimit a b g u)) := by
    apply tendsto_finsetSum
    intro r hr
    exact tendsto_johnsonHattedEdge h (m - r)
  have htwo : Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (nhds 2) :=
    tendsto_const_nhds
  have hquot := (hdiagonal.add (htwo.mul hedge)).div_const
    ((m : ℝ) + 1)
  change Tendsto (fun n : ℕ => terminalRayleigh a b g u m n) atTop _
  simpa only [terminalRayleigh, mul_comm, mul_assoc, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, Nat.cast_add, Nat.cast_one, mul_left_comm] using hquot

theorem terminalRayleigh_le_top
    (a b g u : ℝ) (m n : ℕ)
    (hfit : supportDegree b n + complementDegree g n + m ≤
      terminalDegree u n) :
    terminalRayleigh a b g u m n ≤
      MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalDegree u n) := by
  have hfirst :
      supportDegree b n + complementDegree g n ≤
        terminalDegree u n := by omega
  have hm :
      m ≤ terminalDegree u n -
        (supportDegree b n + complementDegree g n) := by omega
  have hdiag :
      (∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u (m - r) n)) =
      ∑ r ∈ Finset.range (m + 1),
        MetricCodes.johnsonHattedDiagonal n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m + 1 := Finset.mem_range.mp hr
    congr 1
    unfold terminalIndex
    omega
  have hedge :
      (∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalIndex u (m - r) n)) =
      ∑ r ∈ Finset.range m,
        MetricCodes.johnsonHattedEdge n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n - m + r) := by
    apply Finset.sum_congr rfl
    intro r hr
    have hr' : r < m := Finset.mem_range.mp hr
    congr 1
    unfold terminalIndex
    omega
  unfold terminalRayleigh
  rw [hdiag, hedge]
  exact terminal_rayleigh_le_top n (shellWeight a n)
    (supportDegree b n) (complementDegree g n)
    (terminalDegree u n) m hfirst hm

theorem eventually_topEigenvalue_gt
    {d a b g u s : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u)
    (hs : s < MetricCodes.Johnson.spectralLimit a b g u) :
    ∀ᶠ n : ℕ in atTop,
      s < MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
        (supportDegree b n) (complementDegree g n)
        (terminalDegree u n) := by
  let E : ℝ := hattedEdgeLimit a b g u
  let S : ℝ := MetricCodes.Johnson.spectralLimit a b g u
  let ε : ℝ := (S - s) / 2
  have hE : 0 < E := hattedEdgeLimit_pos h
  have hε : 0 < ε := by
    dsimp [ε, S]
    linarith
  obtain ⟨m, hm⟩ := exists_nat_gt (2 * E / ε)
  have hprod : 2 * E < (m : ℝ) * ε :=
    (div_lt_iff₀ hε).mp hm
  have hden : 0 < (m : ℝ) + 1 := by positivity
  have hrem : 2 * E / ((m : ℝ) + 1) < ε := by
    apply (div_lt_iff₀ hden).mpr
    nlinarith
  have hidentity :
      (((m : ℝ) + 1) * hattedDiagonalLimit a b g u +
        2 * (m : ℝ) * hattedEdgeLimit a b g u) /
          ((m : ℝ) + 1) =
        S - 2 * E / ((m : ℝ) + 1) := by
    dsimp [S, E]
    rw [spectralLimit_eq_hatted h]
    field_simp [hden.ne']; ring
  have hbelow :
      s <
        (((m : ℝ) + 1) * hattedDiagonalLimit a b g u +
          2 * (m : ℝ) * hattedEdgeLimit a b g u) /
            ((m : ℝ) + 1) := by
    rw [hidentity]
    dsimp [ε] at hrem
    linarith
  have hquot := (tendsto_terminalRayleigh h m).eventually
    (lt_mem_nhds hbelow)
  filter_upwards [hquot, eventually_terminal_block_fit h m]
    with n hn hfit
  exact hn.trans_le
    (terminalRayleigh_le_top a b g u m n (by omega))

/-- The spectral gap used in the Johnson-code argument. -/
def spectralGap (d a b g u : ℝ) : ℝ :=
  (MetricCodes.Johnson.spectralLimit a b g u -
    MetricCodes.Johnson.asymptoticThreshold d a) / 4

theorem spectralGap_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u) :
    0 < spectralGap d a b g u := by
  have hgap :
      MetricCodes.Johnson.asymptoticThreshold d a <
        MetricCodes.Johnson.spectralLimit a b g u := h.2
  unfold spectralGap
  linarith

theorem eventually_spectralGap_lt
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      spectralGap d a b g u <
        MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n) -
        MetricCodes.Johnson.threshold n (shellWeight a n)
          (Nat.ceil (d * (n : ℝ))) := by
  have hpositive := spectralGap_pos h
  let A := MetricCodes.Johnson.asymptoticThreshold d a
  let S := MetricCodes.Johnson.spectralLimit a b g u
  have hupper : S - spectralGap d a b g u < S := by
    linarith
  have hlower : A < A + spectralGap d a b g u := by
    linarith
  have heigen := eventually_topEigenvalue_gt h.1 hupper
  have hthreshold :=
    (MetricCodes.Johnson.Asymptotics.tendsto_threshold_ceil h.1).eventually
      (gt_mem_nhds hlower)
  filter_upwards [heigen, hthreshold] with n hn ht
  dsimp [A, S] at hn ht
  unfold spectralGap at hpositive hn ht ⊢
  linarith

theorem asymptoticThreshold_lt_one
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    MetricCodes.Johnson.asymptoticThreshold d a < 1 := by
  unfold MetricCodes.Johnson.asymptoticThreshold
  have hden : 0 < 2 * a * (1 - a) := by
    exact mul_pos (mul_pos (by norm_num) h.weight_pos)
      h.weight_complement_pos
  have hquot := div_pos h.distance_pos hden
  linarith

theorem eventually_one_sub_threshold_lt
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      1 - MetricCodes.Johnson.threshold n (shellWeight a n)
        (Nat.ceil (d * (n : ℝ))) <
        2 - MetricCodes.Johnson.asymptoticThreshold d a := by
  have hlimit :
      MetricCodes.Johnson.asymptoticThreshold d a - 1 <
        MetricCodes.Johnson.asymptoticThreshold d a := by linarith
  have hthreshold :=
    (MetricCodes.Johnson.Asymptotics.tendsto_threshold_ceil h).eventually
      (Ioi_mem_nhds hlimit)
  filter_upwards [hthreshold] with n hn
  linarith

end

end SpectralAsymptotics

section


open Filter Topology
open scoped Topology

namespace Rate

open MetricCodes.Johnson.Asymptotics
open MetricCodes.Johnson.SpectralAsymptotics

private def certificateConstant (d a b g u : ℝ) : ℝ :=
  (2 - MetricCodes.Johnson.asymptoticThreshold d a) /
    spectralGap d a b g u

theorem certificateConstant_pos
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u) :
    0 < certificateConstant d a b g u := by
  unfold certificateConstant
  apply div_pos
  · linarith [asymptoticThreshold_lt_one h.1]
  · exact spectralGap_pos h

theorem exists_zero_fibre_feasible
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    ∃ a u : ℝ, MetricCodes.Johnson.Feasible d a 0 0 u := by
  let a : ℝ := d / 2 + 1 / 4
  let u : ℝ := d / 4 + 1 / 4
  have ha : a < (1 : ℝ) / 2 := by
    dsimp [a]
    linarith
  have hu : 0 < u := by
    dsimp [u]
    linarith
  have hua : u < a := by
    dsimp [a, u]
    linarith
  have ha0 : 0 < a := lt_trans hu hua
  have hac : 0 < 1 - a := by linarith
  have hparams : MetricCodes.Johnson.AsymptoticParameters d a 0 0 u := by
    refine ⟨hd, hdhalf, ?_, ha, by norm_num, ?_, by norm_num,
      ?_, ?_, hua, ?_, ?_⟩
    · dsimp [a]
      linarith
    · linarith
    · linarith
    · simpa only [add_zero] using hu
    · simpa only [sub_zero, add_zero] using hua
    · norm_num
      linarith
  let A := a * (1 - a)
  let U := u * (1 - u)
  have hA : 0 < A := by
    dsimp [A]
    exact mul_pos ha0 hac
  have hs : 0 ≤ Real.sqrt U := Real.sqrt_nonneg _
  have hsden : 0 < 1 + 2 * Real.sqrt U := by positivity
  have hdiff : 2 * (A - U) < d := by
    dsimp [A, U, a, u]
    nlinarith [sq_nonneg d]
  have hinner : (A - U) / (1 + 2 * Real.sqrt U) < d / 2 := by
    apply (div_lt_iff₀ hsden).mpr
    nlinarith [mul_nonneg hd.le hs]
  have hquot :
      (A - U) / (A * (1 + 2 * Real.sqrt U)) < d / (2 * A) := by
    calc
      (A - U) / (A * (1 + 2 * Real.sqrt U)) =
          ((A - U) / (1 + 2 * Real.sqrt U)) / A := by
            field_simp [hA.ne', hsden.ne']
      _ < (d / 2) / A :=
        (div_lt_div_iff_of_pos_right hA).mpr hinner
      _ = d / (2 * A) := by ring_nf
  have hboundary :=
    MetricCodes.Johnson.spectralLimit_zero_fibre_boundary hu hua ha
  refine ⟨a, u, hparams, ?_⟩
  change MetricCodes.Johnson.asymptoticThreshold d a <
    MetricCodes.Johnson.spectralLimit a 0 0 u
  unfold MetricCodes.Johnson.asymptoticThreshold
  dsimp [A, U] at hquot
  have hquot' :
      (a * (1 - a) - u * (1 - u)) /
          (a * (1 - a) * (1 + 2 * Real.sqrt (u * (1 - u)))) <
        d / (2 * a * (1 - a)) := by
    convert hquot using 1; ring
  linarith

theorem rateSet_nonempty_of_interior
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    (MetricCodes.Johnson.rateSet d).Nonempty := by
  obtain ⟨a, u, hfeasible⟩ := exists_zero_fibre_feasible hd hdhalf
  exact ⟨MetricCodes.Johnson.shellRate a 0 0 u,
    a, 0, 0, u, hfeasible, rfl⟩

theorem eventually_strict_weight_half
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.AsymptoticParameters d a b g u) :
    ∀ᶠ n : ℕ in atTop, 2 * shellWeight a n < n := by
  have hw := tendsto_shellWeight_ratio h.weight_pos.le
  have hww := tendsto_add_degree_ratio hw hw
  have hstrict := eventually_degree_lt_of_ratio hww
    tendsto_dimension_ratio (by linarith [h.weight_lt_half])
  filter_upwards [hstrict] with n hn
  omega

theorem binaryRate_le_shellRate_of_projectionGrams
    {d a b g u : ℝ}
    (h : MetricCodes.Johnson.Feasible d a b g u)
    (hdata : ∀ᶠ n : ℕ in atTop,
      Nonempty
        (MetricCodes.Johnson.ProjectionGram n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n))) :
    MetricCodes.Hamming.binaryRate d ≤ MetricCodes.Johnson.shellRate a b g u := by
  apply MetricCodes.Johnson.Asymptotics.binaryRate_le_shellRate_of_eventually
    h.1 (certificateConstant_pos h)
  filter_upwards [hdata, eventually_admissibleDegrees h.1,
    eventually_spectralGap_lt h,
    eventually_one_sub_threshold_lt h.1,
    eventually_gt_atTop (0 : ℕ)]
    with n hnonempty hadmissible hgap hnumerator hn
  obtain ⟨data⟩ := hnonempty
  let t := MetricCodes.Johnson.threshold n (shellWeight a n)
    (Nat.ceil (d * (n : ℝ)))
  let lam := MetricCodes.Johnson.topEigenvalue n (shellWeight a n)
    (supportDegree b n) (complementDegree g n)
    (terminalDegree u n)
  let G := spectralGap d a b g u
  let B := 2 - MetricCodes.Johnson.asymptoticThreshold d a
  have hd := MetricCodes.Hamming.ceil_distance_pos h.1.distance_pos hn
  have hG : 0 < G := spectralGap_pos h
  have hB : 0 < B := by
    dsimp [B]
    linarith [asymptoticThreshold_lt_one h.1]
  have hden : 0 < lam - t := by
    dsimp [lam, t, G] at hgap ⊢
    linarith [spectralGap_pos h]
  have ht : 0 < 1 - t := by
    dsimp [t]
    exact sub_pos.mpr
      (MetricCodes.Johnson.threshold_lt_one hadmissible.weight_pos
        hadmissible.weight_lt hd)
  have hratio : (1 - t) / (lam - t) ≤ B / G := by
    apply (div_le_div_iff₀ hden hG).mpr
    calc
      (1 - t) * G ≤ B * G := by
        apply mul_le_mul_of_nonneg_right _ hG.le
        exact le_of_lt hnumerator
      _ ≤ B * (lam - t) := by
        apply mul_le_mul_of_nonneg_left _ hB.le
        exact le_of_lt hgap
  have hfactor : 0 ≤ bassalygoFactor a n := by
    unfold bassalygoFactor
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)
  have hwindow : 0 ≤ windowFibreQuotient a b g u n := by
    unfold windowFibreQuotient
    exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hfinite :=
    MetricCodes.Johnson.finite_binaryCodeNumber_bound_of_projection_gram
      hadmissible hd data (sub_pos.mp hden)
  rw [MetricCodes.Johnson.binaryCodeNumber_eq_hamming] at hfinite
  change
    (MetricCodes.Hamming.codeNumber n
      (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
      bassalygoFactor a n *
        (((1 - t) / (lam - t)) * windowFibreQuotient a b g u n)
    at hfinite
  calc
    (MetricCodes.Hamming.codeNumber n
      (Nat.ceil (d * (n : ℝ))) : ℝ) ≤
        bassalygoFactor a n *
          (((1 - t) / (lam - t)) * windowFibreQuotient a b g u n) :=
      hfinite
    _ ≤ bassalygoFactor a n *
          ((B / G) * windowFibreQuotient a b g u n) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hratio hwindow) hfactor
    _ = certificateConstant d a b g u *
          bassalygoWindowFibreQuotient a b g u n := by
      unfold certificateConstant bassalygoWindowFibreQuotient
      dsimp [B, G]
      ring

theorem binaryRate_le_variationalRate_of_projectionGrams
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2)
    (hdata : ∀ a b g u : ℝ,
      MetricCodes.Johnson.Feasible d a b g u →
        ∀ᶠ n : ℕ in atTop,
          Nonempty
            (MetricCodes.Johnson.ProjectionGram n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalDegree u n))) :
    MetricCodes.Hamming.binaryRate d ≤ MetricCodes.Johnson.variationalRate d := by
  apply le_csInf (rateSet_nonempty_of_interior hd hdhalf)
  rintro r ⟨a, b, g, u, hfeasible, rfl⟩
  exact binaryRate_le_shellRate_of_projectionGrams
    hfeasible (hdata a b g u hfeasible)

theorem binaryRate_le_combinedVariationalRate_of_projectionGrams
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2)
    (hdata : ∀ a b g u : ℝ,
      MetricCodes.Johnson.Feasible d a b g u →
        ∀ᶠ n : ℕ in atTop,
          Nonempty
            (MetricCodes.Johnson.ProjectionGram n (shellWeight a n)
              (supportDegree b n) (complementDegree g n)
              (terminalDegree u n))) :
    MetricCodes.Hamming.binaryRate d ≤
      MetricCodes.Johnson.combinedVariationalRate d := by
  unfold MetricCodes.Johnson.combinedVariationalRate
  exact le_min
    (MetricCodes.Hamming.binaryRate_le_variationalRate hd hdhalf)
    (binaryRate_le_variationalRate_of_projectionGrams hd hdhalf hdata)

end Rate

end

section


open Filter Topology
open scoped Topology
open MetricCodes.Johnson.Asymptotics

theorem eventually_projectionGram
    {d a b g u : ℝ}
    (h : Feasible d a b g u) :
    ∀ᶠ n : ℕ in atTop,
      Nonempty
        (ProjectionGram n (shellWeight a n)
          (supportDegree b n) (complementDegree g n)
          (terminalDegree u n)) := by
  filter_upwards [eventually_admissibleDegrees h.1,
    MetricCodes.Johnson.Rate.eventually_strict_weight_half h.1,
    MetricCodes.Johnson.SpectralAsymptotics.eventually_terminal_block_fit h.1 0]
    with n hadmissible hstrict hfit
  refine ⟨johnsonProjectionGram hadmissible hstrict ?_⟩
  omega

theorem binaryRate_le_combinedVariationalRate
    {d : ℝ} (hd : 0 < d) (hdhalf : d < (1 : ℝ) / 2) :
    MetricCodes.Hamming.binaryRate d ≤ combinedVariationalRate d := by
  apply
    MetricCodes.Johnson.Rate.binaryRate_le_combinedVariationalRate_of_projectionGrams
      hd hdhalf
  intro a b g u hfeasible
  exact eventually_projectionGram hfeasible





end

end Johnson

section

open scoped BigOperators

namespace Numerics

private def kissingA : ℝ := 0.08570143806746

private def kissingB : ℝ := 0.00370282933568

/-- The log series lower used in the metric-code argument. -/
def logSeriesLower (x : ℝ) (m : ℕ) : ℝ :=
  2 * ∑ i ∈ Finset.range m, x ^ (2 * i + 1) / (2 * (i : ℝ) + 1)

/-- The log series upper used in the metric-code argument. -/
def logSeriesUpper (x : ℝ) (m : ℕ) : ℝ :=
  logSeriesLower x m + 2 * (x ^ (2 * m + 1) / (1 - x ^ 2))

theorem log_ratio_lower {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) (m : ℕ) :
    logSeriesLower x m ≤ Real.log ((1 + x) / (1 - x)) := by
  have h := Real.sum_range_le_log_div hx hx' m
  unfold logSeriesLower
  nlinarith

theorem log_ratio_upper {x : ℝ} (hx : 0 ≤ x) (hx' : x < 1) (m : ℕ) :
    Real.log ((1 + x) / (1 - x)) ≤ logSeriesUpper x m := by
  have h := Real.log_div_le_sum_range_add hx hx' m
  unfold logSeriesUpper logSeriesLower
  nlinarith

theorem log_interval_of_series {r x lo hi : ℝ} (m : ℕ)
    (hx : 0 ≤ x) (hx' : x < 1)
    (hr : (1 + x) / (1 - x) = r)
    (hlo : lo < logSeriesLower x m)
    (hhi : logSeriesUpper x m < hi) :
    lo < Real.log r ∧ Real.log r < hi := by
  constructor
  · calc
      lo < logSeriesLower x m := hlo
      _ ≤ Real.log ((1 + x) / (1 - x)) := log_ratio_lower hx hx' m
      _ = Real.log r := by rw [hr]
  · calc
      Real.log r = Real.log ((1 + x) / (1 - x)) := by rw [hr]
      _ ≤ logSeriesUpper x m := log_ratio_upper hx hx' m
      _ < hi := hhi

theorem log_two_interval :
    (693147180559945309 : ℝ) / 10 ^ 18 < Real.log 2 ∧
      Real.log 2 < (693147180559945310 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series (x := (1 : ℝ) / 3) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_kissing_one_add_a_interval :
    (82226264808038924 : ℝ) / 10 ^ 18 < Real.log (1 + kissingA) ∧
      Real.log (1 + kissingA) < (82226264808038925 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (4285071903373 : ℝ) / 104285071903373) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_kissing_scaled_a_interval :
    (315703048970999865 : ℝ) / 10 ^ 18 < Real.log (16 * kissingA) ∧
      Real.log (16 * kissingA) < (315703048970999866 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (1160071903373 : ℝ) / 7410071903373) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingA]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_kissing_one_add_b_interval :
    (3695990739373266 : ℝ) / 10 ^ 18 < Real.log (1 + kissingB) ∧
      Real.log (1 + kissingB) < (3695990739373267 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (5785670837 : ℝ) / 3130785670837) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem log_kissing_inverse_scaled_b_interval :
    (53480621756332520 : ℝ) / 10 ^ 18 <
        Real.log (1 / (256 * kissingB)) ∧
      Real.log (1 / (256 * kissingB)) <
        (53480621756332521 : ℝ) / 10 ^ 18 := by
  refine log_interval_of_series
    (x := (158922394 : ℝ) / 5944593231) 20 ?_ ?_ ?_ ?_ ?_
  · norm_num
  · norm_num
  · norm_num [kissingB]
  · norm_num [logSeriesLower, Finset.sum_range_succ]
  · norm_num [logSeriesUpper, logSeriesLower, Finset.sum_range_succ]

theorem kissing_sqrt_upper :
    Real.sqrt (kissingA * (1 + kissingA)) <
      (30503471040898065 : ℝ) / 10 ^ 17 := by
  apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) <
    (30503471040898065 : ℝ) / 10 ^ 17)).2
  norm_num [kissingA]

theorem kissing_spectral_certificate :
    (1 : ℝ) / 2 < 2 * MetricCodes.Gamma kissingA kissingB := by
  have hrad : 0 < kissingA * (1 + kissingA) := by
    norm_num [kissingA]
  have hsqrt : 0 < Real.sqrt (kissingA * (1 + kissingA)) :=
    Real.sqrt_pos.2 hrad
  have hden : 0 <
      (1 + 2 * kissingA) * Real.sqrt (kissingA * (1 + kissingA)) :=
    mul_pos (by norm_num [kissingA]) hsqrt
  unfold MetricCodes.Gamma
  rw [← mul_div_assoc]
  apply (lt_div_iff₀ hden).2
  have hupper := kissing_sqrt_upper
  norm_num [kissingA, kissingB] at hupper ⊢
  nlinarith

theorem log_kissing_a :
    Real.log kissingA = Real.log (16 * kissingA) - 4 * Real.log 2 := by
  have hmul : Real.log (16 * kissingA) =
      Real.log (16 : ℝ) + Real.log kissingA :=
    Real.log_mul (by norm_num) (by norm_num [kissingA])
  have hpow : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 4 using 1 <;> norm_num
  rw [hpow] at hmul
  linarith

theorem log_kissing_b :
    Real.log kissingB =
      -8 * Real.log 2 - Real.log (1 / (256 * kissingB)) := by
  have hmul : Real.log (256 * kissingB) =
      Real.log (256 : ℝ) + Real.log kissingB :=
    Real.log_mul (by norm_num) (by norm_num [kissingB])
  have hpow : Real.log (256 : ℝ) = 8 * Real.log 2 := by
    convert Real.log_pow (2 : ℝ) 8 using 1 <;> norm_num
  have hinv : Real.log (1 / (256 * kissingB)) =
      -Real.log (256 * kissingB) := by
    rw [one_div, Real.log_inv]
  rw [hpow] at hmul
  linarith

theorem kissing_entropy_certificate :
    MetricCodes.sphericalEntropy kissingA - MetricCodes.sphericalEntropy kissingB <
      (0.397305601680 : ℝ) := by
  have htwo := log_two_interval.1
  have h1a := log_kissing_one_add_a_interval.2
  have hsa := log_kissing_scaled_a_interval.1
  have h1b := log_kissing_one_add_b_interval.1
  have hib := log_kissing_inverse_scaled_b_interval.1
  have hmain :
      (1 + kissingA) * Real.log (1 + kissingA) -
          kissingA * (Real.log (16 * kissingA) - 4 * Real.log 2) -
          ((1 + kissingB) * Real.log (1 + kissingB) -
            kissingB *
              (-8 * Real.log 2 - Real.log (1 / (256 * kissingB)))) <
        (0.397305601680 : ℝ) * Real.log 2 := by
    norm_num [kissingA, kissingB] at htwo h1a hsa h1b hib ⊢
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    MetricCodes.sphericalEntropy kissingA - MetricCodes.sphericalEntropy kissingB =
        ((1 + kissingA) * Real.log (1 + kissingA) -
          kissingA * Real.log kissingA -
          ((1 + kissingB) * Real.log (1 + kissingB) -
            kissingB * Real.log kissingB)) / Real.log 2 := by
          unfold MetricCodes.sphericalEntropy Real.logb
          ring
    _ < (0.397305601680 : ℝ) := by
      apply (div_lt_iff₀ hlog).2
      rw [log_kissing_a, log_kissing_b]
      exact hmain

end Numerics

end

namespace Spherical

section

theorem sphericalEntropy_continuous : Continuous MetricCodes.sphericalEntropy := by
  have hplus :
      Continuous (fun u : ℝ => (1 + u) * Real.log (1 + u)) := by
    simpa only [Function.comp_def, Pi.add_apply] using
      (Real.continuous_mul_log.comp (continuous_const.add continuous_id : Continuous (fun u : ℝ
        => 1 + u)))
  have hnatural : Continuous
      (fun u : ℝ =>
        ((1 + u) * Real.log (1 + u) - u * Real.log u) /
          Real.log 2) :=
    (hplus.sub Real.continuous_mul_log).div_const (Real.log 2)
  convert hnatural using 1
  funext u
  unfold MetricCodes.sphericalEntropy Real.logb
  ring

theorem hasDerivAt_sphericalEntropy {u : ℝ} (hu : 0 < u) :
    HasDerivAt MetricCodes.sphericalEntropy
      (Real.logb 2 ((1 + u) / u)) u := by
  have hplus :=
    (Real.hasDerivAt_mul_log (by linarith : 1 + u ≠ 0)).comp u
      ((hasDerivAt_const u (1 : ℝ)).add (hasDerivAt_id u))
  have hself := Real.hasDerivAt_mul_log hu.ne'
  have hderiv := (hplus.sub hself).div_const (Real.log 2)
  have hfun : MetricCodes.sphericalEntropy =
      (fun x : ℝ =>
        ((1 + x) * Real.log (1 + x) - x * Real.log x) /
          Real.log 2) := by
    funext x
    unfold MetricCodes.sphericalEntropy Real.logb
    ring
  have hvalue :
      Real.logb 2 ((1 + u) / u) =
        (((Real.log (1 + u) + 1) * (0 + 1) -
          (Real.log u + 1)) / Real.log 2) := by
    unfold Real.logb
    rw [Real.log_div (by linarith : 1 + u ≠ 0) hu.ne']
    ring
  rw [hfun, hvalue]
  simpa only [Function.comp_apply, Pi.sub_apply] using hderiv

theorem sphericalEntropy_strictMono :
    StrictMonoOn MetricCodes.sphericalEntropy (Set.Ici (0 : ℝ)) := by
  apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    sphericalEntropy_continuous.continuousOn
  intro u hu
  have hu' : 0 < u := by
    simpa only [interior_Ici, Set.mem_Ioi] using hu
  rw [(hasDerivAt_sphericalEntropy hu').deriv]
  apply Real.logb_pos (by norm_num : (1 : ℝ) < 2)
  apply (lt_div_iff₀ hu').2
  linarith

theorem sphericalEntropy_sub_nonneg {a b : ℝ}
    (hb : 0 ≤ b) (hba : b ≤ a) :
    0 ≤ MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  have ha : 0 ≤ a := hb.trans hba
  exact sub_nonneg.mpr
    (sphericalEntropy_strictMono.monotoneOn hb ha hba)

/-- The feasible used in the spherical-code argument. -/
def Feasible (s a b : ℝ) : Prop :=
  0 < b ∧ b < a ∧ s < 2 * MetricCodes.Gamma a b

/-- The rate set used in the spherical-code argument. -/
def rateSet (s : ℝ) : Set ℝ :=
  {r | ∃ a b : ℝ, Feasible s a b ∧
    r = MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b}

/-- The variational rate used in the spherical-code argument. -/
def variationalRate (s : ℝ) : ℝ := sInf (rateSet s)

theorem rateSet_bddBelow (s : ℝ) : BddBelow (rateSet s) := by
  refine ⟨0, ?_⟩
  rintro r ⟨a, b, ⟨hb, hba, _⟩, rfl⟩
  exact sphericalEntropy_sub_nonneg hb.le hba.le

theorem variationalRate_le_of_feasible {s a b : ℝ}
    (h : Feasible s a b) :
    variationalRate s ≤
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b := by
  exact csInf_le (rateSet_bddBelow s) ⟨a, b, h, rfl⟩

end

section

open Filter Topology
open scoped Topology

theorem Gamma_zero {a : ℝ} (ha : 0 < a) :
    MetricCodes.Gamma a 0 =
      Real.sqrt (a * (1 + a)) / (1 + 2 * a) := by
  have hrad : 0 < a * (1 + a) := by positivity
  have hroot : Real.sqrt (a * (1 + a)) ≠ 0 :=
    (Real.sqrt_pos.2 hrad).ne'
  have hlin : 1 + 2 * a ≠ 0 := by positivity
  have hsquare := Real.sq_sqrt hrad.le
  rw [MetricCodes.Gamma_eq_sub]
  simp only [zero_mul, add_zero, sub_zero]
  field_simp [hroot, hlin]
  nlinarith

theorem classicalThreshold_spectral
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    2 * MetricCodes.Gamma (MetricCodes.classicalThreshold s) 0 = s := by
  have ha : 0 < MetricCodes.classicalThreshold s :=
    MetricCodes.classicalThreshold_pos hs hs'
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hroot : 0 < Real.sqrt (1 - s ^ 2) :=
    Real.sqrt_pos.2 hrad
  have hrootsq := Real.sq_sqrt hrad.le
  have hidentity :
      4 * MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s) =
        s ^ 2 * (1 + 2 * MetricCodes.classicalThreshold s) ^ 2 := by
    unfold MetricCodes.classicalThreshold
    field_simp [hroot.ne']
    nlinarith
  have hinner :
      0 < MetricCodes.classicalThreshold s *
        (1 + MetricCodes.classicalThreshold s) := by positivity
  have hinnersq := Real.sq_sqrt hinner.le
  have hlin : 0 < 1 + 2 * MetricCodes.classicalThreshold s := by positivity
  have htarget :
      2 * Real.sqrt
        (MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s)) =
        s * (1 + 2 * MetricCodes.classicalThreshold s) := by
    apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
    calc
      (2 * Real.sqrt
        (MetricCodes.classicalThreshold s *
          (1 + MetricCodes.classicalThreshold s))) ^ 2 =
          4 * MetricCodes.classicalThreshold s *
            (1 + MetricCodes.classicalThreshold s) := by
            rw [mul_pow, hinnersq]
            ring
      _ = s ^ 2 * (1 + 2 * MetricCodes.classicalThreshold s) ^ 2 :=
        hidentity
      _ = (s * (1 + 2 * MetricCodes.classicalThreshold s)) ^ 2 := by
        ring
  rw [Gamma_zero ha, ← mul_div_assoc]
  exact (div_eq_iff hlin.ne').2 htarget

/-- The spherical improvement path used in the spherical-code argument. -/
def sphericalImprovementPath (a b : ℝ) : ℝ :=
  a + (4 * a + 3) * b

theorem sphericalImprovementSlope_gt_one {a : ℝ} (ha : 0 < a) :
    1 < (4 * a + 3) := by
  linarith

private def sphericalSpectralMarginPolynomial (a c b : ℝ) : ℝ :=
  let T := a * (1 + a)
  let l := 1 + 2 * a
  let p := c * l - 1
  let q := c ^ 2 - 1
  l ^ 2 *
      (T * (2 * p - c * l) +
        b * (p ^ 2 + 2 * T * q - T * c ^ 2) +
        2 * b ^ 2 * p * q + b ^ 3 * q ^ 2) -
    T * (4 * c * l + 4 * c ^ 2 * b) *
      (T + c * l * b + c ^ 2 * b ^ 2)

theorem sphericalSpectralMarginPolynomial_factor (a c b : ℝ) :
    (((a + c * b) * (1 + (a + c * b)) - b * (1 + b)) *
        (1 + 2 * a)) ^ 2 -
      a * (1 + a) * (1 + 2 * (a + c * b)) ^ 2 *
        ((a + c * b) * (1 + (a + c * b))) =
      b * sphericalSpectralMarginPolynomial a c b := by
  unfold sphericalSpectralMarginPolynomial
  ring

theorem sphericalSpectralMarginPolynomial_continuous (a c : ℝ) :
    Continuous (sphericalSpectralMarginPolynomial a c) := by
  unfold sphericalSpectralMarginPolynomial
  fun_prop

theorem sphericalSpectralMarginPolynomial_improvement_zero
    (a : ℝ) :
    sphericalSpectralMarginPolynomial a
      (4 * a + 3) 0 =
      a * (1 + a) * (1 + 2 * a) := by
  unfold sphericalSpectralMarginPolynomial
  ring

theorem eventually_Gamma_improvement {a : ℝ} (ha : 0 < a) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.Gamma a 0 <
        MetricCodes.Gamma (sphericalImprovementPath a b) b := by
  have hzero :
      0 < sphericalSpectralMarginPolynomial a
        (4 * a + 3) 0 := by
    rw [sphericalSpectralMarginPolynomial_improvement_zero]
    positivity
  have hpoly :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        0 < sphericalSpectralMarginPolynomial a
          (4 * a + 3) b := by
    have hcontinuous :
        ContinuousAt
          (sphericalSpectralMarginPolynomial a
            (4 * a + 3)) 0 :=
      (sphericalSpectralMarginPolynomial_continuous
        a (4 * a + 3)).continuousAt
    exact nhdsWithin_le_nhds
      (hcontinuous.tendsto.eventually (lt_mem_nhds hzero))
  have hc : 1 < (4 * a + 3) :=
    sphericalImprovementSlope_gt_one ha
  filter_upwards [hpoly, self_mem_nhdsWithin]
    with b hbpoly (hb : 0 < b)
  have hbpath : b < sphericalImprovementPath a b := by
    unfold sphericalImprovementPath
    nlinarith [mul_pos (sub_pos.mpr hc) hb]
  have hpath : 0 < sphericalImprovementPath a b :=
    hb.trans hbpath
  have hbase : 0 < a * (1 + a) := by positivity
  have hrad :
      0 < sphericalImprovementPath a b *
        (1 + sphericalImprovementPath a b) := by positivity
  have hnum :
      0 < sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b) := by
    have hfactor :
        0 < (sphericalImprovementPath a b - b) *
          (1 + sphericalImprovementPath a b + b) := by positivity
    nlinarith
  have hmargin :
      0 <
        ((sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
          (1 + 2 * a)) ^ 2 -
        a * (1 + a) *
          (1 + 2 * sphericalImprovementPath a b) ^ 2 *
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)) := by
    have hfactor := sphericalSpectralMarginPolynomial_factor
      a (4 * a + 3) b
    change
      0 < (((a + (4 * a + 3) * b) *
          (1 + (a + (4 * a + 3) * b)) -
            b * (1 + b)) * (1 + 2 * a)) ^ 2 -
        a * (1 + a) *
          (1 + 2 * (a + (4 * a + 3) * b)) ^ 2 *
            ((a + (4 * a + 3) * b) *
              (1 + (a + (4 * a + 3) * b)))
    rw [hfactor]
    exact mul_pos hb hbpoly
  have hleftnonneg :
      0 ≤ Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b))) := by
    positivity
  have hrightpos :
      0 < (sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
        (1 + 2 * a) := by positivity
  have hsquare :
      (Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)))) ^ 2 =
        a * (1 + a) *
          (1 + 2 * sphericalImprovementPath a b) ^ 2 *
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b)) := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hbase.le,
      Real.sq_sqrt hrad.le]
    ring
  have hcross :
      Real.sqrt (a * (1 + a)) *
        ((1 + 2 * sphericalImprovementPath a b) *
          Real.sqrt
            (sphericalImprovementPath a b *
              (1 + sphericalImprovementPath a b))) <
        (sphericalImprovementPath a b *
          (1 + sphericalImprovementPath a b) - b * (1 + b)) *
            (1 + 2 * a) := by
    nlinarith
  rw [Gamma_zero ha, MetricCodes.Gamma_eq_sub]
  have hlin : 0 < 1 + 2 * a := by positivity
  have hden :
      0 < (1 + 2 * sphericalImprovementPath a b) *
        Real.sqrt
          (sphericalImprovementPath a b *
            (1 + sphericalImprovementPath a b)) := by positivity
  exact (div_lt_div_iff₀ hlin hden).2 hcross

theorem neg_mul_logb_le_sphericalEntropy {b : ℝ} (hb : 0 ≤ b) :
    b * (-Real.logb 2 b) ≤ MetricCodes.sphericalEntropy b := by
  have hlog : 0 ≤ Real.logb 2 (1 + b) :=
    Real.logb_nonneg (by norm_num) (by linarith)
  have hterm : 0 ≤ (1 + b) * Real.logb 2 (1 + b) := by
    exact mul_nonneg (by linarith) hlog
  unfold MetricCodes.sphericalEntropy
  nlinarith

theorem eventually_sphericalEntropy_improvement {a : ℝ} (ha : 0 < a) :
    ∀ᶠ b : ℝ in 𝓝[>] 0,
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
        MetricCodes.sphericalEntropy b < MetricCodes.sphericalEntropy a := by
  let f : ℝ → ℝ := fun b =>
    MetricCodes.sphericalEntropy (sphericalImprovementPath a b)
  have hinner : DifferentiableAt ℝ (sphericalImprovementPath a) 0 := by
    unfold sphericalImprovementPath
    fun_prop
  have houter :
      DifferentiableAt ℝ MetricCodes.sphericalEntropy
        (sphericalImprovementPath a 0) := by
    simpa only [sphericalImprovementPath, mul_zero, add_zero] using
      (hasDerivAt_sphericalEntropy ha).differentiableAt
  have hf : DifferentiableAt ℝ f 0 :=
    houter.comp 0 hinner
  let M : ℝ := deriv f 0 + 1
  have hM : deriv f 0 < M := by
    dsimp [M]
    linarith
  have hslope := hf.hasDerivAt.tendsto_slope_zero_right
  have hupper :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        b⁻¹ * (MetricCodes.sphericalEntropy
          (sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy a) < M := by
    have h := hslope.eventually (gt_mem_nhds hM)
    filter_upwards [h] with b hb
    simpa [f, sphericalImprovementPath, smul_eq_mul] using hb
  have hloglim :
      Tendsto (fun b : ℝ => -Real.logb 2 b) (𝓝[>] 0) atTop := by
    simpa only [tendsto_neg_atTop_iff, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))
  have hlog :
      ∀ᶠ b : ℝ in 𝓝[>] 0, M < -Real.logb 2 b :=
    hloglim.eventually (eventually_gt_atTop M)
  filter_upwards [hupper, hlog, self_mem_nhdsWithin]
    with b hbound hlogb (hb : 0 < b)
  have houter_bound :
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
        MetricCodes.sphericalEntropy a < b * M := by
    calc
      MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
          MetricCodes.sphericalEntropy a =
        b * (b⁻¹ *
          (MetricCodes.sphericalEntropy (sphericalImprovementPath a b) -
            MetricCodes.sphericalEntropy a)) := by
          field_simp [hb.ne']
      _ < b * M := mul_lt_mul_of_pos_left hbound hb
  have hsingular :
      b * M < b * (-Real.logb 2 b) :=
    mul_lt_mul_of_pos_left hlogb hb
  have hentropy := neg_mul_logb_le_sphericalEntropy hb.le
  linarith

theorem exists_strict_improving_spherical_feasible
    {s : ℝ} (hs : 0 < s) (hs' : s < 1) :
    ∃ a b : ℝ, Feasible s a b ∧
      MetricCodes.sphericalEntropy a - MetricCodes.sphericalEntropy b <
        MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
  let a₀ : ℝ := MetricCodes.classicalThreshold s
  have ha₀ : 0 < a₀ := MetricCodes.classicalThreshold_pos hs hs'
  have hgamma := eventually_Gamma_improvement ha₀
  have hentropy := eventually_sphericalEntropy_improvement ha₀
  have hc : 1 < (4 * a₀ + 3) :=
    sphericalImprovementSlope_gt_one ha₀
  have hall :
      ∀ᶠ b : ℝ in 𝓝[>] 0,
        Feasible s (sphericalImprovementPath a₀ b) b ∧
          MetricCodes.sphericalEntropy (sphericalImprovementPath a₀ b) -
            MetricCodes.sphericalEntropy b <
              MetricCodes.sphericalEntropy (MetricCodes.classicalThreshold s) := by
    filter_upwards [hgamma, hentropy, self_mem_nhdsWithin]
      with b hgamma' hentropy' (hb : 0 < b)
    have hbpath : b < sphericalImprovementPath a₀ b := by
      unfold sphericalImprovementPath
      nlinarith [mul_pos (sub_pos.mpr hc) hb]
    constructor
    · refine ⟨hb, hbpath, ?_⟩
      have hboundary : 2 * MetricCodes.Gamma a₀ 0 = s := by
        dsimp [a₀]
        exact classicalThreshold_spectral hs hs'
      nlinarith
    · simpa only using hentropy'
  obtain ⟨b, hb⟩ := hall.exists
  exact ⟨sphericalImprovementPath a₀ b, b, hb⟩

end

end Spherical

end MetricCodes

section

open Filter MeasureTheory Metric
open scoped ENNReal Pointwise

namespace SpherePacking



end SpherePacking

end

namespace MetricCodes

namespace Spherical

section


open Filter Topology
open scoped Topology

end

section

open Filter Topology
open scoped Topology

theorem classicalThreshold_continuousAt
    {s : ℝ} (hs : -1 < s) (hs' : s < 1) :
    ContinuousAt MetricCodes.classicalThreshold s := by
  have hrad : 0 < 1 - s ^ 2 := by nlinarith
  have hroot : Real.sqrt (1 - s ^ 2) ≠ 0 :=
    (Real.sqrt_pos.mpr hrad).ne'
  unfold MetricCodes.classicalThreshold
  fun_prop (disch := aesop)

theorem sphericalEntropy_eq_logb_add_mul_logb
    {a : ℝ} (ha : 0 < a) :
    MetricCodes.sphericalEntropy a =
      Real.logb 2 (1 + a) + a * Real.logb 2 ((1 + a) / a) := by
  unfold MetricCodes.sphericalEntropy
  rw [Real.logb_div (by positivity) ha.ne']
  ring

end

section

open scoped BigOperators

namespace HigherHierarchy

/-- The spectral atom used in the spherical-code argument. -/
def spectralAtom (u : ℝ) : ℝ :=
  Real.sqrt (u * (1 + u)) / (1 + 2 * u)

/-- The interlacing used in the spherical-code argument. -/
def Interlacing {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : Prop :=
  0 ≤ a (Fin.last r) ∧
    ∀ i : Fin r, a i.castSucc > b i ∧ b i > a i.succ

/-- The lagrange numerator used in the spherical-code argument. -/
def lagrangeNumerator {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) : ℝ :=
  ∏ m : Fin r, (((a ℓ) * (1 + (a ℓ))) - ((b m) * (1 + (b m))))

/-- The lagrange denominator used in the spherical-code argument. -/
def lagrangeDenominator {r : ℕ}
    (a : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) : ℝ :=
  ∏ m : Fin r,
    (((a ℓ) * (1 + (a ℓ))) - ((a (ℓ.succAbove m)) * (1 + (a (ℓ.succAbove m)))))

/-- The lagrange weight used in the spherical-code argument. -/
def lagrangeWeight {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) : ℝ :=
  lagrangeNumerator a b ℓ / lagrangeDenominator a ℓ

/-- The gamma used in the spherical-code argument. -/
def Gamma {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  ∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ * spectralAtom (a ℓ)

/-- The phi used in the spherical-code argument. -/
def Phi {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) : ℝ :=
  (∑ ℓ : Fin (r + 1), MetricCodes.sphericalEntropy (a ℓ)) -
    ∑ m : Fin r, MetricCodes.sphericalEntropy (b m)

theorem Interlacing.strictAnti_ambient {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : StrictAnti a := by
  apply Fin.strictAnti_iff_succ_lt.mpr
  intro i
  exact (h.2 i).2.trans (h.2 i).1

theorem Interlacing.ambient_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin (r + 1)) : 0 ≤ a i := by
  exact h.1.trans (h.strictAnti_ambient.antitone i.le_last)

theorem Interlacing.stabilizer_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) : 0 < b i :=
  (h.ambient_nonneg i.succ).trans_lt (h.2 i).2

theorem quadraticCoordinate_strictMonoOn :
    StrictMonoOn (fun u : ℝ => u * (1 + u)) (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 ≤ x at hx
  change 0 ≤ y at hy
  change x * (1 + x) < y * (1 + y)
  nlinarith [mul_pos (sub_pos.mpr hxy) (by linarith : 0 < 1 + x + y)]

theorem Interlacing.quadratic_injective {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    Function.Injective (fun i => ((a i) * (1 + (a i)))) := by
  intro i j hij
  apply h.strictAnti_ambient.injective
  exact quadraticCoordinate_strictMonoOn.injOn
    (h.ambient_nonneg i) (h.ambient_nonneg j) hij

theorem lagrangeDenominator_eq_prod_erase {r : ℕ}
    (a : Fin (r + 1) → ℝ) (ℓ : Fin (r + 1)) :
    lagrangeDenominator a ℓ =
      ∏ j ∈ Finset.univ.erase ℓ,
        (((a ℓ) * (1 + (a ℓ))) - ((a j) * (1 + (a j)))) := by
  unfold lagrangeDenominator
  classical
  refine Finset.prod_bij (fun j _ => ℓ.succAbove j)
    (fun j _ => ?_) (fun i _ j _ hij => ?_) (fun j hj => ?_)
    (fun _ _ => rfl)
  · simp only [Finset.mem_erase, ne_eq, Fin.succAbove_ne, not_false_eq_true, Finset.mem_univ,
      and_self]
  · exact Fin.succAbove_right_injective hij
  · obtain ⟨hj', _⟩ := Finset.mem_erase.mp hj
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hj'
    exact ⟨i, Finset.mem_univ i, hi⟩

theorem Interlacing.lagrangeDenominator_ne_zero {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) :
    lagrangeDenominator a ℓ ≠ 0 := by
  unfold lagrangeDenominator
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact sub_ne_zero.mpr
    (fun heq => Fin.ne_succAbove ℓ i (h.quadratic_injective heq))

theorem Interlacing.lagrangeFactor_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) (m : Fin r) :
    0 < (((a ℓ) * (1 + (a ℓ))) - ((b m) * (1 + (b m)))) /
      (((a ℓ) * (1 + (a ℓ))) -
        ((a (ℓ.succAbove m)) * (1 + (a (ℓ.succAbove m))))) := by
  by_cases hm : m.castSucc < ℓ
  · rw [Fin.succAbove_of_castSucc_lt ℓ m hm]
    have hmiddle : a ℓ < b m := by
      exact
        (h.strictAnti_ambient.antitone (Fin.castSucc_lt_iff_succ_le.mp hm)).trans_lt
          (h.2 m).2
    have hleft :
        ((a ℓ) * (1 + (a ℓ))) < ((b m) * (1 + (b m))) :=
      quadraticCoordinate_strictMonoOn (h.ambient_nonneg ℓ)
        (h.stabilizer_pos m).le hmiddle
    have hright :
        ((a ℓ) * (1 + (a ℓ))) <
          ((a m.castSucc) * (1 + (a m.castSucc))) :=
      quadraticCoordinate_strictMonoOn (h.ambient_nonneg ℓ)
        (h.ambient_nonneg m.castSucc) (h.strictAnti_ambient hm)
    exact div_pos_of_neg_of_neg (sub_neg.mpr hleft) (sub_neg.mpr hright)
  · have hm' : ℓ ≤ m.castSucc := le_of_not_gt hm
    rw [Fin.succAbove_of_le_castSucc ℓ m hm']
    have hmiddle : b m < a ℓ := by
      exact (h.2 m).1.trans_le (h.strictAnti_ambient.antitone hm')
    have hleft :
        ((b m) * (1 + (b m))) < ((a ℓ) * (1 + (a ℓ))) :=
      quadraticCoordinate_strictMonoOn (h.stabilizer_pos m).le
        (h.ambient_nonneg ℓ) hmiddle
    have hright :
        ((a m.succ) * (1 + (a m.succ))) < ((a ℓ) * (1 + (a ℓ))) :=
      quadraticCoordinate_strictMonoOn (h.ambient_nonneg m.succ)
        (h.ambient_nonneg ℓ)
        (h.strictAnti_ambient (Fin.le_castSucc_iff.mp hm'))
    exact div_pos (sub_pos.mpr hleft) (sub_pos.mpr hright)

theorem Interlacing.lagrangeWeight_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) :
    0 < lagrangeWeight a b ℓ := by
  unfold lagrangeWeight lagrangeNumerator lagrangeDenominator
  rw [← Finset.prod_div_distrib]
  exact Finset.prod_pos fun i _ => h.lagrangeFactor_pos ℓ i

theorem Interlacing.lagrangeWeight_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (ℓ : Fin (r + 1)) :
    0 ≤ lagrangeWeight a b ℓ := (h.lagrangeWeight_pos ℓ).le

private def stabilizerPolynomial {r : ℕ} (b : Fin r → ℝ) : Polynomial ℝ :=
  ∏ m : Fin r, (Polynomial.X - Polynomial.C (((b m) * (1 + (b m)))))

theorem stabilizerPolynomial_monic {r : ℕ} (b : Fin r → ℝ) :
    (stabilizerPolynomial b).Monic := by
  exact Polynomial.monic_prod_X_sub_C
    (fun m : Fin r => ((b m) * (1 + (b m)))) Finset.univ

theorem stabilizerPolynomial_natDegree {r : ℕ} (b : Fin r → ℝ) :
    (stabilizerPolynomial b).natDegree = r := by
  simp only [stabilizerPolynomial, Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_univ, Fintype.card_fin]

theorem stabilizerPolynomial_eval {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ)
    (ℓ : Fin (r + 1)) :
    (stabilizerPolynomial b).eval (((a ℓ) * (1 + (a ℓ)))) =
      lagrangeNumerator a b ℓ := by
  unfold stabilizerPolynomial lagrangeNumerator
  rw [Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

theorem Interlacing.sum_lagrangeWeight {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) :
    (∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ) = 1 := by
  classical
  let P : Polynomial ℝ := stabilizerPolynomial b
  have hmonic : P.Monic := stabilizerPolynomial_monic b
  have hdegree : P.natDegree = r := stabilizerPolynomial_natDegree b
  have hdegree' :
      P.degree < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [Polynomial.degree_eq_natDegree hmonic.ne_zero, hdegree]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add, Nat.cast_one]
    exact_mod_cast Nat.lt_succ_self r
  have hlagrange := Lagrange.coeff_eq_sum
    (s := (Finset.univ : Finset (Fin (r + 1))))
    (v := fun ℓ : Fin (r + 1) => ((a ℓ) * (1 + (a ℓ))))
    (P := P) h.quadratic_injective.injOn hdegree'
  have hcoeff : P.coeff r = 1 := by
    simpa only [hdegree] using hmonic.coeff_natDegree
  rw [Finset.card_univ, Fintype.card_fin, Nat.add_sub_cancel,
    hcoeff] at hlagrange
  symm
  calc
    1 = ∑ ℓ : Fin (r + 1),
        P.eval (((a ℓ) * (1 + (a ℓ)))) /
          ∏ j ∈ Finset.univ.erase ℓ,
            (((a ℓ) * (1 + (a ℓ))) - ((a j) * (1 + (a j)))) := by
          simpa only using hlagrange
    _ = ∑ ℓ : Fin (r + 1), lagrangeWeight a b ℓ := by
          apply Finset.sum_congr rfl
          intro ℓ _
          rw [lagrangeWeight, lagrangeDenominator_eq_prod_erase,
            ← stabilizerPolynomial_eval]

theorem spectralAtom_nonneg {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ spectralAtom u := by
  unfold spectralAtom
  positivity

end HigherHierarchy

end

end Spherical

end MetricCodes


namespace MetricCodes

namespace Spherical

namespace HigherHierarchy

section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal Interval

namespace Arcsine

theorem beta_half_half_eq_pi :
    beta (1 / 2 : ℝ) (1 / 2 : ℝ) = Real.pi := by
  rw [beta, Real.Gamma_one_half_eq]
  norm_num [Real.Gamma_one]
  simpa only [pow_two] using Real.sq_sqrt Real.pi_pos.le

end Arcsine

end

section

open MeasureTheory Real Set
open scoped Interval

namespace ArcsineIntegral

theorem integral_inv_add_mul_cos (a b : ℝ) (h : |b| < a) :
    (∫ θ in (0 : ℝ)..Real.pi, (a + b * Real.cos θ)⁻¹) =
      Real.pi / Real.sqrt (a ^ 2 - b ^ 2) := by
  have hab : -a < b ∧ b < a := abs_lt.mp h
  have hplus : 0 < a + b := by linarith [hab.1]
  have hminus : 0 < a - b := by linarith [hab.2]
  have hdisc : 0 < a ^ 2 - b ^ 2 := by
    nlinarith [mul_pos hplus hminus]
  let c : ℝ := Real.sqrt (a ^ 2 - b ^ 2)
  have hc : 0 < c := Real.sqrt_pos.2 hdisc
  have hden (θ : ℝ) : 0 < a + b * Real.cos θ := by
    have hbound : |b * Real.cos θ| ≤ |b| := by
      rw [abs_mul]
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (Real.abs_cos_le_one θ) (abs_nonneg b)
    linarith [neg_le_of_abs_le hbound]
  let q : ℝ → ℝ := fun θ =>
    (a * Real.cos θ + b) / (a + b * Real.cos θ)
  let F : ℝ → ℝ := fun θ => -Real.arcsin (q θ) / c
  have hqcont : Continuous q := by
    exact ((continuous_const.mul Real.continuous_cos).add continuous_const).div
      (continuous_const.add (continuous_const.mul Real.continuous_cos))
      (fun θ => (hden θ).ne')
  have hFcont : Continuous F :=
    (Real.continuous_arcsin.comp hqcont).neg.div_const c
  have hintegrable :
      IntervalIntegrable (fun θ : ℝ => (a + b * Real.cos θ)⁻¹)
        volume 0 Real.pi := by
    apply Continuous.intervalIntegrable
    exact (continuous_const.add
      (continuous_const.mul Real.continuous_cos)).inv₀
        (fun θ => (hden θ).ne')
  have hderiv : ∀ θ ∈ Set.Ioo (0 : ℝ) Real.pi,
      HasDerivAt F ((a + b * Real.cos θ)⁻¹) θ := by
    intro θ hθ
    have hsin : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
    have hqidentity :
        1 - (q θ) ^ 2 =
          (a ^ 2 - b ^ 2) * (Real.sin θ) ^ 2 /
            (a + b * Real.cos θ) ^ 2 := by
      have htrig : (Real.sin θ) ^ 2 = 1 - (Real.cos θ) ^ 2 := by
        linarith [Real.sin_sq_add_cos_sq θ]
      have hd2 : (a + b * Real.cos θ) ^ 2 ≠ 0 :=
        pow_ne_zero 2 (hden θ).ne'
      rw [htrig]
      dsimp [q]
      rw [div_pow]
      calc
        1 - (a * Real.cos θ + b) ^ 2 / (a + b * Real.cos θ) ^ 2 =
            ((a + b * Real.cos θ) ^ 2 -
              (a * Real.cos θ + b) ^ 2) /
              (a + b * Real.cos θ) ^ 2 := by
          rw [sub_div, div_self hd2]
        _ = (a ^ 2 - b ^ 2) * (1 - Real.cos θ ^ 2) /
              (a + b * Real.cos θ) ^ 2 := by
          congr 1
          ring
    have hqsmall : (q θ) ^ 2 < 1 := by
      have hpos : 0 <
          (a ^ 2 - b ^ 2) * (Real.sin θ) ^ 2 /
            (a + b * Real.cos θ) ^ 2 :=
        div_pos (mul_pos hdisc (sq_pos_of_pos hsin))
          (sq_pos_of_pos (hden θ))
      linarith [hqidentity]
    have hqlower : -1 < q θ := by nlinarith [sq_nonneg (q θ + 1)]
    have hqupper : q θ < 1 := by nlinarith [sq_nonneg (q θ - 1)]
    have hroot :
        Real.sqrt (1 - (q θ) ^ 2) =
          c * Real.sin θ / (a + b * Real.cos θ) := by
      rw [hqidentity, Real.sqrt_div (mul_nonneg hdisc.le (sq_nonneg _)),
        Real.sqrt_mul hdisc.le, Real.sqrt_sq hsin.le,
        Real.sqrt_sq (hden θ).le]
    have hqderiv :
        HasDerivAt q
          (-(a ^ 2 - b ^ 2) * Real.sin θ /
            (a + b * Real.cos θ) ^ 2) θ := by
      dsimp [q]
      refine ((((Real.hasDerivAt_cos θ).const_mul a).add_const b).div
        (((Real.hasDerivAt_cos θ).const_mul b).const_add a)
        (hden θ).ne').congr_deriv ?_
      ring
    have harcsin :=
      (Real.hasDerivAt_arcsin (ne_of_gt hqlower) (ne_of_lt hqupper)).comp
        θ hqderiv
    have hF :
        HasDerivAt F
          (-(1 / Real.sqrt (1 - (q θ) ^ 2) *
            (-(a ^ 2 - b ^ 2) * Real.sin θ /
              (a + b * Real.cos θ) ^ 2)) / c) θ := by
      simpa only [one_div, neg_sub, Function.comp_def, Pi.neg_apply] using harcsin.neg.div_const c
    refine hF.congr_deriv ?_
    rw [hroot]
    have hcsq : c ^ 2 = a ^ 2 - b ^ 2 :=
      Real.sq_sqrt hdisc.le
    field_simp [hc.ne', (hden θ).ne', hsin.ne']
    nlinarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    Real.pi_pos.le hFcont.continuousOn hderiv hintegrable]
  dsimp [F, q]
  rw [Real.cos_pi, Real.cos_zero]
  have hqpi : (a * (-1) + b) / (a + b * (-1)) = -1 := by
    have hne : a + b * (-1) ≠ 0 := by
      simpa only [mul_neg, mul_one, ne_eq, sub_eq_add_neg] using hminus.ne'
    apply (div_eq_iff hne).2
    ring
  have hqzero : (a * 1 + b) / (a + b * 1) = 1 := by
    have hne : a + b * 1 ≠ 0 := by simpa only [mul_one, ne_eq] using hplus.ne'
    apply (div_eq_iff hne).2
    ring
  rw [hqpi, hqzero, Real.arcsin_neg_one, Real.arcsin_one]
  dsimp [c]
  ring

end ArcsineIntegral

end

section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped ENNReal Interval Topology

namespace ArcsineTransform

theorem betaPDFReal_half_half_eq (u : ℝ) (hu₀ : 0 < u) (hu₁ : u < 1) :
    betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u =
      (1 / Real.pi) * (Real.sqrt (u * (1 - u)))⁻¹ := by
  rw [betaPDFReal, ite_eq_left ⟨hu₀, hu₁⟩,
    MetricCodes.Spherical.HigherHierarchy.Arcsine.beta_half_half_eq_pi]
  have hu : 0 ≤ u := hu₀.le
  have hv : 0 ≤ 1 - u := by linarith
  have hpow₁ : u ^ ((1 / 2 : ℝ) - 1) = (Real.sqrt u)⁻¹ := by
    convert Real.rpow_neg hu (1 / 2 : ℝ) using 1 <;>
      norm_num [Real.sqrt_eq_rpow]
  have hpow₂ : (1 - u) ^ ((1 / 2 : ℝ) - 1) =
      (Real.sqrt (1 - u))⁻¹ := by
    convert Real.rpow_neg hv (1 / 2 : ℝ) using 1 <;>
      norm_num [Real.sqrt_eq_rpow]
  rw [hpow₁, hpow₂, Real.sqrt_mul hu, mul_inv_rev]
  ring

theorem integral_beta_half_half_eq_integral_measureT (f : ℝ → ℝ) :
    (∫ u, f u ∂betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) =
      (1 / Real.pi) *
        ∫ z, f ((z + 1) / 2) ∂Polynomial.Chebyshev.measureT := by
  have hmeas : Measurable (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    (measurable_betaPDFReal _ _).ennreal_ofReal
  have hfinite : ∀ᵐ u : ℝ ∂volume,
      betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ) u < ⊤ := by
    filter_upwards [] with u
    simp only [betaPDF, one_div, ENNReal.ofReal_lt_top]
  have hpdf (u : ℝ) :
      0 ≤ betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u := by
    by_cases hu : 0 < u ∧ u < 1
    · exact (betaPDFReal_pos hu.1 hu.2 (by norm_num) (by norm_num)).le
    · simp only [betaPDFReal, hu, ↓reduceIte, Std.le_refl]
  unfold betaMeasure
  rw [integral_withDensity_eq_integral_toReal_smul hmeas hfinite]
  simp_rw [betaPDF, ENNReal.toReal_ofReal (hpdf _), smul_eq_mul]
  rw [Polynomial.Chebyshev.integral_measureT,
    ← intervalIntegral.integral_const_mul]
  have hsupport :
      (∫ u : ℝ, betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u * f u) =
        ∫ u in (0 : ℝ)..1,
          betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u * f u := by
    rw [intervalIntegral.integral_of_le (by norm_num),
      integral_Ioc_eq_integral_Ioo, ← integral_indicator measurableSet_Ioo]
    apply integral_congr_ae
    filter_upwards [] with u
    by_cases hu : u ∈ Set.Ioo (0 : ℝ) 1
    · simp only [one_div, hu, indicator_of_mem]
    · have hu' : ¬ (0 < u ∧ u < 1) := by simpa only [not_and, not_lt, mem_Ioo] using hu
      simp only [betaPDFReal, hu', ↓reduceIte, zero_mul, one_div, ite_mul, hu, not_false_eq_true,
        indicator_of_notMem]
  rw [hsupport]
  let g : ℝ → ℝ := fun z =>
    (1 / Real.pi) * (f ((z + 1) / 2) * (Real.sqrt (1 - z ^ 2))⁻¹)
  have hchange :
      (∫ u in (0 : ℝ)..1, g (2 * u - 1) * 2) =
        ∫ z in (-1 : ℝ)..1, g z := by
    convert intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
      (a := (0 : ℝ)) (b := 1)
      (f := fun u : ℝ => 2 * u - 1) (f' := fun _ : ℝ => 2)
      (g := g)
      (by fun_prop)
      (fun u _ => by
        simpa only [hasDerivAt_sub_const_iff, Pi.mul_apply, id_eq, zero_mul, mul_one, zero_add]
          using
          (((hasDerivAt_const (x := u) (c := (2 : ℝ))).mul (hasDerivAt_id u)).sub_const 1))
      (fun _ _ => by norm_num) using 1 <;> norm_num
  dsimp [g] at hchange
  simp_rw [Real.sqrt_inv]
  rw [← hchange]
  apply intervalIntegral.integral_congr
  intro u hu
  change betaPDFReal (1 / 2 : ℝ) (1 / 2 : ℝ) u * f u =
    (1 / Real.pi) *
      (f ((2 * u - 1 + 1) / 2) *
        (Real.sqrt (1 - (2 * u - 1) ^ 2))⁻¹) * 2
  have hu₀ : 0 ≤ u := by simpa only [zero_le_one, inf_of_le_left] using hu.1
  have hu₁ : u ≤ 1 := by simpa only [zero_le_one, sup_of_le_right] using hu.2
  by_cases hzero : u = 0 ∨ u = 1
  · rcases hzero with rfl | rfl <;> norm_num [betaPDFReal]
  · have hzero₀ : u ≠ 0 := fun h => hzero (Or.inl h)
    have hzero₁ : u ≠ 1 := fun h => hzero (Or.inr h)
    have hupos : 0 < u := lt_of_le_of_ne hu₀ (Ne.symm hzero₀)
    have huone : u < 1 := lt_of_le_of_ne hu₁ hzero₁
    rw [betaPDFReal_half_half_eq u hupos huone]
    have hquad : 1 - (2 * u - 1) ^ 2 = 4 * (u * (1 - u)) := by ring
    have hsqrt :
        Real.sqrt (1 - (2 * u - 1) ^ 2) =
          2 * Real.sqrt (u * (1 - u)) := by
      rw [hquad, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [hsqrt]
    have harg : (2 * u - 1 + 1) / 2 = u := by ring
    rw [harg]
    field_simp

theorem integral_betaMap_half_half_eq_integral_cos
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ t, f t ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        (1 / Real.pi) *
          ∫ θ in (0 : ℝ)..Real.pi, f ((Real.cos θ + 1) / 8) := by
  rw [integral_map (by fun_prop) hf.aestronglyMeasurable,
    integral_beta_half_half_eq_integral_measureT,
    Polynomial.Chebyshev.integral_measureT_eq_integral_cos]
  congr 1
  apply intervalIntegral.integral_congr
  intro θ _
  ring_nf

theorem betaMap_half_half_ae_pos :
    ∀ᵐ t ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4), 0 < t := by
  rw [ae_map_iff (by fun_prop) measurableSet_Ioi]
  change ∀ᵐ t ∂volume.withDensity
    (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)), 0 < t / 4
  have hmeas : Measurable (betaPDF (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    (measurable_betaPDFReal _ _).ennreal_ofReal
  rw [ae_withDensity_iff hmeas]
  filter_upwards [] with t ht
  by_contra hnot
  have htzero : t ≤ 0 := by
    have : t / 4 ≤ 0 := le_of_not_gt hnot
    linarith
  apply ht
  simp only [betaPDF, betaPDFReal, not_lt_of_ge htzero, false_and, ↓reduceIte, ENNReal.ofReal_zero]

instance betaMap_half_half_isProbabilityMeasure :
    IsProbabilityMeasure ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) := by
  let : IsProbabilityMeasure (betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)) :=
    isProbabilityMeasureBeta (by norm_num) (by norm_num)
  exact Measure.isProbabilityMeasure_map (by fun_prop)

theorem arcsine_stieltjes_integrable {x : ℝ} (hx : 0 ≤ x) :
    Integrable (fun t : ℝ => x / (x + t))
      ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
        (fun t : ℝ => t / 4)) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((by fun_prop : Measurable (fun t : ℝ => x / (x + t))).aestronglyMeasurable)
  filter_upwards [betaMap_half_half_ae_pos] with t ht
  have hden : 0 < x + t := by linarith
  have hnonneg : 0 ≤ x / (x + t) := div_nonneg hx hden.le
  simpa only [norm_div, norm_eq_abs, abs_of_nonneg hx, abs_of_pos hden, ge_iff_le] using
    ((div_le_one hden).2 (by linarith : x ≤ x + t))

theorem arcsine_integral_x_div_add {x : ℝ} (hx : 0 < x) :
    (∫ t, x / (x + t) ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        Real.sqrt (x / (x + 1 / 4)) := by
  rw [integral_betaMap_half_half_eq_integral_cos _ (by fun_prop)]
  have hrewrite :
      (∫ θ in (0 : ℝ)..Real.pi,
        x / (x + (Real.cos θ + 1) / 8)) =
          x * ∫ θ in (0 : ℝ)..Real.pi,
            ((x + 1 / 8) + (1 / 8) * Real.cos θ)⁻¹ := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro θ _
    change x / (x + (Real.cos θ + 1) / 8) =
      x * ((x + 1 / 8) + (1 / 8) * Real.cos θ)⁻¹
    rw [div_eq_mul_inv]
    congr 1
    ring
  rw [hrewrite,
    MetricCodes.Spherical.HigherHierarchy.ArcsineIntegral.integral_inv_add_mul_cos
      (x + 1 / 8) (1 / 8) (by
      norm_num [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 8)]
      linarith)]
  have hquad : (x + 1 / 8) ^ 2 - (1 / 8 : ℝ) ^ 2 =
      x * (x + 1 / 4) := by ring
  rw [hquad, Real.sqrt_mul hx.le, Real.sqrt_div hx.le]
  have hsx : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  have hsy : Real.sqrt (x + 1 / 4) ≠ 0 :=
    (Real.sqrt_pos.mpr (by linarith)).ne'
  field_simp [Real.pi_pos.ne', hsx, hsy]
  nlinarith [Real.sq_sqrt hx.le]

theorem arcsine_integral_self_div_add {x : ℝ} (hx : 0 ≤ x) :
    (∫ t, t / (t + x) ∂(betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
      (fun t : ℝ => t / 4)) =
        1 - Real.sqrt (x / (x + 1 / 4)) := by
  by_cases hzero : x = 0
  · subst x
    calc
      (∫ t, t / (t + 0) ∂(betaMeasure (1 / 2 : ℝ)
        (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)) =
          ∫ _t : ℝ, 1 ∂(betaMeasure (1 / 2 : ℝ)
            (1 / 2 : ℝ)).map (fun t : ℝ => t / 4) := by
            apply integral_congr_ae
            filter_upwards [betaMap_half_half_ae_pos] with t ht
            simp only [add_zero, ne_eq, ht.ne', not_false_eq_true, div_self]
      _ = 1 - Real.sqrt (0 / (0 + 1 / 4)) := by norm_num
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hzero)
    calc
      (∫ t, t / (t + x) ∂(betaMeasure (1 / 2 : ℝ)
        (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)) =
          ∫ t, (1 - x / (x + t)) ∂(betaMeasure (1 / 2 : ℝ)
            (1 / 2 : ℝ)).map (fun t : ℝ => t / 4) := by
            apply integral_congr_ae
            filter_upwards [betaMap_half_half_ae_pos] with t ht
            have hden : x + t ≠ 0 := ne_of_gt (by linarith)
            field_simp
            ring
      _ = 1 - (∫ t, x / (x + t) ∂(betaMeasure (1 / 2 : ℝ)
            (1 / 2 : ℝ)).map (fun t : ℝ => t / 4)) := by
            rw [integral_sub (integrable_const _)
              (arcsine_stieltjes_integrable hx)]
            rw [integral_const]
            have hprob : IsProbabilityMeasure
                ((betaMeasure (1 / 2 : ℝ) (1 / 2 : ℝ)).map
                  (fun t : ℝ => t / 4)) :=
              betaMap_half_half_isProbabilityMeasure
            let := hprob
            simp only [smul_eq_mul, mul_one, measureReal_def]
            rw [measure_univ]
            norm_num
      _ = 1 - Real.sqrt (x / (x + 1 / 4)) := by
            rw [arcsine_integral_x_div_add hxpos]

end ArcsineTransform

end

end HigherHierarchy

section

open scoped BigOperators

namespace HigherHierarchyChebyshev

private def zeroAngle (N j : ℕ) : ℝ :=
  ((j : ℝ) * Real.pi) / (N : ℝ)

/-- The zero used in the spherical-code argument. -/
def zero (R : ℝ) (N j : ℕ) : ℝ :=
  R / 2 * (1 + Real.cos (zeroAngle N j))

/-- The stabilizer used in the spherical-code argument. -/
def stabilizer (R : ℝ) (r : ℕ) (i : Fin r) : ℝ :=
  (Real.sqrt (1 + 4 * (zero R (r + 1) (i.val + 1))) - 1) / 2

end HigherHierarchyChebyshev

end

end Spherical

end MetricCodes


namespace MetricCodes

namespace Spherical

section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

end

section

open Filter
open scoped Topology BigOperators Interval

namespace HigherHierarchyChebyshev.Asymptotic

end HigherHierarchyChebyshev.Asymptotic

end

section

open Filter Set
open scoped Topology BigOperators

namespace HigherHierarchy.MidpointQuadrature

end HigherHierarchy.MidpointQuadrature

end

section

open Filter
open MetricCodes.Spherical.HigherHierarchy.MidpointQuadrature
open scoped BigOperators Topology Interval

namespace HigherHierarchyChebyshev.Asymptotic

end HigherHierarchyChebyshev.Asymptotic

end

end Spherical

end MetricCodes

section

open scoped Interval

namespace MetricCodes.Spherical.HigherHierarchyChebyshev

end MetricCodes.Spherical.HigherHierarchyChebyshev

open Filter
open scoped Topology BigOperators

namespace MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

end MetricCodes.Spherical.HigherHierarchyChebyshev.Asymptotic

end

namespace MetricCodes

namespace Spherical

namespace HigherHierarchyChebyshev

namespace Asymptotic

section

open Filter
open scoped Topology

end

section

open Filter
open scoped BigOperators Topology

end

section

end

end Asymptotic

end HigherHierarchyChebyshev

namespace HigherHierarchy

section

open scoped BigOperators

namespace Numerics

/-- The kissing ambient used in the spherical-code argument. -/
def kissingAmbient : Fin 3 → ℝ :=
  ![(0.090531 : ℝ), 0.000565957168637484, 0.00000249433171106134]

/-- The kissing stabilizer used in the spherical-code argument. -/
def kissingStabilizer : Fin 2 → ℝ :=
  ![(0.00693131464159807 : ℝ), 0.0000438056170666568]

@[simp] theorem kissingAmbient_apply (i : Fin 3) :
    kissingAmbient i =
      if i.val = 0 then (0.090531 : ℝ)
      else if i.val = 1 then 0.000565957168637484
      else 0.00000249433171106134 := by
  fin_cases i <;> rfl

@[simp] theorem kissingStabilizer_apply (i : Fin 2) :
    kissingStabilizer i =
      if i.val = 0 then (0.00693131464159807 : ℝ)
      else 0.0000438056170666568 := by
  fin_cases i <;> rfl

@[simp] theorem succAbove_three_20 :
    (2 : Fin 3).succAbove (0 : Fin 2) = 0 := by decide
@[simp] theorem succAbove_three_21 :
    (2 : Fin 3).succAbove (1 : Fin 2) = 1 := by decide

theorem kissing_interlacing :
    Interlacing kissingAmbient kissingStabilizer := by
  constructor
  · change 0 ≤ (0.00000249433171106134 : ℝ)
    norm_num
  · intro i
    fin_cases i <;> constructor <;> norm_num

theorem kissing_sqrt_lower :
    (0.31420830982168 : ℝ) <
        Real.sqrt (((kissingAmbient 0) * (1 + (kissingAmbient 0)))) ∧
      (0.02379658538854 : ℝ) <
        Real.sqrt (((kissingAmbient 1) * (1 + (kissingAmbient 1)))) ∧
      (0.00157934731226 : ℝ) <
        Real.sqrt (((kissingAmbient 2) * (1 + (kissingAmbient 2)))) := by
  constructor
  · apply Real.lt_sqrt_of_sq_lt
    norm_num
  constructor
  · apply Real.lt_sqrt_of_sq_lt
    norm_num
  · apply Real.lt_sqrt_of_sq_lt
    norm_num

theorem kissing_spectral_certificate :
    (0.00000212 : ℝ) <
      2 * Gamma kissingAmbient kissingStabilizer - (1 / 2 : ℝ) := by
  obtain ⟨h₀, h₁, h₂⟩ := kissing_sqrt_lower
  unfold Gamma
  rw [Fin.sum_univ_three]
  norm_num [spectralAtom, lagrangeWeight, lagrangeNumerator,
    lagrangeDenominator,
    Fin.prod_univ_two]
    at h₀ h₁ h₂ ⊢
  norm_num [Fin.ext_iff] at h₀ h₁ h₂ ⊢
  linarith

theorem rational_log_lower {r lo : ℝ} (hr : 1 ≤ r) (m : ℕ)
    (hlo : lo < MetricCodes.Numerics.logSeriesLower
      ((r - 1) / (r + 1)) m) : lo < Real.log r := by
  have hden : 0 < r + 1 := by linarith
  have hx : 0 ≤ (r - 1) / (r + 1) :=
    div_nonneg (sub_nonneg.mpr hr) hden.le
  have hx' : (r - 1) / (r + 1) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  calc
    lo < MetricCodes.Numerics.logSeriesLower
      ((r - 1) / (r + 1)) m := hlo
    _ ≤ Real.log
      ((1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1))) :=
        MetricCodes.Numerics.log_ratio_lower hx hx' m
    _ = Real.log r := by
      congr 1
      field_simp; ring

theorem rational_log_upper {r hi : ℝ} (hr : 1 ≤ r) (m : ℕ)
    (hhi : MetricCodes.Numerics.logSeriesUpper
      ((r - 1) / (r + 1)) m < hi) : Real.log r < hi := by
  have hden : 0 < r + 1 := by linarith
  have hx : 0 ≤ (r - 1) / (r + 1) :=
    div_nonneg (sub_nonneg.mpr hr) hden.le
  have hx' : (r - 1) / (r + 1) < 1 :=
    (div_lt_one hden).mpr (by linarith)
  calc
    Real.log r = Real.log
      ((1 + (r - 1) / (r + 1)) / (1 - (r - 1) / (r + 1))) := by
        congr 1
        field_simp; ring
    _ ≤ MetricCodes.Numerics.logSeriesUpper
      ((r - 1) / (r + 1)) m :=
        MetricCodes.Numerics.log_ratio_upper hx hx' m
    _ < hi := hhi

theorem log_scaled_pow_two {u : ℝ} (hu : u ≠ 0) (k : ℕ) :
    Real.log u = Real.log ((2 : ℝ) ^ k * u) - k * Real.log 2 := by
  have h := Real.log_mul
    (pow_ne_zero k (by norm_num : (2 : ℝ) ≠ 0)) hu
  rw [Real.log_pow] at h
  linarith

theorem kissing_entropy_certificate :
    Phi kissingAmbient kissingStabilizer < (0.396605 : ℝ) := by
  have htwo := MetricCodes.Numerics.log_two_interval.1
  have ha₀plus : Real.log (1 + kissingAmbient 0) < (0.086664734 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₀scale : (0.370525776 : ℝ) < Real.log (16 * kissingAmbient 0) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₁plus : Real.log (1 + kissingAmbient 1) < (0.000565798 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₁scale :
      (0.147626829 : ℝ) < Real.log (2048 * kissingAmbient 1) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₂plus : Real.log (1 + kissingAmbient 2) < (0.000002495 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have ha₂scale :
      (0.268306714 : ℝ) < Real.log (524288 * kissingAmbient 2) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₀plus : (0.006907403 : ℝ) < Real.log (1 + kissingStabilizer 0) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₀scale :
      Real.log (256 * kissingStabilizer 0) < (0.573471664 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₁plus :
      (0.000043804 : ℝ) < Real.log (1 + kissingStabilizer 1) := by
    apply rational_log_lower (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hb₁scale :
      Real.log (32768 * kissingStabilizer 1) < (0.361459204 : ℝ) := by
    apply rational_log_upper (m := 12)
    · norm_num
    · norm_num [MetricCodes.Numerics.logSeriesUpper,
        MetricCodes.Numerics.logSeriesLower, Finset.sum_range_succ]
  have hmain :
      (1 + kissingAmbient 0) * Real.log (1 + kissingAmbient 0) -
          kissingAmbient 0 *
            (Real.log (16 * kissingAmbient 0) - 4 * Real.log 2) +
        ((1 + kissingAmbient 1) * Real.log (1 + kissingAmbient 1) -
          kissingAmbient 1 *
            (Real.log (2048 * kissingAmbient 1) - 11 * Real.log 2)) +
        ((1 + kissingAmbient 2) * Real.log (1 + kissingAmbient 2) -
          kissingAmbient 2 *
            (Real.log (524288 * kissingAmbient 2) - 19 * Real.log 2)) -
        ((1 + kissingStabilizer 0) * Real.log (1 + kissingStabilizer 0) -
          kissingStabilizer 0 *
            (Real.log (256 * kissingStabilizer 0) - 8 * Real.log 2)) -
        ((1 + kissingStabilizer 1) * Real.log (1 + kissingStabilizer 1) -
          kissingStabilizer 1 *
            (Real.log (32768 * kissingStabilizer 1) - 15 * Real.log 2)) <
          (0.396605 : ℝ) * Real.log 2 := by
    norm_num at htwo ha₀plus ha₀scale ha₁plus ha₁scale ha₂plus ha₂scale
    norm_num at hb₀plus hb₀scale hb₁plus hb₁scale ⊢
    linarith
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    Phi kissingAmbient kissingStabilizer =
      ((1 + kissingAmbient 0) * Real.log (1 + kissingAmbient 0) -
          kissingAmbient 0 * Real.log (kissingAmbient 0) +
        ((1 + kissingAmbient 1) * Real.log (1 + kissingAmbient 1) -
          kissingAmbient 1 * Real.log (kissingAmbient 1)) +
        ((1 + kissingAmbient 2) * Real.log (1 + kissingAmbient 2) -
          kissingAmbient 2 * Real.log (kissingAmbient 2)) -
        ((1 + kissingStabilizer 0) * Real.log (1 + kissingStabilizer 0) -
          kissingStabilizer 0 * Real.log (kissingStabilizer 0)) -
        ((1 + kissingStabilizer 1) * Real.log (1 + kissingStabilizer 1) -
          kissingStabilizer 1 * Real.log (kissingStabilizer 1))) /
            Real.log 2 := by
      unfold Phi
      rw [Fin.sum_univ_three, Fin.sum_univ_two]
      unfold MetricCodes.sphericalEntropy Real.logb
      ring
    _ < (0.396605 : ℝ) := by
      apply (div_lt_iff₀ hlog).2
      rw [log_scaled_pow_two (u := kissingAmbient 0) (by norm_num) 4,
        log_scaled_pow_two (u := kissingAmbient 1) (by norm_num) 11,
        log_scaled_pow_two (u := kissingAmbient 2) (by norm_num) 19,
        log_scaled_pow_two (u := kissingStabilizer 0) (by norm_num) 8,
        log_scaled_pow_two (u := kissingStabilizer 1) (by norm_num) 15]
      norm_num at hmain ⊢
      exact hmain

end Numerics

end

section

open Filter Topology
open scoped BigOperators Topology

theorem Interlacing.Phi_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) : 0 ≤ Phi a b := by
  have hlast :
      0 ≤ MetricCodes.sphericalEntropy (a (Fin.last r)) := by
    simpa only [sphericalEntropy_zero, sub_zero] using
      (MetricCodes.Spherical.sphericalEntropy_sub_nonneg (a := a (Fin.last r)) (b := 0) (by
        norm_num) h.1)
  have hrows :
      0 ≤ ∑ i : Fin r,
        (MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i)) := by
    apply Finset.sum_nonneg
    intro i _
    exact MetricCodes.Spherical.sphericalEntropy_sub_nonneg
      (h.stabilizer_pos i).le (h.2 i).1.le
  unfold Phi
  rw [Fin.sum_univ_castSucc]
  calc
    0 ≤ (∑ i : Fin r,
        (MetricCodes.sphericalEntropy (a i.castSucc) -
          MetricCodes.sphericalEntropy (b i))) +
        MetricCodes.sphericalEntropy (a (Fin.last r)) :=
      add_nonneg hrows hlast
    _ = (∑ i : Fin r,
          MetricCodes.sphericalEntropy (a i.castSucc)) +
        MetricCodes.sphericalEntropy (a (Fin.last r)) -
          ∑ i : Fin r, MetricCodes.sphericalEntropy (b i) := by
      rw [Finset.sum_sub_distrib]
      ring

/-- The hierarchy rate set used in the spherical-code argument. -/
def hierarchyRateSet (s : ℝ) : Set ℝ :=
  {z | ∃ (r : ℕ) (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ),
    Interlacing a b ∧ s < 2 * Gamma a b ∧ z = Phi a b}

/-- The hierarchy variational rate used in the spherical-code argument. -/
def hierarchyVariationalRate (s : ℝ) : ℝ := sInf (hierarchyRateSet s)

theorem hierarchyRateSet_bddBelow (s : ℝ) :
    BddBelow (hierarchyRateSet s) := by
  refine ⟨0, ?_⟩
  rintro z ⟨r, a, b, h, _, rfl⟩
  exact h.Phi_nonneg

theorem hierarchyVariationalRate_le_of_feasible {r : ℕ}
    {s : ℝ} {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (hgap : s < 2 * Gamma a b) :
    hierarchyVariationalRate s ≤ Phi a b := by
  exact csInf_le (hierarchyRateSet_bddBelow s)
    ⟨r, a, b, h, hgap, rfl⟩

end

section

open MeasureTheory
open scoped BigOperators Interval

/-- The stieltjes phase used in the spherical-code argument. -/
def stieltjesPhase {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..(a (Fin.last r)) * (1 + a (Fin.last r)), (t + u)⁻¹) +
    ∑ i : Fin r,
      ∫ u in ((b i) * (1 + (b i)))..(a i.castSucc) * (1 + a i.castSucc),
        (t + u)⁻¹

/-- The stieltjes phase product used in the spherical-code argument. -/
def stieltjesPhaseProduct {r : ℕ}
    (a : Fin (r + 1) → ℝ) (b : Fin r → ℝ) (t : ℝ) : ℝ :=
  t * (∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
    (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i)))))

theorem Interlacing.ambient_quadratic_nonneg {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin (r + 1)) :
    0 ≤ ((a i) * (1 + (a i))) := by
  exact mul_nonneg (h.ambient_nonneg i) (by linarith [h.ambient_nonneg i])

theorem Interlacing.stabilizer_quadratic_pos {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) (i : Fin r) :
    0 < ((b i) * (1 + (b i))) := by
  exact mul_pos (h.stabilizer_pos i) (by linarith [h.stabilizer_pos i])

theorem integral_inv_add_eq_log_div
    {t p q : ℝ} (hp : 0 < t + p) (hq : 0 < t + q) :
    (∫ u in p..q, (t + u)⁻¹) = Real.log ((t + q) / (t + p)) := by
  have htranslate :=
    intervalIntegral.integral_comp_add_right (fun u : ℝ => u⁻¹) t
      (a := p) (b := q)
  have heq : (fun u : ℝ => (t + u)⁻¹) =
      (fun u : ℝ => (u + t)⁻¹) := by
    funext u
    rw [add_comm]
  rw [heq]
  rw [htranslate]
  simpa only [add_comm] using integral_inv_of_pos hp hq

theorem stieltjesPhase_eq_log_sum {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    stieltjesPhase a b t =
      Real.log ((t + ((a (Fin.last r)) * (1 + (a (Fin.last r))))) / t) +
        ∑ i : Fin r,
          Real.log ((t + ((a i.castSucc) * (1 + (a i.castSucc)))) /
            (t + ((b i) * (1 + (b i))))) := by
  unfold stieltjesPhase
  rw [integral_inv_add_eq_log_div (by simpa only [add_zero] using ht)
    (lt_of_lt_of_le ht (le_add_of_nonneg_right
      (h.ambient_quadratic_nonneg (Fin.last r))))]
  simp only [add_zero]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_inv_add_eq_log_div
    (lt_of_lt_of_le ht (le_add_of_nonneg_right
      (h.stabilizer_quadratic_pos i).le))
    (lt_of_lt_of_le ht (le_add_of_nonneg_right
      (h.ambient_quadratic_nonneg i.castSucc)))

theorem exp_neg_stieltjesPhase_eq_product {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    Real.exp (-stieltjesPhase a b t) =
      stieltjesPhaseProduct a b t := by
  have hlast : 0 < t + ((a (Fin.last r)) * (1 + (a (Fin.last r)))) := by
    linarith [h.ambient_quadratic_nonneg (Fin.last r)]
  have hambient (i : Fin (r + 1)) :
      0 < t + ((a i) * (1 + (a i))) := by
    linarith [h.ambient_quadratic_nonneg i]
  have hstabilizer (i : Fin r) :
      0 < t + ((b i) * (1 + (b i))) := by
    linarith [h.stabilizer_quadratic_pos i]
  have hexp :
      Real.exp (stieltjesPhase a b t) =
        ((t + ((a (Fin.last r)) * (1 + (a (Fin.last r))))) / t) *
          ∏ i : Fin r,
            ((t + ((a i.castSucc) * (1 + (a i.castSucc)))) /
              (t + ((b i) * (1 + (b i))))) := by
    rw [stieltjesPhase_eq_log_sum h ht, Real.exp_add]
    congr 1
    · exact Real.exp_log (div_pos hlast ht)
    · rw [Real.exp_sum]
      apply Finset.prod_congr rfl
      intro i _
      exact Real.exp_log
        (div_pos (hambient i.castSucc) (hstabilizer i))
  rw [Real.exp_neg, hexp]
  unfold stieltjesPhaseProduct
  rw [Finset.prod_div_distrib, Fin.prod_univ_castSucc]
  have hcast :
      0 < ∏ i : Fin r, (t + ((a i.castSucc) * (1 + (a i.castSucc)))) :=
    Finset.prod_pos fun i _ => hambient i.castSucc
  have hstabprod :
      0 < ∏ i : Fin r, (t + ((b i) * (1 + (b i)))) :=
    Finset.prod_pos fun i _ => hstabilizer i
  field_simp [ht.ne', hlast.ne', hcast.ne', hstabprod.ne']

theorem polynomial_partialFraction {r : ℕ}
    {x : Fin (r + 1) → ℝ} (hx : Function.Injective x)
    (P : Polynomial ℝ)
    (hdegree : P.degree <
      (Finset.univ : Finset (Fin (r + 1))).card)
    {z : ℝ} (hz : ∀ i : Fin (r + 1), z ≠ x i) :
    P.eval z / (∏ i : Fin (r + 1), (z - x i)) =
      ∑ i : Fin (r + 1),
        (P.eval (x i) /
          (∏ j ∈ Finset.univ.erase i, (x i - x j))) /
            (z - x i) := by
  classical
  have hinterpolate :
      P = Lagrange.interpolate
        (Finset.univ : Finset (Fin (r + 1))) x
        (fun i => P.eval (x i)) :=
    Lagrange.eq_interpolate hx.injOn hdegree
  have hvalue := Lagrange.eval_interpolate_not_at_node
    (s := (Finset.univ : Finset (Fin (r + 1))))
    (v := x) (x := z)
    (fun i => P.eval (x i))
    (fun i _ => hz i)
  rw [← hinterpolate] at hvalue
  have hprod : (∏ i : Fin (r + 1), (z - x i)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    exact sub_ne_zero.mpr (hz i)
  have hnodal :
      (Lagrange.nodal
        (Finset.univ : Finset (Fin (r + 1))) x).eval z =
          ∏ i : Fin (r + 1), (z - x i) := by
    simp only [Lagrange.nodal, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
  rw [hnodal] at hvalue
  rw [hvalue, mul_div_cancel_left₀ _ hprod]
  apply Finset.sum_congr rfl
  intro i _
  rw [Lagrange.nodalWeight, Finset.prod_inv_distrib]
  ring

theorem stieltjesPartialFraction {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    (∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
        (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i))))) =
      ∑ i : Fin (r + 1),
        lagrangeWeight a b i / (t + ((a i) * (1 + (a i)))) := by
  classical
  let P := stabilizerPolynomial b
  have hdegree :
      P.degree < (Finset.univ : Finset (Fin (r + 1))).card := by
    rw [Polynomial.degree_eq_natDegree
      (stabilizerPolynomial_monic b).ne_zero,
      stabilizerPolynomial_natDegree]
    simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_add,
      Nat.cast_one]
    exact_mod_cast Nat.lt_succ_self r
  have hraw := polynomial_partialFraction h.quadratic_injective P hdegree
    (z := -t) (fun i => by
      have hnode := h.ambient_quadratic_nonneg i
      linarith)
  have hrewrite :
      (∏ i : Fin r, (-t - ((b i) * (1 + (b i))))) /
          (∏ i : Fin (r + 1), (-t - ((a i) * (1 + (a i))))) =
        ∑ i : Fin (r + 1),
          lagrangeWeight a b i / (-t - ((a i) * (1 + (a i)))) := by
    convert hraw using 1
    · simp only [stabilizerPolynomial, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
        Polynomial.eval_C, P]
    · apply Finset.sum_congr rfl
      intro i _
      rw [stabilizerPolynomial_eval,
        ← lagrangeDenominator_eq_prod_erase]
      rfl
  have hneg (u : ℝ) : -t - u = -(t + u) := by ring
  simp_rw [hneg] at hrewrite
  rw [Finset.prod_neg, Finset.prod_neg] at hrewrite
  simp only [Finset.card_univ, Fintype.card_fin] at hrewrite
  have hsign : (-1 : ℝ) ^ r ≠ 0 := pow_ne_zero _ (by norm_num)
  have hden :
      (∏ i : Fin (r + 1),
        (t + ((a i) * (1 + (a i))))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i _
    have hnode := h.ambient_quadratic_nonneg i
    exact ne_of_gt (by linarith)
  have hleft :
      ((-1 : ℝ) ^ r * (∏ i : Fin r,
          (t + ((b i) * (1 + (b i)))))) /
        ((-1 : ℝ) ^ (r + 1) *
          (∏ i : Fin (r + 1),
            (t + ((a i) * (1 + (a i)))))) =
        -((∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
          (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i)))))) := by
    rw [pow_succ]
    field_simp [hsign, hden]
  rw [hleft] at hrewrite
  simpa only [div_neg, Finset.sum_neg_distrib, neg_inj] using hrewrite

theorem exp_neg_stieltjesPhase_eq_lagrange_sum {r : ℕ}
    {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b) {t : ℝ} (ht : 0 < t) :
    Real.exp (-stieltjesPhase a b t) =
      ∑ i : Fin (r + 1),
        lagrangeWeight a b i *
          (t / (t + ((a i) * (1 + (a i))))) := by
  rw [exp_neg_stieltjesPhase_eq_product h ht]
  unfold stieltjesPhaseProduct
  rw [show t * (∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
      (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i))))) =
        t * ((∏ i : Fin r, (t + ((b i) * (1 + (b i))))) /
          (∏ i : Fin (r + 1), (t + ((a i) * (1 + (a i)))))) by ring]
  rw [stieltjesPartialFraction h ht, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem quadratic_spectralAtom_identity {u : ℝ} (hu : 0 ≤ u) :
    Real.sqrt
      ((u * (1 + u)) / ((u * (1 + u)) + 1 / 4)) =
        2 * spectralAtom u := by
  have hA : 0 ≤ (u * (1 + u)) := by
    positivity
  have hlinear : 0 < 1 + 2 * u := by linarith
  have hden : 0 < (u * (1 + u)) + 1 / 4 := by linarith
  have hroot :
      Real.sqrt ((u * (1 + u)) + 1 / 4) =
        (1 + 2 * u) / 2 := by
    have hsquare := Real.sq_sqrt hden.le
    have hnonneg := Real.sqrt_nonneg
      ((u * (1 + u)) + 1 / 4)
    have htarget :
        ((1 + 2 * u) / 2) ^ 2 = (u * (1 + u)) + 1 / 4 := by
      ring
    nlinarith
  rw [Real.sqrt_div hA, hroot]
  unfold spectralAtom
  field_simp

theorem stieltjesKernel_integrable
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    {x : ℝ} (hx : 0 ≤ x)
    (hpositive : ∀ᵐ t ∂μ, 0 < t) :
    Integrable (fun t : ℝ => t / (t + x)) μ := by
  apply (integrable_const (α := ℝ) (μ := μ) (c := (1 : ℝ))).mono'
    (measurable_id.div (measurable_id.add measurable_const)).aestronglyMeasurable
  filter_upwards [hpositive] with t ht
  have hden : 0 < t + x := by linarith
  have hnonneg : 0 ≤ t / (t + x) := div_nonneg ht.le hden.le
  simp only [Pi.div_apply, Pi.add_apply, id_eq]
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  simpa only [ge_iff_le] using (div_le_one hden).mpr (by linarith)

theorem integral_exp_neg_stieltjesPhase_eq_one_sub_two_Gamma
    {r : ℕ} {a : Fin (r + 1) → ℝ} {b : Fin r → ℝ}
    (h : Interlacing a b)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hpositive : ∀ᵐ t ∂μ, 0 < t)
    (hstieltjes : ∀ i : Fin (r + 1),
      (∫ t : ℝ, t / (t + ((a i) * (1 + (a i)))) ∂μ) =
        1 - 2 * spectralAtom (a i)) :
    (∫ t : ℝ, Real.exp (-stieltjesPhase a b t) ∂μ) =
      1 - 2 * Gamma a b := by
  have hterm (i : Fin (r + 1)) :
      Integrable (fun t : ℝ =>
        lagrangeWeight a b i *
          (t / (t + ((a i) * (1 + (a i)))))) μ :=
    (stieltjesKernel_integrable μ (h.ambient_quadratic_nonneg i)
      hpositive).const_mul _
  calc
    (∫ t : ℝ, Real.exp (-stieltjesPhase a b t) ∂μ) =
        ∫ t : ℝ, ∑ i : Fin (r + 1),
          lagrangeWeight a b i *
            (t / (t + ((a i) * (1 + (a i))))) ∂μ := by
          apply integral_congr_ae
          filter_upwards [hpositive] with t ht
          exact exp_neg_stieltjesPhase_eq_lagrange_sum h ht
    _ = ∑ i : Fin (r + 1),
          lagrangeWeight a b i *
            (∫ t : ℝ, t / (t + ((a i) * (1 + (a i)))) ∂μ) := by
          rw [integral_finsetSum _ (fun i _ => hterm i)]
          apply Finset.sum_congr rfl
          intro i _
          rw [integral_const_mul]
    _ = ∑ i : Fin (r + 1),
          lagrangeWeight a b i *
            (1 - 2 * spectralAtom (a i)) := by
          congr 1
          funext i
          rw [hstieltjes i]
    _ = 1 - 2 * Gamma a b := by
          unfold Gamma
          simp_rw [mul_sub, mul_one]
          rw [Finset.sum_sub_distrib, h.sum_lagrangeWeight]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring

end

section

open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

end

section

end

end HigherHierarchy

end Spherical

end MetricCodes

end MetricCodesNoncomputable
