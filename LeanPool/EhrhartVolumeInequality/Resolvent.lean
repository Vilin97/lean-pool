/-
Copyright (c) 2026 OpenAI and Dean Cureton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Dean Cureton
-/

module

public import LeanPool.EhrhartVolumeInequality.Regularization
import all LeanPool.EhrhartVolumeInequality.Regularization
import Mathlib.Analysis.Normed.Lp.SmoothApprox

/-!
# Ehrhart volume inequality: Resolvent

Mollification, Green operator, and resolvent estimates.
-/

noncomputable local instance {n : ℕ} :
    CoeFun (ContDiffBump (0 : Fin n → ℝ)) (fun _ => (Fin n → ℝ) → ℝ) :=
  ⟨ContDiffBump.toFun⟩

noncomputable section

namespace Ehrhart

open Set MeasureTheory
open scoped BigOperators ENNReal

namespace TorusFriedrichsMollifierEstimates

open Set Function Filter MeasureTheory
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal Topology ContDiff Convolution

private theorem normalizedCoverBump_convolution_sq_le_convolution_sq
    {n : ℕ} {h : LogSpace n → ℝ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) :
    (∫ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) y * h (x - y)
        ∂(volume : Measure (LogSpace n))) ^ 2 ≤
      ∫ y : LogSpace n,
        (complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) y * h (x - y) ^ 2
          ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.lsmul ℝ ℝ
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hκint : Integrable κ (volume : Measure (LogSpace n)) :=
    hκ.integrable_of_hasCompactSupport hκcompact
  have hfirst : Integrable
      (fun y : LogSpace n => κ y * h (x - y))
      (volume : Measure (LogSpace n)) := by
    have hexists := hκcompact.convolutionExists_right L
      (hh.locallyIntegrable (by norm_num)) hκ x
    simpa [L, mul_comm] using hexists.integrable_swap
  have hsecond : Integrable
      (fun y : LogSpace n => κ y * h (x - y) ^ 2)
      (volume : Measure (LogSpace n)) := by
    have hexists := hκcompact.convolutionExists_right L
      hh.integrable_sq.locallyIntegrable hκ x
    simpa [L, mul_comm] using hexists.integrable_swap
  let m : ℝ :=
    ∫ y : LogSpace n, κ y * h (x - y)
      ∂(volume : Measure (LogSpace n))
  have hnonneg :
      0 ≤ ∫ y : LogSpace n,
        κ y * (h (x - y) - m) ^ 2
          ∂(volume : Measure (LogSpace n)) :=
    integral_nonneg (fun y =>
      mul_nonneg
        ((complexShrinkingBump (n := n) k).nonneg_normed y)
        (sq_nonneg _))
  have hexpand :
      (∫ y : LogSpace n,
        κ y * (h (x - y) - m) ^ 2
          ∂(volume : Measure (LogSpace n))) =
      (∫ y : LogSpace n,
        κ y * h (x - y) ^ 2
          ∂(volume : Measure (LogSpace n))) - m ^ 2 := by
    calc
      (∫ y : LogSpace n,
        κ y * (h (x - y) - m) ^ 2
          ∂(volume : Measure (LogSpace n))) =
        ∫ y : LogSpace n,
          ((κ y * h (x - y) ^ 2 -
            (2 * m) * (κ y * h (x - y))) + m ^ 2 * κ y)
          ∂(volume : Measure (LogSpace n)) := by
          apply integral_congr_ae
          filter_upwards with y
          ring
      _ =
          ((∫ y : LogSpace n,
            κ y * h (x - y) ^ 2
              ∂(volume : Measure (LogSpace n))) -
            (2 * m) *
              (∫ y : LogSpace n,
                κ y * h (x - y)
                  ∂(volume : Measure (LogSpace n)))) +
            m ^ 2 *
              (∫ y : LogSpace n, κ y
                ∂(volume : Measure (LogSpace n))) := by
          calc
            (∫ y : LogSpace n,
              (κ y * h (x - y) ^ 2 -
                (2 * m) * (κ y * h (x - y))) + m ^ 2 * κ y
                ∂(volume : Measure (LogSpace n))) =
              (∫ y : LogSpace n,
                κ y * h (x - y) ^ 2 -
                  (2 * m) * (κ y * h (x - y))
                    ∂(volume : Measure (LogSpace n))) +
                ∫ y : LogSpace n, m ^ 2 * κ y
                  ∂(volume : Measure (LogSpace n)) :=
                MeasureTheory.integral_add
                  (hsecond.sub (hfirst.const_mul (2 * m)))
                  (hκint.const_mul (m ^ 2))
            _ = _ := by
              rw [MeasureTheory.integral_sub hsecond
                (hfirst.const_mul (2 * m)),
                MeasureTheory.integral_const_mul,
                MeasureTheory.integral_const_mul]
      _ = _ := by
          change
            ((∫ y : LogSpace n,
              κ y * h (x - y) ^ 2
                ∂(volume : Measure (LogSpace n))) -
              2 * m * m) +
                m ^ 2 *
                  (∫ y : LogSpace n, κ y
                    ∂(volume : Measure (LogSpace n))) = _
          rw [(complexShrinkingBump (n := n) k).integral_normed]
          ring
  change m ^ 2 ≤ _
  linarith [hnonneg, hexpand]

private theorem norm_normalizedCoverMollification_le
    {n : ℕ} {h : LogSpace n → ℂ}
    (k : ℕ) (x : LogSpace n) :
    ‖normalizedCoverMollification h k x‖ ≤
      ∫ y : LogSpace n,
        (complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) y * ‖h (x - y)‖
          ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  change
    ‖(κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))] h) x‖ ≤ _
  rw [MeasureTheory.convolution_def]
  calc
    ‖∫ y : LogSpace n,
      (ContinuousLinearMap.lsmul ℝ ℝ) (κ y) (h (x - y))
        ∂(volume : Measure (LogSpace n))‖ ≤
      ∫ y : LogSpace n,
        ‖(ContinuousLinearMap.lsmul ℝ ℝ) (κ y) (h (x - y))‖
          ∂(volume : Measure (LogSpace n)) :=
      norm_integral_le_integral_norm _
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      change ‖κ y • h (x - y)‖ = κ y * ‖h (x - y)‖
      rw [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg
          ((complexShrinkingBump (n := n) k).nonneg_normed y)]

private theorem normalizedCoverMollification_norm_sq_le_convolution_norm_sq
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) :
    ‖normalizedCoverMollification h k x‖ ^ 2 ≤
      ∫ y : LogSpace n,
        (complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) y * ‖h (x - y)‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
  have hnorm := norm_normalizedCoverMollification_le (h := h) k x
  have hJ := normalizedCoverBump_convolution_sq_le_convolution_sq
    hh.norm k x
  exact (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans hJ

private theorem locallyIntegrable_cover_complex_mul_continuous
    {n : ℕ} {h b : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hb : Continuous b) :
    LocallyIntegrable (fun x => b x * h x)
      (volume : Measure (LogSpace n)) := by
  apply locallyIntegrable_iff.mpr
  intro K hK
  have hprod :=
    (hh.integrableOn_isCompact hK).mul_continuousOn
      hb.continuousOn hK
  simpa only [mul_comm] using hprod

private def normalizedCoverComplexDriftCommutator {n : ℕ}
    (b h : LogSpace n → ℂ) (k : ℕ) (x : LogSpace n) : ℂ :=
  normalizedCoverMollification (fun y => b y * h y) k x -
    b x * normalizedCoverMollification h k x

private theorem continuous_normalizedCoverComplexDriftCommutator
    {n : ℕ} {b h : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hb : Continuous b) (k : ℕ) :
    Continuous (normalizedCoverComplexDriftCommutator b h k) := by
  unfold normalizedCoverComplexDriftCommutator
  exact (contDiff_normalizedCoverMollification
    (locallyIntegrable_cover_complex_mul_continuous hh hb) k 0).continuous.sub
      (hb.mul (contDiff_normalizedCoverMollification hh k 0).continuous)

private theorem normalizedCoverComplexDriftCommutator_eq_integral
    {n : ℕ} {b h : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hb : Continuous b) (k : ℕ) (x : LogSpace n) :
    normalizedCoverComplexDriftCommutator b h k x =
      ∫ y : LogSpace n,
        (b y - b x) * h y *
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) : ℂ)
        ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hbh := locallyIntegrable_cover_complex_mul_continuous hh hb
  have hfirst : Integrable
      (fun y : LogSpace n => b y * h y * (κ (x - y) : ℂ))
      (volume : Measure (LogSpace n)) := by
    have hi := hκcompact.convolutionExists_right
      DolbeaultRegularity.complexRealMultiplication
      hbh hκ x
    simpa only [mul_assoc, complexRealMultiplication_apply, mul_comm] using hi.integrable
  have hsecond : Integrable
      (fun y : LogSpace n => h y * (κ (x - y) : ℂ))
      (volume : Measure (LogSpace n)) := by
    have hi := hκcompact.convolutionExists_right
      DolbeaultRegularity.complexRealMultiplication
      hh hκ x
    simpa only [complexRealMultiplication_apply, mul_comm] using hi.integrable
  unfold normalizedCoverComplexDriftCommutator
  change
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))]
        (fun y => b y * h y)) x -
      b x *
        (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
          (volume : Measure (LogSpace n))] h) x = _
  rw [← congrFun
      (complex_convolution_flip (fun y => b y * h y) κ) x,
    ← congrFun (complex_convolution_flip h κ) x,
    MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  simp_rw [complexRealMultiplication_apply]
  have hfirst' : Integrable
      (fun y : LogSpace n => (κ (x - y) : ℂ) * (b y * h y))
      (volume : Measure (LogSpace n)) := by
    simpa only [mul_comm, mul_assoc] using hfirst
  have hsecond' : Integrable
      (fun y : LogSpace n => (κ (x - y) : ℂ) * h y)
      (volume : Measure (LogSpace n)) := by
    simpa only [mul_comm] using hsecond
  change
    (∫ y : LogSpace n, (κ (x - y) : ℂ) * (b y * h y)
      ∂(volume : Measure (LogSpace n))) -
      b x *
        (∫ y : LogSpace n, (κ (x - y) : ℂ) * h y
          ∂(volume : Measure (LogSpace n))) =
      ∫ y : LogSpace n,
        (b y - b x) * h y * (κ (x - y) : ℂ)
        ∂(volume : Measure (LogSpace n))
  rw [← MeasureTheory.integral_const_mul,
    ← MeasureTheory.integral_sub hfirst' (hsecond'.const_mul (b x))]
  apply integral_congr_ae
  filter_upwards with y
  ring

private theorem norm_normalizedCoverComplexDriftCommutator_le_driftOscillation
    {n : ℕ} {b h : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hb : Continuous b) (k : ℕ) (x : LogSpace n)
    {c : ℝ}
    (hosc : ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 →
        ‖b y - b x‖ ≤ c) :
    ‖normalizedCoverComplexDriftCommutator b h k x‖ ≤
      c *
        ∫ y : LogSpace n,
          ‖h y‖ *
            (complexShrinkingBump (n := n) k).normed
              (volume : Measure (LogSpace n)) (x - y)
          ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.lsmul ℝ ℝ
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hhnorm : LocallyIntegrable
      (fun y : LogSpace n => ‖h y‖)
      (volume : Measure (LogSpace n)) := by
    exact locallyIntegrableOn_univ.mp
      ((hh.locallyIntegrableOn Set.univ).norm)
  have hbase : Integrable
      (fun y : LogSpace n => ‖h y‖ * κ (x - y))
      (volume : Measure (LogSpace n)) := by
    have hi := hκcompact.convolutionExists_right L hhnorm hκ x
    simpa [L] using hi.integrable
  have hmajor : Integrable
      (fun y : LogSpace n => c * (‖h y‖ * κ (x - y)))
      (volume : Measure (LogSpace n)) := hbase.const_mul c
  rw [normalizedCoverComplexDriftCommutator_eq_integral hh hb k x,
    ← MeasureTheory.integral_const_mul]
  apply MeasureTheory.norm_integral_le_of_norm_le hmajor
  filter_upwards with y
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg
      ((complexShrinkingBump (n := n) k).nonneg_normed (x - y))]
  by_cases hz : κ (x - y) = 0
  · simp only [hz, mul_zero, Std.le_refl, κ]
  · calc
      (‖b y - b x‖ * ‖h y‖) * κ (x - y) ≤
        (c * ‖h y‖) * κ (x - y) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hosc y hz) (norm_nonneg _))
            ((complexShrinkingBump (n := n) k).nonneg_normed
              (x - y))
      _ = c * (‖h y‖ * κ (x - y)) := by ring

private theorem coverReal_convolution_comm {n : ℕ}
    (f g : LogSpace n → ℝ) :
    (f ⋆[ContinuousLinearMap.mul ℝ ℝ,
      (volume : Measure (LogSpace n))] g) =
      (g ⋆[ContinuousLinearMap.mul ℝ ℝ,
        (volume : Measure (LogSpace n))] f) := by
  have h := MeasureTheory.convolution_flip
    (μ := (volume : Measure (LogSpace n)))
    (f := g) (g := f) (ContinuousLinearMap.mul ℝ ℝ)
  rw [ContinuousLinearMap.flip_mul] at h
  exact h

private theorem setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_le
    {n : ℕ} {b h : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hb : Continuous b) (k : ℕ)
    {K S : Set (LogSpace n)}
    (hK : IsCompact K) (hS : IsCompact S)
    (hlocal : MemLp h 2 ((volume : Measure (LogSpace n)).restrict S))
    {c : ℝ}
    (hreach : ∀ x ∈ K, ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 → y ∈ S)
    (hosc : ∀ x ∈ K, ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 →
          ‖b y - b x‖ ≤ c) :
    (∫ x in K,
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
        ∂(volume : Measure (LogSpace n))) ≤
      c ^ 2 *
        ∫ y in S, ‖h y‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.mul ℝ ℝ
  let t : LogSpace n → ℂ := S.indicator h
  let q : LogSpace n → ℝ :=
    κ ⋆[L, (volume : Measure (LogSpace n))]
      (fun y : LogSpace n => ‖t y‖ ^ 2)
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hκint : Integrable κ (volume : Measure (LogSpace n)) :=
    hκ.integrable_of_hasCompactSupport hκcompact
  have ht : MemLp t 2 (volume : Measure (LogSpace n)) :=
    (MeasureTheory.memLp_indicator_iff_restrict hS.measurableSet).mpr hlocal
  have hq : Integrable q (volume : Measure (LogSpace n)) :=
    hκint.integrable_convolution L ht.norm.integrable_sq
  have hqnonneg (x : LogSpace n) : 0 ≤ q x := by
    unfold q
    rw [MeasureTheory.convolution_def]
    apply integral_nonneg
    intro y
    change 0 ≤ κ y * ‖t (x - y)‖ ^ 2
    exact mul_nonneg
      ((complexShrinkingBump (n := n) k).nonneg_normed y)
      (sq_nonneg _)
  have htotal :
      (∫ x : LogSpace n, q x
        ∂(volume : Measure (LogSpace n))) =
        ∫ y in S, ‖h y‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
    calc
      (∫ x : LogSpace n, q x
        ∂(volume : Measure (LogSpace n))) =
        (∫ y : LogSpace n, κ y
          ∂(volume : Measure (LogSpace n))) *
          (∫ y : LogSpace n, ‖t y‖ ^ 2
            ∂(volume : Measure (LogSpace n))) := by
            exact MeasureTheory.integral_convolution L
              hκint ht.norm.integrable_sq
      _ = ∫ y : LogSpace n, ‖t y‖ ^ 2
            ∂(volume : Measure (LogSpace n)) := by
            rw [(complexShrinkingBump (n := n) k).integral_normed]
            simp only [one_mul]
      _ = _ := by
        have hsquare :
            (fun y : LogSpace n => ‖t y‖ ^ 2) =
              S.indicator (fun y : LogSpace n => ‖h y‖ ^ 2) := by
          funext y
          by_cases hy : y ∈ S
          · simp only [hy, indicator_of_mem, t]
          · simp only [hy, not_false_eq_true, indicator_of_notMem, norm_zero, ne_eq,
            OfNat.ofNat_ne_zero,
              zero_pow, t]
        rw [hsquare, MeasureTheory.integral_indicator hS.measurableSet]
  have havg (x : LogSpace n) (hx : x ∈ K) :
      (∫ y : LogSpace n, ‖h y‖ * κ (x - y)
        ∂(volume : Measure (LogSpace n))) =
        ∫ z : LogSpace n, κ z * ‖t (x - z)‖
          ∂(volume : Measure (LogSpace n)) := by
    calc
      (∫ y : LogSpace n, ‖h y‖ * κ (x - y)
        ∂(volume : Measure (LogSpace n))) =
          ((fun y : LogSpace n => ‖h y‖)
            ⋆[L, (volume : Measure (LogSpace n))] κ) x := by
              rfl
      _ = ((fun y : LogSpace n => ‖t y‖)
            ⋆[L, (volume : Measure (LogSpace n))] κ) x := by
        rw [MeasureTheory.convolution_def,
          MeasureTheory.convolution_def]
        apply integral_congr_ae
        filter_upwards with y
        by_cases hy : κ (x - y) = 0
        · simp only [hy, ContinuousLinearMap.mul_apply', mul_zero, L]
        · have hyS : y ∈ S := hreach x hx y hy
          simp only [ContinuousLinearMap.mul_apply', hyS, indicator_of_mem, L, t]
      _ = (κ ⋆[L, (volume : Measure (LogSpace n))]
            (fun y : LogSpace n => ‖t y‖)) x := by
        exact congrFun (coverReal_convolution_comm
          (fun y : LogSpace n => ‖t y‖) κ) x
      _ = ∫ z : LogSpace n, κ z * ‖t (x - z)‖
          ∂(volume : Measure (LogSpace n)) := by
            rfl
  have hpoint (x : LogSpace n) (hx : x ∈ K) :
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2 ≤
        c ^ 2 * q x := by
    have hbound :=
      norm_normalizedCoverComplexDriftCommutator_le_driftOscillation
        hh hb k x (hosc x hx)
    change
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ≤
        c *
          (∫ y : LogSpace n, ‖h y‖ * κ (x - y)
            ∂(volume : Measure (LogSpace n))) at hbound
    rw [havg x hx] at hbound
    have hJ := normalizedCoverBump_convolution_sq_le_convolution_sq
      ht.norm k x
    have hJ' :
        (∫ z : LogSpace n, κ z * ‖t (x - z)‖
          ∂(volume : Measure (LogSpace n))) ^ 2 ≤ q x := by
      simpa [κ, q, L, MeasureTheory.convolution_def] using hJ
    calc
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2 ≤
        (c *
          (∫ z : LogSpace n, κ z * ‖t (x - z)‖
            ∂(volume : Measure (LogSpace n)))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hbound 2
      _ = c ^ 2 *
          (∫ z : LogSpace n, κ z * ‖t (x - z)‖
            ∂(volume : Measure (LogSpace n))) ^ 2 := by
              ring
      _ ≤ c ^ 2 * q x :=
          mul_le_mul_of_nonneg_left hJ' (sq_nonneg c)
  have hcommcontinuous :
      Continuous (normalizedCoverComplexDriftCommutator b h k) :=
    continuous_normalizedCoverComplexDriftCommutator hh hb k
  have hcommint : IntegrableOn
      (fun x : LogSpace n =>
        ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2)
      K (volume : Measure (LogSpace n)) :=
    (hcommcontinuous.norm.pow 2).continuousOn.integrableOn_compact hK
  have hmajorint : IntegrableOn
      (fun x : LogSpace n => c ^ 2 * q x)
      K (volume : Measure (LogSpace n)) :=
    (hq.const_mul (c ^ 2)).integrableOn
  calc
    (∫ x in K,
      ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
        ∂(volume : Measure (LogSpace n))) ≤
        ∫ x in K, c ^ 2 * q x
          ∂(volume : Measure (LogSpace n)) :=
      MeasureTheory.setIntegral_mono_on
        hcommint hmajorint hK.measurableSet hpoint
    _ = c ^ 2 *
        (∫ x in K, q x
          ∂(volume : Measure (LogSpace n))) := by
            rw [MeasureTheory.integral_const_mul]
    _ ≤ c ^ 2 *
        (∫ x : LogSpace n, q x
          ∂(volume : Measure (LogSpace n))) :=
        mul_le_mul_of_nonneg_left
          (MeasureTheory.setIntegral_le_integral hq
            (Filter.Eventually.of_forall hqnonneg))
          (sq_nonneg c)
    _ = _ := by rw [htotal]

private theorem setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_tendsto_zero
    {n : ℕ} {b h : LogSpace n → ℂ}
    (hh : LocallyIntegrable h (volume : Measure (LogSpace n)))
    (hlocal : ∀ {S : Set (LogSpace n)}, IsCompact S →
      MemLp h 2 ((volume : Measure (LogSpace n)).restrict S))
    (hb : Continuous b)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  let S : Set (LogSpace n) := Metric.cthickening 1 K
  have hS : IsCompact S := hK.cthickening
  let M : ℝ :=
    ∫ y in S, ‖h y‖ ^ 2
      ∂(volume : Measure (LogSpace n))
  have hM : 0 ≤ M := by
    dsimp [M]
    exact integral_nonneg (fun y => sq_nonneg _)
  have hUC : UniformContinuousOn b S :=
    hS.uniformContinuousOn_of_continuous hb.continuousOn
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hden : 0 < 2 * (M + 1) := by positivity
  let η : ℝ := min 1 (ε / (2 * (M + 1)))
  have hη : 0 < η := by
    dsimp [η]
    exact lt_min zero_lt_one (div_pos hε hden)
  have hηone : η ≤ 1 := min_le_left _ _
  have hηdiv : η ≤ ε / (2 * (M + 1)) := min_le_right _ _
  have hηscale : η * (2 * (M + 1)) ≤ ε :=
    (le_div_iff₀ hden).mp hηdiv
  obtain ⟨δ, hδ, hu⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUC) η hη
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp
      (complexShrinkingBump_rOut_tendsto (n := n)))
      (min 1 δ) (lt_min zero_lt_one hδ)
  refine ⟨N, fun k hk => ?_⟩
  have hr : (complexShrinkingBump (n := n) k).rOut < min 1 δ := by
    have hrmetric := hN k hk
    simpa only [lt_inf_iff, dist_zero_right, Real.norm_eq_abs,
      abs_of_nonneg (complexShrinkingBump (n := n) k).rOut_pos.le]
      using hrmetric
  have hrone : (complexShrinkingBump (n := n) k).rOut < 1 :=
    lt_of_lt_of_le hr (min_le_left _ _)
  have hrdelta : (complexShrinkingBump (n := n) k).rOut < δ :=
    lt_of_lt_of_le hr (min_le_right _ _)
  have hkernelDist (x y : LogSpace n)
      (hy : (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0) :
      dist y x < (complexShrinkingBump (n := n) k).rOut := by
    have hball :
        x - y ∈ Metric.ball (0 : LogSpace n)
          (complexShrinkingBump (n := n) k).rOut := by
      rw [← (complexShrinkingBump (n := n) k).support_normed_eq
        (μ := (volume : Measure (LogSpace n)))]
      exact hy
    have hnorm :
        ‖x - y‖ < (complexShrinkingBump (n := n) k).rOut := by
      simpa only [Metric.mem_ball, dist_zero_right] using hball
    simpa only [dist_eq_norm, norm_sub_rev, gt_iff_lt] using hnorm
  have hreach : ∀ x ∈ K, ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 → y ∈ S := by
    intro x hx y hy
    change y ∈ Metric.cthickening 1 K
    exact Metric.mem_cthickening_of_dist_le y x 1 K hx
      ((hkernelDist x y hy).le.trans hrone.le)
  have hosc : ∀ x ∈ K, ∀ y : LogSpace n,
      (complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) ≠ 0 →
          ‖b y - b x‖ ≤ η := by
    intro x hx y hy
    have hxS : x ∈ S :=
      Metric.self_subset_cthickening K hx
    have hp := hu y (hreach x hx y hy) x hxS
      ((hkernelDist x y hy).trans hrdelta)
    exact le_of_lt (by simpa only [dist_eq_norm] using hp)
  have hL2 :=
    setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_le
      hh hb k hK hS (hlocal hS) (c := η) hreach hosc
  have hηsq : η ^ 2 ≤ η := by
    nlinarith [hη.le, hηone]
  have hfirst : η ^ 2 * M ≤ η * M :=
    mul_le_mul_of_nonneg_right hηsq hM
  have hsecond : η * M ≤ η * (M + 1) :=
    mul_le_mul_of_nonneg_left (by linarith) hη.le
  have hhalf : η * (M + 1) ≤ ε / 2 := by
    nlinarith [hηscale]
  have hbound : η ^ 2 * M < ε :=
    lt_of_le_of_lt (hfirst.trans (hsecond.trans hhalf)) (by linarith)
  have hnonneg :
      0 ≤ ∫ x in K,
        ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)) :=
    integral_nonneg (fun x => sq_nonneg _)
  have hfinal :
      (∫ x in K,
        ‖normalizedCoverComplexDriftCommutator b h k x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) < ε := by
    apply lt_of_le_of_lt hL2
    exact hbound
  simpa only [dist_zero_right, Real.norm_eq_abs, abs_of_nonneg hnonneg, gt_iff_lt] using hfinal

end TorusFriedrichsMollifierEstimates

namespace TorusDeckPeriodization

open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem norm_imaginaryShift_coordinate
    {n : ℕ} (q : Fin n → ℤ) (i : Fin n) :
    ‖TorusCharacters.imaginaryShift q i‖ =
      |(q i : ℝ)| * (2 * Real.pi) := by
  simp only [TorusCharacters.imaginaryShift, Complex.norm_mul, Complex.norm_intCast,
    Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    Complex.norm_I, mul_one]

private def complexDeckPeriodization {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℂ)
    (z : TorusCharacters.LogSpace n) : ℂ :=
  ∑' q : Fin n → ℤ,
    ψ (z + TorusCharacters.imaginaryShift q)

private theorem complexDeckPeriodization_periodic
    {n : ℕ}
    (ψ : TorusCharacters.LogSpace n → ℂ)
    (q : Fin n → ℤ) :
    Function.Periodic (complexDeckPeriodization ψ)
      (TorusCharacters.imaginaryShift q) := by
  intro z
  unfold complexDeckPeriodization
  calc
    (∑' d : Fin n → ℤ,
      ψ (z + TorusCharacters.imaginaryShift q +
        TorusCharacters.imaginaryShift d)) =
      ∑' d : Fin n → ℤ,
        ψ (z + TorusCharacters.imaginaryShift (q + d)) := by
      apply tsum_congr
      intro d
      congr 1
      ext i
      simp only [Pi.add_apply, TorusCharacters.imaginaryShift, Int.cast_add]
      ring
    _ = ∑' d : Fin n → ℤ,
      ψ (z + TorusCharacters.imaginaryShift d) := by
      exact (Equiv.addLeft q).tsum_eq
        (fun d : Fin n → ℤ =>
          ψ (z + TorusCharacters.imaginaryShift d))

private theorem exists_finite_complexDeckPeriodization_support_near
    {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ)
    (x : TorusCharacters.LogSpace n) :
    ∃ s : Finset (Fin n → ℤ),
      ∀ᶠ y : TorusCharacters.LogSpace n in 𝓝 x,
        ∀ q : Fin n → ℤ,
          q ∉ s →
            ψ (y + TorusCharacters.imaginaryShift q) = 0 := by
  classical
  obtain ⟨R, hRpos, hR⟩ :=
    hψcompact.isBounded.exists_pos_norm_le
  obtain ⟨N, hN⟩ := exists_nat_gt
    ((R + (‖x‖ + 1)) / (2 * Real.pi))
  let s : Finset (Fin n → ℤ) :=
    Fintype.piFinset
      (fun _ : Fin n => Finset.Icc (-(N : ℤ)) (N : ℤ))
  refine ⟨s, ?_⟩
  filter_upwards
    [Metric.ball_mem_nhds x (show 0 < (1 : ℝ) by norm_num)]
    with y hy
  intro q hq
  by_contra hnonzero
  have hsupport :
      y + TorusCharacters.imaginaryShift q ∈ tsupport ψ :=
    subset_closure ((mem_support).mpr hnonzero)
  have himage :
      ‖y + TorusCharacters.imaginaryShift q‖ ≤ R :=
    hR _ hsupport
  have hyx : ‖y - x‖ < 1 := by
    simpa only [Metric.mem_ball, dist_eq_norm] using hy
  have hybound : ‖y‖ ≤ ‖x‖ + 1 := by
    calc
      ‖y‖ = ‖(y - x) + x‖ := by abel_nf
      _ ≤ ‖y - x‖ + ‖x‖ := norm_add_le _ _
      _ ≤ ‖x‖ + 1 := by linarith
  have hdeck :
      ‖TorusCharacters.imaginaryShift q‖ ≤
        R + (‖x‖ + 1) := by
    calc
      ‖TorusCharacters.imaginaryShift q‖ =
          ‖(y + TorusCharacters.imaginaryShift q) - y‖ := by
            abel_nf
      _ ≤ ‖y + TorusCharacters.imaginaryShift q‖ + ‖y‖ :=
        norm_sub_le _ _
      _ ≤ R + (‖x‖ + 1) := add_le_add himage hybound
  have hpos : 0 < 2 * Real.pi := by positivity
  have hNmul :
      R + (‖x‖ + 1) < (N : ℝ) * (2 * Real.pi) :=
    (div_lt_iff₀ hpos).mp hN
  have hmember : q ∈ s := by
    apply Fintype.mem_piFinset.mpr
    intro i
    have hcoord :=
      (norm_le_pi_norm (TorusCharacters.imaginaryShift q) i).trans
        hdeck
    rw [norm_imaginaryShift_coordinate] at hcoord
    have habs : |(q i : ℝ)| < (N : ℝ) :=
      lt_of_mul_lt_mul_right (lt_of_le_of_lt hcoord hNmul) hpos.le
    have hleft : (-(N : ℤ)) ≤ q i := by
      exact_mod_cast (le_of_lt (abs_lt.mp habs).1)
    have hright : q i ≤ (N : ℤ) := by
      exact_mod_cast (le_of_lt (abs_lt.mp habs).2)
    exact Finset.mem_Icc.mpr ⟨hleft, hright⟩
  exact hq hmember

private theorem contDiff_complexDeckPeriodization
    {n : ℕ} {r : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψ : ContDiff ℝ r ψ)
    (hψcompact : HasCompactSupport ψ) :
    ContDiff ℝ r (complexDeckPeriodization ψ) := by
  classical
  apply contDiff_iff_contDiffAt.mpr
  intro x
  obtain ⟨s, hs⟩ :=
    exists_finite_complexDeckPeriodization_support_near hψcompact x
  let F : TorusCharacters.LogSpace n → ℂ :=
    fun y => ∑ q ∈ s,
      ψ (y + TorusCharacters.imaginaryShift q)
  have hF : ContDiff ℝ r F := by
    dsimp [F]
    apply ContDiff.sum
    intro q hq
    exact hψ.comp (contDiff_id.add contDiff_const)
  apply hF.contDiffAt.congr_of_eventuallyEq
  filter_upwards [hs] with y hy
  change
    (∑' q : Fin n → ℤ,
      ψ (y + TorusCharacters.imaginaryShift q)) =
      ∑ q ∈ s, ψ (y + TorusCharacters.imaginaryShift q)
  exact tsum_eq_sum (fun q hq => hy q hq)

end TorusDeckPeriodization

namespace TorusDeckCompactSupport

open Set Function Filter MeasureTheory Matrix
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open MatrixTorusBochnerIdentity TorusDeckPeriodization
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
    {n : ℕ}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ) :
    HasCompactSupport
      (torusScalarRepresentative (complexDeckPeriodization ψ)) := by
  classical
  let K : Set (WeightedTorusHilbert.LogTorus n) :=
    complexTorusCoverProjection n '' tsupport ψ
  have hK : IsCompact K :=
    hψcompact.image (continuous_complexTorusCoverProjection n)
  apply HasCompactSupport.intro hK
  intro p hp
  by_contra hnonzero
  obtain ⟨z, hz⟩ :=
    (complexTorusCoverProjection_isOpenQuotientMap n).surjective p
  have hvalue : complexDeckPeriodization ψ z ≠ 0 := by
    intro hzero
    apply hnonzero
    have hrep := congrFun
      (complexTorusCoverLift_torusScalarRepresentative_eq
        (complexDeckPeriodization ψ)
        (fun q => complexDeckPeriodization_periodic ψ q)) z
    change
      torusScalarRepresentative (complexDeckPeriodization ψ)
        (complexTorusCoverProjection n z) =
        complexDeckPeriodization ψ z at hrep
    rw [hz, hzero] at hrep
    exact hrep
  have hexists :
      ∃ q : Fin n → ℤ,
        ψ (z + TorusCharacters.imaginaryShift q) ≠ 0 := by
    by_contra hnone
    push Not at hnone
    apply hvalue
    simp only [complexDeckPeriodization, hnone, tsum_zero]
  obtain ⟨q, hq⟩ := hexists
  apply hp
  refine ⟨z + TorusCharacters.imaginaryShift q,
    subset_closure ((mem_support).mpr hq), ?_⟩
  rw [complexTorusCoverProjection_imaginaryShift, hz]

end TorusDeckCompactSupport

namespace TorusDeckGraphAdjoint

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault WeightedTorusBrascampLieb TorusDeckPeriodization TorusDeckCompactSupport
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem continuous_torusFunctionBarPartialRepresentative_of_periodic
    {n : ℕ}
    {F : TorusCharacters.LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q)) :
    Continuous (torusFunctionBarPartialRepresentative F) := by
  change Continuous
    (fun p : LogTorus n =>
      WithLp.toLp 2
        (fun j : Fin n => sourceTorusBarPartial F j p))
  exact (PiLp.continuous_toLp 2
    (fun _ : Fin n => ℂ)).comp
      (continuous_pi (fun j =>
        continuous_sourceTorusBarPartial hF hperiod j))

private theorem hasCompactSupport_torusFunctionBarPartialRepresentative_of_periodic
    {n : ℕ}
    (F : TorusCharacters.LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F
        (TorusCharacters.imaginaryShift q))
    (hcompact : HasCompactSupport (torusScalarRepresentative F)) :
    HasCompactSupport (torusFunctionBarPartialRepresentative F) := by
  classical
  let K : Set (LogTorus n) :=
    ⋃ j : Fin n, tsupport (sourceTorusBarPartial F j)
  have hK : IsCompact K :=
    isCompact_iUnion (fun j : Fin n =>
      hasCompactSupport_sourceTorusBarPartial F hperiod hcompact j)
  apply HasCompactSupport.intro hK
  intro p hp
  ext j
  change sourceTorusBarPartial F j p = 0
  by_contra hnonzero
  apply hp
  exact Set.mem_iUnion.mpr
    ⟨j, subset_closure ((mem_support).mpr hnonzero)⟩

private theorem complexDeckPeriodization_scalar_memLp
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ) :
    MemLp
      (torusScalarRepresentative (complexDeckPeriodization ψ)) 2
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  exact
    (continuous_torusScalarRepresentative_of_periodic
      (contDiff_complexDeckPeriodization hψ hψcompact).continuous
      (fun q => complexDeckPeriodization_periodic ψ q)).memLp_of_hasCompactSupport
      (hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
        hψcompact)

private theorem complexDeckPeriodization_barPartial_memLp
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ) :
    MemLp
      (torusFunctionBarPartialRepresentative
        (complexDeckPeriodization ψ)) 2
      (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  apply
    (continuous_torusFunctionBarPartialRepresentative_of_periodic
      ((contDiff_complexDeckPeriodization hψ hψcompact).of_le
        (by norm_num))
      (fun q => complexDeckPeriodization_periodic ψ q)).memLp_of_hasCompactSupport
  exact
    hasCompactSupport_torusFunctionBarPartialRepresentative_of_periodic
      (complexDeckPeriodization ψ)
      (fun q => complexDeckPeriodization_periodic ψ q)
      (hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
        hψcompact)

private theorem angularWeakDolbeaultResolvent_smoothGraphTest_adjoint
    {n : ℕ} (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hFcont : ContDiff ℝ 3 F)
    (hFperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hFcompact : HasCompactSupport (torusScalarRepresentative F))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    @inner ℂ (angularWeightedFormL2 a) _
      (WithLp.snd
        (angularWeakDolbeaultResolvent a f :
          angularDolbeaultGraphAmbient a))
      (angularBarPartialL2OfRepresentative a F hD) =
    @inner ℂ (angularWeightedScalarL2 a) _
      (f - angularWeakScalarResolventCLM a f)
      (angularScalarL2OfRepresentative a F hF) := by
  let v : angularDolbeaultGraph a :=
    ⟨WithLp.toLp 2
      (angularScalarL2OfRepresentative a F hF,
       angularBarPartialL2OfRepresentative a F hD),
      smoothAngularDolbeaultGraph_mem
        a F hFcont hFperiod hFcompact hF hD⟩
  exact angularWeakDolbeaultResolvent_form_adjoint a f v

private theorem angularWeakDolbeaultResolvent_smoothGraphTest_adjoint_integral
    {n : ℕ} (a : LogTorus n → ℝ)
    (f : angularWeightedScalarL2 a)
    (F : TorusCharacters.LogSpace n → ℂ)
    (hFcont : ContDiff ℝ 3 F)
    (hFperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (TorusCharacters.imaginaryShift q))
    (hFcompact : HasCompactSupport (torusScalarRepresentative F))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) q)
        (torusFunctionBarPartialRepresentative F q)
      ∂(angularWeightedTorusMeasure a)) =
    (∫ q : LogTorus n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f) q)
        (torusScalarRepresentative F q)
      ∂(angularWeightedTorusMeasure a)) := by
  have h := angularWeakDolbeaultResolvent_smoothGraphTest_adjoint
    a f F hFcont hFperiod hFcompact hF hD
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def] at h
  calc
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) q)
        (torusFunctionBarPartialRepresentative F q)
      ∂(angularWeightedTorusMeasure a)) =
      ∫ q : LogTorus n,
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          ((WithLp.snd
            (angularWeakDolbeaultResolvent a f :
              angularDolbeaultGraphAmbient a)) q)
          ((angularBarPartialL2OfRepresentative a F hD) q)
        ∂(angularWeightedTorusMeasure a) := by
      apply integral_congr_ae
      filter_upwards [hD.coeFn_toLp] with q hq
      unfold angularBarPartialL2OfRepresentative
      rw [hq]
    _ = ∫ q : LogTorus n,
        @inner ℂ ℂ _
          ((f - angularWeakScalarResolventCLM a f) q)
          ((angularScalarL2OfRepresentative a F hF) q)
        ∂(angularWeightedTorusMeasure a) := h
    _ = ∫ q : LogTorus n,
        @inner ℂ ℂ _
          ((f - angularWeakScalarResolventCLM a f) q)
          (torusScalarRepresentative F q)
        ∂(angularWeightedTorusMeasure a) := by
      apply integral_congr_ae
      filter_upwards [hF.coeFn_toLp] with q hq
      unfold angularScalarL2OfRepresentative
      rw [hq]

private theorem angularWeakDolbeaultResolvent_complexDeckPeriodization_adjoint_integral
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ) :
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) q)
        (torusFunctionBarPartialRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) =
    (∫ q : LogTorus n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f) q)
        (torusScalarRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) := by
  exact angularWeakDolbeaultResolvent_smoothGraphTest_adjoint_integral
    a f (complexDeckPeriodization ψ)
    (contDiff_complexDeckPeriodization hψ hψcompact)
    (fun q => complexDeckPeriodization_periodic ψ q)
    (hasCompactSupport_torusScalarRepresentative_complexDeckPeriodization
      hψcompact)
    (complexDeckPeriodization_scalar_memLp ha hψ hψcompact)
    (complexDeckPeriodization_barPartial_memLp ha hψ hψcompact)

end TorusDeckGraphAdjoint

namespace TorusDeckFundamentalCell

open Set Function Filter MeasureTheory Matrix
open WeightedTorusDistributionBridge TorusDeckPeriodization
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem angularFundamentalBox_integer_shift_eq_zero
    {n : ℕ} {b t : Space n}
    (ht : t ∈ angularFundamentalBox b)
    {q : Fin n → ℤ}
    (hq : (fun i : Fin n => t i + (q i : ℝ)) ∈
      angularFundamentalBox b) :
    q = 0 := by
  funext i
  have hti := ht i
  have hqi := hq i
  change b i < t i ∧ t i ≤ b i + 1 at hti
  change b i < t i + (q i : ℝ) ∧
    t i + (q i : ℝ) ≤ b i + 1 at hqi
  have hlow : (-1 : ℝ) < (q i : ℝ) := by
    linarith
  have hupp : (q i : ℝ) < 1 := by
    linarith
  have hlowz : (-1 : ℤ) < q i := by
    exact_mod_cast hlow
  have huppz : q i < (1 : ℤ) := by
    exact_mod_cast hupp
  have hz : q i = 0 := by
    omega
  simpa only [Pi.zero_apply] using hz

private theorem complexDeckPeriodization_eq_of_fundamentalCell
    {n : ℕ}
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hcell : tsupport ψ ⊆
      {z : TorusCharacters.LogSpace n |
        ((logarithmicCoordinatesEquiv n).symm z).2 ∈
          angularFundamentalBox b})
    (x t : Space n)
    (ht : t ∈ angularFundamentalBox b) :
    complexDeckPeriodization ψ
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) =
      ψ (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) := by
  classical
  unfold complexDeckPeriodization
  refine (tsum_eq_single (0 : Fin n → ℤ) ?_).trans ?_
  · intro q hq
    by_contra hnonzero
    have hs := hcell
      (subset_closure ((mem_support).mpr hnonzero))
    rw [← logarithmicPoint_integer_add] at hs
    have hshift :
        (fun i : Fin n => t i + (q i : ℝ)) ∈
          angularFundamentalBox b := by
      change
        ((logarithmicCoordinatesEquiv n).symm
          (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
            x (fun i : Fin n => t i + (q i : ℝ)))).2 ∈
            angularFundamentalBox b at hs
      simpa only [← logarithmicCoordinatesEquiv_apply,
        ContinuousLinearEquiv.symm_apply_apply] using hs
    exact hq (angularFundamentalBox_integer_shift_eq_zero ht hshift)
  · have hzero :
        TorusCharacters.imaginaryShift
          (0 : Fin n → ℤ) = 0 := by
      ext i
      simp only [TorusCharacters.imaginaryShift, Pi.zero_apply, Int.cast_zero, zero_mul]
    rw [hzero, add_zero]

end TorusDeckFundamentalCell

namespace TorusWeightedBaseAE

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert JetEnvelopeSlopeConvergence WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology ContDiff

private theorem angularWeightedTorus_ae_iff_base
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (P : LogTorus n → Prop) :
    (∀ᵐ p ∂(angularWeightedTorusMeasure a), P p) ↔
      ∀ᵐ p ∂(sourceTorusBaseMeasure n), P p := by
  rw [angularWeightedTorusMeasure]
  have hd : Measurable
      (fun p : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a p)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  rw [ae_withDensity_iff hd]
  constructor
  · intro h
    filter_upwards [h] with p hp
    exact hp
      (ENNReal.ofReal_pos.mpr
        (angularWeightedTorusDensity_pos a p)).ne'
  · intro h
    filter_upwards [h] with p hp _
    exact hp

private theorem angularWeightedTorus_ae_eq_base
    {n : ℕ} {E : Type*}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {f g : LogTorus n → E}
    (h : f =ᵐ[angularWeightedTorusMeasure a] g) :
    f =ᵐ[sourceTorusBaseMeasure n] g :=
  (angularWeightedTorus_ae_iff_base ha
    (fun p : LogTorus n => f p = g p)).mp h

private theorem angularWeightedLp_aestronglyMeasurable_base
    {n : ℕ} {E : Type*}
    [NormedAddCommGroup E]
    {a : LogTorus n → ℝ}
    (f : MeasureTheory.Lp E 2 (angularWeightedTorusMeasure a)) :
    AEStronglyMeasurable
      (fun p : LogTorus n => f p)
      (sourceTorusBaseMeasure n) := by
  exact (MeasureTheory.Lp.stronglyMeasurable f).aestronglyMeasurable

end TorusWeightedBaseAE

namespace BergmanJetStrictMixedLocalCore

open Set Function Filter MeasureTheory
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusVectorClosedGraphWeakBridge WeightedTorusDolbeault
open scoped BigOperators ENNReal InnerProductSpace Topology

private theorem angularMemLp_locallyIntegrable_base
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {g : LogTorus n → ℂ}
    (hg : MemLp g 2 (angularWeightedTorusMeasure a)) :
    LocallyIntegrable g (sourceTorusBaseMeasure n) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  apply locallyIntegrable_iff.mpr
  intro S hS
  have hweighted : IntegrableOn g S (angularWeightedTorusMeasure a) :=
    (hg.locallyIntegrable (by norm_num)).integrableOn_isCompact hS
  unfold angularWeightedTorusMeasure at hweighted
  change Integrable g
    (((sourceTorusBaseMeasure n).withDensity
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a q))).restrict S)
    at hweighted
  rw [restrict_withDensity hS.measurableSet] at hweighted
  have hdmeas :
      Measurable
        (fun q : LogTorus n =>
          ENNReal.ofReal (angularWeightedTorusDensity a q)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  have hdfinite :
      ∀ᵐ q : LogTorus n
        ∂((sourceTorusBaseMeasure n).restrict S),
        ENNReal.ofReal (angularWeightedTorusDensity a q) < ⊤ :=
    Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top)
  have hscaled :=
    (integrable_withDensity_iff_integrable_smul'
      hdmeas hdfinite).mp hweighted
  have hexp :
      IntegrableOn
        (fun q : LogTorus n =>
          (Real.exp (-a q) : ℂ) * g q)
        S (sourceTorusBaseMeasure n) := by
    apply hscaled.congr
    filter_upwards [] with q
    simp only [angularWeightedTorusDensity, (Real.exp_pos (-a q)).le, ENNReal.toReal_ofReal,
      Complex.real_smul, Complex.ofReal_exp, Complex.ofReal_neg]
  have hreciprocal :
      Continuous
        (fun q : LogTorus n => (Real.exp (a q) : ℂ)) :=
    Complex.continuous_ofReal.comp
      (Real.continuous_exp.comp ha)
  have hproduct :=
    hexp.mul_continuousOn hreciprocal.continuousOn hS
  refine hproduct.congr_fun ?_ hS.measurableSet
  intro q hq
  have hcancel :
      (Real.exp (-a q) : ℂ) *
        (Real.exp (a q) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero, Complex.ofReal_one]
  calc
    ((Real.exp (-a q) : ℂ) * g q) *
        (Real.exp (a q) : ℂ) =
      ((Real.exp (-a q) : ℂ) *
        (Real.exp (a q) : ℂ)) * g q := by
          ring
    _ = g q := by rw [hcancel, one_mul]

private theorem angularWeightedScalarL2_locallyIntegrable_base
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (f : angularWeightedScalarL2 a) :
    LocallyIntegrable
      (fun q : LogTorus n => f q)
      (sourceTorusBaseMeasure n) :=
  angularMemLp_locallyIntegrable_base ha
    (MeasureTheory.Lp.memLp f)

private theorem angularWeightedFormCoordinate_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (i : Fin n) :
    MemLp
      (fun q : LogTorus n =>
        (W q : EuclideanSpace ℂ (Fin n)) i)
      2 (angularWeightedTorusMeasure a) := by
  simpa only [formCoordinateCLM, EuclideanSpace.coe_proj, comp_def] using
    (formCoordinateCLM i).comp_memLp'
      (MeasureTheory.Lp.memLp W)

private theorem angularWeightedFormCoordinate_locallyIntegrable_base
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (W : angularWeightedFormL2 a) (i : Fin n) :
    LocallyIntegrable
      (fun q : LogTorus n =>
        (W q : EuclideanSpace ℂ (Fin n)) i)
      (sourceTorusBaseMeasure n) :=
  angularMemLp_locallyIntegrable_base ha
    (angularWeightedFormCoordinate_memLp W i)

private theorem angularWeightedScalarCoverLift_locallyIntegrable
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (f : angularWeightedScalarL2 a) :
    LocallyIntegrable
      (complexTorusCoverLift
        (fun q : LogTorus n => f q))
      (volume : Measure (LogSpace n)) := by
  apply complexTorusCoverLift_locallyIntegrable
  simpa only [unweightedTorusMeasure, sourceTorusBaseMeasure] using
    angularWeightedScalarL2_locallyIntegrable_base ha f

private theorem angularWeightedFormCoordinateCoverLift_locallyIntegrable
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (W : angularWeightedFormL2 a) (i : Fin n) :
    LocallyIntegrable
      (complexTorusCoverLift
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) i))
      (volume : Measure (LogSpace n)) := by
  apply complexTorusCoverLift_locallyIntegrable
  simpa only [unweightedTorusMeasure, sourceTorusBaseMeasure] using
    angularWeightedFormCoordinate_locallyIntegrable_base
      ha W i

private theorem angularMemLp_restrict_base_isCompact
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {g : LogTorus n → ℂ}
    (hg : MemLp g 2 (angularWeightedTorusMeasure a))
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    MemLp g 2 ((sourceTorusBaseMeasure n).restrict S) := by
  have hmeas :
      AEStronglyMeasurable g
        ((sourceTorusBaseMeasure n).restrict S) :=
    (angularMemLp_locallyIntegrable_base
      ha hg).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hsq :
      Integrable
        (fun q : LogTorus n => ‖g q‖ ^ 2)
        (angularWeightedTorusMeasure a) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hg.aestronglyMeasurable).mp hg
  have hweighted := hsq.integrableOn (s := S)
  unfold angularWeightedTorusMeasure at hweighted
  change Integrable
    (fun q : LogTorus n => ‖g q‖ ^ 2)
    (((sourceTorusBaseMeasure n).withDensity
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a q))).restrict S)
    at hweighted
  rw [restrict_withDensity hS.measurableSet] at hweighted
  have hdmeas :
      Measurable
        (fun q : LogTorus n =>
          ENNReal.ofReal (angularWeightedTorusDensity a q)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  have hdfinite :
      ∀ᵐ q : LogTorus n
        ∂((sourceTorusBaseMeasure n).restrict S),
        ENNReal.ofReal (angularWeightedTorusDensity a q) < ⊤ :=
    Filter.Eventually.of_forall
      (fun _ => ENNReal.ofReal_lt_top)
  have hscaled :=
    (integrable_withDensity_iff_integrable_smul'
      hdmeas hdfinite).mp hweighted
  have hexp :
      IntegrableOn
        (fun q : LogTorus n =>
          Real.exp (-a q) * ‖g q‖ ^ 2)
        S (sourceTorusBaseMeasure n) := by
    apply hscaled.congr
    filter_upwards [] with q
    simp only [angularWeightedTorusDensity, (Real.exp_pos (-a q)).le, ENNReal.toReal_ofReal,
      smul_eq_mul]
  have hreciprocal :
      Continuous
        (fun q : LogTorus n => Real.exp (a q)) :=
    Real.continuous_exp.comp ha
  have hproduct :=
    hexp.mul_continuousOn hreciprocal.continuousOn hS
  refine hproduct.congr_fun ?_ hS.measurableSet
  intro q hq
  have hcancel :
      Real.exp (-a q) * Real.exp (a q) = 1 := by
    rw [← Real.exp_add]
    simp only [neg_add_cancel, Real.exp_zero]
  calc
    (Real.exp (-a q) * ‖g q‖ ^ 2) * Real.exp (a q) =
      (Real.exp (-a q) * Real.exp (a q)) * ‖g q‖ ^ 2 := by
        ring
    _ = ‖g q‖ ^ 2 := by rw [hcancel, one_mul]

private theorem angularMemLp_normSquared_locallyIntegrable_base
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {g : LogTorus n → ℂ}
    (hg : MemLp g 2 (angularWeightedTorusMeasure a)) :
    LocallyIntegrable
      (fun q : LogTorus n => ((‖g q‖ ^ 2 : ℝ) : ℂ))
      (sourceTorusBaseMeasure n) := by
  apply locallyIntegrable_iff.mpr
  intro S hS
  have hgS := angularMemLp_restrict_base_isCompact ha hg hS
  have hsq :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hgS.aestronglyMeasurable).mp hgS
  exact hsq.ofReal (𝕜 := ℂ)

private theorem angularWeightedScalarCoverLift_memLp_restrict_volume_isCompact
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    {S : Set (LogSpace n)} (hS : IsCompact S) :
    MemLp
      (complexTorusCoverLift
        (fun q : LogTorus n => f q))
      2 ((volume : Measure (LogSpace n)).restrict S) := by
  have hmeas :
      AEStronglyMeasurable
        (complexTorusCoverLift
          (fun q : LogTorus n => f q))
        ((volume : Measure (LogSpace n)).restrict S) :=
    (angularWeightedScalarCoverLift_locallyIntegrable
      ha f).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hbase :=
    angularMemLp_normSquared_locallyIntegrable_base
      ha (MeasureTheory.Lp.memLp f)
  have hcover :=
    complexTorusCoverLift_locallyIntegrable
      (show
        LocallyIntegrable
          (fun q : LogTorus n => ((‖f q‖ ^ 2 : ℝ) : ℂ))
          (unweightedTorusMeasure n) by
        simpa only [Complex.ofReal_pow, unweightedTorusMeasure, sourceTorusBaseMeasure]
          using hbase)
  have hsq := (hcover.integrableOn_isCompact hS).re
  apply hsq.congr
  filter_upwards [] with z
  change
    (((‖f (complexTorusCoverProjection n z)‖ ^ 2 : ℝ) : ℂ)).re =
      ‖f (complexTorusCoverProjection n z)‖ ^ 2
  exact Complex.ofReal_re _

private theorem angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (W : angularWeightedFormL2 a) (i : Fin n)
    {S : Set (LogSpace n)} (hS : IsCompact S) :
    MemLp
      (complexTorusCoverLift
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) i))
      2 ((volume : Measure (LogSpace n)).restrict S) := by
  have hmeas :
      AEStronglyMeasurable
        (complexTorusCoverLift
          (fun q : LogTorus n =>
            (W q : EuclideanSpace ℂ (Fin n)) i))
        ((volume : Measure (LogSpace n)).restrict S) :=
    (angularWeightedFormCoordinateCoverLift_locallyIntegrable
      ha W i).aestronglyMeasurable.mono_measure
        Measure.restrict_le_self
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm hmeas).mpr
  have hbase :=
    angularMemLp_normSquared_locallyIntegrable_base
      ha (angularWeightedFormCoordinate_memLp W i)
  have hcover :=
    complexTorusCoverLift_locallyIntegrable
      (show
        LocallyIntegrable
          (fun q : LogTorus n =>
            ((‖(W q : EuclideanSpace ℂ (Fin n)) i‖ ^ 2 : ℝ) : ℂ))
          (unweightedTorusMeasure n) by
        simpa only [Complex.ofReal_pow, unweightedTorusMeasure, sourceTorusBaseMeasure]
          using hbase)
  have hsq := (hcover.integrableOn_isCompact hS).re
  apply hsq.congr
  filter_upwards [] with z
  change
    (((‖(W (complexTorusCoverProjection n z) :
      EuclideanSpace ℂ (Fin n)) i‖ ^ 2 : ℝ) : ℂ)).re =
      ‖(W (complexTorusCoverProjection n z) :
        EuclideanSpace ℂ (Fin n)) i‖ ^ 2
  exact Complex.ofReal_re _

end BergmanJetStrictMixedLocalCore

namespace MatrixTorusDolbeaultGraph

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusMatrixSquareRootContinuity
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate
  Matrix.Norms.L2Operator ContDiff

private def angularMatrixSquareRoot {n : ℕ}
    (H : LogTorus n → Matrix (Fin n) (Fin n) ℂ)
    (q : LogTorus n) : Matrix (Fin n) (Fin n) ℂ :=
  CFC.sqrt (H q)

private theorem angularMatrixSquareRoot_posDef {n : ℕ}
    {H : LogTorus n → Matrix (Fin n) (Fin n) ℂ}
    (hH : ∀ q, (H q).PosDef) (q : LogTorus n) :
    (angularMatrixSquareRoot H q).PosDef := by
  exact (hH q).isStrictlyPositive.sqrt.posDef

private theorem continuous_angularMatrixSquareRoot {n : ℕ}
    {H : LogTorus n → Matrix (Fin n) (Fin n) ℂ}
    (hcont : Continuous H)
    (hH : ∀ q, (H q).PosDef) :
    Continuous (angularMatrixSquareRoot H) := by
  exact continuous_complexMatrixSquareRoot hcont
    (fun q => (hH q).posSemidef)

private theorem continuous_angularMatrixSquareRoot_inverse {n : ℕ}
    {H : LogTorus n → Matrix (Fin n) (Fin n) ℂ}
    (hcont : Continuous H)
    (hH : ∀ q, (H q).PosDef) :
    Continuous (fun q => (angularMatrixSquareRoot H q)⁻¹) := by
  exact continuous_complexMatrixSquareRoot_inverse hcont hH

end MatrixTorusDolbeaultGraph

namespace TorusDeckWeightedUnfolding

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open WeightedTorusBochner TorusWeightedBaseAE
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold

private theorem angularWeightedTorus_integral_eq_realFundamentalCell
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    {G : LogTorus n → ℂ}
    (hG : AEStronglyMeasurable G (sourceTorusBaseMeasure n)) :
    (∫ q : LogTorus n, G q ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a G
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
  let H : LogTorus n → ℂ :=
    angularUnweightedTorusIntegrand a G
  have hH : AEStronglyMeasurable H (sourceTorusBaseMeasure n) := by
    exact ((Complex.continuous_ofReal.comp
      (continuous_angularWeightedTorusDensity ha)).aestronglyMeasurable).mul
      hG
  have hp := realTorusCoverProjection_measurePreserving
    (volume : Measure (Space n)) b
  have hmap :
      Measure.map (realTorusCoverProjection n)
        (realFundamentalCellMeasure b) =
        sourceTorusBaseMeasure n := by
    simpa only [realFundamentalCellMeasure, sourceTorusBaseMeasure]
      using hp.map_eq
  calc
    (∫ q : LogTorus n, G q ∂(angularWeightedTorusMeasure a)) =
      ∫ q : LogTorus n, H q
        ∂(sourceTorusBaseMeasure n) :=
      (integral_angularUnweightedTorusIntegrand_eq_weighted ha G).symm
    _ = ∫ q : LogTorus n, H q
        ∂(Measure.map (realTorusCoverProjection n)
          (realFundamentalCellMeasure b)) := by rw [hmap]
    _ = ∫ p : Space n × Space n,
        H (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
      apply MeasureTheory.integral_map
        hp.measurable.aemeasurable
      rw [hmap]
      exact hH

private theorem angularWeightedScalarL2_inner_integral_eq_realFundamentalCell
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    (f : angularWeightedScalarL2 a)
    {G : LogTorus n → ℂ}
    (hG : Continuous G) :
    (∫ q : LogTorus n,
      @inner ℂ ℂ _ (f q) (G q)
        ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a
          (fun q : LogTorus n => @inner ℂ ℂ _ (f q) (G q))
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
  apply angularWeightedTorus_integral_eq_realFundamentalCell ha b
  exact (angularWeightedLp_aestronglyMeasurable_base f).inner
    hG.aestronglyMeasurable

private theorem angularWeightedFormL2_inner_integral_eq_realFundamentalCell
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    (W : angularWeightedFormL2 a)
    {V : LogTorus n → EuclideanSpace ℂ (Fin n)}
    (hV : Continuous V) :
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q) (V q)
        ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a
          (fun q : LogTorus n =>
            @inner ℂ (EuclideanSpace ℂ (Fin n)) _ (W q) (V q))
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
  apply angularWeightedTorus_integral_eq_realFundamentalCell ha b
  exact (angularWeightedLp_aestronglyMeasurable_base W).inner
    hV.aestronglyMeasurable

private theorem exists_finite_complex_fundamental_test_partition
    {n : ℕ}
    {ψ : LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ) :
    ∃ (s : Finset (LogSpace n))
      (χ : LogSpace n → LogSpace n → ℝ),
      (∀ i, ContDiff ℝ ∞ (χ i)) ∧
      (∀ i, tsupport (χ i) ⊆
        coverFundamentalInterior (coverCenteredFundamentalBase i)) ∧
      (∀ z : LogSpace n,
        ψ z = ∑ i ∈ s, (χ i z : ℂ) * ψ z) := by
  classical
  let E := LogSpace n
  let U : E → Set E := fun z =>
    coverFundamentalInterior (coverCenteredFundamentalBase z)
  have hUopen : ∀ z : E, IsOpen (U z) := fun z =>
    coverFundamentalInterior_isOpen (coverCenteredFundamentalBase z)
  have hUcover : tsupport ψ ⊆ ⋃ z : E, U z := by
    intro z _
    exact Set.mem_iUnion_of_mem z
      (self_mem_coverFundamentalInterior z)
  obtain ⟨ρ, hρ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate
      (I := 𝓘(ℝ, E)) (isClosed_tsupport ψ) U hUopen hUcover
  have hfinite :
      {i : E | (Function.support (ρ i) ∩ tsupport ψ).Nonempty}.Finite :=
    ρ.locallyFinite.finite_nonempty_inter_compact hψcompact
  let s : Finset E := hfinite.toFinset
  refine ⟨s, fun i z => ρ i z, ?_, ?_, ?_⟩
  · intro i
    exact (ρ i).contMDiff.contDiff
  · intro i
    exact hρ i
  · intro z
    by_cases hz : z ∈ tsupport ψ
    · have hsubset : ρ.finsupport z ⊆ s := by
        intro i hi
        apply hfinite.mem_toFinset.mpr
        refine ⟨z, ?_, hz⟩
        exact (ρ.mem_finsupport z).mp hi
      have hone := ρ.sum_finsupport' z hz hsubset
      have honeC : (∑ i ∈ s, (ρ i z : ℂ)) = 1 := by
        exact_mod_cast hone
      calc
        ψ z = (1 : ℂ) * ψ z := by simp only [one_mul]
        _ = (∑ i ∈ s, (ρ i z : ℂ)) * ψ z := by rw [honeC]
        _ = ∑ i ∈ s, (ρ i z : ℂ) * ψ z := by
          rw [Finset.sum_mul]
    · have hz0 : ψ z = 0 :=
        image_eq_zero_of_notMem_tsupport hz
      simp only [hz0, mul_zero, Finset.sum_const_zero]

end TorusDeckWeightedUnfolding

namespace TorusDeckFullCellDerivative

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge TorusDeckPeriodization TorusDeckFundamentalCell
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff

private theorem complexDeckPeriodization_eventuallyEq_on_fundamentalCell
    {n : ℕ}
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b)
    (x t : Space n)
    (ht : t ∈ angularFundamentalBox b) :
    complexDeckPeriodization ψ =ᶠ[
      𝓝 (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t)] ψ := by
  classical
  let z : TorusCharacters.LogSpace n :=
    JointHolomorphicLaurentFourierCompatibility.logarithmicPoint x t
  have hnot : ∀ q : Fin n → ℤ,
      q ≠ 0 →
        z + TorusCharacters.imaginaryShift q ∉ tsupport ψ := by
    intro q hq hzsupport
    have hinside := hcell hzsupport
    dsimp [z] at hinside
    rw [← logarithmicPoint_integer_add] at hinside
    have hshift :
        (fun i : Fin n => t i + (q i : ℝ)) ∈
          angularFundamentalBox b := by
      have hinner :
          (fun i : Fin n => t i + (q i : ℝ)) ∈
            angularFundamentalInterior b := by
        change
          ((logarithmicCoordinatesEquiv n).symm
            (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
              x (fun i : Fin n => t i + (q i : ℝ)))).2 ∈
              angularFundamentalInterior b at hinside
        simpa only [← logarithmicCoordinatesEquiv_apply,
          ContinuousLinearEquiv.symm_apply_apply] using hinside
      intro i
      exact ⟨(hinner i).1, (hinner i).2.le⟩
    exact hq (angularFundamentalBox_integer_shift_eq_zero ht hshift)
  have hvanish : ∀ q : Fin n → ℤ,
      q ≠ 0 →
        ∀ᶠ w : TorusCharacters.LogSpace n in 𝓝 z,
          ψ (w + TorusCharacters.imaginaryShift q) = 0 := by
    intro q hq
    have hzero := (notMem_tsupport_iff_eventuallyEq).mp (hnot q hq)
    have htranslate :
        Tendsto
          (fun w : TorusCharacters.LogSpace n =>
            w + TorusCharacters.imaginaryShift q)
          (𝓝 z)
          (𝓝 (z + TorusCharacters.imaginaryShift q)) :=
      (continuous_id.add continuous_const).continuousAt
    filter_upwards [htranslate hzero] with w hw
    simpa only [Pi.zero_apply, preimage_ofPred_eq, mem_ofPred_eq] using hw
  obtain ⟨s, hs⟩ :=
    exists_finite_complexDeckPeriodization_support_near hψcompact z
  have hall :
      ∀ᶠ w : TorusCharacters.LogSpace n in 𝓝 z,
        ∀ q ∈ s, q ≠ 0 →
          ψ (w + TorusCharacters.imaginaryShift q) = 0 := by
    apply (Filter.eventually_all_finset s).mpr
    intro q _
    by_cases hq : q = 0
    · exact Filter.Eventually.of_forall
        (fun _ hne => (hne hq).elim)
    · exact (hvanish q hq).mono (fun _ hw _ => hw)
  have hdeckzero :
      TorusCharacters.imaginaryShift
        (0 : Fin n → ℤ) = 0 := by
    ext i
    simp only [TorusCharacters.imaginaryShift, Pi.zero_apply, Int.cast_zero, zero_mul]
  change complexDeckPeriodization ψ =ᶠ[𝓝 z] ψ
  filter_upwards [hs, hall] with w hw hwall
  change
    (∑' q : Fin n → ℤ,
      ψ (w + TorusCharacters.imaginaryShift q)) = ψ w
  calc
    (∑' q : Fin n → ℤ,
      ψ (w + TorusCharacters.imaginaryShift q)) =
      ∑ q ∈ s,
        ψ (w + TorusCharacters.imaginaryShift q) :=
      tsum_eq_sum (fun q hq => hw q hq)
    _ = ψ (w + TorusCharacters.imaginaryShift
      (0 : Fin n → ℤ)) := by
      exact Finset.sum_eq_single (0 : Fin n → ℤ)
        (fun q hqs hq => hwall q hqs hq)
        (fun hzero => hw (0 : Fin n → ℤ) hzero)
    _ = ψ w := by
      rw [hdeckzero, add_zero]

private theorem barPartial_complexDeckPeriodization_eq_on_fundamentalCell
    {n : ℕ}
    {b : Space n}
    {ψ : TorusCharacters.LogSpace n → ℂ}
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b)
    (x t : Space n)
    (ht : t ∈ angularFundamentalBox b)
    (j : Fin n) :
    barPartialCoordinate (complexDeckPeriodization ψ)
      (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
        x t) j =
      barPartialCoordinate ψ
        (JointHolomorphicLaurentFourierCompatibility.logarithmicPoint
          x t) j := by
  have hd :=
    (complexDeckPeriodization_eventuallyEq_on_fundamentalCell
      hψcompact hcell x t ht).fderiv_eq (𝕜 := ℝ)
  unfold barPartialCoordinate
  rw [hd]

end TorusDeckFullCellDerivative

namespace MatrixTorusCompactGreen

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge
open WeightedTorusDolbeault TorusWeightedBaseAE
open scoped BigOperators ENNReal InnerProductSpace Topology
  MatrixOrder ComplexOrder ComplexConjugate ContDiff

private def realAngularWeightedFundamentalCellMeasure {n : ℕ}
    (a : LogTorus n → ℝ) (b : Space n) :
    Measure (Space n × Space n) :=
  (realFundamentalCellMeasure b).withDensity
    (fun p => ENNReal.ofReal
      (angularWeightedTorusDensity a (realTorusCoverProjection n p)))

private theorem continuous_realTorusCoverProjection (n : ℕ) :
    Continuous (realTorusCoverProjection n) := by
  change Continuous (fun p : Space n × Space n =>
    (p.1, angularCoverProjection n p.2))
  exact (continuous_fst : Continuous
    (fun p : Space n × Space n => p.1)).prodMk
      ((continuous_angularCoverProjection n).comp
        (continuous_snd : Continuous
          (fun p : Space n × Space n => p.2)))

private theorem realAngularWeightedFundamentalCell_measurePreserving
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (b : Space n) :
    MeasurePreserving (realTorusCoverProjection n)
      (realAngularWeightedFundamentalCellMeasure a b)
      (angularWeightedTorusMeasure a) := by
  have hp : MeasurePreserving (realTorusCoverProjection n)
      (realFundamentalCellMeasure b) (sourceTorusBaseMeasure n) := by
    simpa only [realFundamentalCellMeasure, sourceTorusBaseMeasure] using
      realTorusCoverProjection_measurePreserving
        (volume : Measure (Space n)) b
  refine ⟨hp.measurable, ?_⟩
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hp.measurable hs]
  change
    (realFundamentalCellMeasure b).withDensity
      (fun p => ENNReal.ofReal
        (angularWeightedTorusDensity a
          (realTorusCoverProjection n p)))
        (realTorusCoverProjection n ⁻¹' s) =
      (sourceTorusBaseMeasure n).withDensity
        (fun q => ENNReal.ofReal
          (angularWeightedTorusDensity a q)) s
  rw [MeasureTheory.withDensity_apply _ (hp.measurable hs),
    MeasureTheory.withDensity_apply _ hs]
  exact hp.setLIntegral_comp_preimage hs
    (ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable)

private abbrev angularWeightedCellScalarL2 {n : ℕ}
    (a : LogTorus n → ℝ) (b : Space n) :=
  MeasureTheory.Lp ℂ 2 (realAngularWeightedFundamentalCellMeasure a b)

private abbrev angularWeightedCellFormL2 {n : ℕ}
    (a : LogTorus n → ℝ) (b : Space n) :=
  MeasureTheory.Lp (EuclideanSpace ℂ (Fin n)) 2
    (realAngularWeightedFundamentalCellMeasure a b)

private def angularScalarFundamentalLiftLI {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) :
    angularWeightedScalarL2 a →ₗᵢ[ℂ]
      angularWeightedCellScalarL2 a b :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (realTorusCoverProjection n)
    (realAngularWeightedFundamentalCell_measurePreserving ha b)

private def angularFormFundamentalLiftLI {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) :
    angularWeightedFormL2 a →ₗᵢ[ℂ]
      angularWeightedCellFormL2 a b :=
  MeasureTheory.Lp.compMeasurePreservingₗᵢ ℂ
    (realTorusCoverProjection n)
    (realAngularWeightedFundamentalCell_measurePreserving ha b)

private theorem angularScalarFundamentalLiftLI_ae_eq {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) (f : angularWeightedScalarL2 a) :
    (fun p : Space n × Space n =>
      angularScalarFundamentalLiftLI ha b f p)
        =ᵐ[realAngularWeightedFundamentalCellMeasure a b]
      (fun p => f (realTorusCoverProjection n p)) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (realAngularWeightedFundamentalCell_measurePreserving ha b)

private theorem angularFormFundamentalLiftLI_ae_eq {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) (f : angularWeightedFormL2 a) :
    (fun p : Space n × Space n =>
      angularFormFundamentalLiftLI ha b f p)
        =ᵐ[realAngularWeightedFundamentalCellMeasure a b]
      (fun p => f (realTorusCoverProjection n p)) := by
  exact MeasureTheory.Lp.coeFn_compMeasurePreserving f
    (realAngularWeightedFundamentalCell_measurePreserving ha b)

private theorem realAngularWeightedFundamentalCellMeasure_isLocallyFinite
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (b : Space n) :
    IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) := by
  let : IsLocallyFiniteMeasure (realFundamentalCellMeasure b) :=
    realFundamentalCellMeasure_isLocallyFinite b
  exact IsLocallyFiniteMeasure.withDensity_ofReal
    ((continuous_angularWeightedTorusDensity ha).comp
      (continuous_realTorusCoverProjection n))

private def inverseAngularCoverWeight {n : ℕ}
    (a : LogTorus n → ℝ)
    (p : Space n × Space n) : ℂ :=
  (Real.exp (a (realTorusCoverProjection n p)) : ℂ)

private theorem continuous_inverseAngularCoverWeight {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a) :
    Continuous (inverseAngularCoverWeight a) := by
  exact Complex.continuous_ofReal.comp
    (Real.continuous_exp.comp
      (ha.comp (continuous_realTorusCoverProjection n)))

private def angularWeightedCellAdjointScalarTest {n : ℕ}
    (a : LogTorus n → ℝ) (ψ : LogSpace n → ℝ)
    (j : Fin n) (p : Space n × Space n) : ℂ :=
  inverseAngularCoverWeight a p *
    coverAdjointScalarTest ψ j (logarithmicCoordinatesEquiv n p)

private def angularWeightedCellAdjointVectorTest {n : ℕ}
    (a : LogTorus n → ℝ) (ψ : LogSpace n → ℝ)
    (j : Fin n) (p : Space n × Space n) :
    EuclideanSpace ℂ (Fin n) :=
  inverseAngularCoverWeight a p •
    coverAdjointVectorTest ψ j (logarithmicCoordinatesEquiv n p)

private theorem continuous_angularWeightedCellAdjointScalarTest {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (j : Fin n) :
    Continuous (angularWeightedCellAdjointScalarTest a ψ j) := by
  exact (continuous_inverseAngularCoverWeight ha).mul
    ((continuous_coverAdjointScalarTest hψ j).comp
      (logarithmicCoordinatesEquiv n).continuous)

private theorem continuous_angularWeightedCellAdjointVectorTest {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (j : Fin n) :
    Continuous (angularWeightedCellAdjointVectorTest a ψ j) := by
  exact (continuous_inverseAngularCoverWeight ha).smul
    ((continuous_coverAdjointVectorTest hψ.continuous j).comp
      (logarithmicCoordinatesEquiv n).continuous)

private theorem compactSupport_angularWeightedCellAdjointScalarTest {n : ℕ}
    (a : LogTorus n → ℝ) {ψ : LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (angularWeightedCellAdjointScalarTest a ψ j) := by
  have hcomp : HasCompactSupport
      (fun p : Space n × Space n =>
        coverAdjointScalarTest ψ j
          (logarithmicCoordinatesEquiv n p)) := by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph, comp_def] using
      (compactSupport_coverAdjointScalarTest hψcompact j).comp_homeomorph
        (logarithmicCoordinatesEquiv n).toHomeomorph
  exact hcomp.mul_left

private theorem compactSupport_angularWeightedCellAdjointVectorTest {n : ℕ}
    (a : LogTorus n → ℝ) {ψ : LogSpace n → ℝ}
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    HasCompactSupport (angularWeightedCellAdjointVectorTest a ψ j) := by
  have hcomp : HasCompactSupport
      (fun p : Space n × Space n =>
        ψ (logarithmicCoordinatesEquiv n p)) := by
    simpa only [ContinuousLinearEquiv.coe_toHomeomorph, comp_def] using
      hψcompact.comp_homeomorph
        (logarithmicCoordinatesEquiv n).toHomeomorph
  refine hcomp.mono ?_
  intro p hp
  exact mt (fun h => by
    simp only [angularWeightedCellAdjointVectorTest, coverAdjointVectorTest, h, Complex.ofReal_zero,
      mul_zero, smul_eq_zero, PiLp.single_eq_zero_iff, or_true]) hp

private def angularWeightedCellAdjointVectorL2 {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    angularWeightedCellFormL2 a b := by
  letI : IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) :=
    realAngularWeightedFundamentalCellMeasure_isLocallyFinite ha b
  exact ((continuous_angularWeightedCellAdjointVectorTest
      ha hψ j).memLp_of_hasCompactSupport
      (μ := realAngularWeightedFundamentalCellMeasure a b)
      (compactSupport_angularWeightedCellAdjointVectorTest
        a hψcompact j)).toLp
      (angularWeightedCellAdjointVectorTest a ψ j)

private theorem angularWeightedCellAdjointVectorL2_ae_eq {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) {ψ : LogSpace n → ℝ}
    (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (fun p : Space n × Space n =>
      angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j p)
        =ᵐ[realAngularWeightedFundamentalCellMeasure a b]
      angularWeightedCellAdjointVectorTest a ψ j := by
  let : IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) :=
    realAngularWeightedFundamentalCellMeasure_isLocallyFinite ha b
  simpa only [angularWeightedCellAdjointVectorL2] using
    (MeasureTheory.MemLp.coeFn_toLp
      ((continuous_angularWeightedCellAdjointVectorTest
        ha hψ j).memLp_of_hasCompactSupport
        (μ := realAngularWeightedFundamentalCellMeasure a b)
        (compactSupport_angularWeightedCellAdjointVectorTest
          a hψcompact j)))

private theorem angularWeight_mul_inverseAngularCoverWeight {n : ℕ}
    (a : LogTorus n → ℝ)
    (p : Space n × Space n) :
    ((ENNReal.ofReal
      (angularWeightedTorusDensity a
        (realTorusCoverProjection n p))).toReal : ℂ) *
      inverseAngularCoverWeight a p = 1 := by
  simp only [angularWeightedTorusDensity,
    ENNReal.toReal_ofReal (Real.exp_pos _).le,
    inverseAngularCoverWeight]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  simp only [neg_add_cancel, Real.exp_zero, Complex.ofReal_one]

private theorem angularWeightedCellVector_inner_eq_unweighted {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (f : angularWeightedFormL2 a) :
    @inner ℂ (angularWeightedCellFormL2 a b) _
      (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
      (angularFormFundamentalLiftLI ha b f) =
        ∫ p : Space n × Space n,
          (2 : ℂ) *
            (((f (realTorusCoverProjection n p) :
              EuclideanSpace ℂ (Fin n)) j) *
                (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
          ∂(realFundamentalCellMeasure b) := by
  calc
    _ = ∫ p : Space n × Space n,
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (angularWeightedCellAdjointVectorTest a ψ j p)
          (f (realTorusCoverProjection n p))
        ∂(realAngularWeightedFundamentalCellMeasure a b) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [angularWeightedCellAdjointVectorL2_ae_eq
          ha b hψ hψcompact j,
         angularFormFundamentalLiftLI_ae_eq ha b f]
        with p ht hf
      rw [ht, hf]
    _ = _ := by
      have hd : Measurable
          (fun p : Space n × Space n =>
            ENNReal.ofReal
              (angularWeightedTorusDensity a
                (realTorusCoverProjection n p))) :=
        ENNReal.measurable_ofReal.comp
          ((continuous_angularWeightedTorusDensity ha).comp
            (continuous_realTorusCoverProjection n)).measurable
      rw [realAngularWeightedFundamentalCellMeasure,
        integral_withDensity_eq_integral_toReal_smul
          hd (Filter.Eventually.of_forall
            (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with p
      have hc := angularWeight_mul_inverseAngularCoverWeight a p
      unfold angularWeightedCellAdjointVectorTest coverAdjointVectorTest
      rw [inner_smul_left, EuclideanSpace.inner_single_left]
      simp only [inverseAngularCoverWeight,
        map_mul, map_ofNat, Complex.conj_ofReal,
        Complex.real_smul] at hc ⊢
      calc
        _ = (((ENNReal.ofReal
              (angularWeightedTorusDensity a
                (realTorusCoverProjection n p))).toReal : ℂ) *
              (Real.exp
                (a (realTorusCoverProjection n p)) : ℂ)) *
            ((2 : ℂ) *
              (((f (realTorusCoverProjection n p) :
                EuclideanSpace ℂ (Fin n)) j) *
                  (ψ (logarithmicCoordinatesEquiv n p) : ℂ))) := by
            ring
        _ = _ := by rw [hc, one_mul]

private theorem angularWeightedCellVector_inner_eq_jacobian_cover {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (f : angularWeightedFormL2 a) :
    @inner ℂ (angularWeightedCellFormL2 a b) _
      (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
      (angularFormFundamentalLiftLI ha b f) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          (2 : ℂ) *
            (complexTorusCoverLift
              (fun q : LogTorus n =>
                (f q : EuclideanSpace ℂ (Fin n)) j) z *
                (ψ z : ℂ))
          ∂(volume : Measure (LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        (2 : ℂ) *
          (((f (realTorusCoverProjection n p) :
            EuclideanSpace ℂ (Fin n)) j) *
              (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
        ∂(realFundamentalCellMeasure b) :=
      angularWeightedCellVector_inner_eq_unweighted
        ha b hψ hψcompact j f
    _ = ∫ p : Space n × Space n,
        (2 : ℂ) *
          (complexTorusCoverLift
            (fun q : LogTorus n =>
              (f q : EuclideanSpace ℂ (Fin n)) j)
              (logarithmicCoordinatesEquiv n p) *
            (ψ (logarithmicCoordinatesEquiv n p) : ℂ))
        ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold complexTorusCoverLift complexTorusCoverProjection
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := by
      apply realFundamentalCell_integral_eq_coverJacobian b
        (fun z =>
          (2 : ℂ) *
            (complexTorusCoverLift
              (fun q : LogTorus n =>
                (f q : EuclideanSpace ℂ (Fin n)) j) z *
                  (ψ z : ℂ)))
      intro p hp
      rw [(coverTest_zero_outside_fundamentalCell hcell p hp).1]
      simp only [Complex.ofReal_zero, mul_zero]

private theorem angularWeightedTorus_complexCoverLift_ae_eq {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    {f g : LogTorus n → ℂ}
    (h : f =ᵐ[angularWeightedTorusMeasure a] g) :
    complexTorusCoverLift f =ᵐ[(volume : Measure (LogSpace n))]
      complexTorusCoverLift g := by
  apply complexTorusCoverLift_ae_eq
  simpa only [unweightedTorusMeasure, sourceTorusBaseMeasure] using
    angularWeightedTorus_ae_eq_base ha h

private theorem angularFormGraphGenerator_complexCoverLift_ae_eq
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (F : LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) (j : Fin n) :
    complexTorusCoverLift
      (fun q : LogTorus n =>
        (angularBarPartialL2OfRepresentative a F hD q :
          EuclideanSpace ℂ (Fin n)) j)
        =ᵐ[(volume : Measure (LogSpace n))]
      (fun z => barPartialCoordinate F z j) := by
  have hrow := hD.coeFn_toLp
  have hj :
      (fun q : LogTorus n =>
        (angularBarPartialL2OfRepresentative a F hD q :
          EuclideanSpace ℂ (Fin n)) j)
        =ᵐ[angularWeightedTorusMeasure a]
      (fun q : LogTorus n =>
        (torusFunctionBarPartialRepresentative F q :
          EuclideanSpace ℂ (Fin n)) j) := by
    filter_upwards [hrow] with q hq
    exact congrFun (congrArg WithLp.ofLp hq) j
  have h := angularWeightedTorus_complexCoverLift_ae_eq ha hj
  rw [complexTorusCoverLift_barPartialRepresentative_eq
    F hperiod j] at h
  exact h

end MatrixTorusCompactGreen

namespace TorusNoncompactBochner

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert TorusCharacters ComplexKillingSaturationBridge MatrixTorusBochnerIdentity
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private theorem complexScalar_integral_mul_conj_re_eq_L2_norm_sq
    {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {F : X → ℂ}
    (hF : MemLp F 2 μ) :
    (∫ x : X, F x * conj (F x) ∂μ).re =
      ‖hF.toLp F‖ ^ 2 := by
  have hre :
      (∫ x : X, F x * conj (F x) ∂μ) =
        ∫ x : X,
          @inner ℂ ℂ _ ((hF.toLp F) x) ((hF.toLp F) x) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hF.coeFn_toLp] with x hx
    rw [hx, RCLike.inner_apply]
  rw [hre, ← MeasureTheory.L2.inner_def]
  change
    RCLike.re
      (@inner ℂ (MeasureTheory.Lp ℂ 2 μ) _
        (hF.toLp F) (hF.toLp F)) =
      ‖hF.toLp F‖ ^ 2
  exact (norm_sq_eq_re_inner (hF.toLp F)).symm

private theorem angularTorus_compact_form_curvature_le_adjoint_add_exterior
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : LogSpace n → Fin n → ℂ)
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hW : ∀ i : Fin n, ContDiff ℝ 2 (fun z => W z i))
    (hWp : ∀ (i : Fin n) (q : Fin n → ℤ),
      Function.Periodic (fun z => W z i)
        (imaginaryShift q))
    (hWc : ∀ i : Fin n,
      HasCompactSupport (torusScalarRepresentative (fun z => W z i))) :
    (∫ p : LogTorus n,
      angularTorusFormCurvatureDensity a W p
        ∂(angularWeightedTorusMeasure a)).re ≤
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p)
          ∂(angularWeightedTorusMeasure a)).re +
    (∫ p : LogTorus n,
      sourceTorusFormExteriorDerivativeDensity W p
        ∂(angularWeightedTorusMeasure a)).re := by
  let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
  have hfull : Integrable
      (sourceTorusFormFullDerivativeDensity W) μ :=
    integrable_angularTorusFormFullDerivativeDensity
      W ha hW hWp hWc
  have hfull_nonneg :
      0 ≤ (∫ p : LogTorus n,
        sourceTorusFormFullDerivativeDensity W p ∂μ).re := by
    change 0 ≤ RCLike.re
      (∫ p : LogTorus n,
        sourceTorusFormFullDerivativeDensity W p ∂μ)
    rw [← integral_re hfull]
    exact MeasureTheory.integral_nonneg
      (fun p => sourceTorusFormFullDerivativeDensity_re_nonneg W p)
  have hboch :=
    angularTorus_weighted_complex_dolbeault_form_bochner_identity
      W ha ha2 hW hWp hWc
  have hre := congrArg Complex.re hboch
  simp only [Complex.add_re] at hre
  change
    (∫ p : LogTorus n,
      angularTorusFormCurvatureDensity a W p ∂μ).re ≤
    (∫ p : LogTorus n,
      angularTorusFormAdjoint a W p *
        conj (angularTorusFormAdjoint a W p) ∂μ).re +
    (∫ p : LogTorus n,
      sourceTorusFormExteriorDerivativeDensity W p ∂μ).re
  linarith

/-- A quadratic bound for the norm of a difference of complex numbers. -/
public
theorem complex_norm_sub_sq_le_two_mul_add
    (z w : ℂ) :
    ‖z - w‖ ^ 2 ≤ 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  have hsub := norm_sub_le z w
  have hsq : ‖z - w‖ ^ 2 ≤ (‖z‖ + ‖w‖) ^ 2 := by
    exact (sq_le_sq₀ (norm_nonneg _) (add_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hsub
  nlinarith [sq_nonneg (‖z‖ - ‖w‖)]

private theorem complexEuclidean_antisymmetric_energy_le_two_norm_sq
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) :
    ((∑ i : Fin n, ∑ j : Fin n,
      (M (i, j) - M (j, i)) *
        conj (M (i, j) - M (j, i))) / 2 : ℂ).re
      ≤ 2 * ‖M‖ ^ 2 := by
  change
    ((∑ i : Fin n, ∑ j : Fin n,
      (M (i, j) - M (j, i)) *
        conj (M (i, j) - M (j, i))) / ((2 : ℝ) : ℂ)).re
      ≤ 2 * ‖M‖ ^ 2
  rw [Complex.div_ofReal_re]
  simp_rw [Complex.re_sum, Complex.mul_conj,
    Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  have hsum :
      ∑ i : Fin n, ∑ j : Fin n, ‖M (i, j) - M (j, i)‖ ^ 2 ≤
        ∑ i : Fin n, ∑ j : Fin n,
          2 * (‖M (i, j)‖ ^ 2 + ‖M (j, i)‖ ^ 2) := by
    exact Finset.sum_le_sum (fun i _ =>
      Finset.sum_le_sum (fun j _ =>
        complex_norm_sub_sq_le_two_mul_add (M (i, j)) (M (j, i))))
  have hswap :
      (∑ i : Fin n, ∑ j : Fin n, ‖M (j, i)‖ ^ 2) =
        ∑ i : Fin n, ∑ j : Fin n, ‖M (i, j)‖ ^ 2 := by
    rw [Finset.sum_comm]
  simp only [mul_add, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hswap] at hsum
  nlinarith

private theorem sourceTorusBarPartial_cutoffPhysicalField_antisymmetric
    {n : ℕ}
    {W : LogSpace n → LogSpace n}
    (hW : ContDiff ℝ 2 W)
    (hclosed : ∀ q : LogTorus n,
      Matrix.IsSymm (fun i j : Fin n =>
        sourceTorusBarPartial (fun z => W z i) j q))
    (m : ℕ) (i j : Fin n) (p : LogTorus n) :
    sourceTorusBarPartial
        (fun z => cutoffPhysicalField m W z i) j p -
      sourceTorusBarPartial
        (fun z => cutoffPhysicalField m W z j) i p =
      sourceCutoffDerivativeCommutator m W p (i, j) -
        sourceCutoffDerivativeCommutator m W p (j, i) := by
  rw [sourceTorusBarPartial_cutoffPhysicalField m hW i j p,
    sourceTorusBarPartial_cutoffPhysicalField m hW j i p,
    (hclosed p).apply j i]
  change
    ((sourceRadialCutoff m p : ℂ) *
        sourceTorusBarPartial (fun z => W z j) i p +
      torusScalarRepresentative (fun z => W z i) p *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) j p) -
      ((sourceRadialCutoff m p : ℂ) *
        sourceTorusBarPartial (fun z => W z j) i p +
      torusScalarRepresentative (fun z => W z j) p *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) i p) =
      torusScalarRepresentative (fun z => W z i) p *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) j p -
      torusScalarRepresentative (fun z => W z j) p *
        sourceTorusBarPartial (complexSourceCoverRadialCutoff m) i p
  ring

end TorusNoncompactBochner

namespace TorusMollifiedBochner

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusDistributionBridge TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff

private theorem barPartial_barPartial_commute
    {n : ℕ}
    {F : LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F)
    (z : LogSpace n) (i j : Fin n) :
    barPartialCoordinate
      (fun w => barPartialCoordinate F w i) z j =
      barPartialCoordinate
        (fun w => barPartialCoordinate F w j) z i := by
  let ei₀ : LogSpace n := Pi.single i (1 : ℂ)
  let ei₁ : LogSpace n := Pi.single i Complex.I
  let ej₀ : LogSpace n := Pi.single j (1 : ℂ)
  let ej₁ : LogSpace n := Pi.single j Complex.I
  change
    ((fderiv ℝ
        (fun w => barPartialCoordinate F w i) z) ej₀ +
      Complex.I *
        (fderiv ℝ
          (fun w => barPartialCoordinate F w i) z) ej₁) / 2 =
      ((fderiv ℝ
          (fun w => barPartialCoordinate F w j) z) ei₀ +
        Complex.I *
          (fderiv ℝ
            (fun w => barPartialCoordinate F w j) z) ei₁) / 2
  rw [fderiv_barPartialCoordinate hF z ej₀ i,
    fderiv_barPartialCoordinate hF z ej₁ i,
    fderiv_barPartialCoordinate hF z ei₀ j,
    fderiv_barPartialCoordinate hF z ei₁ j]
  change
    (((fderiv ℝ (fun w => (fderiv ℝ F w) ei₀) z) ej₀ +
        Complex.I *
          (fderiv ℝ (fun w => (fderiv ℝ F w) ei₁) z) ej₀) / 2 +
      Complex.I *
        (((fderiv ℝ (fun w => (fderiv ℝ F w) ei₀) z) ej₁ +
          Complex.I *
            (fderiv ℝ (fun w => (fderiv ℝ F w) ei₁) z) ej₁) / 2)) / 2 =
    (((fderiv ℝ (fun w => (fderiv ℝ F w) ej₀) z) ei₀ +
        Complex.I *
          (fderiv ℝ (fun w => (fderiv ℝ F w) ej₁) z) ei₀) / 2 +
      Complex.I *
        (((fderiv ℝ (fun w => (fderiv ℝ F w) ej₀) z) ei₁ +
          Complex.I *
            (fderiv ℝ (fun w => (fderiv ℝ F w) ej₁) z) ei₁) / 2)) / 2
  rw [fderiv_directional_commute hF z ei₀ ej₀,
    fderiv_directional_commute hF z ei₁ ej₀,
    fderiv_directional_commute hF z ei₀ ej₁,
    fderiv_directional_commute hF z ei₁ ej₁]
  ring

private theorem sourceTorusClosedForm_barPartial
    {n : ℕ}
    {F : LogSpace n → ℂ}
    (hF : ContDiff ℝ 2 F) :
    ∀ q : LogTorus n,
      Matrix.IsSymm (fun i j : Fin n =>
        sourceTorusBarPartial
          (fun z => barPartialCoordinate F z i) j q) := by
  intro q
  apply Matrix.IsSymm.ext
  intro i j
  exact barPartial_barPartial_commute hF _ j i

private def angularGraphMollifiedPhysicalField
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a) (k : ℕ) :
    LogSpace n → LogSpace n :=
  fun z i => normalizedCoverMollification
    (complexTorusCoverLift
      (fun q : LogTorus n =>
        (W q : EuclideanSpace ℂ (Fin n)) i)) k z

private theorem angularGraphMollifiedPhysicalField_periodic
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (k : ℕ) (q : Fin n → ℤ) :
    Function.Periodic (angularGraphMollifiedPhysicalField W k)
      (imaginaryShift q) := by
  intro z
  funext i
  exact normalizedCoverMollification_periodic
    (fun d => complexTorusCoverLift_periodic
      (fun p : LogTorus n =>
        (W p : EuclideanSpace ℂ (Fin n)) i) d)
    k q z

end TorusMollifiedBochner

namespace WeightedTorusScalarCompactGreen

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open ComplexKillingSaturationBridge DolbeaultGraphDistributionBridge WeightedTorusDistributionBridge
open WeightedTorusGraphWeakBridge WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault
open TorusWeakDolbeaultMollification TorusMollifiedBochner BergmanJetStrictMixedLocalCore
open MatrixTorusCompactGreen
open scoped BigOperators ENNReal InnerProductSpace Topology
  ComplexConjugate ContDiff Convolution Manifold

private def angularWeightedCellAdjointScalarL2 {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    angularWeightedCellScalarL2 a b := by
  letI : IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) :=
    realAngularWeightedFundamentalCellMeasure_isLocallyFinite ha b
  exact ((continuous_angularWeightedCellAdjointScalarTest
      ha hψ j).memLp_of_hasCompactSupport
      (μ := realAngularWeightedFundamentalCellMeasure a b)
      (compactSupport_angularWeightedCellAdjointScalarTest
        a hψcompact j)).toLp
      (angularWeightedCellAdjointScalarTest a ψ j)

private theorem angularWeightedCellAdjointScalarL2_ae_eq {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (fun p : Space n × Space n =>
      angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j p)
      =ᵐ[realAngularWeightedFundamentalCellMeasure a b]
        angularWeightedCellAdjointScalarTest a ψ j := by
  let : IsLocallyFiniteMeasure
      (realAngularWeightedFundamentalCellMeasure a b) :=
    realAngularWeightedFundamentalCellMeasure_isLocallyFinite ha b
  simpa only [angularWeightedCellAdjointScalarL2] using
    (MeasureTheory.MemLp.coeFn_toLp
      ((continuous_angularWeightedCellAdjointScalarTest
        ha hψ j).memLp_of_hasCompactSupport
        (μ := realAngularWeightedFundamentalCellMeasure a b)
        (compactSupport_angularWeightedCellAdjointScalarTest
          a hψcompact j)))

private theorem angularWeightedCellScalar_inner_eq_unweighted {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (f : angularWeightedScalarL2 a) :
    @inner ℂ (angularWeightedCellScalarL2 a b) _
      (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
      (angularScalarFundamentalLiftLI ha b f) =
        ∫ p : Space n × Space n,
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
          ∂(realFundamentalCellMeasure b) := by
  calc
    _ = ∫ p : Space n × Space n,
        @inner ℂ ℂ _
          (angularWeightedCellAdjointScalarTest a ψ j p)
          (f (realTorusCoverProjection n p))
        ∂(realAngularWeightedFundamentalCellMeasure a b) := by
      rw [MeasureTheory.L2.inner_def]
      apply integral_congr_ae
      filter_upwards
        [angularWeightedCellAdjointScalarL2_ae_eq
          ha b hψ hψcompact j,
         angularScalarFundamentalLiftLI_ae_eq ha b f]
        with p ht hf
      rw [ht, hf]
    _ = _ := by
      have hd : Measurable
          (fun p : Space n × Space n =>
            ENNReal.ofReal
              (angularWeightedTorusDensity a
                (realTorusCoverProjection n p))) :=
        ENNReal.measurable_ofReal.comp
          ((continuous_angularWeightedTorusDensity ha).comp
            (continuous_realTorusCoverProjection n)).measurable
      rw [realAngularWeightedFundamentalCellMeasure,
        integral_withDensity_eq_integral_toReal_smul
          hd (Filter.Eventually.of_forall
            (fun _ => ENNReal.ofReal_lt_top))]
      apply integral_congr_ae
      filter_upwards [] with p
      have hc := angularWeight_mul_inverseAngularCoverWeight a p
      rw [RCLike.inner_apply]
      change
        (ENNReal.ofReal
          (angularWeightedTorusDensity a
            (realTorusCoverProjection n p))).toReal •
          (f (realTorusCoverProjection n p) *
            star (angularWeightedCellAdjointScalarTest a ψ j p)) =
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
      simp only [angularWeightedCellAdjointScalarTest,
        coverAdjointScalarTest, StarMul.star_mul,
        inverseAngularCoverWeight, Complex.star_def,
        Complex.conj_ofReal, starRingEnd_self_apply,
        Complex.real_smul] at hc ⊢
      calc
        _ = (((ENNReal.ofReal
              (angularWeightedTorusDensity a
                (realTorusCoverProjection n p))).toReal : ℂ) *
              (Real.exp
                (a (realTorusCoverProjection n p)) : ℂ)) *
            (coverBarPartialTest ψ j
              (logarithmicCoordinatesEquiv n p) *
              f (realTorusCoverProjection n p)) := by
            ring
        _ = _ := by rw [hc, one_mul]; ring

private theorem angularWeightedCellScalar_inner_eq_jacobian_cover {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (f : angularWeightedScalarL2 a) :
    @inner ℂ (angularWeightedCellScalarL2 a b) _
      (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
      (angularScalarFundamentalLiftLI ha b f) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          complexTorusCoverLift (fun q : LogTorus n => f q) z *
            coverBarPartialTest ψ j z
          ∂(volume : Measure (LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
          f (realTorusCoverProjection n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
          ∂(realFundamentalCellMeasure b) :=
      angularWeightedCellScalar_inner_eq_unweighted
        ha b hψ hψcompact j f
    _ = ∫ p : Space n × Space n,
          complexTorusCoverLift (fun q : LogTorus n => f q)
            (logarithmicCoordinatesEquiv n p) *
            coverBarPartialTest ψ j (logarithmicCoordinatesEquiv n p)
          ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards [] with p
      unfold complexTorusCoverLift complexTorusCoverProjection
      rw [ContinuousLinearEquiv.symm_apply_apply]
    _ = _ := by
      apply realFundamentalCell_integral_eq_coverJacobian b
        (fun z =>
          complexTorusCoverLift (fun q : LogTorus n => f q) z *
            coverBarPartialTest ψ j z)
      intro p hp
      rw [(coverTest_zero_outside_fundamentalCell hcell p hp).2 j,
        mul_zero]

private def angularCellScalarAdjointFunctional {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) (u : angularWeightedCellScalarL2 a b) :
    angularDolbeaultGraphAmbient a →L[ℂ] ℂ :=
  ((innerSL ℂ u).comp
    (angularScalarFundamentalLiftLI ha b).toContinuousLinearMap).comp
      (WithLp.fstL 2 ℂ
        (angularWeightedScalarL2 a) (angularWeightedFormL2 a))

private def angularCellFormAdjointFunctional {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n) (u : angularWeightedCellFormL2 a b) :
    angularDolbeaultGraphAmbient a →L[ℂ] ℂ :=
  ((innerSL ℂ u).comp
    (angularFormFundamentalLiftLI ha b).toContinuousLinearMap).comp
      (WithLp.sndL 2 ℂ
        (angularWeightedScalarL2 a) (angularWeightedFormL2 a))

private def angularCellWeakAdjointFunctional {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    angularDolbeaultGraphAmbient a →L[ℂ] ℂ :=
  angularCellScalarAdjointFunctional ha b
    (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j) +
  angularCellFormAdjointFunctional ha b
    (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)

private theorem angularCellWeakAdjointFunctional_apply {n : ℕ}
    {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n)
    (v : angularDolbeaultGraphAmbient a) :
    angularCellWeakAdjointFunctional ha b hψ hψcompact j v =
      @inner ℂ (angularWeightedCellScalarL2 a b) _
        (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
        (angularScalarFundamentalLiftLI ha b (WithLp.fst v)) +
      @inner ℂ (angularWeightedCellFormL2 a b) _
        (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
        (angularFormFundamentalLiftLI ha b (WithLp.snd v)) := by
  rfl

private theorem angularScalarGraphGenerator_complexCoverLift_ae_eq
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (F : LogSpace n → ℂ)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a)) :
    complexTorusCoverLift
      (fun q : LogTorus n => angularScalarL2OfRepresentative a F hF q)
        =ᵐ[(volume : Measure (LogSpace n))] F := by
  have h := angularWeightedTorus_complexCoverLift_ae_eq
    ha hF.coeFn_toLp
  change
    complexTorusCoverLift
      (fun q : LogTorus n => angularScalarL2OfRepresentative a F hF q)
      =ᵐ[(volume : Measure (LogSpace n))]
        complexTorusCoverLift (torusScalarRepresentative F) at h
  simpa only [complexTorusCoverLift_torusScalarRepresentative_eq F hperiod] using h

private theorem angularCellWeakAdjointFunctional_smoothGraph_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    {F : LogSpace n → ℂ} (hF₁ : ContDiff ℝ 1 F)
    (hperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q))
    (hF : MemLp (torusScalarRepresentative F) 2
      (angularWeightedTorusMeasure a))
    (hD : MemLp (torusFunctionBarPartialRepresentative F) 2
      (angularWeightedTorusMeasure a)) (j : Fin n) :
    angularCellWeakAdjointFunctional ha b hψ hψcompact j
      (WithLp.toLp 2
        (angularScalarL2OfRepresentative a F hF,
         angularBarPartialL2OfRepresentative a F hD)) = 0 := by
  rw [angularCellWeakAdjointFunctional_apply]
  change
    @inner ℂ (angularWeightedCellScalarL2 a b) _
      (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
      (angularScalarFundamentalLiftLI ha b
        (angularScalarL2OfRepresentative a F hF)) +
    @inner ℂ (angularWeightedCellFormL2 a b) _
      (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
      (angularFormFundamentalLiftLI ha b
        (angularBarPartialL2OfRepresentative a F hD)) = 0
  rw [angularWeightedCellScalar_inner_eq_jacobian_cover
    ha b hψ hψcompact hcell j,
    angularWeightedCellVector_inner_eq_jacobian_cover
      ha b hψ hψcompact hcell j]
  have hgreen :
      (∫ z : LogSpace n,
        complexTorusCoverLift
          (fun q : LogTorus n =>
            angularScalarL2OfRepresentative a F hF q) z *
            coverBarPartialTest ψ j z
        ∂(volume : Measure (LogSpace n))) =
        -(2 : ℂ) *
          (∫ z : LogSpace n,
            complexTorusCoverLift
              (fun q : LogTorus n =>
                (angularBarPartialL2OfRepresentative a F hD q :
                  EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ)
            ∂(volume : Measure (LogSpace n))) := by
    calc
      _ = ∫ z : LogSpace n,
          F z * coverBarPartialTest ψ j z
          ∂(volume : Measure (LogSpace n)) := by
        apply integral_congr_ae
        filter_upwards
          [angularScalarGraphGenerator_complexCoverLift_ae_eq
            ha F hperiod hF] with z hz
        rw [hz]
      _ = -(2 : ℂ) *
          (∫ z : LogSpace n,
            barPartialCoordinate F z j * (ψ z : ℂ)
              ∂(volume : Measure (LogSpace n))) :=
        complex_compact_barPartial_green hF₁ hψ hψcompact j
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards
          [angularFormGraphGenerator_complexCoverLift_ae_eq
            ha F hperiod hD j] with z hz
        rw [hz]
  rw [integral_const_mul]
  rw [← smul_add, hgreen]
  simp only [neg_mul, neg_add_cancel, smul_zero]

private theorem angularCellWeakAdjointFunctional_closedGraph_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) (v : angularDolbeaultGraphAmbient a)
    (hv : v ∈ angularDolbeaultGraph a) :
    angularCellWeakAdjointFunctional ha b hψ hψcompact j v = 0 := by
  let L : angularDolbeaultGraphAmbient a →L[ℂ] ℂ :=
    angularCellWeakAdjointFunctional ha b hψ hψcompact j
  have hspan :
      Submodule.span ℂ (smoothAngularDolbeaultGraphSet a) ≤ L.ker := by
    apply Submodule.span_le.mpr
    intro v hv'
    rcases hv' with
      ⟨F, hF, hperiod, _hcompact, hFLp, hDLp, rfl⟩
    exact angularCellWeakAdjointFunctional_smoothGraph_zero
      ha b hψ hψcompact hcell
      (hF.of_le (by norm_num)) hperiod hFLp hDLp j
  have hgraph : angularDolbeaultGraph a ≤ L.ker := by
    unfold angularDolbeaultGraph
    exact Submodule.topologicalClosure_minimal
      (Submodule.span ℂ (smoothAngularDolbeaultGraphSet a))
      hspan L.isClosed_ker
  exact hgraph hv

private theorem angularDolbeaultGraph_compact_barPartial_green_of_fundamentalCell
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    (b : Space n)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalCell b)
    (j : Fin n) :
    (∫ z : LogSpace n,
      complexTorusCoverLift (fun q : LogTorus n => f q) z *
        coverBarPartialTest ψ j z
      ∂(volume : Measure (LogSpace n))) =
      -(2 : ℂ) *
        (∫ z : LogSpace n,
          complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ)
          ∂(volume : Measure (LogSpace n))) := by
  have hz := angularCellWeakAdjointFunctional_closedGraph_zero
    ha b hψ hψcompact hcell j (WithLp.toLp 2 (f, W)) hgraph
  rw [angularCellWeakAdjointFunctional_apply] at hz
  change
    @inner ℂ (angularWeightedCellScalarL2 a b) _
      (angularWeightedCellAdjointScalarL2 ha b hψ hψcompact j)
      (angularScalarFundamentalLiftLI ha b f) +
    @inner ℂ (angularWeightedCellFormL2 a b) _
      (angularWeightedCellAdjointVectorL2 ha b hψ hψcompact j)
      (angularFormFundamentalLiftLI ha b W) = 0 at hz
  rw [angularWeightedCellScalar_inner_eq_jacobian_cover
    ha b hψ hψcompact hcell j,
    angularWeightedCellVector_inner_eq_jacobian_cover
      ha b hψ hψcompact hcell j, ← smul_add] at hz
  have hinner :
      (∫ z : LogSpace n,
        complexTorusCoverLift (fun q : LogTorus n => f q) z *
          coverBarPartialTest ψ j z
        ∂(volume : Measure (LogSpace n))) +
      (∫ z : LogSpace n,
        (2 : ℂ) *
          (complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ))
        ∂(volume : Measure (LogSpace n))) = 0 :=
    (smul_eq_zero.mp hz).resolve_left
      (logarithmicCoverJacobianFactor_pos n).ne'
  rw [integral_const_mul] at hinner
  linear_combination hinner

private theorem angularDolbeaultGraph_compact_barPartial_green
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    {ψ : LogSpace n → ℝ} (hψ : ContDiff ℝ 1 ψ)
    (hψcompact : HasCompactSupport ψ) (j : Fin n) :
    (∫ z : LogSpace n,
      complexTorusCoverLift (fun q : LogTorus n => f q) z *
        coverBarPartialTest ψ j z
      ∂(volume : Measure (LogSpace n))) =
      -(2 : ℂ) *
        (∫ z : LogSpace n,
          complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z * (ψ z : ℂ)
          ∂(volume : Measure (LogSpace n))) := by
  classical
  obtain ⟨s, χ, hχ, hχsupport, hpartition⟩ :=
    exists_finite_fundamental_test_partition hψcompact
  let ξ : LogSpace n → LogSpace n → ℝ :=
    fun i z => χ i z * ψ z
  have hξ : ∀ i, ContDiff ℝ 1 (ξ i) := by
    intro i
    exact (hχ i).mul hψ
  have hξcompact : ∀ i, HasCompactSupport (ξ i) := by
    intro i
    exact hψcompact.mul_left
  have hξcell : ∀ i,
      tsupport (ξ i) ⊆ coverFundamentalCell (coverCenteredFundamentalBase i) := by
    intro i
    apply coverTestWithinFundamentalCell_of_tsupport_subset_interior
    exact tsupport_mul_subset_left.trans (hχsupport i)
  have hψsum : ψ = fun z => ∑ i ∈ s, ξ i z := by
    funext z
    exact hpartition z
  have hfloc := angularWeightedScalarCoverLift_locallyIntegrable
    ha f
  have hwloc := angularWeightedFormCoordinateCoverLift_locallyIntegrable
    ha W j
  have hintf : ∀ i ∈ s, Integrable
      (fun z : LogSpace n =>
        complexTorusCoverLift
          (fun q : LogTorus n => f q) z *
            coverBarPartialTest (ξ i) j z)
      (volume : Measure (LogSpace n)) := by
    intro i _
    simpa only [smul_eq_mul] using
      hfloc.integrable_smul_right_of_hasCompactSupport
        (continuous_coverBarPartialTest (hξ i) j)
        (compactSupport_coverBarPartialTest (hξcompact i) j)
  have hintw : ∀ i ∈ s, Integrable
      (fun z : LogSpace n =>
        complexTorusCoverLift
          (fun q : LogTorus n =>
            (W q : EuclideanSpace ℂ (Fin n)) j) z *
              (ξ i z : ℂ))
      (volume : Measure (LogSpace n)) := by
    intro i _
    simpa only [Function.comp_apply, smul_eq_mul] using
      hwloc.integrable_smul_right_of_hasCompactSupport
        (Complex.continuous_ofReal.comp (hξ i).continuous)
        (compactSupport_complexOfReal (hξcompact i))
  calc
    _ = ∫ z : LogSpace n,
        ∑ i ∈ s,
          complexTorusCoverLift
            (fun q : LogTorus n => f q) z *
              coverBarPartialTest (ξ i) j z
        ∂(volume : Measure (LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hψsum, coverBarPartialTest_finset_sum s ξ
        (fun i _ => hξ i) j z, Finset.mul_sum]
    _ = ∑ i ∈ s,
      (∫ z : LogSpace n,
        complexTorusCoverLift
          (fun q : LogTorus n => f q) z *
            coverBarPartialTest (ξ i) j z
        ∂(volume : Measure (LogSpace n))) :=
      integral_finsetSum s hintf
    _ = ∑ i ∈ s,
      (-(2 : ℂ) *
        (∫ z : LogSpace n,
          complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z *
                (ξ i z : ℂ)
          ∂(volume : Measure (LogSpace n)))) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact angularDolbeaultGraph_compact_barPartial_green_of_fundamentalCell
        ha f W hgraph (coverCenteredFundamentalBase i)
        (hξ i) (hξcompact i) (hξcell i) j
    _ = -(2 : ℂ) *
      (∫ z : LogSpace n,
        ∑ i ∈ s,
          complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) z *
                (ξ i z : ℂ)
        ∂(volume : Measure (LogSpace n))) := by
      rw [integral_finsetSum s hintw]
      simp only [neg_mul, Finset.sum_neg_distrib, Finset.mul_sum]
    _ = _ := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hpartition z]
      simp only [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, ξ]

private theorem angularDolbeaultGraph_normalizedCoverMollification_barPartial
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    (k : ℕ) (x : LogSpace n) (j : Fin n) :
    barPartialCoordinate
      (normalizedCoverMollification
        (complexTorusCoverLift (fun q : LogTorus n => f q)) k) x j =
      normalizedCoverMollification
        (complexTorusCoverLift
          (fun q : LogTorus n =>
            (W q : EuclideanSpace ℂ (Fin n)) j)) k x := by
  apply barPartial_normalizedCoverMollification_eq_of_compact_green
    (angularWeightedScalarCoverLift_locallyIntegrable ha f)
  intro ψ hψ hψcompact i
  exact angularDolbeaultGraph_compact_barPartial_green
    ha f W hgraph hψ hψcompact i

private theorem contDiff_angularGraphMollifiedPhysicalField
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (W : angularWeightedFormL2 a)
    (k r : ℕ) :
    ContDiff ℝ r (angularGraphMollifiedPhysicalField W k) := by
  apply contDiff_pi.mpr
  intro i
  exact contDiff_normalizedCoverMollification
    (angularWeightedFormCoordinateCoverLift_locallyIntegrable
      ha W i) k r

private theorem sourceTorusClosedForm_angularGraphMollifiedPhysicalField
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    (k : ℕ) :
    ∀ q : LogTorus n,
      Matrix.IsSymm (fun i j : Fin n =>
        MatrixTorusBochnerIdentity.sourceTorusBarPartial
          (fun z => angularGraphMollifiedPhysicalField W k z i) j q) := by
  let F : LogSpace n → ℂ :=
    normalizedCoverMollification
      (complexTorusCoverLift (fun q : LogTorus n => f q)) k
  have hF : ContDiff ℝ 2 F :=
    contDiff_normalizedCoverMollification
      (angularWeightedScalarCoverLift_locallyIntegrable ha f) k 2
  have hident (z : LogSpace n) (i : Fin n) :
      barPartialCoordinate F z i =
        angularGraphMollifiedPhysicalField W k z i :=
    angularDolbeaultGraph_normalizedCoverMollification_barPartial
      ha f W hgraph k z i
  have hclosed := sourceTorusClosedForm_barPartial hF
  intro q
  apply Matrix.IsSymm.ext
  intro i j
  have hi :
      (fun z => angularGraphMollifiedPhysicalField W k z i) =
        (fun z => barPartialCoordinate F z i) := by
    funext z
    exact (hident z i).symm
  have hj :
      (fun z => angularGraphMollifiedPhysicalField W k z j) =
        (fun z => barPartialCoordinate F z j) := by
    funext z
    exact (hident z j).symm
  rw [hj, hi]
  exact (hclosed q).apply i j

end WeightedTorusScalarCompactGreen

namespace TorusMollificationLocalL2Bounds

open Set Function Filter MeasureTheory
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open TorusFriedrichsMollifierEstimates
open scoped BigOperators ENNReal Topology ContDiff Convolution

private theorem normalizedCoverMollification_memLp
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) :
    MemLp (normalizedCoverMollification h k) 2
      (volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.mul ℝ ℝ
  let q : LogSpace n → ℝ :=
    κ ⋆[L, (volume : Measure (LogSpace n))]
      (fun x : LogSpace n => ‖h x‖ ^ 2)
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hκint : Integrable κ (volume : Measure (LogSpace n)) :=
    hκ.integrable_of_hasCompactSupport hκcompact
  have hq : Integrable q (volume : Measure (LogSpace n)) :=
    hκint.integrable_convolution L hh.norm.integrable_sq
  have hc : Continuous (normalizedCoverMollification h k) :=
    (contDiff_normalizedCoverMollification
      (hh.locallyIntegrable (by norm_num)) k 0).continuous
  apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
    hc.aestronglyMeasurable).mpr
  apply hq.mono' (hc.norm.pow 2).aestronglyMeasurable
  filter_upwards [] with x
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa [q, κ, L, MeasureTheory.convolution_def] using
    normalizedCoverMollification_norm_sq_le_convolution_norm_sq hh k x

private theorem integral_norm_sq_normalizedCoverMollification_le
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) :
    (∫ x : LogSpace n,
      ‖normalizedCoverMollification h k x‖ ^ 2
      ∂(volume : Measure (LogSpace n))) ≤
      ∫ x : LogSpace n, ‖h x‖ ^ 2
        ∂(volume : Measure (LogSpace n)) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
    ContinuousLinearMap.mul ℝ ℝ
  let q : LogSpace n → ℝ :=
    κ ⋆[L, (volume : Measure (LogSpace n))]
      (fun x : LogSpace n => ‖h x‖ ^ 2)
  have hκ : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hκint : Integrable κ (volume : Measure (LogSpace n)) :=
    hκ.integrable_of_hasCompactSupport hκcompact
  have hq : Integrable q (volume : Measure (LogSpace n)) :=
    hκint.integrable_convolution L hh.norm.integrable_sq
  have hsquare : Integrable
      (fun x : LogSpace n =>
        ‖normalizedCoverMollification h k x‖ ^ 2)
      (volume : Measure (LogSpace n)) :=
    (normalizedCoverMollification_memLp hh k).norm.integrable_sq
  calc
    (∫ x : LogSpace n,
      ‖normalizedCoverMollification h k x‖ ^ 2
      ∂(volume : Measure (LogSpace n))) ≤
        ∫ x : LogSpace n, q x
          ∂(volume : Measure (LogSpace n)) := by
          apply integral_mono hsquare hq
          intro x
          simpa only [convolution_def, ContinuousLinearMap.mul_apply', q, κ, L] using
            normalizedCoverMollification_norm_sq_le_convolution_norm_sq
              hh k x
    _ =
        (∫ x : LogSpace n, κ x
          ∂(volume : Measure (LogSpace n))) *
        (∫ x : LogSpace n, ‖h x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) := by
          exact MeasureTheory.integral_convolution L
            hκint hh.norm.integrable_sq
    _ = _ := by
      rw [(complexShrinkingBump (n := n) k).integral_normed]
      simp only [one_mul]

private theorem complexShrinkingBump_rOut_le_one
    {n : ℕ} (k : ℕ) :
    (complexShrinkingBump (n := n) k).rOut ≤ 1 := by
  change 1 / ((k : ℝ) + 1) ≤ 1
  rw [div_le_iff₀ (by positivity)]
  norm_num

end TorusMollificationLocalL2Bounds

namespace TorusWeightedCoverAdjointGreen

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge WeightedTorusGraphWeakBridge
open WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault WeightedTorusBochner WeightedTorusBrascampLieb TorusDeckPeriodization
open TorusDeckGraphAdjoint TorusDeckFundamentalCell TorusDeckFullCellDerivative
open TorusDeckWeightedUnfolding
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold

private theorem ae_mem_angularFundamentalBox_realFundamentalCell
    {n : ℕ}
    (b : Space n) :
    ∀ᵐ p : Space n × Space n
      ∂(realFundamentalCellMeasure b),
      p.2 ∈ angularFundamentalBox b := by
  rw [realFundamentalCellMeasure_eq_restrict]
  filter_upwards
    [ae_restrict_mem
      (MeasurableSet.univ.prod
        (measurableSet_angularFundamentalBox b))]
    with p hp
  exact hp.2

private theorem angularWeightedScalarL2_periodized_cell_inner_eq_cover
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b) :
    (∫ q : LogTorus n,
      @inner ℂ ℂ _
        (f q)
        (torusScalarRepresentative (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          @inner ℂ ℂ _
            (f (complexTorusCoverProjection n z))
            (ψ z)
          ∂(coverWeightedMeasure (angularCoverPotential a))) := by
  let F : LogSpace n → ℂ := complexDeckPeriodization ψ
  let g : LogSpace n → ℂ := fun z =>
    complexCoverWeight (angularCoverPotential a) z *
      @inner ℂ ℂ _
        (f (complexTorusCoverProjection n z)) (ψ z)
  have hFperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q) :=
    fun q => complexDeckPeriodization_periodic ψ q
  have hFcontinuous : Continuous (torusScalarRepresentative F) :=
    continuous_torusScalarRepresentative_of_periodic
      (contDiff_complexDeckPeriodization hψ hψcompact).continuous
      hFperiod
  have hhalf : tsupport ψ ⊆
      {z : LogSpace n |
        ((logarithmicCoordinatesEquiv n).symm z).2 ∈
          angularFundamentalBox b} := by
    intro z hz i
    have hi := hcell hz i
    exact ⟨hi.1, hi.2.le⟩
  calc
    (∫ q : LogTorus n,
      @inner ℂ ℂ _ (f q) (torusScalarRepresentative F q)
      ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a
          (fun q : LogTorus n =>
            @inner ℂ ℂ _ (f q) (torusScalarRepresentative F q))
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) :=
      angularWeightedScalarL2_inner_integral_eq_realFundamentalCell
        ha b f hFcontinuous
    _ = ∫ p : Space n × Space n,
        g (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards
        [ae_mem_angularFundamentalBox_realFundamentalCell b]
        with p hp
      have hrep :
          torusScalarRepresentative F
            (realTorusCoverProjection n p) =
          ψ (logarithmicCoordinatesEquiv n p) := by
        change
          torusScalarRepresentative F
            (p.1, angularCoverProjection n p.2) =
          ψ (logarithmicCoordinatesEquiv n p)
        rw [periodic_torusScalarRepresentative_logarithmicPoint
          F hFperiod p.1 p.2]
        change
          complexDeckPeriodization ψ
            (logarithmicPoint p.1 p.2) =
          ψ (logarithmicPoint p.1 p.2)
        exact complexDeckPeriodization_eq_of_fundamentalCell
          hhalf p.1 p.2 hp
      have hproj :
          complexTorusCoverProjection n
            (logarithmicCoordinatesEquiv n p) =
            realTorusCoverProjection n p := by
        change
          complexTorusCoverProjection n
            (logarithmicPoint p.1 p.2) =
            realTorusCoverProjection n (p.1, p.2)
        exact complexTorusCoverProjection_logarithmicPoint p.1 p.2
      change
        (angularWeightedTorusDensity a
          (realTorusCoverProjection n p) : ℂ) *
            @inner ℂ ℂ _
              (f (realTorusCoverProjection n p))
              (torusScalarRepresentative F
                (realTorusCoverProjection n p)) =
        complexCoverWeight (angularCoverPotential a)
          (logarithmicCoordinatesEquiv n p) *
            @inner ℂ ℂ _
              (f (complexTorusCoverProjection n
                (logarithmicCoordinatesEquiv n p)))
              (ψ (logarithmicCoordinatesEquiv n p))
      rw [hrep, hproj]
      simp only [complexCoverWeight, coverWeight,
        angularCoverPotential, angularWeightedTorusDensity, hproj]
    _ = logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n, g z
          ∂(volume : Measure (LogSpace n))) := by
      apply realFundamentalCell_integral_eq_coverJacobian b g
      intro p hp
      have hz : logarithmicCoordinatesEquiv n p ∉ tsupport ψ := by
        intro hz
        apply hp
        have hh := hhalf hz
        change
          ((logarithmicCoordinatesEquiv n).symm
            (logarithmicCoordinatesEquiv n p)).2 ∈
            angularFundamentalBox b at hh
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
      have hzero := image_eq_zero_of_notMem_tsupport hz
      simp only [RCLike.inner_apply, hzero, zero_mul, mul_zero, g]
    _ = logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          @inner ℂ ℂ _
            (f (complexTorusCoverProjection n z))
            (ψ z)
          ∂(coverWeightedMeasure (angularCoverPotential a))) := by
      congr 1
      exact
        (integral_coverWeightedMeasure
          (continuous_angularCoverPotential ha)
          (fun z : LogSpace n =>
            @inner ℂ ℂ _
              (f (complexTorusCoverProjection n z))
              (ψ z))).symm

private theorem angularWeightedFormL2_periodized_cell_inner_eq_cover
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    (W : angularWeightedFormL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b) :
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W q)
        (torusFunctionBarPartialRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate ψ z j))
          ∂(coverWeightedMeasure (angularCoverPotential a))) := by
  let F : LogSpace n → ℂ := complexDeckPeriodization ψ
  let g : LogSpace n → ℂ := fun z =>
    complexCoverWeight (angularCoverPotential a) z *
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W (complexTorusCoverProjection n z))
        (WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate ψ z j))
  have hFperiod : ∀ q : Fin n → ℤ,
      Function.Periodic F (imaginaryShift q) :=
    fun q => complexDeckPeriodization_periodic ψ q
  have hFcontinuous :
      Continuous (torusFunctionBarPartialRepresentative F) :=
    continuous_torusFunctionBarPartialRepresentative_of_periodic
      ((contDiff_complexDeckPeriodization hψ hψcompact).of_le
        (by norm_num)) hFperiod
  have hhalf : tsupport ψ ⊆
      {z : LogSpace n |
        ((logarithmicCoordinatesEquiv n).symm z).2 ∈
          angularFundamentalBox b} := by
    intro z hz i
    have hi := hcell hz i
    exact ⟨hi.1, hi.2.le⟩
  calc
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W q) (torusFunctionBarPartialRepresentative F q)
      ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularUnweightedTorusIntegrand a
          (fun q : LogTorus n =>
            @inner ℂ (EuclideanSpace ℂ (Fin n)) _
              (W q) (torusFunctionBarPartialRepresentative F q))
          (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) :=
      angularWeightedFormL2_inner_integral_eq_realFundamentalCell
        ha b W hFcontinuous
    _ = ∫ p : Space n × Space n,
        g (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b) := by
      apply integral_congr_ae
      filter_upwards
        [ae_mem_angularFundamentalBox_realFundamentalCell b]
        with p hp
      have hrow :
          torusFunctionBarPartialRepresentative F
            (realTorusCoverProjection n p) =
          WithLp.toLp 2
            (fun j : Fin n =>
              barPartialCoordinate ψ
                (logarithmicCoordinatesEquiv n p) j) := by
        ext j
        change
          torusScalarRepresentative
            (fun z : LogSpace n => barPartialCoordinate F z j)
            (p.1, angularCoverProjection n p.2) =
          barPartialCoordinate ψ
            (logarithmicCoordinatesEquiv n p) j
        rw [periodic_torusScalarRepresentative_logarithmicPoint
          (fun z : LogSpace n => barPartialCoordinate F z j)
          (fun q => barPartialCoordinate_periodic F hFperiod j q)
          p.1 p.2]
        change
          barPartialCoordinate (complexDeckPeriodization ψ)
            (logarithmicPoint p.1 p.2) j =
          barPartialCoordinate ψ
            (logarithmicPoint p.1 p.2) j
        exact barPartial_complexDeckPeriodization_eq_on_fundamentalCell
          hψcompact hcell p.1 p.2 hp j
      have hproj :
          complexTorusCoverProjection n
            (logarithmicCoordinatesEquiv n p) =
            realTorusCoverProjection n p := by
        change
          complexTorusCoverProjection n
            (logarithmicPoint p.1 p.2) =
            realTorusCoverProjection n (p.1, p.2)
        exact complexTorusCoverProjection_logarithmicPoint p.1 p.2
      change
        (angularWeightedTorusDensity a
          (realTorusCoverProjection n p) : ℂ) *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (realTorusCoverProjection n p))
            (torusFunctionBarPartialRepresentative F
              (realTorusCoverProjection n p)) =
        complexCoverWeight (angularCoverPotential a)
          (logarithmicCoordinatesEquiv n p) *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n
              (logarithmicCoordinatesEquiv n p)))
            (WithLp.toLp 2
              (fun j : Fin n =>
                barPartialCoordinate ψ
                  (logarithmicCoordinatesEquiv n p) j))
      rw [hrow, hproj]
      simp only [complexCoverWeight, coverWeight,
        angularCoverPotential, angularWeightedTorusDensity, hproj]
    _ = logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n, g z
          ∂(volume : Measure (LogSpace n))) := by
      apply realFundamentalCell_integral_eq_coverJacobian b g
      intro p hp
      have hz : logarithmicCoordinatesEquiv n p ∉ tsupport ψ := by
        intro hz
        apply hp
        have hh := hhalf hz
        change
          ((logarithmicCoordinatesEquiv n).symm
            (logarithmicCoordinatesEquiv n p)).2 ∈
            angularFundamentalBox b at hh
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hh
      have hzero :
          WithLp.toLp 2
            (fun j : Fin n =>
              barPartialCoordinate ψ
                (logarithmicCoordinatesEquiv n p) j) =
            (0 : EuclideanSpace ℂ (Fin n)) := by
        ext j
        unfold barPartialCoordinate
        rw [fderiv_of_notMem_tsupport ℝ hz]
        simp only [_root_.zero_apply, mul_zero, add_zero, zero_div, PiLp.zero_apply]
      simp only [hzero, inner_zero_right, mul_zero, g]
    _ = logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n,
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate ψ z j))
          ∂(coverWeightedMeasure (angularCoverPotential a))) := by
      congr 1
      exact
        (integral_coverWeightedMeasure
          (continuous_angularCoverPotential ha)
          (fun z : LogSpace n =>
            @inner ℂ (EuclideanSpace ℂ (Fin n)) _
              (W (complexTorusCoverProjection n z))
              (WithLp.toLp 2
                (fun j : Fin n => barPartialCoordinate ψ z j)))).symm

private theorem angularWeakDolbeaultResolvent_weighted_cover_green_of_fundamentalInterior
    {n : ℕ}
    {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (b : Space n)
    (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ)
    (hψcompact : HasCompactSupport ψ)
    (hcell : tsupport ψ ⊆ coverFundamentalInterior b) :
    (∫ z : LogSpace n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
              (complexTorusCoverProjection n z))
        (WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate ψ z j))
      ∂(coverWeightedMeasure (angularCoverPotential a))) =
    (∫ z : LogSpace n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f)
          (complexTorusCoverProjection n z))
        (ψ z)
      ∂(coverWeightedMeasure (angularCoverPotential a))) := by
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a)
  let r : angularWeightedScalarL2 a :=
    f - angularWeakScalarResolventCLM a f
  have hform := angularWeightedFormL2_periodized_cell_inner_eq_cover
    ha b W hψ hψcompact hcell
  have hscalar := angularWeightedScalarL2_periodized_cell_inner_eq_cover
    ha b r hψ hψcompact hcell
  have htorus :=
    angularWeakDolbeaultResolvent_complexDeckPeriodization_adjoint_integral
      ha f hψ hψcompact
  change
    (∫ q : LogTorus n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W q)
        (torusFunctionBarPartialRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) =
    (∫ q : LogTorus n,
      @inner ℂ ℂ _
        (r q)
        (torusScalarRepresentative
          (complexDeckPeriodization ψ) q)
      ∂(angularWeightedTorusMeasure a)) at htorus
  rw [hform, hscalar] at htorus
  have hzero :
      logarithmicCoverJacobianFactor n •
        ((∫ z : LogSpace n,
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate ψ z j))
          ∂(coverWeightedMeasure (angularCoverPotential a))) -
          (∫ z : LogSpace n,
            @inner ℂ ℂ _
              (r (complexTorusCoverProjection n z))
              (ψ z)
            ∂(coverWeightedMeasure (angularCoverPotential a)))) = 0 := by
    rw [smul_sub, htorus, sub_self]
  have hcover :
      (∫ z : LogSpace n,
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (W (complexTorusCoverProjection n z))
          (WithLp.toLp 2
            (fun j : Fin n => barPartialCoordinate ψ z j))
        ∂(coverWeightedMeasure (angularCoverPotential a))) =
      (∫ z : LogSpace n,
        @inner ℂ ℂ _
          (r (complexTorusCoverProjection n z))
          (ψ z)
        ∂(coverWeightedMeasure (angularCoverPotential a))) := by
    apply sub_eq_zero.mp
    exact (smul_eq_zero.mp hzero).resolve_left
      (logarithmicCoverJacobianFactor_pos n).ne'
  exact hcover

end TorusWeightedCoverAdjointGreen

namespace TorusWeightedCoverGlobalGreen

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold

private theorem locallyIntegrable_complex_inner_mul_integrable
    {E : Type*} [MeasurableSpace E] [TopologicalSpace E]
    [OpensMeasurableSpace E] [T2Space E]
    {μ : Measure E} {F G : E → ℂ}
    (hF : LocallyIntegrable F μ)
    (hG : Continuous G)
    (hGcompact : HasCompactSupport G) :
    Integrable (fun z => @inner ℂ ℂ _ (F z) (G z)) μ := by
  have hconjcontinuous : Continuous (fun z => conj (G z)) :=
    Complex.continuous_conj.comp hG
  have hconjcompact : HasCompactSupport (fun z => conj (G z)) := by
    simpa only [comp_def] using
      hGcompact.comp_left (g := (starRingEnd ℂ)) (map_zero _)
  have hmul : Integrable (fun z => F z * conj (G z)) μ := by
    simpa only [smul_eq_mul] using
      hF.integrable_smul_right_of_hasCompactSupport
        hconjcontinuous hconjcompact
  have hc := Complex.conjCLE.toContinuousLinearMap.integrable_comp hmul
  simpa only [RCLike.inner_apply, ContinuousLinearEquiv.coe_coe, ContinuousAlgEquiv.coeCLE_apply,
    map_mul, Complex.conjCAE_apply, RingHomCompTriple.comp_apply, RingHom.id_apply,
    mul_comm] using hc

private theorem barPartialCoordinate_finset_sum_complex
    {n : ℕ} {ι : Type*} (s : Finset ι)
    (ψ : ι → LogSpace n → ℂ)
    (hψ : ∀ i ∈ s, ContDiff ℝ 1 (ψ i))
    (j : Fin n) (z : LogSpace n) :
    barPartialCoordinate (fun w => ∑ i ∈ s, ψ i w) z j =
      ∑ i ∈ s, barPartialCoordinate (ψ i) z j := by
  unfold barPartialCoordinate
  rw [fderiv_fun_sum
    (fun i hi => (hψ i hi).differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true]) z)]
  simp only [_root_.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib, div_eq_mul_inv,
    Finset.sum_mul]

end TorusWeightedCoverGlobalGreen

namespace TorusWeightedAdjointMollification

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedTorusDistributionBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault TorusWeakDolbeaultMollification
open TorusFriedrichsMollifierEstimates TorusMollifiedBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private def angularMollifiedPhysicalAdjointDriftCommutator
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a) (k : ℕ)
    (x : LogSpace n) : ℂ :=
  ∑ j : Fin n,
    normalizedCoverComplexDriftCommutator
      (fun z : LogSpace n =>
        holomorphicCoordinate
          (fun y => (angularCoverPotential a y : ℂ)) z j)
      (complexTorusCoverLift
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) j)) k x

private theorem coverFormAdjoint_angularGraphMollifiedPhysicalField_eq
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a) (k : ℕ) (x : LogSpace n) :
    coverFormAdjoint (angularCoverPotential a)
      (angularGraphMollifiedPhysicalField W k) x =
      (∑ j : Fin n,
        (holomorphicCoordinate
          (normalizedCoverMollification
            (complexTorusCoverLift
              (fun q : LogTorus n =>
                (W q : EuclideanSpace ℂ (Fin n)) j)) k)
          x j -
        normalizedCoverMollification
          (fun y : LogSpace n =>
            holomorphicCoordinate
              (fun v => (angularCoverPotential a v : ℂ)) y j *
              complexTorusCoverLift
                (fun q : LogTorus n =>
                  (W q : EuclideanSpace ℂ (Fin n)) j) y) k x)) +
      angularMollifiedPhysicalAdjointDriftCommutator W k x := by
  simp only [coverFormAdjoint, weightedHolomorphicDerivative,
    angularGraphMollifiedPhysicalField,
    angularMollifiedPhysicalAdjointDriftCommutator,
    normalizedCoverComplexDriftCommutator,
    Finset.sum_sub_distrib]
  have hcomm :
      (∑ j : Fin n,
        normalizedCoverMollification
          (complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j)) k x *
          holomorphicCoordinate
            (fun y => (angularCoverPotential a y : ℂ)) x j) =
      (∑ j : Fin n,
        holomorphicCoordinate
          (fun y => (angularCoverPotential a y : ℂ)) x j *
        normalizedCoverMollification
          (complexTorusCoverLift
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j)) k x) := by
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcomm]
  ring

private theorem complex_norm_add_sq_le_two_mul_add (u v : ℂ) :
    ‖u + v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
  have h := norm_add_le u v
  have hu : 0 ≤ ‖u‖ := norm_nonneg _
  have hv : 0 ≤ ‖v‖ := norm_nonneg _
  have hs : 0 ≤ ‖u + v‖ := norm_nonneg _
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

private theorem finite_complex_local_square_integral_sum_tendsto_zero
    {n : ℕ} {ι : Type*}
    (s : Finset ι)
    (g : ι → ℕ → LogSpace n → ℂ)
    {K : Set (LogSpace n)} (hK : IsCompact K)
    (hcontinuous : ∀ i ∈ s, ∀ k : ℕ, Continuous (g i k))
    (hvanish : ∀ i ∈ s,
      Tendsto
        (fun k : ℕ =>
          ∫ x in K, ‖g i k x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
        atTop (nhds 0)) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K, ‖∑ i ∈ s, g i k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.sum_empty, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow,
               integral_zero, tendsto_const_nhds_iff]
  | @insert i s hi ih =>
    have hice : ∀ k : ℕ, Continuous (g i k) :=
      fun k => hcontinuous i (Finset.mem_insert_self i s) k
    have hsce : ∀ j ∈ s, ∀ k : ℕ, Continuous (g j k) := by
      intro j hj k
      exact hcontinuous j (Finset.mem_insert_of_mem hj) k
    have hival :
        Tendsto
          (fun k : ℕ =>
            ∫ x in K, ‖g i k x‖ ^ 2
              ∂(volume : Measure (LogSpace n)))
          atTop (nhds 0) :=
      hvanish i (Finset.mem_insert_self i s)
    have hsval : ∀ j ∈ s,
        Tendsto
          (fun k : ℕ =>
            ∫ x in K, ‖g j k x‖ ^ 2
              ∂(volume : Measure (LogSpace n)))
          atTop (nhds 0) := by
      intro j hj
      exact hvanish j (Finset.mem_insert_of_mem hj)
    have hrest := ih hsce hsval
    have hbound (k : ℕ) :
        (∫ x in K, ‖∑ j ∈ insert i s, g j k x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) ≤
        2 *
          ((∫ x in K, ‖g i k x‖ ^ 2
              ∂(volume : Measure (LogSpace n))) +
           (∫ x in K, ‖∑ j ∈ s, g j k x‖ ^ 2
              ∂(volume : Measure (LogSpace n)))) := by
      have hci : Continuous (fun x : LogSpace n => ‖g i k x‖ ^ 2) :=
        (hice k).norm.pow 2
      have hcs : Continuous
          (fun x : LogSpace n => ‖∑ j ∈ s, g j k x‖ ^ 2) :=
        (continuous_finsetSum s (fun j hj => hsce j hj k)).norm.pow 2
      have hinti : IntegrableOn
          (fun x : LogSpace n => ‖g i k x‖ ^ 2) K
          (volume : Measure (LogSpace n)) :=
        hci.locallyIntegrable.integrableOn_isCompact hK
      have hints : IntegrableOn
          (fun x : LogSpace n => ‖∑ j ∈ s, g j k x‖ ^ 2) K
          (volume : Measure (LogSpace n)) :=
        hcs.locallyIntegrable.integrableOn_isCompact hK
      have hintadd : IntegrableOn
          (fun x : LogSpace n =>
            2 * (‖g i k x‖ ^ 2 + ‖∑ j ∈ s, g j k x‖ ^ 2)) K
          (volume : Measure (LogSpace n)) :=
        (hinti.add hints).const_mul (2 : ℝ)
      have hcadd : Continuous
          (fun x : LogSpace n =>
            ‖g i k x + ∑ j ∈ s, g j k x‖ ^ 2) :=
        ((hice k).add
          (continuous_finsetSum s
            (fun j hj => hsce j hj k))).norm.pow 2
      have hintleft : IntegrableOn
          (fun x : LogSpace n =>
            ‖g i k x + ∑ j ∈ s, g j k x‖ ^ 2) K
          (volume : Measure (LogSpace n)) :=
        hcadd.locallyIntegrable.integrableOn_isCompact hK
      calc
        (∫ x in K, ‖∑ j ∈ insert i s, g j k x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) =
          ∫ x in K, ‖g i k x + ∑ j ∈ s, g j k x‖ ^ 2
            ∂(volume : Measure (LogSpace n)) := by
              simp only [hi, not_false_eq_true, Finset.sum_insert]
        _ ≤ ∫ x in K,
              2 * (‖g i k x‖ ^ 2 + ‖∑ j ∈ s, g j k x‖ ^ 2)
              ∂(volume : Measure (LogSpace n)) := by
          apply MeasureTheory.setIntegral_mono
          · exact hintleft
          · exact hintadd
          · intro x
            exact complex_norm_add_sq_le_two_mul_add
              (g i k x) (∑ j ∈ s, g j k x)
        _ = 2 *
          ((∫ x in K, ‖g i k x‖ ^ 2
              ∂(volume : Measure (LogSpace n))) +
           (∫ x in K, ‖∑ j ∈ s, g j k x‖ ^ 2
              ∂(volume : Measure (LogSpace n)))) := by
          rw [integral_const_mul, integral_add hinti hints]
    have hupper :
        Tendsto
          (fun k : ℕ =>
            2 *
              ((∫ x in K, ‖g i k x‖ ^ 2
                  ∂(volume : Measure (LogSpace n))) +
               (∫ x in K, ‖∑ j ∈ s, g j k x‖ ^ 2
                  ∂(volume : Measure (LogSpace n)))))
          atTop (nhds 0) := by
      (convert (hival.add hrest).const_mul (2 : ℝ) using 1; norm_num)
    exact squeeze_zero
      (fun k => integral_nonneg (fun x => sq_nonneg _))
      hbound hupper

end TorusWeightedAdjointMollification

namespace TorusWeightedDensityConvolutionDivergence

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters DolbeaultRegularity
open DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity
open TorusWeakDolbeaultMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem holomorphicCoordinate_normalizedCoverMollification_eq_kernel
    {n : ℕ} {g : LogSpace n → ℂ}
    (hg : LocallyIntegrable g (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) (j : Fin n) :
    holomorphicCoordinate (normalizedCoverMollification g k) x j =
      -(∫ y : LogSpace n,
        g y *
          conj (barPartialCoordinate
            (fun z : LogSpace n =>
              ((complexShrinkingBump (n := n) k).normed
                (volume : Measure (LogSpace n)) (x - z) : ℂ)) y j)
        ∂(volume : Measure (LogSpace n))) := by
  let E := LogSpace n
  let μ : Measure E := volume
  let L : ℂ →L[ℝ] ℝ →L[ℝ] ℂ := complexRealMultiplication
  let κ : E → ℝ :=
    (complexShrinkingBump (n := n) k).normed μ
  let v₀ : E := Pi.single j (1 : ℂ)
  let v₁ : E := Pi.single j Complex.I
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hκcompact : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hderiv := hκcompact.hasFDerivAt_convolution_right
    L hg hκ x
  have hint : Integrable
      (fun t : E =>
        (L.precompR E) (g t) (fderiv ℝ κ (x - t))) μ :=
    (hκcompact.fderiv ℝ).convolutionExists_right
      (L.precompR E) hg
        (hκ.continuous_fderiv (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) x
  have hfirst : Integrable
      (fun t : E => g t * ((fderiv ℝ κ (x - t)) v₀ : ℂ)) μ := by
    have h := hint.apply_continuousLinearMap v₀
    apply h.congr
    filter_upwards [] with t
    simp only [complexRealMultiplication, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.lsmul_flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      Complex.real_smul, mul_comm, L]
  have hsecond : Integrable
      (fun t : E => g t * ((fderiv ℝ κ (x - t)) v₁ : ℂ)) μ := by
    have h := hint.apply_continuousLinearMap v₁
    apply h.congr
    filter_upwards [] with t
    simp only [complexRealMultiplication, ContinuousLinearMap.precompR_apply,
      ContinuousLinearMap.lsmul_flip_apply, ContinuousLinearMap.compL_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply,
      Complex.real_smul, mul_comm, L]
  have htranslated :
      Differentiable ℝ (fun t : E => κ (x - t)) :=
    (translatedRealKernel_contDiff hκ x).differentiable (by simp only [ne_eq, one_ne_zero,
      not_false_eq_true])
  have hkernel (y : E) :
      conj (barPartialCoordinate
        (fun z : E => (κ (x - z) : ℂ)) y j) =
      -((((fderiv ℝ κ (x - y)) v₀ : ℂ) -
        Complex.I * ((fderiv ℝ κ (x - y)) v₁ : ℂ)) / 2) := by
    unfold barPartialCoordinate
    rw [fderiv_complexOfReal htranslated y v₀,
      fderiv_complexOfReal htranslated y v₁,
      translatedRealKernel_fderiv hκ x y v₀,
      translatedRealKernel_fderiv hκ x y v₁]
    (simp only [Complex.ofReal_neg, mul_neg, div_eq_mul_inv, map_mul, map_add, map_neg,
      Complex.conj_ofReal, Complex.conj_I, neg_mul, neg_neg, map_inv₀, map_ofNat]; ring)
  change
    holomorphicCoordinate
      (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, μ] g) x j =
      -(∫ y : E,
        g y *
          conj (barPartialCoordinate
            (fun z : E => (κ (x - z) : ℂ)) y j)
        ∂μ)
  rw [← complex_convolution_flip]
  unfold holomorphicCoordinate
  rw [hderiv.fderiv, MeasureTheory.convolution_def,
    ContinuousLinearMap.integral_apply hint v₀,
    ContinuousLinearMap.integral_apply hint v₁]
  change
    ((∫ y : E,
      (L (g y)) ((fderiv ℝ κ (x - y)) v₀) ∂μ) -
      Complex.I *
        (∫ y : E,
          (L (g y)) ((fderiv ℝ κ (x - y)) v₁) ∂μ)) / 2 =
    -(∫ y : E,
      g y *
        conj (barPartialCoordinate
          (fun z : E => (κ (x - z) : ℂ)) y j)
      ∂μ)
  have hsplit :
      (∫ y : E,
        (g y * ((fderiv ℝ κ (x - y)) v₀ : ℂ) -
          Complex.I *
            (g y * ((fderiv ℝ κ (x - y)) v₁ : ℂ))) / 2
        ∂μ) =
      ((∫ y : E,
        g y * ((fderiv ℝ κ (x - y)) v₀ : ℂ) ∂μ) -
        Complex.I *
          (∫ y : E,
            g y * ((fderiv ℝ κ (x - y)) v₁ : ℂ) ∂μ)) / 2 := by
    rw [integral_div,
      integral_sub hfirst (hsecond.const_mul Complex.I),
      integral_const_mul]
  calc
    ((∫ y : E,
      (L (g y)) ((fderiv ℝ κ (x - y)) v₀) ∂μ) -
      Complex.I *
        (∫ y : E,
          (L (g y)) ((fderiv ℝ κ (x - y)) v₁) ∂μ)) / 2 =
      ∫ y : E,
        (g y * ((fderiv ℝ κ (x - y)) v₀ : ℂ) -
          Complex.I *
            (g y * ((fderiv ℝ κ (x - y)) v₁ : ℂ))) / 2
        ∂μ := by
      simpa only [complexRealMultiplication_apply, mul_comm, L] using hsplit.symm
    _ = -(∫ y : E,
      g y *
        conj (barPartialCoordinate
          (fun z : E => (κ (x - z) : ℂ)) y j)
      ∂μ) := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [hkernel y]
      ring

private theorem normalizedCoverMollification_eq_kernel_integral
    {n : ℕ} (g : LogSpace n → ℂ)
    (k : ℕ) (x : LogSpace n) :
    normalizedCoverMollification g k x =
      ∫ y : LogSpace n,
        g y *
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) : ℂ)
        ∂(volume : Measure (LogSpace n)) := by
  unfold normalizedCoverMollification
  rw [← complex_convolution_flip,
    MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [complexRealMultiplication_apply, mul_comm]

end TorusWeightedDensityConvolutionDivergence

namespace TorusDensityAdaptedWeightedAdjoint

open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultGraphDistributionBridge WeightedDolbeaultBochnerIdentity
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem holomorphicCoordinate_complexCoverWeight
    {n : ℕ} {a : LogSpace n → ℝ}
    (ha : ContDiff ℝ 1 a) (x : LogSpace n) (j : Fin n) :
    holomorphicCoordinate (complexCoverWeight a) x j =
      -complexCoverWeight a x *
        holomorphicCoordinate (fun y => (a y : ℂ)) x j := by
  unfold holomorphicCoordinate
  rw [fderiv_complexCoverWeight ha x (Pi.single j (1 : ℂ)),
    fderiv_complexCoverWeight ha x (Pi.single j Complex.I),
    fderiv_complexOfReal
      (ha.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) x (Pi.single j
        (1 : ℂ)),
    fderiv_complexOfReal
      (ha.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) x (Pi.single j
        Complex.I)]
  ring

end TorusDensityAdaptedWeightedAdjoint

namespace TorusCompactTestGreen

open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity TorusWeakDolbeaultMollification
open TorusMollificationLocalL2Bounds
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem normalizedCoverMollification_tendsto_of_continuous
    {n : ℕ} {g : LogSpace n → ℂ}
    (hg : Continuous g) (x : LogSpace n) :
    Tendsto (fun k : ℕ => normalizedCoverMollification g k x)
      atTop (nhds (g x)) := by
  exact ContDiffBump.convolution_tendsto_right_of_continuous
    (complexShrinkingBump_rOut_tendsto (n := n)) hg x

private theorem tsupport_normalizedCoverMollification_subset_cthickening
    {n : ℕ} {g : LogSpace n → ℂ}
    (k : ℕ) :
    tsupport (normalizedCoverMollification g k) ⊆
      Metric.cthickening 1 (tsupport g) := by
  apply closure_minimal _ Metric.isClosed_cthickening
  intro x hx
  have hs := MeasureTheory.support_convolution_subset_swap
    (ContinuousLinearMap.lsmul ℝ ℝ) hx
  obtain ⟨u, hu, v, hv, huv⟩ := hs
  have hvball : v ∈ Metric.ball (0 : LogSpace n)
      (complexShrinkingBump (n := n) k).rOut := by
    rw [← (complexShrinkingBump (n := n) k).support_normed_eq
      (μ := (volume : Measure (LogSpace n)))]
    exact hv
  have hvnorm : ‖v‖ ≤ 1 := by
    have hvlt : ‖v‖ < (complexShrinkingBump (n := n) k).rOut := by
      simpa only [Metric.mem_ball, dist_zero_right] using hvball
    exact hvlt.le.trans (complexShrinkingBump_rOut_le_one k)
  subst x
  apply Metric.mem_cthickening_of_dist_le
    (u + v) u 1 (tsupport g) (subset_closure hu)
  simpa only [dist_eq_norm, add_sub_cancel_left] using hvnorm

private theorem norm_normalizedCoverMollification_le_of_continuous_bound
    {n : ℕ} {g : LogSpace n → ℂ}
    (hg : Continuous g) {B : ℝ}
    (hB : 0 ≤ B) (hgb : ∀ x : LogSpace n, ‖g x‖ ≤ B)
    (k : ℕ) (x : LogSpace n) :
    ‖normalizedCoverMollification g k x‖ ≤ B := by
  have ht := MeasureTheory.dist_convolution_le
    (μ := (volume : Measure (LogSpace n)))
    (f := (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n)))
    (g := g) (x₀ := x)
    (R := (complexShrinkingBump (n := n) k).rOut)
    (ε := B) (z₀ := (0 : ℂ)) hB
    (by
      rw [(complexShrinkingBump (n := n) k).support_normed_eq])
    ((complexShrinkingBump (n := n) k).nonneg_normed)
    ((complexShrinkingBump (n := n) k).integral_normed)
    hg.aestronglyMeasurable
    (by
      intro y _
      simpa only [dist_zero_right] using hgb y)
  simpa only [normalizedCoverMollification, ge_iff_le, dist_zero_right] using ht

end TorusCompactTestGreen

namespace TorusStrongCoverMollification

open Set Function Filter MeasureTheory
open TorusCharacters MatrixTorusBochnerCoreApproximation TorusWeakDolbeaultMollification
open TorusMollificationLocalL2Bounds TorusCompactTestGreen
open scoped ENNReal Topology ContDiff Convolution

private theorem normalizedCoverMollification_L2_norm_le
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) :
    ‖(normalizedCoverMollification_memLp hh k).toLp
      (normalizedCoverMollification h k)‖ ≤
    ‖hh.toLp h‖ := by
  have hsq :
      ‖(normalizedCoverMollification_memLp hh k).toLp
        (normalizedCoverMollification h k)‖ ^ 2 ≤
      ‖hh.toLp h‖ ^ 2 := by
    calc
      ‖(normalizedCoverMollification_memLp hh k).toLp
        (normalizedCoverMollification h k)‖ ^ 2 =
        ∫ x : LogSpace n,
          ‖normalizedCoverMollification h k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
            rw [complexLp_norm_sq_eq_integral]
            apply integral_congr_ae
            filter_upwards
              [(normalizedCoverMollification_memLp hh k).coeFn_toLp]
              with x hx
            rw [hx]
      _ ≤ ∫ x : LogSpace n, ‖h x‖ ^ 2
          ∂(volume : Measure (LogSpace n)) :=
            integral_norm_sq_normalizedCoverMollification_le hh k
      _ = ‖hh.toLp h‖ ^ 2 := by
            rw [complexLp_norm_sq_eq_integral]
            apply integral_congr_ae
            filter_upwards [hh.coeFn_toLp] with x hx
            rw [hx]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem tendsto_integral_norm_sq_normalizedCoverMollification_sub_of_continuous_compact
    {n : ℕ} {h : LogSpace n → ℂ}
    (hc : Continuous h) (hs : HasCompactSupport h) :
    Tendsto
      (fun k : ℕ =>
        ∫ x : LogSpace n,
          ‖normalizedCoverMollification h k x - h x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  obtain ⟨B, hB⟩ := hc.bounded_above_of_compact_support hs
  have hB₀ : 0 ≤ B := (norm_nonneg (h 0)).trans (hB 0)
  let S : Set (LogSpace n) := Metric.cthickening 1 (tsupport h)
  have hS : IsCompact S := hs.cthickening
  have hsubset : tsupport h ⊆ S := by
    intro x hx
    apply Metric.mem_cthickening_of_dist_le x x 1 (tsupport h) hx
    simp only [dist_self, zero_le_one]
  have hdom : Integrable
      (S.indicator
        (fun _ : LogSpace n => (2 * B) ^ 2))
      (volume : Measure (LogSpace n)) := by
    apply IntegrableOn.integrable_indicator _ hS.measurableSet
    exact continuous_const.continuousOn.integrableOn_compact hS
  have hconv := MeasureTheory.tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure (LogSpace n)))
    (F := fun k : ℕ => fun x : LogSpace n =>
      ‖normalizedCoverMollification h k x - h x‖ ^ 2)
    (f := fun _ : LogSpace n => (0 : ℝ))
    (S.indicator (fun _ : LogSpace n => (2 * B) ^ 2))
    (by
      intro k
      exact (((contDiff_normalizedCoverMollification
        hc.locallyIntegrable k 0).continuous.sub hc).norm.pow 2).aestronglyMeasurable)
    hdom
    (by
      intro k
      filter_upwards [] with x
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      by_cases hx : x ∈ S
      · rw [Set.indicator_of_mem hx]
        apply (sq_le_sq₀ (norm_nonneg _)
          (mul_nonneg (by norm_num) hB₀)).mpr
        calc
          ‖normalizedCoverMollification h k x - h x‖ ≤
              ‖normalizedCoverMollification h k x‖ + ‖h x‖ :=
                norm_sub_le _ _
          _ ≤ B + B := add_le_add
            (norm_normalizedCoverMollification_le_of_continuous_bound
              hc hB₀ hB k x) (hB x)
          _ = 2 * B := by ring
      · have hmx : normalizedCoverMollification h k x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hm
          exact hx
            (tsupport_normalizedCoverMollification_subset_cthickening
              k hm)
        have hhx : h x = 0 := by
          apply image_eq_zero_of_notMem_tsupport
          intro hh
          exact hx (hsubset hh)
        simp only [hmx, hhx, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
          zero_pow,
          Set.indicator_of_notMem hx, Std.le_refl])
    (by
      filter_upwards [] with x
      have ht : Tendsto
          (fun k : ℕ =>
            normalizedCoverMollification h k x - h x)
          atTop (nhds (0 : ℂ)) := by
        simpa only [sub_self] using
          (normalizedCoverMollification_tendsto_of_continuous
            hc x).sub (tendsto_const_nhds (x := h x))
      simpa only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
        zero_pow] using ht.norm.pow 2)
  simpa only [integral_zero] using hconv

private theorem normalizedCoverMollification_continuous_compact_L2_tendsto
    {n : ℕ} {h : LogSpace n → ℂ}
    (hc : Continuous h) (hs : HasCompactSupport h) :
    Tendsto
      (fun k : ℕ =>
        (normalizedCoverMollification_memLp
          (hc.memLp_of_hasCompactSupport hs) k).toLp
            (normalizedCoverMollification h k))
      atTop
      (nhds
        ((hc.memLp_of_hasCompactSupport hs).toLp h)) := by
  let hh : MemLp h 2 (volume : Measure (LogSpace n)) :=
    hc.memLp_of_hasCompactSupport hs
  change Tendsto
    (fun k : ℕ =>
      (normalizedCoverMollification_memLp hh k).toLp
        (normalizedCoverMollification h k))
    atTop (nhds (hh.toLp h))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq (k : ℕ) :
      ‖(normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k) -
        hh.toLp h‖ ^ 2 =
      ∫ x : LogSpace n,
        ‖normalizedCoverMollification h k x - h x‖ ^ 2
        ∂(volume : Measure (LogSpace n)) := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards
      [MeasureTheory.Lp.coeFn_sub
        ((normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k)) (hh.toLp h),
       (normalizedCoverMollification_memLp hh k).coeFn_toLp,
       hh.coeFn_toLp]
      with x hsub hmoll hx
    rw [hsub]
    change
      ‖((normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k)) x -
        (hh.toLp h) x‖ ^ 2 = _
    rw [hmoll, hx]
  have hsqtendsto :
      Tendsto
        (fun k : ℕ =>
          ‖(normalizedCoverMollification_memLp hh k).toLp
              (normalizedCoverMollification h k) -
            hh.toLp h‖ ^ 2)
        atTop (nhds 0) := by
    simpa only [hsq] using
      tendsto_integral_norm_sq_normalizedCoverMollification_sub_of_continuous_compact
        hc hs
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    hsqtendsto
  simpa only [comp_def, norm_nonneg, Real.sqrt_sq, Real.sqrt_zero] using hsqrt

end TorusStrongCoverMollification

namespace TorusClosedMollifierAdjoint

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity WeightedTorusDolbeault
open TorusDensityAdaptedWeightedAdjoint
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private def translatedDensityCancelledCoverKernel
    {n : ℕ} (a : LogTorus n → ℝ)
    (k : ℕ) (x : LogSpace n) (y : LogSpace n) : ℝ :=
  (complexShrinkingBump (n := n) k).normed
    (volume : Measure (LogSpace n)) (x - y) /
    coverWeight (angularCoverPotential a) y

private theorem contDiff_translatedDensityCancelledCoverKernel
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 1 (angularCoverPotential a))
    (k : ℕ) (x : LogSpace n) :
    ContDiff ℝ 1 (translatedDensityCancelledCoverKernel a k x) := by
  unfold translatedDensityCancelledCoverKernel
  exact ((complexShrinkingBump (n := n) k).contDiff_normed.comp
    (contDiff_const.sub contDiff_id)).div
      (contDiff_coverWeight ha)
      (fun y => (coverWeight_pos (angularCoverPotential a) y).ne')

private theorem hasCompactSupport_translatedDensityCancelledCoverKernel
    {n : ℕ} (a : LogTorus n → ℝ)
    (k : ℕ) (x : LogSpace n) :
    HasCompactSupport (translatedDensityCancelledCoverKernel a k x) := by
  have hκ := (complexShrinkingBump (n := n) k).hasCompactSupport_normed
    (μ := (volume : Measure (LogSpace n)))
  have ht := translatedRealKernel_hasCompactSupport hκ x
  have hm : HasCompactSupport
      (fun y : LogSpace n =>
        (complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) (x - y) *
        (coverWeight (angularCoverPotential a) y)⁻¹) := ht.mul_right
  have hkernel :
      translatedDensityCancelledCoverKernel a k x =
        (fun y : LogSpace n =>
          (complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) *
          (coverWeight (angularCoverPotential a) y)⁻¹) := by
    funext y
    exact div_eq_mul_inv _ _
  rw [hkernel]
  exact hm

private theorem complexCoverWeight_mul_translatedDensityCancelledCoverKernel
    {n : ℕ} (a : LogTorus n → ℝ)
    (k : ℕ) (x y : LogSpace n) :
    complexCoverWeight (angularCoverPotential a) y *
      (translatedDensityCancelledCoverKernel a k x y : ℂ) =
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) : ℂ) := by
  unfold translatedDensityCancelledCoverKernel complexCoverWeight
  push_cast
  have hne : (coverWeight (angularCoverPotential a) y : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (coverWeight_pos (angularCoverPotential a) y).ne'
  field_simp

private theorem complexCoverWeight_mul_conj_barPartial_translatedDensityCancelledCoverKernel
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : ContDiff ℝ 1 (angularCoverPotential a))
    (k : ℕ) (x y : LogSpace n) (j : Fin n) :
    complexCoverWeight (angularCoverPotential a) y *
      conj (barPartialCoordinate
        (fun z : LogSpace n =>
          (translatedDensityCancelledCoverKernel a k x z : ℂ)) y j) =
      conj (barPartialCoordinate
        (fun z : LogSpace n =>
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - z) : ℂ)) y j) +
      ((complexShrinkingBump (n := n) k).normed
        (volume : Measure (LogSpace n)) (x - y) : ℂ) *
        holomorphicCoordinate
          (fun z : LogSpace n =>
            (angularCoverPotential a z : ℂ)) y j := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let χ : LogSpace n → ℝ :=
    translatedDensityCancelledCoverKernel a k x
  let d : LogSpace n → ℂ :=
    complexCoverWeight (angularCoverPotential a)
  let ψ : LogSpace n → ℂ := fun z => (χ z : ℂ)
  let η : LogSpace n → ℂ := fun z => (κ (x - z) : ℂ)
  have hχ : ContDiff ℝ 1 χ :=
    contDiff_translatedDensityCancelledCoverKernel ha k x
  have hψ : ContDiff ℝ 1 ψ :=
    Complex.ofRealCLM.contDiff.comp hχ
  have hd : ContDiff ℝ 1 d := contDiff_complexCoverWeight ha
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hηreal : Differentiable ℝ (fun z : LogSpace n => κ (x - z)) :=
    (hκ.comp (contDiff_const.sub contDiff_id)).differentiable (by simp only [ne_eq, one_ne_zero,
      not_false_eq_true])
  have hproduct : (fun z : LogSpace n => d z * ψ z) = η := by
    funext z
    exact complexCoverWeight_mul_translatedDensityCancelledCoverKernel
      a k x z
  have hmul :
      holomorphicCoordinate η y j =
        d y * holomorphicCoordinate ψ y j +
          ψ y *
            (-d y * holomorphicCoordinate
              (fun z : LogSpace n =>
                (angularCoverPotential a z : ℂ)) y j) := by
    calc
      holomorphicCoordinate η y j =
          holomorphicCoordinate (fun z => d z * ψ z) y j := by
            rw [hproduct]
      _ = d y * holomorphicCoordinate ψ y j +
          ψ y * holomorphicCoordinate d y j :=
        holomorphicCoordinate_mul
          (hd.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true]))
          (hψ.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) y j
      _ = _ := by
        rw [holomorphicCoordinate_complexCoverWeight ha y j]
  change
    d y * conj (barPartialCoordinate ψ y j) =
      conj (barPartialCoordinate η y j) +
      η y * holomorphicCoordinate
        (fun z : LogSpace n =>
          (angularCoverPotential a z : ℂ)) y j
  rw [conj_barPartialCoordinate_real
        (hχ.differentiable (by simp only [ne_eq, one_ne_zero, not_false_eq_true])) y j,
      conj_barPartialCoordinate_real hηreal y j]
  have hp := congrFun hproduct y
  rw [← hp]
  rw [hmul]
  ring

end TorusClosedMollifierAdjoint

namespace TorusStrongCoverMollificationDensity

open Set Function Filter MeasureTheory Matrix
open TorusCharacters DolbeaultRegularity MatrixTorusBochnerCoreApproximation
open TorusWeakDolbeaultMollification TorusMollificationLocalL2Bounds TorusStrongCoverMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem normalizedCoverMollification_sub
    {n : ℕ} {g h : LogSpace n → ℂ}
    (hg : MemLp g 2 (volume : Measure (LogSpace n)))
    (hh : MemLp h 2 (volume : Measure (LogSpace n)))
    (k : ℕ) (x : LogSpace n) :
    normalizedCoverMollification (fun y => g y - h y) k x =
      normalizedCoverMollification g k x -
        normalizedCoverMollification h k x := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  have hc : Continuous κ :=
    (complexShrinkingBump (n := n) k).continuous_normed
  have hs : HasCompactSupport κ :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
  have hgi := (hs.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hc
      (hg.locallyIntegrable (by norm_num))) x
  have hhi := (hs.convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) hc
      (hh.locallyIntegrable (by norm_num))) x
  change
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))]
      (fun y => g y - h y)) x =
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))] g) x -
    (κ ⋆[ContinuousLinearMap.lsmul ℝ ℝ,
      (volume : Measure (LogSpace n))] h) x
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def,
    MeasureTheory.convolution_def,
    ← MeasureTheory.integral_sub hgi hhi]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [ContinuousLinearMap.map_sub, ContinuousLinearMap.lsmul_apply, Complex.real_smul]

private def normalizedCoverMollificationL2
    {n : ℕ} (k : ℕ)
    (u : MeasureTheory.Lp ℂ 2 (volume : Measure (LogSpace n))) :
    MeasureTheory.Lp ℂ 2 (volume : Measure (LogSpace n)) :=
  (normalizedCoverMollification_memLp (MeasureTheory.Lp.memLp u) k).toLp
    (normalizedCoverMollification (fun x : LogSpace n => u x) k)

private theorem normalizedCoverMollificationL2_sub
    {n : ℕ} (k : ℕ)
    (u v : MeasureTheory.Lp ℂ 2 (volume : Measure (LogSpace n))) :
    normalizedCoverMollificationL2 k u -
      normalizedCoverMollificationL2 k v =
    (normalizedCoverMollification_memLp
      ((MeasureTheory.Lp.memLp u).sub (MeasureTheory.Lp.memLp v)) k).toLp
      (normalizedCoverMollification
        (fun x : LogSpace n => u x - v x) k) := by
  let hmem : MemLp (fun x : LogSpace n => u x - v x)
      2 (volume : Measure (LogSpace n)) :=
    (MeasureTheory.Lp.memLp u).sub (MeasureTheory.Lp.memLp v)
  change
    normalizedCoverMollificationL2 k u -
      normalizedCoverMollificationL2 k v =
      (normalizedCoverMollification_memLp hmem k).toLp
        (normalizedCoverMollification
          (fun x : LogSpace n => u x - v x) k)
  apply MeasureTheory.Lp.ext
  filter_upwards
    [MeasureTheory.Lp.coeFn_sub
      (normalizedCoverMollificationL2 k u)
      (normalizedCoverMollificationL2 k v),
     (normalizedCoverMollification_memLp
       (MeasureTheory.Lp.memLp u) k).coeFn_toLp,
     (normalizedCoverMollification_memLp
       (MeasureTheory.Lp.memLp v) k).coeFn_toLp,
     (normalizedCoverMollification_memLp hmem k).coeFn_toLp]
    with x hsub hu hv hdiff
  rw [hsub]
  change
    (normalizedCoverMollificationL2 k u) x -
      (normalizedCoverMollificationL2 k v) x = _
  change
    ((normalizedCoverMollification_memLp
        (MeasureTheory.Lp.memLp u) k).toLp
      (normalizedCoverMollification (fun x : LogSpace n => u x) k)) x -
    ((normalizedCoverMollification_memLp
        (MeasureTheory.Lp.memLp v) k).toLp
      (normalizedCoverMollification (fun x : LogSpace n => v x) k)) x = _
  rw [hu, hv, hdiff,
    normalizedCoverMollification_sub
      (MeasureTheory.Lp.memLp u) (MeasureTheory.Lp.memLp v) k x]

private theorem normalizedCoverMollificationL2_dist_le
    {n : ℕ} (k : ℕ)
    (u v : MeasureTheory.Lp ℂ 2 (volume : Measure (LogSpace n))) :
    dist (normalizedCoverMollificationL2 k u)
      (normalizedCoverMollificationL2 k v) ≤ dist u v := by
  rw [dist_eq_norm, normalizedCoverMollificationL2_sub]
  let hmem : MemLp (fun x : LogSpace n => u x - v x)
      2 (volume : Measure (LogSpace n)) :=
    (MeasureTheory.Lp.memLp u).sub (MeasureTheory.Lp.memLp v)
  have hc := normalizedCoverMollification_L2_norm_le hmem k
  rw [dist_eq_norm]
  calc
    _ ≤ ‖hmem.toLp
          (fun x : LogSpace n => u x - v x)‖ := hc
    _ = ‖u - v‖ := by
      congr 1
      apply MeasureTheory.Lp.ext
      filter_upwards
        [hmem.coeFn_toLp,
         MeasureTheory.Lp.coeFn_sub u v] with x hx hsub
      rw [hx, hsub]
      rfl

private theorem normalizedCoverMollification_congr_ae
    {n : ℕ} {g h : LogSpace n → ℂ}
    (hgh : g =ᵐ[(volume : Measure (LogSpace n))] h)
    (k : ℕ) :
    normalizedCoverMollification g k =
      normalizedCoverMollification h k := by
  unfold normalizedCoverMollification
  exact MeasureTheory.convolution_congr
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (Filter.Eventually.of_forall (fun _ => rfl)) hgh

private theorem normalizedCoverMollificationL2_toLp
    {n : ℕ} {g : LogSpace n → ℂ}
    (hg : MemLp g 2 (volume : Measure (LogSpace n)))
    (k : ℕ) :
    normalizedCoverMollificationL2 k (hg.toLp g) =
      (normalizedCoverMollification_memLp hg k).toLp
        (normalizedCoverMollification g k) := by
  apply MeasureTheory.Lp.ext
  filter_upwards
    [(normalizedCoverMollification_memLp
      (MeasureTheory.Lp.memLp (hg.toLp g)) k).coeFn_toLp,
     (normalizedCoverMollification_memLp hg k).coeFn_toLp]
    with x hleft hright
  change
    ((normalizedCoverMollification_memLp
      (MeasureTheory.Lp.memLp (hg.toLp g)) k).toLp
        (normalizedCoverMollification
          (fun y : LogSpace n => (hg.toLp g) y) k)) x = _
  rw [hleft, hright]
  exact congrFun
    (normalizedCoverMollification_congr_ae hg.coeFn_toLp k) x

private theorem normalizedCoverMollificationL2_tendsto
    {n : ℕ}
    (u : MeasureTheory.Lp ℂ 2 (volume : Measure (LogSpace n))) :
    Tendsto
      (fun k : ℕ => normalizedCoverMollificationL2 k u)
      atTop (nhds u) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hquarter : 0 < ε / 4 := by positivity
  have hdense :
      Dense
        {v : MeasureTheory.Lp ℂ 2
            (volume : Measure (LogSpace n)) |
          ∃ g : LogSpace n → ℂ,
            v =ᵐ[(volume : Measure (LogSpace n))] g ∧
              HasCompactSupport g ∧ ContDiff ℝ ∞ g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  obtain ⟨v, ⟨g, hvg, hgs, hgd⟩, huv⟩ :=
    hdense.exists_dist_lt u hquarter
  let hg : MemLp g 2 (volume : Measure (LogSpace n)) :=
    hgd.continuous.memLp_of_hasCompactSupport hgs
  have hv : v = hg.toLp g := by
    apply MeasureTheory.Lp.ext
    exact hvg.trans hg.coeFn_toLp.symm
  have hvconv :
      Tendsto
        (fun k : ℕ => normalizedCoverMollificationL2 k v)
        atTop (nhds v) := by
    subst v
    simpa only [normalizedCoverMollificationL2_toLp] using
      normalizedCoverMollification_continuous_compact_L2_tendsto
        hgd.continuous hgs
  obtain ⟨N, hN⟩ :=
    (Metric.tendsto_atTop.mp hvconv) (ε / 4) hquarter
  refine ⟨N, fun k hk => ?_⟩
  calc
    dist (normalizedCoverMollificationL2 k u) u ≤
        dist (normalizedCoverMollificationL2 k u)
          (normalizedCoverMollificationL2 k v) +
        dist (normalizedCoverMollificationL2 k v) v +
        dist v u := by
          calc
            dist (normalizedCoverMollificationL2 k u) u ≤
                dist (normalizedCoverMollificationL2 k u)
                  (normalizedCoverMollificationL2 k v) +
                dist (normalizedCoverMollificationL2 k v) u :=
                  dist_triangle _ _ _
            _ ≤ _ := by
              linarith [dist_triangle
                (normalizedCoverMollificationL2 k v) v u]
    _ ≤ dist u v +
        dist (normalizedCoverMollificationL2 k v) v +
        dist v u := by
          gcongr
          exact normalizedCoverMollificationL2_dist_le k u v
    _ < ε := by
          rw [dist_comm v u]
          nlinarith [hN k hk]

private theorem normalizedCoverMollification_global_L2_tendsto
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n))) :
    Tendsto
      (fun k : ℕ =>
        (normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k))
      atTop (nhds (hh.toLp h)) := by
  simpa only [normalizedCoverMollificationL2_toLp] using
    normalizedCoverMollificationL2_tendsto (hh.toLp h)

private theorem tendsto_integral_norm_sq_normalizedCoverMollification_sub
    {n : ℕ} {h : LogSpace n → ℂ}
    (hh : MemLp h 2 (volume : Measure (LogSpace n))) :
    Tendsto
      (fun k : ℕ =>
        ∫ x : LogSpace n,
          ‖normalizedCoverMollification h k x - h x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp
    (normalizedCoverMollification_global_L2_tendsto hh)
  have hsq (k : ℕ) :
      ‖(normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k) -
        hh.toLp h‖ ^ 2 =
      ∫ x : LogSpace n,
        ‖normalizedCoverMollification h k x - h x‖ ^ 2
          ∂(volume : Measure (LogSpace n)) := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards
      [MeasureTheory.Lp.coeFn_sub
        ((normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k)) (hh.toLp h),
       (normalizedCoverMollification_memLp hh k).coeFn_toLp,
       hh.coeFn_toLp]
      with x hsub hm hx
    rw [hsub]
    change
      ‖((normalizedCoverMollification_memLp hh k).toLp
          (normalizedCoverMollification h k)) x -
        (hh.toLp h) x‖ ^ 2 = _
    rw [hm, hx]
  simpa only [hsq, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
    hnorm.pow 2

private theorem normalizedCoverMollification_indicator_cthickening_eq_on
    {n : ℕ} {h : LogSpace n → ℂ}
    {K : Set (LogSpace n)} (_ : IsCompact K)
    (k : ℕ) (x : LogSpace n) (hx : x ∈ K) :
    normalizedCoverMollification h k x =
      normalizedCoverMollification
        ((Metric.cthickening 1 K).indicator h) k x := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  unfold normalizedCoverMollification
  rw [MeasureTheory.convolution_def,
    MeasureTheory.convolution_def]
  apply integral_congr_ae
  filter_upwards [] with y
  by_cases hy : κ y = 0
  · simp only [hy, map_zero, _root_.zero_apply, κ]
  · have hball :
        y ∈ Metric.ball (0 : LogSpace n)
          (complexShrinkingBump (n := n) k).rOut := by
        rw [← (complexShrinkingBump (n := n) k).support_normed_eq
          (μ := (volume : Measure (LogSpace n)))]
        exact hy
    have hnorm :
        ‖y‖ < (complexShrinkingBump (n := n) k).rOut := by
      simpa only [Metric.mem_ball, dist_zero_right] using hball
    have hxy : x - y ∈ Metric.cthickening 1 K := by
      apply Metric.mem_cthickening_of_dist_le
        (x - y) x 1 K hx
      rw [dist_eq_norm]
      have heq : (x - y) - x = -y := by abel
      rw [heq, norm_neg]
      exact hnorm.le.trans (complexShrinkingBump_rOut_le_one k)
    simp only [ContinuousLinearMap.lsmul_apply, Complex.real_smul, Set.indicator_of_mem hxy]

private theorem normalizedCoverMollification_localL2_tendsto_zero
    {n : ℕ} {h : LogSpace n → ℂ}
    (_ : LocallyIntegrable h (volume : Measure (LogSpace n)))
    {K : Set (LogSpace n)} (hK : IsCompact K)
    (hlocal : MemLp h 2
      ((volume : Measure (LogSpace n)).restrict
        (Metric.cthickening 1 K))) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverMollification h k x - h x‖ ^ 2
            ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  let S : Set (LogSpace n) := Metric.cthickening 1 K
  let z : LogSpace n → ℂ := S.indicator h
  have hS : IsCompact S := hK.cthickening
  have hz : MemLp z 2 (volume : Measure (LogSpace n)) :=
    (MeasureTheory.memLp_indicator_iff_restrict
      hS.measurableSet).mpr hlocal
  have hagree (k : ℕ) :
      (∫ x in K,
        ‖normalizedCoverMollification h k x - h x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) =
      (∫ x in K,
        ‖normalizedCoverMollification z k x - z x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
    have hxs : x ∈ S := Metric.self_subset_cthickening K hx
    change
      ‖normalizedCoverMollification h k x - h x‖ ^ 2 =
        ‖normalizedCoverMollification
          ((Metric.cthickening 1 K).indicator h) k x -
          (Metric.cthickening 1 K).indicator h x‖ ^ 2
    rw [normalizedCoverMollification_indicator_cthickening_eq_on
      hK k x hx, Set.indicator_of_mem hxs]
  have hbound (k : ℕ) :
      (∫ x in K,
        ‖normalizedCoverMollification h k x - h x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) ≤
      (∫ x : LogSpace n,
        ‖normalizedCoverMollification z k x - z x‖ ^ 2
          ∂(volume : Measure (LogSpace n))) := by
    rw [hagree k]
    apply MeasureTheory.setIntegral_le_integral
      ((normalizedCoverMollification_memLp hz k).sub hz).norm.integrable_sq
    exact Filter.Eventually.of_forall (fun x => sq_nonneg _)
  exact squeeze_zero
    (fun k => integral_nonneg (fun x => sq_nonneg _))
    hbound
    (tendsto_integral_norm_sq_normalizedCoverMollification_sub hz)

end TorusStrongCoverMollificationDensity

namespace TorusStrongWeightedTorusDescent

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence
open JointHolomorphicLaurentFourierCompatibility ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge WeightedTorusClosedGraphWeakBridge MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeightedCoverAdjointGreen
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private def sourceCompactAngularCoverBox
    {n : ℕ} (S : Set (LogTorus n)) : Set (LogSpace n) :=
  (logarithmicCoordinatesEquiv n) ''
    ((Prod.fst '' S) ×ˢ
      Set.univ.pi (fun _ : Fin n => Set.Icc (0 : ℝ) 1))

private theorem isCompact_sourceCompactAngularCoverBox
    {n : ℕ} {S : Set (LogTorus n)} (hS : IsCompact S) :
    IsCompact (sourceCompactAngularCoverBox S) := by
  unfold sourceCompactAngularCoverBox
  exact ((hS.image continuous_fst).prod
    (isCompact_univ_pi fun _ : Fin n => isCompact_Icc)).image
      (logarithmicCoordinatesEquiv n).continuous

private theorem logarithmicPoint_mem_sourceCompactAngularCoverBox
    {n : ℕ} {S : Set (LogTorus n)}
    (p : Space n × Space n)
    (hbox : p.2 ∈ angularFundamentalBox (0 : Space n))
    (hS : realTorusCoverProjection n p ∈ S) :
    logarithmicPoint p.1 p.2 ∈ sourceCompactAngularCoverBox S := by
  refine ⟨p, ⟨?_, ?_⟩, ?_⟩
  · exact ⟨realTorusCoverProjection n p, hS, rfl⟩
  · intro i _
    have hi := hbox i
    exact ⟨hi.1.le, by simpa only [Pi.zero_apply, zero_add] using hi.2⟩
  · simpa only [Prod.mk.eta] using logarithmicCoordinatesEquiv_apply p.1 p.2

private theorem torusScalarRepresentative_realTorusCoverProjection
    {n : ℕ} (F : LogSpace n → ℂ)
    (p : Space n × Space n)
    (hbox : p.2 ∈ angularFundamentalBox (0 : Space n)) :
    torusScalarRepresentative F (realTorusCoverProjection n p) =
      F (logarithmicPoint p.1 p.2) := by
  apply coverRepresentative_coe
  intro i _
  simpa only [mem_Ioc, Pi.zero_apply, zero_add] using hbox i

private theorem angularWeightedTorus_integral_real_eq_realFundamentalCell
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (b : Space n)
    {G : LogTorus n → ℝ}
    (hG : AEStronglyMeasurable G (sourceTorusBaseMeasure n)) :
    (∫ q : LogTorus n, G q
      ∂(angularWeightedTorusMeasure a)) =
      ∫ p : Space n × Space n,
        angularWeightedTorusDensity a
            (realTorusCoverProjection n p) *
          G (realTorusCoverProjection n p)
        ∂(realFundamentalCellMeasure b) := by
  have hd : Measurable
      (fun q : LogTorus n =>
        ENNReal.ofReal (angularWeightedTorusDensity a q)) :=
    ENNReal.measurable_ofReal.comp
      (continuous_angularWeightedTorusDensity ha).measurable
  have hp := realTorusCoverProjection_measurePreserving
    (volume : Measure (Space n)) b
  have hmap :
      Measure.map (realTorusCoverProjection n)
        (realFundamentalCellMeasure b) =
        sourceTorusBaseMeasure n := by
    simpa only [realFundamentalCellMeasure, sourceTorusBaseMeasure]
      using hp.map_eq
  rw [angularWeightedTorusMeasure,
    integral_withDensity_eq_integral_toReal_smul hd
      (Filter.Eventually.of_forall fun q => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal
    (angularWeightedTorusDensity_pos a _).le, smul_eq_mul]
  calc
    (∫ q : LogTorus n,
      angularWeightedTorusDensity a q * G q
        ∂(sourceTorusBaseMeasure n)) =
      ∫ q : LogTorus n,
        angularWeightedTorusDensity a q * G q
          ∂(Measure.map (realTorusCoverProjection n)
            (realFundamentalCellMeasure b)) := by rw [hmap]
    _ = _ := by
      apply MeasureTheory.integral_map
        hp.measurable.aemeasurable
      rw [hmap]
      exact (continuous_angularWeightedTorusDensity ha).aestronglyMeasurable.mul hG

private theorem realFundamentalCell_integral_real_eq_coverJacobian
    {n : ℕ} (b : Space n)
    (g : LogSpace n → ℝ)
    (hsupport : ∀ p : Space n × Space n,
      p.2 ∉ angularFundamentalBox b →
        g (logarithmicCoordinatesEquiv n p) = 0) :
    (∫ p : Space n × Space n,
      g (logarithmicCoordinatesEquiv n p)
        ∂(realFundamentalCellMeasure b)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n, g z
          ∂(volume : Measure (LogSpace n))) := by
  calc
    _ = ∫ p : Space n × Space n,
        g (logarithmicCoordinatesEquiv n p)
          ∂(volume : Measure
            (Space n × Space n)) := by
      rw [realFundamentalCellMeasure_eq_restrict b]
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro p hp
      apply hsupport p
      simpa only [mem_prod, mem_univ, true_and] using hp
    _ = ∫ z : LogSpace n, g z
          ∂(logarithmicCoverPushforward n) := by
      simpa only using
        (logarithmicCoordinates_measurePreserving n).integral_comp
          (logarithmicCoordinatesEquiv n).toHomeomorph.measurableEmbedding g
    _ = _ := by
      rw [logarithmicCoverPushforward_eq_smul_volume,
        integral_smul_nnreal_measure]

private theorem angularWeightedTorus_compact_scalarRepresentative_majorant
    {n : ℕ} {a : LogTorus n → ℝ}
    {f : LogTorus n → ℂ}
    {F : ℕ → LogSpace n → ℂ}
    {S : Set (LogTorus n)}
    (K T : Set (LogSpace n))
    (hK : K = sourceCompactAngularCoverBox S)
    (hT : T =
      {z | ((logarithmicCoordinatesEquiv n).symm z).2 ∈
        angularFundamentalBox (0 : Space n)})
    (J : ℕ → LogSpace n → ℝ)
    (hJ : J = fun k z =>
      T.indicator
        (((complexTorusCoverProjection n) ⁻¹' S).indicator
          (fun w : LogSpace n =>
            angularWeightedTorusDensity a
                (complexTorusCoverProjection n w) *
              ‖F k w - complexTorusCoverLift f w‖ ^ 2)) z)
    (B : ℝ) (hBpos : 0 ≤ B)
    (hB : ∀ q : LogTorus n, q ∈ S →
      angularWeightedTorusDensity a q ≤ B)
    (k : ℕ) (z : LogSpace n) :
    0 ≤ J k z ∧
      J k z ≤
        B * K.indicator
          (fun w : LogSpace n =>
            ‖F k w - complexTorusCoverLift f w‖ ^ 2) z := by
  subst K
  subst T
  subst J
  dsimp only
  by_cases ht :
      ((logarithmicCoordinatesEquiv n).symm z).2 ∈
        angularFundamentalBox (0 : Space n)
  · have htT : z ∈
        {w | ((logarithmicCoordinatesEquiv n).symm w).2 ∈
          angularFundamentalBox (0 : Space n)} := ht
    by_cases hs : complexTorusCoverProjection n z ∈ S
    · let p : Space n × Space n :=
        (logarithmicCoordinatesEquiv n).symm z
      have hpbox : p.2 ∈
          angularFundamentalBox (0 : Space n) := ht
      have hproj : realTorusCoverProjection n p ∈ S := by
        simpa only [complexTorusCoverProjection] using hs
      have hz : z ∈ sourceCompactAngularCoverBox S := by
        have hmem :=
          logarithmicPoint_mem_sourceCompactAngularCoverBox
            p hpbox hproj
        have hpoint : logarithmicPoint p.1 p.2 = z := by
          change (logarithmicCoordinatesEquiv n) p = z
          exact (logarithmicCoordinatesEquiv n).apply_symm_apply z
        rw [hpoint] at hmem
        exact hmem
      have hs' :
          z ∈ (complexTorusCoverProjection n) ⁻¹' S := hs
      rw [Set.indicator_of_mem htT,
        Set.indicator_of_mem hs', Set.indicator_of_mem hz]
      exact ⟨mul_nonneg
        (angularWeightedTorusDensity_pos a _).le
        (sq_nonneg _),
        mul_le_mul_of_nonneg_right (hB _ hs) (sq_nonneg _)⟩
    · have hs' :
          z ∉ (complexTorusCoverProjection n) ⁻¹' S := hs
      have hright :
          0 ≤ B * (sourceCompactAngularCoverBox S).indicator
            (fun w : LogSpace n =>
              ‖F k w - complexTorusCoverLift f w‖ ^ 2) z := by
        apply mul_nonneg hBpos
        by_cases hz : z ∈ sourceCompactAngularCoverBox S
        · simp only [Set.indicator_of_mem hz, norm_nonneg,
            pow_succ_nonneg]
        · simp only [Set.indicator_of_notMem hz, Std.le_refl]
      rw [Set.indicator_of_mem htT,
        Set.indicator_of_notMem hs']
      exact ⟨le_rfl, hright⟩
  · have htT : z ∉
        {w | ((logarithmicCoordinatesEquiv n).symm w).2 ∈
          angularFundamentalBox (0 : Space n)} := ht
    have hright :
        0 ≤ B * (sourceCompactAngularCoverBox S).indicator
          (fun w : LogSpace n =>
            ‖F k w - complexTorusCoverLift f w‖ ^ 2) z := by
      apply mul_nonneg hBpos
      by_cases hz : z ∈ sourceCompactAngularCoverBox S
      · simp only [Set.indicator_of_mem hz, norm_nonneg,
          pow_succ_nonneg]
      · simp only [Set.indicator_of_notMem hz, Std.le_refl]
    rw [Set.indicator_of_notMem htT]
    exact ⟨le_rfl, hright⟩

private theorem angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    {f : LogTorus n → ℂ}
    (hfbase : AEStronglyMeasurable f (sourceTorusBaseMeasure n))
    (_ : LocallyIntegrable
      (complexTorusCoverLift f)
      (volume : Measure (LogSpace n)))
    (hflocal : ∀ {K : Set (LogSpace n)}, IsCompact K →
      MemLp (complexTorusCoverLift f) 2
        ((volume : Measure (LogSpace n)).restrict K))
    {F : ℕ → LogSpace n → ℂ}
    (hF : ∀ k : ℕ, Continuous (F k))
    (hFp : ∀ (k : ℕ) (d : Fin n → ℤ),
      Function.Periodic (F k) (imaginaryShift d))
    (hcover : ∀ {K : Set (LogSpace n)}, IsCompact K →
      Tendsto
        (fun k : ℕ =>
          ∫ z in K,
            ‖F k z - complexTorusCoverLift f z‖ ^ 2
              ∂(volume : Measure (LogSpace n)))
        atTop (nhds 0))
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun k : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative (F k) q - f q‖ ^ 2
            ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  classical
  let K : Set (LogSpace n) := sourceCompactAngularCoverBox S
  have hK : IsCompact K :=
    isCompact_sourceCompactAngularCoverBox hS
  obtain ⟨B₀, hB₀⟩ :=
    hS.bddAbove_image
      (continuous_angularWeightedTorusDensity ha).continuousOn
  let B : ℝ := max B₀ 0
  have hBpos : 0 ≤ B := le_max_right _ _
  have hB (q : LogTorus n) (hq : q ∈ S) :
      angularWeightedTorusDensity a q ≤ B :=
    (hB₀ ⟨q, hq, rfl⟩).trans (le_max_left _ _)
  let T : Set (LogSpace n) :=
    {z | ((logarithmicCoordinatesEquiv n).symm z).2 ∈
      angularFundamentalBox (0 : Space n)}
  let J : ℕ → LogSpace n → ℝ := fun k z =>
    T.indicator
      (((complexTorusCoverProjection n) ⁻¹' S).indicator
        (fun w : LogSpace n =>
          angularWeightedTorusDensity a
              (complexTorusCoverProjection n w) *
            ‖F k w - complexTorusCoverLift f w‖ ^ 2)) z
  have htorus (k : ℕ) :
      Continuous (torusScalarRepresentative (F k)) :=
    continuous_torusScalarRepresentative_of_periodic
      (hF k) (hFp k)
  have hbase (k : ℕ) :
      AEStronglyMeasurable
        (fun q : LogTorus n =>
          ‖torusScalarRepresentative (F k) q - f q‖ ^ 2)
        (sourceTorusBaseMeasure n) :=
    ((htorus k).aestronglyMeasurable.sub hfbase).norm.pow 2
  have hident (k : ℕ) :
      (∫ q in S,
        ‖torusScalarRepresentative (F k) q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) =
      logarithmicCoverJacobianFactor n •
        (∫ z : LogSpace n, J k z
          ∂(volume : Measure (LogSpace n))) := by
    rw [← MeasureTheory.integral_indicator hS.measurableSet]
    rw [angularWeightedTorus_integral_real_eq_realFundamentalCell
      ha (0 : Space n)
      ((hbase k).indicator hS.measurableSet)]
    rw [← realFundamentalCell_integral_real_eq_coverJacobian
      (0 : Space n) (J k)]
    · apply integral_congr_ae
      filter_upwards
        [ae_mem_angularFundamentalBox_realFundamentalCell
          (0 : Space n)] with p hp
      have hrep := torusScalarRepresentative_realTorusCoverProjection
        (F k) p hp
      have hT : (logarithmicCoordinatesEquiv n) p ∈ T := by
        change
          (((logarithmicCoordinatesEquiv n).symm
            ((logarithmicCoordinatesEquiv n) p)).2 ∈
              angularFundamentalBox (0 : Space n))
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp
      have hproj :
          complexTorusCoverProjection n
            ((logarithmicCoordinatesEquiv n) p) =
            realTorusCoverProjection n p := by
        simp only [complexTorusCoverProjection, ContinuousLinearEquiv.symm_apply_apply]
      by_cases hs : realTorusCoverProjection n p ∈ S
      · have hpre :
            (logarithmicCoordinatesEquiv n) p ∈
              (complexTorusCoverProjection n) ⁻¹' S := by
          simpa only [mem_preimage, hproj] using hs
        simp only [J, Set.indicator_of_mem hT,
          Set.indicator_of_mem hpre,
          Set.indicator_of_mem hs]
        rw [hproj]
        simp only [complexTorusCoverLift]
        rw [hproj]
        change
          angularWeightedTorusDensity a
              (realTorusCoverProjection n p) *
            ‖torusScalarRepresentative (F k)
                (realTorusCoverProjection n p) -
              f (realTorusCoverProjection n p)‖ ^ 2 =
          angularWeightedTorusDensity a
              (realTorusCoverProjection n p) *
            ‖F k ((logarithmicCoordinatesEquiv n) p) -
              f (realTorusCoverProjection n p)‖ ^ 2
        rw [hrep]
        congr 3
      · have hpre :
            (logarithmicCoordinatesEquiv n) p ∉
              (complexTorusCoverProjection n) ⁻¹' S := by
          simpa only [mem_preimage, hproj] using hs
        simp only [Set.indicator_of_notMem hs, mul_zero, Set.indicator_of_mem hT,
          Set.indicator_of_notMem hpre, J]
    · intro p hp
      have hT : (logarithmicCoordinatesEquiv n) p ∉ T := by
        change
          ¬ (((logarithmicCoordinatesEquiv n).symm
            ((logarithmicCoordinatesEquiv n) p)).2 ∈
              angularFundamentalBox (0 : Space n))
        simpa only [ContinuousLinearEquiv.symm_apply_apply] using hp
      simp only [Set.indicator_of_notMem hT, J]
  have hmajor (k : ℕ) (z : LogSpace n) :
      0 ≤ J k z ∧
      J k z ≤
        B * K.indicator
          (fun w : LogSpace n =>
            ‖F k w - complexTorusCoverLift f w‖ ^ 2) z := by
    exact angularWeightedTorus_compact_scalarRepresentative_majorant
      (a := a) (f := f) (F := F) (S := S)
      K T rfl rfl J rfl B hBpos hB k z
  have hbound (k : ℕ) :
      (∫ q in S,
        ‖torusScalarRepresentative (F k) q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) ≤
      (logarithmicCoverJacobianFactor n : ℝ) * B *
        (∫ z in K,
          ‖F k z - complexTorusCoverLift f z‖ ^ 2
            ∂(volume : Measure (LogSpace n))) := by
    rw [hident k]
    have hFmem : MemLp (F k) 2
        ((volume : Measure (LogSpace n)).restrict K) := by
      apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
        ((hF k).aestronglyMeasurable.mono_measure
          Measure.restrict_le_self)).mpr
      exact ((hF k).norm.pow 2).continuousOn.integrableOn_compact hK
    have heint :
        IntegrableOn
          (fun z : LogSpace n =>
            ‖F k z - complexTorusCoverLift f z‖ ^ 2)
          K (volume : Measure (LogSpace n)) :=
      (hFmem.sub (hflocal hK)).norm.integrable_sq
    have hupper :
        (∫ z : LogSpace n, J k z
          ∂(volume : Measure (LogSpace n))) ≤
        B *
          (∫ z in K,
            ‖F k z - complexTorusCoverLift f z‖ ^ 2
              ∂(volume : Measure (LogSpace n))) := by
      calc
        (∫ z : LogSpace n, J k z
          ∂(volume : Measure (LogSpace n))) ≤
          ∫ z : LogSpace n,
            B * K.indicator
              (fun w : LogSpace n =>
                ‖F k w - complexTorusCoverLift f w‖ ^ 2) z
            ∂(volume : Measure (LogSpace n)) := by
              apply MeasureTheory.integral_mono_of_nonneg
                (Filter.Eventually.of_forall
                  (fun z => (hmajor k z).1))
                ((heint.integrable_indicator hK.measurableSet).const_mul B)
              exact Filter.Eventually.of_forall
                (fun z => (hmajor k z).2)
        _ = _ := by
          rw [MeasureTheory.integral_const_mul,
            MeasureTheory.integral_indicator hK.measurableSet]
    change
      (logarithmicCoverJacobianFactor n : ℝ) *
          (∫ z : LogSpace n, J k z
            ∂(volume : Measure (LogSpace n))) ≤ _
    calc
      _ ≤ (logarithmicCoverJacobianFactor n : ℝ) *
          (B *
            (∫ z in K,
              ‖F k z - complexTorusCoverLift f z‖ ^ 2
                ∂(volume : Measure (LogSpace n)))) :=
        mul_le_mul_of_nonneg_left hupper
          (NNReal.coe_nonneg _)
      _ = _ := by ring
  apply squeeze_zero
    (fun k => integral_nonneg (fun q => sq_nonneg _))
    hbound
  simpa only [mul_zero] using
    (hcover hK).const_mul
      ((logarithmicCoverJacobianFactor n : ℝ) * B)

end TorusStrongWeightedTorusDescent

namespace TorusHomogeneousFriedrichs

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeSlopeConvergence ComplexKillingSaturationBridge
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge WeightedTorusDolbeault
open TorusWeightedBaseAE TorusWeakDolbeaultMollification TorusStrongCoverMollificationDensity
open TorusStrongWeightedTorusDescent TorusFriedrichsMollifierEstimates
open TorusWeightedAdjointMollification BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem angularScalarCoverLift_normalizedCoverMollification_localL2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverMollification
              (complexTorusCoverLift
                (fun q : LogTorus n => f q)) k x -
            complexTorusCoverLift
              (fun q : LogTorus n => f q) x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  exact normalizedCoverMollification_localL2_tendsto_zero
    (angularWeightedScalarCoverLift_locallyIntegrable ha f)
    hK
    (angularWeightedScalarCoverLift_memLp_restrict_volume_isCompact
      ha f hK.cthickening)

private theorem angularFormCoordinateCoverLift_normalizedCoverMollification_localL2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (W : angularWeightedFormL2 a) (j : Fin n)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverMollification
              (complexTorusCoverLift
                (fun q : LogTorus n =>
                  (W q : EuclideanSpace ℂ (Fin n)) j)) k x -
            complexTorusCoverLift
              (fun q : LogTorus n =>
                (W q : EuclideanSpace ℂ (Fin n)) j) x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  exact normalizedCoverMollification_localL2_tendsto_zero
    (angularWeightedFormCoordinateCoverLift_locallyIntegrable
      ha W j)
    hK
    (angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
      ha W j hK.cthickening)

private theorem scalar_mollification_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (f : angularWeightedScalarL2 a)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun k : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative
              (normalizedCoverMollification
                (complexTorusCoverLift
                  (fun r : LogTorus n => f r)) k) q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  apply angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
    ha (angularWeightedLp_aestronglyMeasurable_base f)
    (angularWeightedScalarCoverLift_locallyIntegrable ha f)
  · intro K hK
    exact angularWeightedScalarCoverLift_memLp_restrict_volume_isCompact
      ha f hK
  · intro k
    exact (contDiff_normalizedCoverMollification
      (angularWeightedScalarCoverLift_locallyIntegrable ha f) k 0).continuous
  · intro k d
    exact normalizedCoverMollification_periodic
      (fun e => complexTorusCoverLift_periodic
        (fun q : LogTorus n => f q) e) k d
  · intro K hK
    exact
      angularScalarCoverLift_normalizedCoverMollification_localL2_tendsto_zero
        ha f hK
  · exact hS

private theorem formCoordinate_mollification_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (W : angularWeightedFormL2 a) (j : Fin n)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun k : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative
              (normalizedCoverMollification
                (complexTorusCoverLift
                  (fun r : LogTorus n =>
                    (W r : EuclideanSpace ℂ (Fin n)) j)) k) q -
            (W q : EuclideanSpace ℂ (Fin n)) j‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  have hbase : AEStronglyMeasurable
      (fun q : LogTorus n =>
        (W q : EuclideanSpace ℂ (Fin n)) j)
      (sourceTorusBaseMeasure n) :=
    (PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp_aestronglyMeasurable
      (angularWeightedLp_aestronglyMeasurable_base W)
  apply angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
    ha hbase
    (angularWeightedFormCoordinateCoverLift_locallyIntegrable
      ha W j)
  · intro K hK
    exact angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
      ha W j hK
  · intro k
    exact (contDiff_normalizedCoverMollification
      (angularWeightedFormCoordinateCoverLift_locallyIntegrable
        ha W j) k 0).continuous
  · intro k d
    exact normalizedCoverMollification_periodic
      (fun e => complexTorusCoverLift_periodic
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) j) e) k d
  · intro K hK
    exact
      angularFormCoordinateCoverLift_normalizedCoverMollification_localL2_tendsto_zero
        ha W j hK
  · exact hS

private theorem angularFormCoordinateCoverLift_complexDriftCommutator_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (W : angularWeightedFormL2 a) (j : Fin n)
    {b : LogSpace n → ℂ} (hb : Continuous b)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverComplexDriftCommutator b
            (complexTorusCoverLift
              (fun q : LogTorus n =>
                (W q : EuclideanSpace ℂ (Fin n)) j)) k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  exact
    setIntegral_norm_sq_normalizedCoverComplexDriftCommutator_tendsto_zero
      (angularWeightedFormCoordinateCoverLift_locallyIntegrable
        ha W j)
      (fun {_} hS =>
        angularWeightedFormCoordinateCoverLift_memLp_restrict_volume_isCompact
          ha W j hS)
      hb hK

private theorem angularFormCoordinateCoverLift_holomorphicDriftCommutator_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a) (i j : Fin n)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖normalizedCoverComplexDriftCommutator
            (fun z => holomorphicCoordinate
              (fun w => (angularCoverPotential a w : ℂ)) z i)
            (complexTorusCoverLift
              (fun q : LogTorus n =>
                (W q : EuclideanSpace ℂ (Fin n)) j)) k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  apply angularFormCoordinateCoverLift_complexDriftCommutator_tendsto_zero
    ha W j (K := K) (hK := hK)
  exact (contDiff_holomorphicCoordinate
    (Complex.ofRealCLM.contDiff.comp ha2) i).continuous

private theorem angularMollifiedPhysicalAdjointDriftCommutator_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a)
    {K : Set (LogSpace n)} (hK : IsCompact K) :
    Tendsto
      (fun k : ℕ =>
        ∫ x in K,
          ‖angularMollifiedPhysicalAdjointDriftCommutator W k x‖ ^ 2
          ∂(volume : Measure (LogSpace n)))
      atTop (nhds 0) := by
  unfold angularMollifiedPhysicalAdjointDriftCommutator
  apply finite_complex_local_square_integral_sum_tendsto_zero
    Finset.univ _ hK
  · intro j _ k
    apply continuous_normalizedCoverComplexDriftCommutator
      (angularWeightedFormCoordinateCoverLift_locallyIntegrable
        ha W j)
    exact (contDiff_holomorphicCoordinate
      (Complex.ofRealCLM.contDiff.comp ha2) j).continuous
  · intro j _
    exact
      angularFormCoordinateCoverLift_holomorphicDriftCommutator_tendsto_zero
        ha ha2 W j j hK

end TorusHomogeneousFriedrichs

namespace RadialPhysicalInverseSquareRootEnergy

open Set Function Filter MeasureTheory Matrix
open RadialSchurBlock
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology ContDiff

private theorem complexEuclideanMatrixAction_mul
    {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    Matrix.toEuclideanLin A (Matrix.toEuclideanLin B v) =
      Matrix.toEuclideanLin (A * B) v := by
  ext i
  change
    (A *ᵥ (B *ᵥ (fun j : Fin n => v j))) i =
      ((A * B) *ᵥ (fun j : Fin n => v j)) i
  rw [Matrix.mulVec_mulVec]

private theorem complexHermitianMatrixAction_norm_sq
    {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.IsHermitian)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin A v‖ ^ 2 =
      RCLike.re
        (@inner ℂ (EuclideanSpace ℂ (Fin n)) _ v
          (Matrix.toEuclideanLin (A * A) v)) := by
  calc
    ‖Matrix.toEuclideanLin A v‖ ^ 2 =
        RCLike.re
          (@inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (Matrix.toEuclideanLin A v)
            (Matrix.toEuclideanLin A v)) :=
      norm_sq_eq_re_inner (Matrix.toEuclideanLin A v)
    _ = RCLike.re
          (@inner ℂ (EuclideanSpace ℂ (Fin n)) _ v
            (Matrix.toEuclideanLin A
              (Matrix.toEuclideanLin A v))) := by
      apply congrArg RCLike.re
      exact (Matrix.isSymmetric_toEuclideanLin_iff.mpr hA)
        v (Matrix.toEuclideanLin A v)
    _ = _ := by
      rw [complexEuclideanMatrixAction_mul]

private theorem complexPositiveInverseSquareRootAction_norm_sq
    {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹) v‖ ^ 2 =
      RCLike.re
        (@inner ℂ (EuclideanSpace ℂ (Fin n)) _ v
          (Matrix.toEuclideanLin (A⁻¹) v)) := by
  rw [complexHermitianMatrixAction_norm_sq
    hA.isStrictlyPositive.sqrt.posDef.inv.isHermitian]
  rw [← Matrix.mul_inv_rev,
    CFC.sqrt_mul_sqrt_self A hA.posSemidef.nonneg]

private theorem sourceComplexRowSchurEnergyDensity_eq_inverseSquareRoot_norm_sq
    {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ) :
    sourceComplexRowSchurEnergyDensity A b =
      ‖Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹)
        (WithLp.toLp 2 (star b))‖ ^ 2 := by
  rw [complexPositiveInverseSquareRootAction_norm_sq hA]
  rw [sourceComplexRowSchurEnergyDensity_eq,
    EuclideanSpace.inner_eq_star_dotProduct]
  change
    (b ⬝ᵥ (A⁻¹ *ᵥ star b)).re =
      ((A⁻¹ *ᵥ star b) ⬝ᵥ star (star b)).re
  rw [star_star, dotProduct_comm]

private theorem complexPositiveInverseSquareRootAction_pairing
    {n : ℕ}
    {A : Matrix (Fin n) (Fin n) ℂ}
    (hA : A.PosDef)
    (b : Fin n → ℂ)
    (v : EuclideanSpace ℂ (Fin n)) :
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
      (Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹)
        (WithLp.toLp 2 (star b)))
      (Matrix.toEuclideanLin (CFC.sqrt A) v) =
      b ⬝ᵥ (fun i : Fin n => v i) := by
  have hroot := hA.isStrictlyPositive.sqrt.posDef
  have hdet : IsUnit (CFC.sqrt A).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hroot.isUnit
  calc
    @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹)
          (WithLp.toLp 2 (star b)))
        (Matrix.toEuclideanLin (CFC.sqrt A) v) =
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (WithLp.toLp 2 (star b))
        (Matrix.toEuclideanLin ((CFC.sqrt A)⁻¹)
          (Matrix.toEuclideanLin (CFC.sqrt A) v)) :=
      (Matrix.isSymmetric_toEuclideanLin_iff.mpr
        hroot.inv.isHermitian)
        (WithLp.toLp 2 (star b))
        (Matrix.toEuclideanLin (CFC.sqrt A) v)
    _ = @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (WithLp.toLp 2 (star b)) v := by
      rw [complexEuclideanMatrixAction_mul,
        Matrix.nonsing_inv_mul _ hdet]
      congr 1
      ext i
      simp only [toLpLin_one, LinearMap.id_coe, id_eq]
    _ = b ⬝ᵥ (fun i : Fin n => v i) := by
      rw [EuclideanSpace.inner_eq_star_dotProduct]
      change
        ((fun i : Fin n => v i) ⬝ᵥ star (star b)) =
          b ⬝ᵥ (fun i : Fin n => v i)
      rw [star_star, dotProduct_comm]

end RadialPhysicalInverseSquareRootEnergy

namespace RadialPhysicalResolventDefectReduction

open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private theorem complexHilbert_norm_le_of_mem_closure_inner_bound
    {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : E) (S : Set E) (hf : f ∈ closure S)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ g ∈ S,
      ‖@inner ℂ E _ f g‖ ≤ B * ‖g‖) :
    ‖f‖ ≤ B := by
  let T : Set E :=
    {g : E | ‖@inner ℂ E _ f g‖ ≤ B * ‖g‖}
  have hT : IsClosed T := by
    exact isClosed_le
      ((continuous_const.inner continuous_id).norm)
      (continuous_const.mul continuous_norm)
  have hST : S ⊆ T := by
    intro g hg
    exact hbound g hg
  have hself : f ∈ T := (closure_minimal hST hT) hf
  change ‖@inner ℂ E _ f f‖ ≤ B * ‖f‖ at hself
  have hsq : ‖f‖ ^ 2 ≤ B * ‖f‖ := by
    simpa only [inner_self_eq_norm_sq_to_K, Complex.coe_algebraMap, norm_pow, Complex.norm_real,
      norm_norm] using hself
  by_cases hfzero : ‖f‖ = 0
  · rw [hfzero]
    exact hB
  · have hfpos : 0 < ‖f‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hfzero)
    nlinarith

end RadialPhysicalResolventDefectReduction

namespace RadialPhysicalVelocityCompactGraph

open Set Function Filter MeasureTheory Matrix
open MatrixTorusBochnerCore MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private theorem contDiff_complexSourceCoverRadialCutoff_all
    {n : ℕ} (m r : ℕ) :
    ContDiff ℝ r (complexSourceCoverRadialCutoff (n := n) m) := by
  unfold complexSourceCoverRadialCutoff sourceCoverRadialCutoff
  exact Complex.ofRealCLM.contDiff.comp
    ((WeightedResolventConstantCore.growingBump
      (n := n) m).contDiff.comp
        (sourceCoverRadialLinear n).contDiff)

end RadialPhysicalVelocityCompactGraph

namespace TorusRootCurvatureCoercivity

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert ComplexKillingSaturationBridge WeightedTorusBochner
open WeightedTorusBrascampLieb
open scoped BigOperators ENNReal ComplexConjugate ComplexOrder
  InnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology ContDiff

private def angularTorusConjugatePhysicalFormVector {n : ℕ}
    (W : LogSpace n → Fin n → ℂ) (q : LogTorus n) :
    EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2
    (star (fun i : Fin n =>
      torusScalarRepresentative (fun z => W z i) q))

private theorem angularTorusFormCurvatureDensity_eq_conjugatePhysical_inner
    {n : ℕ} (a : LogTorus n → ℝ)
    (W : LogSpace n → Fin n → ℂ) (q : LogTorus n) :
    angularTorusFormCurvatureDensity a W q =
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (angularTorusConjugatePhysicalFormVector W q)
        (Matrix.toEuclideanLin
          (angularTorusComplexHessianMatrix a q)
          (angularTorusConjugatePhysicalFormVector W q)) := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  simp only [angularTorusFormCurvatureDensity, mul_comm, mul_assoc, dotProduct,
    angularTorusConjugatePhysicalFormVector, toLpLin_toLp, toLin'_apply, mulVec,
    angularTorusComplexHessianMatrix, Pi.star_apply, RCLike.star_def,
    RingHomCompTriple.comp_apply, RingHom.id_apply, Finset.sum_mul, mul_left_comm]

end TorusRootCurvatureCoercivity

namespace RadialPhysicalResolventRootCutoffPairing

open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology

private def angularEuclideanConjugation {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) : EuclideanSpace ℂ (Fin n) :=
  WithLp.toLp 2 (star (fun j : Fin n => v j))

private theorem norm_angularEuclideanConjugation {n : ℕ}
    (v : EuclideanSpace ℂ (Fin n)) :
    ‖angularEuclideanConjugation v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [angularEuclideanConjugation, Pi.star_apply, RCLike.star_def, RCLike.norm_conj]

private theorem continuous_complexEuclideanConjugatedMatrixAction {n : ℕ} :
    Continuous
      (fun Av : Matrix (Fin n) (Fin n) ℂ ×
          EuclideanSpace ℂ (Fin n) =>
        Matrix.toEuclideanLin Av.1
          (angularEuclideanConjugation Av.2)) := by
  change Continuous
    (fun Av : Matrix (Fin n) (Fin n) ℂ ×
        EuclideanSpace ℂ (Fin n) =>
      WithLp.toLp 2 (fun i : Fin n =>
        ∑ j : Fin n, Av.1 i j * conj (Av.2 j)))
  apply (PiLp.continuous_toLp 2 (fun _ : Fin n => ℂ)).comp
  apply continuous_pi
  intro i
  apply continuous_finsetSum
  intro j _
  exact (continuous_fst.matrix_elem i j).mul
    (Complex.continuous_conj.comp
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) j).comp
        continuous_snd))

private theorem aestronglyMeasurable_complexEuclideanConjugatedMatrixAction
    {n : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {A : X → Matrix (Fin n) (Fin n) ℂ}
    {V : X → EuclideanSpace ℂ (Fin n)}
    (hA : AEStronglyMeasurable A μ)
    (hV : AEStronglyMeasurable V μ) :
    AEStronglyMeasurable
      (fun x : X =>
        Matrix.toEuclideanLin (A x)
          (angularEuclideanConjugation (V x))) μ := by
  change AEStronglyMeasurable
    ((fun Av : Matrix (Fin n) (Fin n) ℂ ×
        EuclideanSpace ℂ (Fin n) =>
      Matrix.toEuclideanLin Av.1
        (angularEuclideanConjugation Av.2)) ∘
      (fun x : X => (A x, V x))) μ
  exact (continuous_complexEuclideanConjugatedMatrixAction
    (n := n)).comp_aestronglyMeasurable (hA.prodMk hV)

end RadialPhysicalResolventRootCutoffPairing

namespace TorusWeakRadialCutoffCommutator

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore WeightedTorusDolbeault
open MatrixTorusBochnerCoreConvergence
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology ContDiff

private theorem continuous_complexEuclideanOuterProduct_uncurry
    {n : ℕ} :
    Continuous
      (fun vw : EuclideanSpace ℂ (Fin n) ×
          EuclideanSpace ℂ (Fin n) =>
        complexEuclideanOuterProduct vw.1 vw.2) := by
  change Continuous
    (fun vw : EuclideanSpace ℂ (Fin n) ×
        EuclideanSpace ℂ (Fin n) =>
      WithLp.toLp 2 (fun ij : Fin n × Fin n =>
        vw.1 ij.1 * vw.2 ij.2))
  apply (PiLp.continuous_toLp 2
    (fun _ : Fin n × Fin n => ℂ)).comp
  apply continuous_pi
  intro ij
  exact
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) ij.1).comp
      continuous_fst).mul
    ((PiLp.continuous_apply 2 (fun _ : Fin n => ℂ) ij.2).comp
      continuous_snd)

private def angularWeakSourceCutoffDerivativeCommutator
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) (q : LogTorus n) :
    EuclideanSpace ℂ (Fin n × Fin n) :=
  complexEuclideanOuterProduct (W q)
    (sourceCutoffBarGradient m q)

private theorem angularWeakSourceCutoffDerivativeCommutator_aestronglyMeasurable
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) :
    AEStronglyMeasurable
      (angularWeakSourceCutoffDerivativeCommutator W m)
      (angularWeightedTorusMeasure a) := by
  change AEStronglyMeasurable
    ((fun vw : EuclideanSpace ℂ (Fin n) ×
        EuclideanSpace ℂ (Fin n) =>
      complexEuclideanOuterProduct vw.1 vw.2) ∘
      (fun q : LogTorus n =>
        (W q, sourceCutoffBarGradient m q)))
    (angularWeightedTorusMeasure a)
  exact (continuous_complexEuclideanOuterProduct_uncurry
    (n := n)).comp_aestronglyMeasurable
      ((MeasureTheory.Lp.memLp W).aestronglyMeasurable.prodMk
        (continuous_sourceCutoffBarGradient m).aestronglyMeasurable)

private theorem angularWeakSourceCutoffDerivativeCommutator_norm
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) (q : LogTorus n) :
    ‖angularWeakSourceCutoffDerivativeCommutator W m q‖ =
      ‖W q‖ * ‖sourceCutoffBarGradient m q‖ := by
  exact complexEuclideanOuterProduct_norm
    (W q) (sourceCutoffBarGradient m q)

private theorem angularWeakSourceCutoffDerivativeCommutator_norm_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) (q : LogTorus n) :
    ‖angularWeakSourceCutoffDerivativeCommutator W m q‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) * ‖W q‖ := by
  rw [angularWeakSourceCutoffDerivativeCommutator_norm]
  calc
    ‖W q‖ * ‖sourceCutoffBarGradient m q‖ ≤
      ‖W q‖ * (((m : ℝ) + 1)⁻¹ * C) :=
        mul_le_mul_of_nonneg_left
          (sourceCutoffBarGradient_norm_le hC m q)
          (norm_nonneg _)
    _ = _ := by ring

private theorem angularWeakSourceCutoffDerivativeCommutator_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    MemLp
      (angularWeakSourceCutoffDerivativeCommutator W m)
      2 (angularWeightedTorusMeasure a) := by
  apply (MeasureTheory.Lp.memLp W).of_le_mul
    (c := ((m : ℝ) + 1)⁻¹ * C)
    (angularWeakSourceCutoffDerivativeCommutator_aestronglyMeasurable
      W m)
  filter_upwards [] with q
  exact angularWeakSourceCutoffDerivativeCommutator_norm_le
    W hC m q

private theorem angularWeakSourceCutoffDerivativeCommutator_L2_norm_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    ‖(angularWeakSourceCutoffDerivativeCommutator_memLp
      W hC m).toLp
        (angularWeakSourceCutoffDerivativeCommutator W m)‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) * ‖W‖ := by
  have hcmp := complexLp_norm_le_of_ae_norm_le
    (angularWeakSourceCutoffDerivativeCommutator_memLp W hC m)
    (MeasureTheory.Lp.memLp W)
    (C := ((m : ℝ) + 1)⁻¹ * C)
    (mul_nonneg (by positivity) hC₀)
    (by
      filter_upwards [] with q
      exact angularWeakSourceCutoffDerivativeCommutator_norm_le
        W hC m q)
  simpa only [Lp.norm_toLp, ge_iff_le, Lp.toLp_coeFn] using hcmp

private theorem angularWeakSourceCutoffDerivativeCommutator_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C) :
    Tendsto
      (fun m : ℕ =>
        (angularWeakSourceCutoffDerivativeCommutator_memLp
          W hC m).toLp
            (angularWeakSourceCutoffDerivativeCommutator W m))
      atTop
      (nhds
        (0 : MeasureTheory.Lp
          (EuclideanSpace ℂ (Fin n × Fin n)) 2
          (angularWeightedTorusMeasure a))) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun m => norm_nonneg _)
    (fun m => angularWeakSourceCutoffDerivativeCommutator_L2_norm_le
      W hC₀ hC m)
  have ht := inv_nat_add_one_tendsto_zero.mul_const
    (C * ‖W‖)
  simpa only [mul_assoc, zero_mul] using ht

private def angularWeakSourceCutoffAdjointCommutator
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) (q : LogTorus n) : ℂ :=
  @inner ℂ (EuclideanSpace ℂ (Fin n)) _
    (sourceCutoffBarGradient m q) (W q)

private theorem angularWeakSourceCutoffAdjointCommutator_aestronglyMeasurable
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (m : ℕ) :
    AEStronglyMeasurable
      (angularWeakSourceCutoffAdjointCommutator W m)
      (angularWeightedTorusMeasure a) := by
  exact
    ((continuous_sourceCutoffBarGradient m).aestronglyMeasurable).inner
      (MeasureTheory.Lp.memLp W).aestronglyMeasurable

private theorem angularWeakSourceCutoffAdjointCommutator_norm_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) (q : LogTorus n) :
    ‖angularWeakSourceCutoffAdjointCommutator W m q‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) * ‖W q‖ := by
  unfold angularWeakSourceCutoffAdjointCommutator
  exact (norm_inner_le_norm _ _).trans
    (mul_le_mul_of_nonneg_right
      (sourceCutoffBarGradient_norm_le hC m q)
      (norm_nonneg _))

private theorem angularWeakSourceCutoffAdjointCommutator_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    MemLp
      (angularWeakSourceCutoffAdjointCommutator W m)
      2 (angularWeightedTorusMeasure a) := by
  apply (MeasureTheory.Lp.memLp W).of_le_mul
    (c := ((m : ℝ) + 1)⁻¹ * C)
    (angularWeakSourceCutoffAdjointCommutator_aestronglyMeasurable
      W m)
  filter_upwards [] with q
  exact angularWeakSourceCutoffAdjointCommutator_norm_le W hC m q

private theorem angularWeakSourceCutoffAdjointCommutator_L2_norm_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) :
    ‖(angularWeakSourceCutoffAdjointCommutator_memLp
      W hC m).toLp
        (angularWeakSourceCutoffAdjointCommutator W m)‖ ≤
      (((m : ℝ) + 1)⁻¹ * C) * ‖W‖ := by
  have hcmp := complexLp_norm_le_of_ae_norm_le
    (angularWeakSourceCutoffAdjointCommutator_memLp W hC m)
    (MeasureTheory.Lp.memLp W)
    (C := ((m : ℝ) + 1)⁻¹ * C)
    (mul_nonneg (by positivity) hC₀)
    (by
      filter_upwards [] with q
      exact angularWeakSourceCutoffAdjointCommutator_norm_le
        W hC m q)
  simpa only [Lp.norm_toLp, ge_iff_le, Lp.toLp_coeFn] using hcmp

private theorem angularWeakSourceCutoffAdjointCommutator_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C) :
    Tendsto
      (fun m : ℕ =>
        (angularWeakSourceCutoffAdjointCommutator_memLp
          W hC m).toLp
            (angularWeakSourceCutoffAdjointCommutator W m))
      atTop
      (nhds
        (0 : angularWeightedScalarL2 a)) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero (fun m => norm_nonneg _)
    (fun m => angularWeakSourceCutoffAdjointCommutator_L2_norm_le
      W hC₀ hC m)
  have ht := inv_nat_add_one_tendsto_zero.mul_const
    (C * ‖W‖)
  simpa only [mul_assoc, zero_mul] using ht

end TorusWeakRadialCutoffCommutator

namespace TorusWeakRadialExteriorEnergy

open Set Function Filter MeasureTheory Matrix
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Topology

private def complexEuclideanAntisymmetricEnergy
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) : ℂ :=
  (∑ i : Fin n, ∑ j : Fin n,
    (M (i, j) - M (j, i)) *
      conj (M (i, j) - M (j, i))) / 2

private theorem complexEuclideanAntisymmetricEnergy_im
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) :
    (complexEuclideanAntisymmetricEnergy M).im = 0 := by
  unfold complexEuclideanAntisymmetricEnergy
  change
    ((∑ i : Fin n, ∑ j : Fin n,
      (M (i, j) - M (j, i)) *
        conj (M (i, j) - M (j, i))) /
      ((2 : ℝ) : ℂ)).im = 0
  rw [Complex.div_ofReal_im]
  simp_rw [Complex.im_sum, Complex.mul_conj, Complex.ofReal_im]
  simp only [Finset.sum_const_zero, zero_div]

private theorem complexEuclideanAntisymmetricEnergy_re_nonneg
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) :
    0 ≤ (complexEuclideanAntisymmetricEnergy M).re := by
  unfold complexEuclideanAntisymmetricEnergy
  change
    0 ≤ ((∑ i : Fin n, ∑ j : Fin n,
      (M (i, j) - M (j, i)) *
        conj (M (i, j) - M (j, i))) /
      ((2 : ℝ) : ℂ)).re
  rw [Complex.div_ofReal_re]
  simp_rw [Complex.re_sum, Complex.mul_conj, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq]
  positivity

private theorem norm_complexEuclideanAntisymmetricEnergy
    {n : ℕ}
    (M : EuclideanSpace ℂ (Fin n × Fin n)) :
    ‖complexEuclideanAntisymmetricEnergy M‖ =
      (complexEuclideanAntisymmetricEnergy M).re := by
  have hre : complexEuclideanAntisymmetricEnergy M =
      (((complexEuclideanAntisymmetricEnergy M).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simp only [complexEuclideanAntisymmetricEnergy_im M, Complex.ofReal_im]
  calc
    ‖complexEuclideanAntisymmetricEnergy M‖ =
      ‖(((complexEuclideanAntisymmetricEnergy M).re : ℝ) : ℂ)‖ :=
        congrArg norm hre
    _ = |(complexEuclideanAntisymmetricEnergy M).re| := by
      rw [Complex.norm_real, Real.norm_eq_abs]
    _ = (complexEuclideanAntisymmetricEnergy M).re :=
      abs_of_nonneg (complexEuclideanAntisymmetricEnergy_re_nonneg M)

private theorem continuous_complexEuclideanAntisymmetricEnergy
    {n : ℕ} :
    Continuous (complexEuclideanAntisymmetricEnergy (n := n)) := by
  unfold complexEuclideanAntisymmetricEnergy
  apply Continuous.div_const
  apply continuous_finsetSum
  intro i _
  apply continuous_finsetSum
  intro j _
  have hij : Continuous
      (fun M : EuclideanSpace ℂ (Fin n × Fin n) =>
        M (i, j) - M (j, i)) :=
    (PiLp.continuous_apply 2
      (fun _ : Fin n × Fin n => ℂ) (i, j)).sub
      (PiLp.continuous_apply 2
        (fun _ : Fin n × Fin n => ℂ) (j, i))
  exact hij.mul (Complex.continuous_conj.comp hij)

end TorusWeakRadialExteriorEnergy

namespace TorusWeakRadialBochnerUpperBound

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore WeightedTorusDolbeault
open MatrixTorusBochnerCoreDensity TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology

private def angularWeakSourceCutoffAdjointDefectL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (d : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    {C : ℝ}
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C)
    (m : ℕ) : angularWeightedScalarL2 a :=
  -(angularSourceRadialCutoff_smul_memLp
      (MeasureTheory.Lp.memLp d) m).toLp
        (fun q : LogTorus n =>
          (sourceRadialCutoff m q : ℂ) • d q) +
    (angularWeakSourceCutoffAdjointCommutator_memLp W hC m).toLp
      (angularWeakSourceCutoffAdjointCommutator W m)

private theorem angularWeakSourceCutoffAdjointDefectL2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ}
    (d : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    {C : ℝ} (hC₀ : 0 ≤ C)
    (hC : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ C) :
    Tendsto
      (fun m : ℕ => angularWeakSourceCutoffAdjointDefectL2 d W hC m)
      atTop (nhds (-d)) := by
  have hcut :
      Tendsto
        (fun m : ℕ =>
          (angularSourceRadialCutoff_smul_memLp
            (MeasureTheory.Lp.memLp d) m).toLp
              (fun q : LogTorus n =>
                (sourceRadialCutoff m q : ℂ) • d q))
        atTop (nhds d) := by
    simpa only [MeasureTheory.Lp.toLp_coeFn] using
      (angularSourceRadialCutoff_smul_L2_tendsto
        (MeasureTheory.Lp.memLp d))
  have hcomm :=
    angularWeakSourceCutoffAdjointCommutator_L2_tendsto_zero
      W hC₀ hC
  simpa only [angularWeakSourceCutoffAdjointDefectL2, smul_eq_mul, add_zero] using
    hcut.neg.add hcomm

end TorusWeakRadialBochnerUpperBound

namespace TorusClosedMollifiedRootBochner

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative
open WeightedDolbeaultBochnerIdentity MatrixTorusBochnerIdentity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault WeightedTorusBochner
open WeightedTorusBrascampLieb TorusNoncompactBochner TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace Topology ContDiff

private theorem angularTorusFormAdjoint_eq_coverFormAdjoint
    {n : ℕ} (a : LogTorus n → ℝ)
    (V : LogSpace n → LogSpace n) (q : LogTorus n) :
    angularTorusFormAdjoint a V q =
      coverFormAdjoint (angularCoverPotential a) V
        (sourceTorusCoverPoint q) := by
  rfl

private theorem angularWeakDolbeaultResolvent_components_mem_graph
    {n : ℕ} (a : LogTorus n → ℝ)
    (g : angularWeightedScalarL2 a) :
    WithLp.toLp 2
      (angularWeakScalarResolventCLM a g,
       WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)) ∈
      angularDolbeaultGraph a := by
  have h := (angularWeakDolbeaultResolvent a g).property
  rw [angularWeakScalarResolventCLM_apply]
  change WithLp.toLp 2
    ((angularWeakDolbeaultResolvent a g :
      angularDolbeaultGraphAmbient a).ofLp) ∈
    angularDolbeaultGraph a
  rw [WithLp.toLp_ofLp]
  exact h

private theorem sourceTorusFormExteriorDerivativeDensity_cutoff_eq_antisymmetric
    {n : ℕ} {V : LogSpace n → LogSpace n}
    (hV : ContDiff ℝ 2 V)
    (hclosed : ∀ q : LogTorus n,
      Matrix.IsSymm (fun i j : Fin n =>
        sourceTorusBarPartial (fun z => V z i) j q))
    (m : ℕ) (q : LogTorus n) :
    sourceTorusFormExteriorDerivativeDensity
        (cutoffPhysicalField m V) q =
      complexEuclideanAntisymmetricEnergy
        (sourceCutoffDerivativeCommutator m V q) := by
  unfold sourceTorusFormExteriorDerivativeDensity
    complexEuclideanAntisymmetricEnergy
  simp_rw [sourceTorusBarPartial_cutoffPhysicalField_antisymmetric
    hV hclosed m]

end TorusClosedMollifiedRootBochner

namespace TorusStrongWeightedRadialCutoff

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open WeightedTorusDolbeault
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℕ → LogTorus n → E}
    {f : LogTorus n → E}
    (hlocal : ∀ (k : ℕ) {S : Set (LogTorus n)}, IsCompact S →
      IntegrableOn
        (fun q : LogTorus n => ‖F k q - f q‖ ^ 2)
        S (angularWeightedTorusMeasure a))
    (hconv : ∀ {S : Set (LogTorus n)}, IsCompact S →
      Tendsto
        (fun k : ℕ =>
          ∫ q in S, ‖F k q - f q‖ ^ 2
            ∂(angularWeightedTorusMeasure a))
        atTop (nhds 0))
    (m : ℕ) :
    Tendsto
      (fun k : ℕ =>
        ∫ q : LogTorus n,
          ‖(sourceRadialCutoff m q : ℂ) • F k q -
            (sourceRadialCutoff m q : ℂ) • f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  classical
  let S : Set (LogTorus n) :=
    tsupport (sourceRadialCutoff (n := n) m)
  have hS : IsCompact S :=
    sourceRadialCutoff_hasCompactSupport m
  have hpoint (k : ℕ) (q : LogTorus n) :
      ‖(sourceRadialCutoff m q : ℂ) • F k q -
          (sourceRadialCutoff m q : ℂ) • f q‖ ^ 2 ≤
        S.indicator
          (fun p : LogTorus n => ‖F k p - f p‖ ^ 2) q := by
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      have hscalar : ‖(sourceRadialCutoff m q : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
        exact sourceRadialCutoff_le_one m q
      have hnorm :
          ‖(sourceRadialCutoff m q : ℂ) • F k q -
            (sourceRadialCutoff m q : ℂ) • f q‖ ≤
          ‖F k q - f q‖ := by
        rw [← smul_sub, norm_smul]
        calc
          ‖(sourceRadialCutoff m q : ℂ)‖ * ‖F k q - f q‖ ≤
              1 * ‖F k q - f q‖ :=
            mul_le_mul_of_nonneg_right hscalar
              (norm_nonneg _)
          _ = _ := one_mul _
      exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hnorm
    · have hzero : sourceRadialCutoff m q = 0 :=
        image_eq_zero_of_notMem_tsupport hq
      simp only [hzero, Complex.ofReal_zero, zero_smul, sub_self, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, Set.indicator_of_notMem hq, Std.le_refl]
  have hbound (k : ℕ) :
      (∫ q : LogTorus n,
        ‖(sourceRadialCutoff m q : ℂ) • F k q -
          (sourceRadialCutoff m q : ℂ) • f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) ≤
      ∫ q in S, ‖F k q - f q‖ ^ 2
        ∂(angularWeightedTorusMeasure a) := by
    calc
      _ ≤ ∫ q : LogTorus n,
        S.indicator
          (fun p : LogTorus n => ‖F k p - f p‖ ^ 2) q
          ∂(angularWeightedTorusMeasure a) := by
        apply MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall
            (fun q => sq_nonneg _))
          ((hlocal k hS).integrable_indicator hS.measurableSet)
        exact Filter.Eventually.of_forall (hpoint k)
      _ = _ := MeasureTheory.integral_indicator hS.measurableSet
  exact squeeze_zero
    (fun k => integral_nonneg (fun q => sq_nonneg _))
    hbound
    (hconv hS)

private theorem angularWeightedLp_tendsto_of_squared_error_integral
    {n : ℕ} {a : LogTorus n → ℝ}
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    {F : ℕ → LogTorus n → E} {f : LogTorus n → E}
    (hF : ∀ k : ℕ, MemLp (F k) 2 (angularWeightedTorusMeasure a))
    (hf : MemLp f 2 (angularWeightedTorusMeasure a))
    (hconv : Tendsto
      (fun k : ℕ =>
        ∫ q : LogTorus n, ‖F k q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0)) :
    Tendsto
      (fun k : ℕ => (hF k).toLp (F k))
      atTop (nhds (hf.toLp f)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq (k : ℕ) :
      ‖(hF k).toLp (F k) - hf.toLp f‖ ^ 2 =
        ∫ q : LogTorus n, ‖F k q - f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a) := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards
      [MeasureTheory.Lp.coeFn_sub
        ((hF k).toLp (F k)) (hf.toLp f),
       (hF k).coeFn_toLp, hf.coeFn_toLp]
      with q hsub hleft hright
    rw [hsub]
    change
      ‖((hF k).toLp (F k)) q - (hf.toLp f) q‖ ^ 2 = _
    rw [hleft, hright]
  have hsqtendsto :
      Tendsto
        (fun k : ℕ => ‖(hF k).toLp (F k) - hf.toLp f‖ ^ 2)
        atTop (nhds 0) := by
    simpa only [hsq] using hconv
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp
    hsqtendsto
  simpa only [comp_def, norm_nonneg, Real.sqrt_sq, Real.sqrt_zero] using hsqrt

end TorusStrongWeightedRadialCutoff

namespace RadialPhysicalResolventRootCutoffUniformExtraction

open Set Function Filter MeasureTheory Matrix
open WeightedTorusHilbert WeightedResolventConstantCore MatrixTorusBochnerCoreDensity
open scoped BigOperators ENNReal InnerProductSpace Topology

private theorem sourceRadialCutoff_eventually_one_on_compact
    {n : ℕ} {s : Set (LogTorus n)}
    (hs : IsCompact s) :
    ∀ᶠ m : ℕ in atTop,
      ∀ q ∈ s, sourceRadialCutoff m q = 1 := by
  have hrad : IsCompact
      ((fun q : LogTorus n => q.1) '' s) :=
    hs.image continuous_fst
  obtain ⟨R, hR⟩ := hrad.exists_bound_of_continuousOn
    (continuous_id : Continuous
      (fun x : Space n => x)).continuousOn
  obtain ⟨N, hN⟩ := exists_nat_gt R
  filter_upwards [eventually_ge_atTop N] with m hm
  intro q hq
  change growingBump m q.1 = 1
  apply (growingBump m).one_of_mem_closedBall
  rw [Metric.mem_closedBall, dist_zero_right]
  change ‖q.1‖ ≤ (m : ℝ) + 1
  have hNm : (N : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hqR := hR q.1 ⟨q, hq, rfl⟩
  change ‖q.1‖ ≤ R at hqR
  linarith

end RadialPhysicalResolventRootCutoffUniformExtraction

namespace TorusWeakResolventRootBochner

open Set Function Filter MeasureTheory Matrix
open RadialPhysicalResolventRootCutoffPairing
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff

private theorem angularEuclideanConjugation_sub
    {n : ℕ} (v w : EuclideanSpace ℂ (Fin n)) :
    angularEuclideanConjugation (v - w) =
      angularEuclideanConjugation v -
        angularEuclideanConjugation w := by
  ext i
  change conj (v i - w i) = conj (v i) - conj (w i)
  exact map_sub (starRingEnd ℂ) (v i) (w i)

private theorem angularEuclideanConjugation_real_smul
    {n : ℕ} (c : ℝ) (v : EuclideanSpace ℂ (Fin n)) :
    angularEuclideanConjugation ((c : ℂ) • v) =
      (c : ℂ) • angularEuclideanConjugation v := by
  ext i
  change conj ((c : ℂ) * v i) = (c : ℂ) * conj (v i)
  simp only [map_mul, Complex.conj_ofReal]

end TorusWeakResolventRootBochner

namespace TorusWeakRadialExteriorMollification

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedPoincare WeightedBrascampLieb
open WeightedResolventConstantCore EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open TorusMollifiedBochner TorusNoncompactBochner TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff

private theorem sourceCutoffBarGradient_hasCompactSupport
    {n : ℕ} (m : ℕ) :
    HasCompactSupport (sourceCutoffBarGradient (n := n) m) := by
  let S : Set (LogTorus n) :=
    tsupport (fun x : Space n => growingBump m x) ×ˢ
      (Set.univ : Set (AngularTorus n))
  have hS : IsCompact S :=
    (growingBump (n := n) m).hasCompactSupport.prod isCompact_univ
  apply HasCompactSupport.intro hS
  intro q hq
  have hrad :
      q.1 ∉ tsupport
        (fun x : Space n => growingBump m x) := by
    intro hbase
    exact hq ⟨hbase, Set.mem_univ q.2⟩
  have hder :
      fderiv ℝ
        (fun x : Space n => growingBump m x) q.1 = 0 :=
    fderiv_of_notMem_tsupport ℝ hrad
  have hgrad :
      euclideanGradient
        (fun x : Space n => growingBump m x) q.1 = 0 := by
    ext i
    simp only [euclideanGradient, coordinateGradient, hder, _root_.zero_apply, PiLp.zero_apply]
  apply norm_eq_zero.mp
  rw [sourceCutoffBarGradient_norm_eq, hgrad, norm_zero]

private theorem sourceCutoffDerivativeCommutator_hasCompactSupport
    {n : ℕ} (m : ℕ)
    (V : LogSpace n → LogSpace n) :
    HasCompactSupport (sourceCutoffDerivativeCommutator m V) := by
  apply (sourceCutoffBarGradient_hasCompactSupport m).mono
  intro q hq
  change sourceCutoffBarGradient m q ≠ 0
  intro hz
  apply hq
  rw [sourceCutoffDerivativeCommutator_eq_outerProduct, hz]
  ext ij
  simp only [complexEuclideanOuterProduct, PiLp.zero_apply, mul_zero]

private theorem mollifiedRadialMatrixCommutator_sub_weak
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) (q : LogTorus n) :
    sourceCutoffDerivativeCommutator m
        (angularGraphMollifiedPhysicalField W ℓ) q -
      angularWeakSourceCutoffDerivativeCommutator W m q =
      complexEuclideanOuterProduct
        (torusFormRepresentative
          (angularGraphMollifiedPhysicalField W ℓ) q - W q)
        (sourceCutoffBarGradient m q) := by
  rw [sourceCutoffDerivativeCommutator_eq_outerProduct]
  unfold angularWeakSourceCutoffDerivativeCommutator
  ext ij
  change
    (torusFormRepresentative
        (angularGraphMollifiedPhysicalField W ℓ) q) ij.1 *
        (sourceCutoffBarGradient m q) ij.2 -
      (W q) ij.1 * (sourceCutoffBarGradient m q) ij.2 =
      ((torusFormRepresentative
          (angularGraphMollifiedPhysicalField W ℓ) q) ij.1 -
        (W q) ij.1) * (sourceCutoffBarGradient m q) ij.2
  ring

private theorem complexEuclideanAntisymmetricEnergy_integrable_of_memLp
    {n : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {M : X → EuclideanSpace ℂ (Fin n × Fin n)}
    (hM : MemLp M 2 μ) :
    Integrable
      (fun x : X => complexEuclideanAntisymmetricEnergy (M x)) μ := by
  have hsq : Integrable (fun x : X => ‖M x‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hM.aestronglyMeasurable).mp hM
  apply (hsq.const_mul (2 : ℝ)).mono'
    ((continuous_complexEuclideanAntisymmetricEnergy (n := n)).comp_aestronglyMeasurable
      hM.aestronglyMeasurable)
  filter_upwards [] with x
  rw [norm_complexEuclideanAntisymmetricEnergy]
  exact complexEuclidean_antisymmetric_energy_le_two_norm_sq (M x)

private theorem integral_complexEuclideanAntisymmetricEnergy_le_of_memLp
    {n : ℕ} {X : Type*} [MeasurableSpace X]
    {μ : Measure X}
    {M : X → EuclideanSpace ℂ (Fin n × Fin n)}
    (hM : MemLp M 2 μ) :
    (∫ x : X,
      complexEuclideanAntisymmetricEnergy (M x) ∂μ).re ≤
      2 * ‖hM.toLp M‖ ^ 2 := by
  have hsq : Integrable (fun x : X => ‖M x‖ ^ 2) μ :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm
      hM.aestronglyMeasurable).mp hM
  have hext := complexEuclideanAntisymmetricEnergy_integrable_of_memLp hM
  calc
    (∫ x : X,
      complexEuclideanAntisymmetricEnergy (M x) ∂μ).re =
        ∫ x : X,
          (complexEuclideanAntisymmetricEnergy (M x)).re ∂μ :=
            (integral_re hext).symm
    _ ≤ ∫ x : X, (2 : ℝ) * ‖M x‖ ^ 2 ∂μ :=
      integral_mono hext.re (hsq.const_mul 2)
        (fun x => complexEuclidean_antisymmetric_energy_le_two_norm_sq
          (M x))
    _ = 2 * ∫ x : X, ‖M x‖ ^ 2 ∂μ :=
      integral_const_mul 2 _
    _ = 2 * ‖hM.toLp M‖ ^ 2 := by
      congr 1
      rw [complexLp_norm_sq_eq_integral]
      apply integral_congr_ae
      filter_upwards [hM.coeFn_toLp] with x hx
      rw [hx]

end TorusWeakRadialExteriorMollification

namespace TorusStrongWeightedCutoffAdjoint

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert JetEnvelopeRightDerivative
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerCoreConvergence MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBochner TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusWeightedAdjointMollification TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem torusScalarRepresentative_eq_sourceTorusCoverPoint
    {n : ℕ} (F : LogSpace n → ℂ) (q : LogTorus n) :
    torusScalarRepresentative F q = F (sourceTorusCoverPoint q) := by
  rfl

private theorem angularMollifiedPhysicalAdjointDriftCommutator_periodic
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (k : ℕ) (d : Fin n → ℤ) :
    Function.Periodic
      (angularMollifiedPhysicalAdjointDriftCommutator W k)
      (imaginaryShift d) := by
  intro z
  unfold angularMollifiedPhysicalAdjointDriftCommutator
  apply Finset.sum_congr rfl
  intro j _
  let b : LogSpace n → ℂ := fun x =>
    holomorphicCoordinate
      (fun y => (angularCoverPotential a y : ℂ)) x j
  let h : LogSpace n → ℂ :=
    complexTorusCoverLift
      (fun q => (W q : EuclideanSpace ℂ (Fin n)) j)
  have hb : ∀ e : Fin n → ℤ,
      Function.Periodic b (imaginaryShift e) := by
    intro e
    exact holomorphicCoordinate_periodic
      (fun y => (angularCoverPotential a y : ℂ))
      (complexAngularCoverPotential_periodic a) j e
  have hh : ∀ e : Fin n → ℤ,
      Function.Periodic h (imaginaryShift e) := by
    intro e
    exact complexTorusCoverLift_periodic
      (fun q => (W q : EuclideanSpace ℂ (Fin n)) j) e
  have hp : ∀ e : Fin n → ℤ,
      Function.Periodic (fun x => b x * h x)
        (imaginaryShift e) := by
    intro e x
    change b (x + imaginaryShift e) * h (x + imaginaryShift e) =
      b x * h x
    rw [hb e x, hh e x]
  change
    normalizedCoverMollification (fun x => b x * h x)
        k (z + imaginaryShift d) -
      b (z + imaginaryShift d) *
        normalizedCoverMollification h k (z + imaginaryShift d) =
      normalizedCoverMollification (fun x => b x * h x) k z -
        b z * normalizedCoverMollification h k z
  rw [normalizedCoverMollification_periodic hp k d z,
    hb d z, normalizedCoverMollification_periodic hh k d z]

private theorem angularClosedMollifiedRadialAdjointCommutator_sub_weak
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) (q : LogTorus n) :
    angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ) q -
      angularWeakSourceCutoffAdjointCommutator W m q =
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (sourceCutoffBarGradient m q)
        (torusFormRepresentative
          (angularGraphMollifiedPhysicalField W ℓ) q - W q) := by
  unfold angularSourceCutoffAdjointCommutator
    angularWeakSourceCutoffAdjointCommutator
  rw [inner_sub_right]

end TorusStrongWeightedCutoffAdjoint

namespace TorusHomogeneousCutoffAdjoint

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open ComplexKillingSaturationBridge WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation MatrixTorusBochnerIdentity
open WeightedTorusDolbeault TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusFriedrichsMollifierEstimates TorusWeightedAdjointMollification
open TorusStrongWeightedTorusDescent TorusStrongWeightedRadialCutoff TorusFriedrichsCutoff
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem continuous_angularMollifiedPhysicalAdjointDriftCommutator
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a) (k : ℕ) :
    Continuous (angularMollifiedPhysicalAdjointDriftCommutator W k) := by
  unfold angularMollifiedPhysicalAdjointDriftCommutator
  apply continuous_finsetSum
  intro j _
  apply continuous_normalizedCoverComplexDriftCommutator
    (angularWeightedFormCoordinateCoverLift_locallyIntegrable ha W j)
  exact (contDiff_holomorphicCoordinate
    (Complex.ofRealCLM.contDiff.comp ha2) j).continuous

private theorem graphField_mollification_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ} (ha : Continuous a)
    (W : angularWeightedFormL2 a)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun k : ℕ =>
        ∫ q in S,
          ‖torusFormRepresentative
              (angularGraphMollifiedPhysicalField W k) q - W q‖ ^ 2
            ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  classical
  let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
  let : IsLocallyFiniteMeasure μ :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts μ :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  let e : Fin n → ℕ → LogTorus n → ℂ :=
    fun j k q =>
      torusScalarRepresentative
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n =>
              (W r : EuclideanSpace ℂ (Fin n)) j)) k) q -
        (W q : EuclideanSpace ℂ (Fin n)) j
  have hvanish (j : Fin n) :
      Tendsto
        (fun k : ℕ => ∫ q in S, ‖e j k q‖ ^ 2 ∂μ)
        atTop (nhds 0) :=
    TorusHomogeneousFriedrichs.formCoordinate_mollification_L2_tendsto_zero
        ha W j hS
  have hsum := tendsto_finsetSum Finset.univ
    (fun (j : Fin n) _ => hvanish j)
  have hint (j : Fin n) (k : ℕ) :
      IntegrableOn (fun q : LogTorus n => ‖e j k q‖ ^ 2) S μ := by
    have hmoll : Continuous
        (fun q : LogTorus n =>
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n =>
                  (W r : EuclideanSpace ℂ (Fin n)) j)) k) q) := by
      apply continuous_torusScalarRepresentative_of_periodic
      · exact (contDiff_normalizedCoverMollification
          (angularWeightedFormCoordinateCoverLift_locallyIntegrable
            ha W j) k 0).continuous
      · intro d
        exact normalizedCoverMollification_periodic
          (fun d' => complexTorusCoverLift_periodic
            (fun q : LogTorus n =>
              (W q : EuclideanSpace ℂ (Fin n)) j) d') k d
    have hM : MemLp
        (fun q : LogTorus n =>
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n =>
                  (W r : EuclideanSpace ℂ (Fin n)) j)) k) q)
        2 (μ.restrict S) := by
      apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
        (hmoll.aestronglyMeasurable.mono_measure
          Measure.restrict_le_self)).mpr
      exact (hmoll.norm.pow 2).continuousOn.integrableOn_compact hS
    have hW : MemLp
        (fun q : LogTorus n =>
          (W q : EuclideanSpace ℂ (Fin n)) j)
        2 (μ.restrict S) := by
      exact ((MeasureTheory.Lp.memLp W).mono_measure
        Measure.restrict_le_self).continuousLinearMap_comp
          (PiLp.proj (𝕜 := ℂ) 2 (fun _ : Fin n => ℂ) j)
    exact (hM.sub hW).norm.integrable_sq
  have hpoint (k : ℕ) (q : LogTorus n) :
      ‖torusFormRepresentative
          (angularGraphMollifiedPhysicalField W k) q - W q‖ ^ 2 =
      ∑ j : Fin n, ‖e j k q‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    congr 1
  have hident (k : ℕ) :
      (∫ q in S,
        ‖torusFormRepresentative
            (angularGraphMollifiedPhysicalField W k) q - W q‖ ^ 2
          ∂μ) =
      ∑ j : Fin n, (∫ q in S, ‖e j k q‖ ^ 2 ∂μ) := by
    calc
      _ = ∫ q in S, ∑ j : Fin n, ‖e j k q‖ ^ 2 ∂μ := by
        apply integral_congr_ae
        filter_upwards [] with q
        exact hpoint k q
      _ = _ := MeasureTheory.integral_finsetSum Finset.univ
        (fun j _ => hint j k)
  have ht :
      Tendsto
        (fun k : ℕ =>
          ∑ j : Fin n, (∫ q in S, ‖e j k q‖ ^ 2 ∂μ))
        atTop (nhds 0) := by
    simpa only [Finset.sum_const_zero] using hsum
  exact ht.congr'
    (Filter.Eventually.of_forall (fun k => (hident k).symm))

private theorem angularMollifiedPhysicalAdjointDriftCommutator_compact_weighted_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a)
    {S : Set (LogTorus n)} (hS : IsCompact S) :
    Tendsto
      (fun ℓ : ℕ =>
        ∫ q in S,
          ‖torusScalarRepresentative
              (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  have hzloc : LocallyIntegrable
      (complexTorusCoverLift (fun _ : LogTorus n => (0 : ℂ)))
      (volume : Measure (LogSpace n)) := by
    have hzero :
        complexTorusCoverLift (fun _ : LogTorus n => (0 : ℂ)) =
          (fun _ : LogSpace n => (0 : ℂ)) := by
      funext x
      rfl
    rw [hzero]
    exact locallyIntegrable_zero
  have hzmem : ∀ {K : Set (LogSpace n)}, IsCompact K →
      MemLp (complexTorusCoverLift (fun _ : LogTorus n => (0 : ℂ)))
        2 ((volume : Measure (LogSpace n)).restrict K) := by
    intro K _
    change MemLp (fun _ : LogSpace n => (0 : ℂ)) 2
      ((volume : Measure (LogSpace n)).restrict K)
    exact MeasureTheory.MemLp.zero
  have h :=
    angularWeightedTorus_compact_scalarRepresentative_L2_tendsto_of_cover
      (f := fun _ : LogTorus n => (0 : ℂ))
      ha aestronglyMeasurable_zero hzloc hzmem
      (F := fun ℓ => angularMollifiedPhysicalAdjointDriftCommutator W ℓ)
      (fun ℓ => continuous_angularMollifiedPhysicalAdjointDriftCommutator
        ha ha2 W ℓ)
      (fun ℓ d =>
        TorusStrongWeightedCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_periodic
          W ℓ d)
      (by
        intro K hK
        simpa only [complexTorusCoverLift, sub_zero] using
          (TorusHomogeneousFriedrichs.angularMollifiedPhysicalAdjointDriftCommutator_tendsto_zero
              ha ha2 W hK))
      hS
  simpa only [sub_zero] using h

private theorem angularClosedMollifiedDrift_fixedRadialCutoff_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) :
    MemLp
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q)
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hd : Continuous
      (torusScalarRepresentative
        (angularMollifiedPhysicalAdjointDriftCommutator W ℓ)) :=
    continuous_torusScalarRepresentative_of_periodic
      (continuous_angularMollifiedPhysicalAdjointDriftCommutator
        ha ha2 W ℓ)
      (TorusStrongWeightedCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_periodic W ℓ)
  have hc : Continuous
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q) :=
    (Complex.continuous_ofReal.comp
      (continuous_sourceRadialCutoff m)).smul hd
  have hs : HasCompactSupport
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q) := by
    apply (sourceRadialCutoff_hasCompactSupport m).mono
    intro q hq
    change sourceRadialCutoff m q ≠ 0
    intro hz
    apply hq
    simp only [hz, Complex.ofReal_zero, smul_eq_mul, zero_mul]
  exact hc.memLp_of_hasCompactSupport hs

private theorem angularClosedMollifiedDrift_fixedRadialCutoff_L2_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a) (m : ℕ) :
    Tendsto
      (fun ℓ : ℕ =>
        (angularClosedMollifiedDrift_fixedRadialCutoff_memLp
          ha ha2 W ℓ m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q))
      atTop (nhds (0 : angularWeightedScalarL2 a)) := by
  have hlocal : ∀ (ℓ : ℕ) {S : Set (LogTorus n)}, IsCompact S →
      IntegrableOn
        (fun q : LogTorus n =>
          ‖torusScalarRepresentative
              (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q -
            (0 : ℂ)‖ ^ 2)
        S (angularWeightedTorusMeasure a) := by
    intro ℓ S hS
    let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
      angularWeightedTorusMeasure_isLocallyFinite ha
    have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
      isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    have hd : Continuous
        (torusScalarRepresentative
          (angularMollifiedPhysicalAdjointDriftCommutator W ℓ)) :=
      continuous_torusScalarRepresentative_of_periodic
        (continuous_angularMollifiedPhysicalAdjointDriftCommutator
          ha ha2 W ℓ)
        (TorusStrongWeightedCutoffAdjoint.angularMollifiedPhysicalAdjointDriftCommutator_periodic
          W ℓ)
    change Integrable
      (fun q : LogTorus n =>
        ‖torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q -
          (0 : ℂ)‖ ^ 2)
      ((angularWeightedTorusMeasure a).restrict S)
    have hi : IntegrableOn
        (fun q : LogTorus n =>
          ‖torusScalarRepresentative
              (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q‖ ^ 2)
        S (angularWeightedTorusMeasure a) :=
      (hd.norm.pow 2).continuousOn.integrableOn_compact hS
    change Integrable
      (fun q : LogTorus n =>
        ‖torusScalarRepresentative
            (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q‖ ^ 2)
      ((angularWeightedTorusMeasure a).restrict S) at hi
    refine hi.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [sub_zero]
  have hc : Tendsto
      (fun ℓ : ℕ =>
        ∫ q : LogTorus n,
          ‖(sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q -
            (sourceRadialCutoff m q : ℂ) • (0 : ℂ)‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) :=
    angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
      hlocal
      (by
        intro S hS
        simpa only [sub_zero] using
          angularMollifiedPhysicalAdjointDriftCommutator_compact_weighted_L2_tendsto_zero
            ha ha2 W hS)
      m
  have ht := angularWeightedLp_tendsto_of_squared_error_integral
    (fun ℓ => angularClosedMollifiedDrift_fixedRadialCutoff_memLp
      ha ha2 W ℓ m)
    (MeasureTheory.MemLp.zero :
      MemLp (fun _ : LogTorus n => (0 : ℂ)) 2
        (angularWeightedTorusMeasure a))
    (by simpa only [smul_eq_mul, Pi.zero_apply, sub_zero, Complex.norm_mul, Complex.norm_real,
          Real.norm_eq_abs, mul_zero] using hc)
  simpa only [smul_eq_mul, MemLp.toLp_zero] using ht

private theorem angularWeightedScalar_fixedRadialCutoff_mollification_integral_tendsto_zero
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a) (m : ℕ) :
    Tendsto
      (fun k : ℕ =>
        ∫ q : LogTorus n,
          ‖(sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (normalizedCoverMollification
                  (complexTorusCoverLift
                    (fun r : LogTorus n => f r)) k) q -
            (sourceRadialCutoff m q : ℂ) • f q‖ ^ 2
          ∂(angularWeightedTorusMeasure a))
      atTop (nhds 0) := by
  apply angularWeightedTorus_fixedRadialCutoff_smul_error_integral_tendsto_zero
    (F := fun k q =>
      torusScalarRepresentative
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n => f r)) k) q)
    (f := fun q => f q)
    (m := m)
  · intro k S hS
    let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
    let : IsLocallyFiniteMeasure μ :=
      angularWeightedTorusMeasure_isLocallyFinite ha
    have : IsFiniteMeasureOnCompacts μ :=
      isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
    have hc : Continuous
        (torusScalarRepresentative
          (normalizedCoverMollification
            (complexTorusCoverLift
              (fun r : LogTorus n => f r)) k)) := by
      apply continuous_torusScalarRepresentative_of_periodic
      · exact (contDiff_normalizedCoverMollification
          (angularWeightedScalarCoverLift_locallyIntegrable
            ha f) k 0).continuous
      · intro d
        exact normalizedCoverMollification_periodic
          (fun d' => complexTorusCoverLift_periodic
            (fun q : LogTorus n => f q) d') k d
    have hM : MemLp
        (torusScalarRepresentative
          (normalizedCoverMollification
            (complexTorusCoverLift
              (fun r : LogTorus n => f r)) k))
        2 (μ.restrict S) := by
      apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
        (hc.aestronglyMeasurable.mono_measure
          Measure.restrict_le_self)).mpr
      exact (hc.norm.pow 2).continuousOn.integrableOn_compact hS
    exact (hM.sub ((MeasureTheory.Lp.memLp f).mono_measure
      Measure.restrict_le_self)).norm.integrable_sq
  · intro S hS
    exact TorusHomogeneousFriedrichs.scalar_mollification_L2_tendsto_zero
        ha f hS

private theorem fixedRadialCutoff_mollification_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a)
    (m k : ℕ) :
    MemLp
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n => f r)) k) q)
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hmoll : Continuous
      (torusScalarRepresentative
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n => f r)) k)) := by
    apply continuous_torusScalarRepresentative_of_periodic
    · exact (contDiff_normalizedCoverMollification
        (angularWeightedScalarCoverLift_locallyIntegrable
          ha f) k 0).continuous
    · intro d
      exact normalizedCoverMollification_periodic
        (fun d' => complexTorusCoverLift_periodic
          (fun q : LogTorus n => f q) d') k d
  have hcont : Continuous
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n => f r)) k) q) :=
    (Complex.continuous_ofReal.comp
      (continuous_sourceRadialCutoff m)).smul hmoll
  have hsupp : HasCompactSupport
      (fun q : LogTorus n =>
        (sourceRadialCutoff m q : ℂ) •
          torusScalarRepresentative
            (normalizedCoverMollification
              (complexTorusCoverLift
                (fun r : LogTorus n => f r)) k) q) := by
    apply (sourceRadialCutoff_hasCompactSupport m).mono
    intro q hq
    change sourceRadialCutoff m q ≠ 0
    intro hzero
    apply hq
    simp only [hzero, Complex.ofReal_zero, smul_eq_mul, zero_mul]
  exact hcont.memLp_of_hasCompactSupport hsupp

private theorem angularWeightedScalar_fixedRadialCutoff_mollification_L2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a) (m : ℕ) :
    Tendsto
      (fun k : ℕ =>
        (fixedRadialCutoff_mollification_memLp
          ha f m k).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (normalizedCoverMollification
                  (complexTorusCoverLift
                    (fun r : LogTorus n => f r)) k) q))
      atTop
      (nhds
        ((angularSourceRadialCutoff_smul_memLp
          (MeasureTheory.Lp.memLp f) m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) • f q))) := by
  apply angularWeightedLp_tendsto_of_squared_error_integral
    (fun k => fixedRadialCutoff_mollification_memLp
      ha f m k)
    (angularSourceRadialCutoff_smul_memLp
      (MeasureTheory.Lp.memLp f) m)
  exact angularWeightedScalar_fixedRadialCutoff_mollification_integral_tendsto_zero
    ha f m

end TorusHomogeneousCutoffAdjoint

namespace TorusHomogeneousRadialMatrix

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert WeightedBrascampLieb
open WeightedResolventConstantCore MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault TorusMollifiedBochner
open TorusWeakRadialCutoffCommutator TorusWeakRadialExteriorMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff

private theorem angularClosedMollifiedRadialMatrixCommutator_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) :
    MemLp
      (sourceCutoffDerivativeCommutator m
        (angularGraphMollifiedPhysicalField W ℓ))
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  exact
    (continuous_sourceCutoffDerivativeCommutator m
      (WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
        ha W ℓ 2)
      (angularGraphMollifiedPhysicalField_periodic W ℓ)).memLp_of_hasCompactSupport
        (sourceCutoffDerivativeCommutator_hasCompactSupport m
          (angularGraphMollifiedPhysicalField W ℓ))

private def angularClosedMollifiedRadialMatrixCommutatorL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) :
    MeasureTheory.Lp
      (EuclideanSpace ℂ (Fin n × Fin n)) 2
      (angularWeightedTorusMeasure a) :=
  (angularClosedMollifiedRadialMatrixCommutator_memLp
    ha W ℓ m).toLp
      (sourceCutoffDerivativeCommutator m
        (angularGraphMollifiedPhysicalField W ℓ))

private theorem angularClosedMollifiedRadialMatrixCommutatorL2_sub_norm_sq_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B) :
    ‖angularClosedMollifiedRadialMatrixCommutatorL2 ha W ℓ m -
      (angularWeakSourceCutoffDerivativeCommutator_memLp
        W hB m).toLp
        (angularWeakSourceCutoffDerivativeCommutator W m)‖ ^ 2 ≤
      (((m : ℝ) + 1)⁻¹ * B) ^ 2 *
        (∫ q in tsupport (sourceCutoffBarGradient (n := n) m),
          ‖torusFormRepresentative
              (angularGraphMollifiedPhysicalField W ℓ) q - W q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) := by
  let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
  let S : Set (LogTorus n) :=
    tsupport (sourceCutoffBarGradient (n := n) m)
  let V : LogSpace n → LogSpace n :=
    angularGraphMollifiedPhysicalField W ℓ
  let A : ℝ := ((m : ℝ) + 1)⁻¹ * B
  let M : MeasureTheory.Lp
      (EuclideanSpace ℂ (Fin n × Fin n)) 2 μ :=
    angularClosedMollifiedRadialMatrixCommutatorL2 ha W ℓ m
  let R : MeasureTheory.Lp
      (EuclideanSpace ℂ (Fin n × Fin n)) 2 μ :=
    (angularWeakSourceCutoffDerivativeCommutator_memLp
      W hB m).toLp
        (angularWeakSourceCutoffDerivativeCommutator W m)
  have hA : 0 ≤ A := mul_nonneg (by positivity) hB₀
  let : IsLocallyFiniteMeasure μ :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts μ :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hS : IsCompact S :=
    (sourceCutoffBarGradient_hasCompactSupport m).isCompact
  have hV : ContDiff ℝ 2 V :=
    WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2
  have hp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d) :=
    angularGraphMollifiedPhysicalField_periodic W ℓ
  have hVc : Continuous (torusFormRepresentative V) :=
    continuous_torusFormRepresentative_of_smooth_periodic hV hp
  have hVm : MemLp (torusFormRepresentative V) 2
      (μ.restrict S) := by
    apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (hVc.aestronglyMeasurable.mono_measure
        Measure.restrict_le_self)).mpr
    exact (hVc.norm.pow 2).continuousOn.integrableOn_compact hS
  have hWm : MemLp (fun q : LogTorus n => W q) 2
      (μ.restrict S) :=
    (MeasureTheory.Lp.memLp W).mono_measure
      Measure.restrict_le_self
  have hdiff : IntegrableOn
      (fun q : LogTorus n =>
        ‖torusFormRepresentative V q - W q‖ ^ 2) S μ :=
    (hVm.sub hWm).norm.integrable_sq
  have hMmem := angularClosedMollifiedRadialMatrixCommutator_memLp
    ha W ℓ m
  have hRmem := angularWeakSourceCutoffDerivativeCommutator_memLp
    W hB m
  have hM :
      (fun q : LogTorus n => M q) =ᵐ[μ]
        sourceCutoffDerivativeCommutator m V := by
    simpa [M, μ, V,
      angularClosedMollifiedRadialMatrixCommutatorL2]
      using hMmem.coeFn_toLp
  have hR :
      (fun q : LogTorus n => R q) =ᵐ[μ]
        angularWeakSourceCutoffDerivativeCommutator W m := by
    simpa only using hRmem.coeFn_toLp
  have hnorm :
      ‖M - R‖ ^ 2 =
        ∫ q : LogTorus n,
          ‖sourceCutoffDerivativeCommutator m V q -
            angularWeakSourceCutoffDerivativeCommutator W m q‖ ^ 2
          ∂μ := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Lp.coeFn_sub M R, hM, hR]
      with q hsub hm hr
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hm, hr]
  have hleft : Integrable
      (fun q : LogTorus n =>
        ‖sourceCutoffDerivativeCommutator m V q -
          angularWeakSourceCutoffDerivativeCommutator W m q‖ ^ 2)
      μ :=
    (hMmem.sub hRmem).norm.integrable_sq
  have hright : Integrable
      (S.indicator
        (fun q : LogTorus n =>
          A ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2)) μ :=
    (MeasureTheory.integrable_indicator_iff hS.measurableSet).mpr
      (hdiff.const_mul (A ^ 2))
  have hpoint (q : LogTorus n) :
      ‖sourceCutoffDerivativeCommutator m V q -
        angularWeakSourceCutoffDerivativeCommutator W m q‖ ^ 2 ≤
      S.indicator
        (fun r : LogTorus n =>
          A ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q := by
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      have hb :
          ‖sourceCutoffDerivativeCommutator m V q -
            angularWeakSourceCutoffDerivativeCommutator W m q‖ ≤
            A * ‖torusFormRepresentative V q - W q‖ := by
        rw [TorusWeakRadialExteriorMollification.mollifiedRadialMatrixCommutator_sub_weak,
          complexEuclideanOuterProduct_norm]
        calc
          ‖torusFormRepresentative V q - W q‖ *
              ‖sourceCutoffBarGradient m q‖ ≤
            ‖torusFormRepresentative V q - W q‖ * A :=
              mul_le_mul_of_nonneg_left
                (sourceCutoffBarGradient_norm_le hB m q)
                (norm_nonneg _)
          _ = _ := mul_comm _ _
      calc
        _ ≤ (A * ‖torusFormRepresentative V q - W q‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg hA (norm_nonneg _))).mpr hb
        _ = _ := by rw [mul_pow]
    · rw [Set.indicator_of_notMem hq,
        TorusWeakRadialExteriorMollification.mollifiedRadialMatrixCommutator_sub_weak]
      have hz : sourceCutoffBarGradient m q = 0 :=
        image_eq_zero_of_notMem_tsupport hq
      rw [hz]
      have houter :
          complexEuclideanOuterProduct
            (torusFormRepresentative V q - W q)
            (0 : EuclideanSpace ℂ (Fin n)) = 0 := by
        ext ij
        simp only [complexEuclideanOuterProduct, PiLp.sub_apply, PiLp.zero_apply, mul_zero]
      rw [houter]
      simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Std.le_refl]
  change ‖M - R‖ ^ 2 ≤
    A ^ 2 *
      (∫ q in S,
        ‖torusFormRepresentative V q - W q‖ ^ 2 ∂μ)
  rw [hnorm]
  calc
    _ ≤ ∫ q : LogTorus n,
      S.indicator
        (fun r : LogTorus n =>
          A ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q
      ∂μ := integral_mono hleft hright hpoint
    _ = ∫ q in S,
      A ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2
      ∂μ := MeasureTheory.integral_indicator hS.measurableSet
    _ = _ := integral_const_mul (A ^ 2) _

private theorem angularClosedMollifiedRadialMatrixCommutatorL2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B)
    (m : ℕ) :
    Tendsto
      (fun ℓ : ℕ =>
        angularClosedMollifiedRadialMatrixCommutatorL2 ha W ℓ m)
      atTop
      (nhds
        ((angularWeakSourceCutoffDerivativeCommutator_memLp
          W hB m).toLp
            (angularWeakSourceCutoffDerivativeCommutator W m))) := by
  have hS := (sourceCutoffBarGradient_hasCompactSupport
    (n := n) m).isCompact
  have hlocal :=
    TorusHomogeneousCutoffAdjoint.graphField_mollification_L2_tendsto_zero
      ha W hS
  have hsq :
      Tendsto
        (fun ℓ : ℕ =>
          ‖angularClosedMollifiedRadialMatrixCommutatorL2
              ha W ℓ m -
            (angularWeakSourceCutoffDerivativeCommutator_memLp
              W hB m).toLp
                (angularWeakSourceCutoffDerivativeCommutator W m)‖ ^ 2)
        atTop (nhds 0) := by
    apply squeeze_zero (fun ℓ => sq_nonneg _)
      (fun ℓ =>
        angularClosedMollifiedRadialMatrixCommutatorL2_sub_norm_sq_le
          ha W ℓ m hB₀ hB)
    simpa only [mul_zero] using hlocal.const_mul
      ((((m : ℝ) + 1)⁻¹ * B) ^ 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_nonneg, Real.sqrt_sq, Real.sqrt_zero] using hsq.sqrt

end TorusHomogeneousRadialMatrix

namespace TorusHomogeneousResolventGreen

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert
open WeightedDolbeaultBochnerIdentity WeightedTorusDistributionBridge
open WeightedTorusClosedGraphWeakBridge WeightedTorusDolbeault WeightedTorusBrascampLieb
open TorusDeckWeightedUnfolding TorusWeightedCoverAdjointGreen TorusWeightedCoverGlobalGreen
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution Manifold

private theorem angularWeightedScalarCover_density_inner_integrable
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : Continuous ψ) (hψcompact : HasCompactSupport ψ) :
    Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ ℂ _
            (f (complexTorusCoverProjection n z)) (ψ z))
      (volume : Measure (LogSpace n)) := by
  have hd : Continuous
      (complexCoverWeight (angularCoverPotential a)) :=
    Complex.continuous_ofReal.comp
      (continuous_coverWeight (continuous_angularCoverPotential ha))
  have hG : Continuous
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z * ψ z) :=
    hd.mul hψ
  have hGc : HasCompactSupport
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z * ψ z) :=
    hψcompact.mul_left
  have h := locallyIntegrable_complex_inner_mul_integrable
    (angularWeightedScalarCoverLift_locallyIntegrable ha f) hG hGc
  simpa only [RCLike.inner_apply, mul_left_comm, complexTorusCoverLift, mul_comm, mul_assoc] using h

private theorem angularWeightedFormCover_density_inner_integrable
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 1 ψ) (hψcompact : HasCompactSupport ψ) :
    Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate ψ z j)))
      (volume : Measure (LogSpace n)) := by
  have hd : Continuous
      (complexCoverWeight (angularCoverPotential a)) :=
    Complex.continuous_ofReal.comp
      (continuous_coverWeight (continuous_angularCoverPotential ha))
  have hj : ∀ j : Fin n, Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ ℂ _
            ((W (complexTorusCoverProjection n z) :
              EuclideanSpace ℂ (Fin n)) j)
            (barPartialCoordinate ψ z j))
      (volume : Measure (LogSpace n)) := by
    intro j
    have hG : Continuous
        (fun z : LogSpace n =>
          complexCoverWeight (angularCoverPotential a) z *
            barPartialCoordinate ψ z j) :=
      hd.mul (continuous_barPartialCoordinate hψ j)
    have hGc : HasCompactSupport
        (fun z : LogSpace n =>
          complexCoverWeight (angularCoverPotential a) z *
            barPartialCoordinate ψ z j) :=
      (compactSupport_barPartialCoordinate hψcompact j).mul_left
    have h := locallyIntegrable_complex_inner_mul_integrable
      (angularWeightedFormCoordinateCoverLift_locallyIntegrable
        ha W j) hG hGc
    simpa only [RCLike.inner_apply, mul_left_comm, complexTorusCoverLift, mul_comm, mul_assoc]
      using h
  have hsum := integrable_finsetSum
    (Finset.univ : Finset (Fin n)) (fun j _ => hj j)
  simpa only [PiLp.inner_apply, RCLike.inner_apply, Finset.mul_sum] using hsum

private theorem angularWeakDolbeaultResolvent_weighted_cover_green
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (f : angularWeightedScalarL2 a)
    {ψ : LogSpace n → ℂ}
    (hψ : ContDiff ℝ 3 ψ) (hψcompact : HasCompactSupport ψ) :
    (∫ z : LogSpace n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
              (complexTorusCoverProjection n z))
        (WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate ψ z j))
      ∂(coverWeightedMeasure (angularCoverPotential a))) =
    (∫ z : LogSpace n,
      @inner ℂ ℂ _
        ((f - angularWeakScalarResolventCLM a f)
          (complexTorusCoverProjection n z))
        (ψ z)
      ∂(coverWeightedMeasure (angularCoverPotential a))) := by
  classical
  obtain ⟨s, χ, hχ, hχsupport, hpartition⟩ :=
    exists_finite_complex_fundamental_test_partition hψcompact
  let ξ : LogSpace n → LogSpace n → ℂ :=
    fun i z => (χ i z : ℂ) * ψ z
  have hξ : ∀ i, ContDiff ℝ 3 (ξ i) := by
    intro i
    exact (Complex.ofRealCLM.contDiff.comp
      ((hχ i).of_le
        (WithTop.coe_le_coe.mpr
          (show (3 : ℕ∞) ≤ ⊤ from le_top)))).mul hψ
  have hξcompact : ∀ i, HasCompactSupport (ξ i) := by
    intro i
    exact hψcompact.mul_left
  have hξcell : ∀ i,
      tsupport (ξ i) ⊆
        coverFundamentalInterior (coverCenteredFundamentalBase i) := by
    intro i
    change tsupport (fun z => (χ i z : ℂ) * ψ z) ⊆ _
    refine tsupport_mul_subset_left.trans ?_
    refine (closure_mono ?_).trans (hχsupport i)
    intro z hz
    change (χ i z : ℂ) ≠ 0 at hz
    change χ i z ≠ 0
    intro hzzero
    apply hz
    simp only [hzzero, Complex.ofReal_zero]
  have hψsum : ψ = fun z => ∑ i ∈ s, ξ i z := by
    funext z
    exact hpartition z
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a)
  let r : angularWeightedScalarL2 a :=
    f - angularWeakScalarResolventCLM a f
  have hintW : ∀ i ∈ s, Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate (ξ i) z j)))
      (volume : Measure (LogSpace n)) := by
    intro i _
    exact angularWeightedFormCover_density_inner_integrable
      ha W ((hξ i).of_le (by norm_num)) (hξcompact i)
  have hintr : ∀ i ∈ s, Integrable
      (fun z : LogSpace n =>
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ ℂ _
            (r (complexTorusCoverProjection n z)) (ξ i z))
      (volume : Measure (LogSpace n)) := by
    intro i _
    exact angularWeightedScalarCover_density_inner_integrable
      ha r (hξ i).continuous (hξcompact i)
  have hrow (z : LogSpace n) :
      WithLp.toLp 2 (fun j : Fin n => barPartialCoordinate ψ z j) =
        ∑ i ∈ s, WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate (ξ i) z j) := by
    ext j
    simpa only [hψsum, WithLp.ofLp_sum, Finset.sum_apply] using
      (barPartialCoordinate_finset_sum_complex s ξ
        (fun i _ => (hξ i).of_le (by norm_num)) j z)
  change
    (∫ z : LogSpace n,
      @inner ℂ (EuclideanSpace ℂ (Fin n)) _
        (W (complexTorusCoverProjection n z))
        (WithLp.toLp 2
          (fun j : Fin n => barPartialCoordinate ψ z j))
      ∂(coverWeightedMeasure (angularCoverPotential a))) =
    (∫ z : LogSpace n,
      @inner ℂ ℂ _
        (r (complexTorusCoverProjection n z)) (ψ z)
      ∂(coverWeightedMeasure (angularCoverPotential a)))
  rw [integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha),
      integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha)]
  calc
    (∫ z : LogSpace n,
      complexCoverWeight (angularCoverPotential a) z *
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (W (complexTorusCoverProjection n z))
          (WithLp.toLp 2
            (fun j : Fin n => barPartialCoordinate ψ z j))
      ∂(volume : Measure (LogSpace n))) =
      ∫ z : LogSpace n, ∑ i ∈ s,
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate (ξ i) z j))
        ∂(volume : Measure (LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hrow z]
      rw [inner_sum]
      simp only [Finset.mul_sum]
    _ = ∑ i ∈ s,
      ∫ z : LogSpace n,
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate (ξ i) z j))
          ∂(volume : Measure (LogSpace n)) :=
      integral_finsetSum s hintW
    _ = ∑ i ∈ s,
      ∫ z : LogSpace n,
        complexCoverWeight (angularCoverPotential a) z *
          @inner ℂ ℂ _
            (r (complexTorusCoverProjection n z)) (ξ i z)
          ∂(volume : Measure (LogSpace n)) := by
      apply Finset.sum_congr rfl
      intro i _
      have hi :=
        angularWeakDolbeaultResolvent_weighted_cover_green_of_fundamentalInterior
          ha (coverCenteredFundamentalBase i) f
          (hξ i) (hξcompact i) (hξcell i)
      change
        (∫ z : LogSpace n,
          @inner ℂ (EuclideanSpace ℂ (Fin n)) _
            (W (complexTorusCoverProjection n z))
            (WithLp.toLp 2
              (fun j : Fin n => barPartialCoordinate (ξ i) z j))
          ∂(coverWeightedMeasure (angularCoverPotential a))) =
        (∫ z : LogSpace n,
          @inner ℂ ℂ _
            (r (complexTorusCoverProjection n z)) (ξ i z)
          ∂(coverWeightedMeasure (angularCoverPotential a))) at hi
      rw [integral_coverWeightedMeasure
            (continuous_angularCoverPotential ha),
          integral_coverWeightedMeasure
            (continuous_angularCoverPotential ha)] at hi
      exact hi
    _ = ∫ z : LogSpace n, ∑ i ∈ s,
      complexCoverWeight (angularCoverPotential a) z *
        @inner ℂ ℂ _
          (r (complexTorusCoverProjection n z)) (ξ i z)
        ∂(volume : Measure (LogSpace n)) :=
      (integral_finsetSum s hintr).symm
    _ = ∫ z : LogSpace n,
      complexCoverWeight (angularCoverPotential a) z *
        @inner ℂ ℂ _
          (r (complexTorusCoverProjection n z)) (ψ z)
        ∂(volume : Measure (LogSpace n)) := by
      apply integral_congr_ae
      filter_upwards [] with z
      rw [hψsum]
      simp only [RCLike.inner_apply, Finset.sum_mul, Finset.mul_sum]

end TorusHomogeneousResolventGreen

namespace TorusHomogeneousClosedResolventAdjoint

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert DolbeaultRegularity
open WeightedTorusDistributionBridge WeightedDolbeaultBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBrascampLieb TorusWeakDolbeaultMollification TorusFriedrichsMollifierEstimates
open TorusMollifiedBochner TorusWeightedAdjointMollification
open TorusWeightedDensityConvolutionDivergence TorusClosedMollifierAdjoint
open BergmanJetStrictMixedLocalCore
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder Topology ContDiff Convolution

private theorem contDiff_translatedDensityCancelledCoverKernel_three
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (k : ℕ) (x : LogSpace n) :
    ContDiff ℝ 3 (translatedDensityCancelledCoverKernel a k x) := by
  unfold translatedDensityCancelledCoverKernel
  exact ((complexShrinkingBump (n := n) k).contDiff_normed.comp
    (contDiff_const.sub contDiff_id)).div
      ha3.neg.exp
      (fun y => (coverWeight_pos (angularCoverPotential a) y).ne')

private theorem angularWeakDolbeaultResolvent_unweighted_translated_bump_green
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (f : angularWeightedScalarL2 a)
    (k : ℕ) (x : LogSpace n) :
    (∫ y : LogSpace n,
      ∑ j : Fin n,
        ((WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a))
          (complexTorusCoverProjection n y) :
          EuclideanSpace ℂ (Fin n)) j *
        (conj (barPartialCoordinate
          (fun z : LogSpace n =>
            ((complexShrinkingBump (n := n) k).normed
              (volume : Measure (LogSpace n)) (x - z) : ℂ)) y j) +
          ((complexShrinkingBump (n := n) k).normed
            (volume : Measure (LogSpace n)) (x - y) : ℂ) *
            holomorphicCoordinate
              (fun z : LogSpace n =>
                (angularCoverPotential a z : ℂ)) y j)
      ∂(volume : Measure (LogSpace n))) =
    (∫ y : LogSpace n,
      ((f - angularWeakScalarResolventCLM a f)
        (complexTorusCoverProjection n y)) *
        ((complexShrinkingBump (n := n) k).normed
          (volume : Measure (LogSpace n)) (x - y) : ℂ)
      ∂(volume : Measure (LogSpace n))) := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let χ : LogSpace n → ℝ :=
    translatedDensityCancelledCoverKernel a k x
  let ψ : LogSpace n → ℂ := fun y => (χ y : ℂ)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a)
  let r : angularWeightedScalarL2 a :=
    f - angularWeakScalarResolventCLM a f
  let d : LogSpace n → ℂ :=
    complexCoverWeight (angularCoverPotential a)
  have ha1 : ContDiff ℝ 1 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  have hχ : ContDiff ℝ 3 χ :=
    contDiff_translatedDensityCancelledCoverKernel_three ha3 k x
  have hψ : ContDiff ℝ 3 ψ :=
    Complex.ofRealCLM.contDiff.comp hχ
  have hψcompact : HasCompactSupport ψ := by
    have ht := hasCompactSupport_translatedDensityCancelledCoverKernel
      a k x
    simpa only [comp_def] using
      ht.comp_left (g := Complex.ofReal) (by simp only [Complex.ofReal_zero])
  have hg :=
    TorusHomogeneousResolventGreen.angularWeakDolbeaultResolvent_weighted_cover_green
      ha f hψ hψcompact
  rw [integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha),
      integral_coverWeightedMeasure
        (continuous_angularCoverPotential ha)] at hg
  change
    (∫ y : LogSpace n,
      d y *
        @inner ℂ (EuclideanSpace ℂ (Fin n)) _
          (W (complexTorusCoverProjection n y))
          (WithLp.toLp 2
            (fun j : Fin n => barPartialCoordinate ψ y j))
      ∂(volume : Measure (LogSpace n))) =
    (∫ y : LogSpace n,
      d y * @inner ℂ ℂ _
        (r (complexTorusCoverProjection n y)) (ψ y)
      ∂(volume : Measure (LogSpace n))) at hg
  have hconj :
      (∫ y : LogSpace n,
        ∑ j : Fin n,
          d y *
            ((W (complexTorusCoverProjection n y) :
              EuclideanSpace ℂ (Fin n)) j) *
            conj (barPartialCoordinate ψ y j)
        ∂(volume : Measure (LogSpace n))) =
      (∫ y : LogSpace n,
        d y * (r (complexTorusCoverProjection n y)) * ψ y
        ∂(volume : Measure (LogSpace n))) := by
    calc
      _ = conj
          (∫ y : LogSpace n,
            d y *
              @inner ℂ (EuclideanSpace ℂ (Fin n)) _
                (W (complexTorusCoverProjection n y))
                (WithLp.toLp 2
                  (fun j : Fin n => barPartialCoordinate ψ y j))
            ∂(volume : Measure (LogSpace n))) := by
        rw [← integral_conj]
        apply integral_congr_ae
        filter_upwards [] with y
        simp only [complexCoverWeight, mul_assoc, PiLp.inner_apply, RCLike.inner_apply, mul_comm,
          Finset.mul_sum, map_sum, map_mul, Complex.conj_ofReal, RingHomCompTriple.comp_apply,
          RingHom.id_apply, d]
      _ = conj
          (∫ y : LogSpace n,
            d y * @inner ℂ ℂ _
              (r (complexTorusCoverProjection n y)) (ψ y)
            ∂(volume : Measure (LogSpace n))) :=
        congrArg (starRingEnd ℂ) hg
      _ = _ := by
        rw [← integral_conj]
        apply integral_congr_ae
        filter_upwards [] with y
        simp only [d, ψ, complexCoverWeight, RCLike.inner_apply,
          map_mul, Complex.conj_conj, Complex.conj_ofReal]
        ring
  change
    (∫ y : LogSpace n,
      ∑ j : Fin n,
        ((W (complexTorusCoverProjection n y) :
          EuclideanSpace ℂ (Fin n)) j) *
          (conj (barPartialCoordinate
            (fun z : LogSpace n => (κ (x - z) : ℂ)) y j) +
            (κ (x - y) : ℂ) *
              holomorphicCoordinate
                (fun z : LogSpace n =>
                  (angularCoverPotential a z : ℂ)) y j)
      ∂(volume : Measure (LogSpace n))) =
    (∫ y : LogSpace n,
      (r (complexTorusCoverProjection n y)) * (κ (x - y) : ℂ)
      ∂(volume : Measure (LogSpace n)))
  calc
    _ = (∫ y : LogSpace n,
      ∑ j : Fin n,
        d y *
          ((W (complexTorusCoverProjection n y) :
            EuclideanSpace ℂ (Fin n)) j) *
          conj (barPartialCoordinate ψ y j)
      ∂(volume : Measure (LogSpace n))) := by
      apply integral_congr_ae
      filter_upwards [] with y
      apply Finset.sum_congr rfl
      intro j _
      have he :=
        complexCoverWeight_mul_conj_barPartial_translatedDensityCancelledCoverKernel
          ha1 k x y j
      change
        ((W (complexTorusCoverProjection n y) :
          EuclideanSpace ℂ (Fin n)) j) *
          (conj (barPartialCoordinate
            (fun z : LogSpace n => (κ (x - z) : ℂ)) y j) +
            (κ (x - y) : ℂ) *
              holomorphicCoordinate
                (fun z : LogSpace n =>
                  (angularCoverPotential a z : ℂ)) y j) =
        d y *
          ((W (complexTorusCoverProjection n y) :
            EuclideanSpace ℂ (Fin n)) j) *
          conj (barPartialCoordinate ψ y j)
      change
        ((W (complexTorusCoverProjection n y) :
          EuclideanSpace ℂ (Fin n)) j) *
          (conj (barPartialCoordinate
            (fun z : LogSpace n => (κ (x - z) : ℂ)) y j) +
            (κ (x - y) : ℂ) *
              holomorphicCoordinate
                (fun z : LogSpace n =>
                  (angularCoverPotential a z : ℂ)) y j) =
        complexCoverWeight (angularCoverPotential a) y *
          ((W (complexTorusCoverProjection n y) :
            EuclideanSpace ℂ (Fin n)) j) *
          conj (barPartialCoordinate
            (fun z : LogSpace n =>
              (translatedDensityCancelledCoverKernel a k x z : ℂ)) y j)
      rw [← he]
      ring
    _ = (∫ y : LogSpace n,
      d y * (r (complexTorusCoverProjection n y)) * ψ y
      ∂(volume : Measure (LogSpace n))) := hconj
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      have he := complexCoverWeight_mul_translatedDensityCancelledCoverKernel
        a k x y
      change
        complexCoverWeight (angularCoverPotential a) y *
          (r (complexTorusCoverProjection n y)) *
            (translatedDensityCancelledCoverKernel a k x y : ℂ) =
        (r (complexTorusCoverProjection n y)) * (κ (x - y) : ℂ)
      rw [mul_right_comm, he]
      simp only [mul_comm, κ]

private theorem angularWeakDolbeaultResolvent_closed_mollified_divergence
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (f : angularWeightedScalarL2 a)
    (k : ℕ) (x : LogSpace n) :
    (∑ j : Fin n,
      (holomorphicCoordinate
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun q : LogTorus n =>
              ((WithLp.snd
                (angularWeakDolbeaultResolvent a f :
                  angularDolbeaultGraphAmbient a)) q :
                EuclideanSpace ℂ (Fin n)) j)) k) x j -
      normalizedCoverMollification
        (fun y : LogSpace n =>
          holomorphicCoordinate
            (fun z : LogSpace n =>
              (angularCoverPotential a z : ℂ)) y j *
            complexTorusCoverLift
              (fun q : LogTorus n =>
                ((WithLp.snd
                  (angularWeakDolbeaultResolvent a f :
                    angularDolbeaultGraphAmbient a)) q :
                  EuclideanSpace ℂ (Fin n)) j) y) k x)) =
    -normalizedCoverMollification
      (complexTorusCoverLift
        (fun q : LogTorus n =>
          (f - angularWeakScalarResolventCLM a f) q)) k x := by
  let κ : LogSpace n → ℝ :=
    (complexShrinkingBump (n := n) k).normed
      (volume : Measure (LogSpace n))
  let η : LogSpace n → ℂ := fun y => (κ (x - y) : ℂ)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a f :
        angularDolbeaultGraphAmbient a)
  let r : angularWeightedScalarL2 a :=
    f - angularWeakScalarResolventCLM a f
  let w : Fin n → LogSpace n → ℂ :=
    fun j y =>
      ((W (complexTorusCoverProjection n y) :
        EuclideanSpace ℂ (Fin n)) j)
  let b : Fin n → LogSpace n → ℂ :=
    fun j y => holomorphicCoordinate
      (fun z : LogSpace n =>
        (angularCoverPotential a z : ℂ)) y j
  have ha1 : ContDiff ℝ 1 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  have hκ : ContDiff ℝ 1 κ :=
    (complexShrinkingBump (n := n) k).contDiff_normed
  have hη : ContDiff ℝ 1 η :=
    Complex.ofRealCLM.contDiff.comp
      (hκ.comp (contDiff_const.sub contDiff_id))
  have hκcompact :=
    (complexShrinkingBump (n := n) k).hasCompactSupport_normed
      (μ := (volume : Measure (LogSpace n)))
  have hηcompact : HasCompactSupport η := by
    simpa only [comp_def] using
      (translatedRealKernel_hasCompactSupport hκcompact x).comp_left
        (g := Complex.ofReal) (by simp only [Complex.ofReal_zero])
  have hw (j : Fin n) :
      LocallyIntegrable (w j) (volume : Measure (LogSpace n)) := by
    exact angularWeightedFormCoordinateCoverLift_locallyIntegrable
      ha W j
  have hb (j : Fin n) : Continuous (b j) := by
    exact continuous_holomorphicCoordinate
      (Complex.ofRealCLM.contDiff.comp ha1) j
  have hbw (j : Fin n) :
      LocallyIntegrable (fun y : LogSpace n => b j y * w j y)
        (volume : Measure (LogSpace n)) :=
    locallyIntegrable_cover_complex_mul_continuous (hw j) (hb j)
  have hconjcont (j : Fin n) :
      Continuous (fun y : LogSpace n =>
        conj (barPartialCoordinate η y j)) :=
    Complex.continuous_conj.comp (continuous_barPartialCoordinate hη j)
  have hconjcompact (j : Fin n) :
      HasCompactSupport (fun y : LogSpace n =>
        conj (barPartialCoordinate η y j)) := by
    simpa only [comp_def] using
      (compactSupport_barPartialCoordinate hηcompact j).comp_left
        (g := (starRingEnd ℂ)) (map_zero _)
  have hi (j : Fin n) :
      Integrable
        (fun y : LogSpace n =>
          w j y * conj (barPartialCoordinate η y j))
        (volume : Measure (LogSpace n)) := by
    simpa only [smul_eq_mul] using
      (hw j).integrable_smul_right_of_hasCompactSupport
        (hconjcont j) (hconjcompact j)
  have hbint (j : Fin n) :
      Integrable
        (fun y : LogSpace n =>
          (b j y * w j y) * η y)
        (volume : Measure (LogSpace n)) := by
    simpa only [smul_eq_mul] using
      (hbw j).integrable_smul_right_of_hasCompactSupport
        hη.continuous hηcompact
  have hsplit (j : Fin n) :
      (∫ y : LogSpace n,
        w j y *
          (conj (barPartialCoordinate η y j) + η y * b j y)
        ∂(volume : Measure (LogSpace n))) =
      (∫ y : LogSpace n,
        w j y * conj (barPartialCoordinate η y j)
        ∂(volume : Measure (LogSpace n))) +
      (∫ y : LogSpace n,
        (b j y * w j y) * η y
        ∂(volume : Measure (LogSpace n))) := by
    rw [← integral_add (hi j) (hbint j)]
    apply integral_congr_ae
    filter_upwards [] with y
    ring
  have hwhole (j : Fin n) :
      Integrable
        (fun y : LogSpace n =>
          w j y *
            (conj (barPartialCoordinate η y j) + η y * b j y))
        (volume : Measure (LogSpace n)) := by
    have hs := (hi j).add (hbint j)
    apply hs.congr
    filter_upwards [] with y
    change
      w j y * conj (barPartialCoordinate η y j) +
          (b j y * w j y) * η y =
        w j y *
          (conj (barPartialCoordinate η y j) + η y * b j y)
    ring
  have hgreen :=
    angularWeakDolbeaultResolvent_unweighted_translated_bump_green
      ha ha3 f k x
  change
    (∫ y : LogSpace n,
      ∑ j : Fin n,
        w j y *
          (conj (barPartialCoordinate η y j) + η y * b j y)
      ∂(volume : Measure (LogSpace n))) =
    (∫ y : LogSpace n,
      r (complexTorusCoverProjection n y) * η y
      ∂(volume : Measure (LogSpace n))) at hgreen
  rw [integral_finsetSum Finset.univ
    (fun j _ => hwhole j)] at hgreen
  change
    (∑ j : Fin n,
      (holomorphicCoordinate
        (normalizedCoverMollification (w j) k) x j -
      normalizedCoverMollification
        (fun y : LogSpace n => b j y * w j y) k x)) =
      -normalizedCoverMollification
        (fun y : LogSpace n =>
          r (complexTorusCoverProjection n y)) k x
  calc
    _ = ∑ j : Fin n,
      (-(∫ y : LogSpace n,
          w j y * conj (barPartialCoordinate η y j)
          ∂(volume : Measure (LogSpace n))) -
       (∫ y : LogSpace n,
          (b j y * w j y) * η y
          ∂(volume : Measure (LogSpace n)))) := by
      apply Finset.sum_congr rfl
      intro j _
      rw [holomorphicCoordinate_normalizedCoverMollification_eq_kernel
        (hw j) k x j,
        normalizedCoverMollification_eq_kernel_integral
          (fun y : LogSpace n => b j y * w j y) k x]
    _ = -(∑ j : Fin n,
      ∫ y : LogSpace n,
        w j y *
          (conj (barPartialCoordinate η y j) + η y * b j y)
        ∂(volume : Measure (LogSpace n))) := by
      simp_rw [hsplit]
      simp only [Finset.sum_sub_distrib, Finset.sum_neg_distrib,
        Finset.sum_add_distrib]
      ring
    _ = -(∫ y : LogSpace n,
      r (complexTorusCoverProjection n y) * η y
      ∂(volume : Measure (LogSpace n))) :=
      congrArg Neg.neg hgreen
    _ = _ := by
      rw [normalizedCoverMollification_eq_kernel_integral]

private theorem coverFormAdjoint_mollifiedWeakResolvent_eq
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (f : angularWeightedScalarL2 a)
    (k : ℕ) (x : LogSpace n) :
    coverFormAdjoint (angularCoverPotential a)
      (angularGraphMollifiedPhysicalField
        (WithLp.snd
          (angularWeakDolbeaultResolvent a f :
            angularDolbeaultGraphAmbient a)) k) x =
      -normalizedCoverMollification
        (complexTorusCoverLift
          (fun q : LogTorus n =>
            (f - angularWeakScalarResolventCLM a f) q)) k x +
        angularMollifiedPhysicalAdjointDriftCommutator
          (WithLp.snd
            (angularWeakDolbeaultResolvent a f :
              angularDolbeaultGraphAmbient a)) k x := by
  rw [coverFormAdjoint_angularGraphMollifiedPhysicalField_eq,
    angularWeakDolbeaultResolvent_closed_mollified_divergence
      ha ha3 f k x]

end TorusHomogeneousClosedResolventAdjoint

namespace TorusHomogeneousSmoothRootBochner

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert EqualitySaturatingKillingPaths
open MatrixTorusBochnerCoreDensity MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence MatrixTorusBochnerIdentity WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph
open RadialPhysicalInverseSquareRootEnergy TorusRootCurvatureCoercivity TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusMollifiedBochner TorusWeakRadialExteriorEnergy
open TorusClosedMollifiedRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff

private def angularSmoothCompactHessianRootVector
    {n : ℕ} (a : LogTorus n → ℝ)
    (V : LogSpace n → LogSpace n)
    (m : ℕ) (q : LogTorus n) : EuclideanSpace ℂ (Fin n) :=
  Matrix.toEuclideanLin
    (angularMatrixSquareRoot (angularTorusComplexHessianMatrix a) q)
    (angularTorusConjugatePhysicalFormVector
      (cutoffPhysicalField m V) q)

private theorem angularCurvatureDensity_re_eq_squareRoot_norm_sq
    {n : ℕ} {a : LogTorus n → ℝ}
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → Fin n → ℂ) (q : LogTorus n) :
    (angularTorusFormCurvatureDensity a V q).re =
      ‖Matrix.toEuclideanLin
        (angularMatrixSquareRoot (angularTorusComplexHessianMatrix a) q)
        (angularTorusConjugatePhysicalFormVector V q)‖ ^ 2 := by
  rw [angularTorusFormCurvatureDensity_eq_conjugatePhysical_inner]
  rw [complexHermitianMatrixAction_norm_sq
    (angularMatrixSquareRoot_posDef hH q).isHermitian]
  rw [show
    angularMatrixSquareRoot (angularTorusComplexHessianMatrix a) q *
      angularMatrixSquareRoot (angularTorusComplexHessianMatrix a) q =
        angularTorusComplexHessianMatrix a q from
      CFC.sqrt_mul_sqrt_self _ (hH q).posSemidef.nonneg]
  rfl

private theorem continuous_angularSmoothCompactHessianRootVector
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → LogSpace n)
    (hV : ContDiff ℝ 2 V)
    (hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d))
    (m : ℕ) :
    Continuous (angularSmoothCompactHessianRootVector a V m) := by
  have hroot := continuous_angularMatrixSquareRoot
    (continuous_angularTorusComplexHessianMatrix ha2) hH
  have hform :=
    continuous_torusFormRepresentative_of_smooth_periodic
      (contDiff_cutoffPhysicalField m hV)
      (cutoffPhysicalField_periodic m hVp)
  change Continuous
    (fun q : LogTorus n =>
      Matrix.toEuclideanLin
        (angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q)
        (angularEuclideanConjugation
          (torusFormRepresentative (cutoffPhysicalField m V) q)))
  change Continuous
    ((fun Av : Matrix (Fin n) (Fin n) ℂ ×
        EuclideanSpace ℂ (Fin n) =>
      Matrix.toEuclideanLin Av.1
        (angularEuclideanConjugation Av.2)) ∘
      (fun q : LogTorus n =>
        (angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q,
         torusFormRepresentative (cutoffPhysicalField m V) q)))
  exact (continuous_complexEuclideanConjugatedMatrixAction
    (n := n)).comp (hroot.prodMk hform)

private theorem hasCompactSupport_angularSmoothCompactHessianRootVector
    {n : ℕ} (a : LogTorus n → ℝ)
    (V : LogSpace n → LogSpace n) (m : ℕ) :
    HasCompactSupport (angularSmoothCompactHessianRootVector a V m) := by
  apply (sourceRadialCutoff_hasCompactSupport m).mono
  intro q hq
  change angularSmoothCompactHessianRootVector a V m q ≠ 0 at hq
  change sourceRadialCutoff m q ≠ 0
  intro hzero
  apply hq
  change
    Matrix.toEuclideanLin
      (angularMatrixSquareRoot
        (angularTorusComplexHessianMatrix a) q)
      (angularEuclideanConjugation
        (torusFormRepresentative
          (cutoffPhysicalField m V) q)) = 0
  rw [torusFormRepresentative_cutoffPhysicalField m V q, hzero]
  ext i
  simp only [angularEuclideanConjugation, Complex.ofReal_zero, zero_smul, PiLp.zero_apply,
    toLpLin_toLp, toLin'_apply, mulVec, dotProduct, Pi.star_apply, star_zero, mul_zero,
    Finset.sum_const_zero]

private theorem angularSmoothCompactHessianRootVector_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → LogSpace n)
    (hV : ContDiff ℝ 2 V)
    (hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d))
    (m : ℕ) :
    MemLp (angularSmoothCompactHessianRootVector a V m)
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  exact
    (continuous_angularSmoothCompactHessianRootVector
      ha2 hH V hV hVp m).memLp_of_hasCompactSupport
      (hasCompactSupport_angularSmoothCompactHessianRootVector a V m)

private theorem angularSmoothCompactHessianRootVector_L2_norm_sq
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → LogSpace n)
    (hV : ContDiff ℝ 2 V)
    (hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d))
    (m : ℕ) :
    ‖(angularSmoothCompactHessianRootVector_memLp
      ha ha2 hH V hV hVp m).toLp
        (angularSmoothCompactHessianRootVector a V m)‖ ^ 2 =
    (∫ q : LogTorus n,
      angularTorusFormCurvatureDensity a
        (cutoffPhysicalField m V) q
      ∂(angularWeightedTorusMeasure a)).re := by
  have hcurv : Integrable
      (angularTorusFormCurvatureDensity a
        (cutoffPhysicalField m V))
      (angularWeightedTorusMeasure a) :=
    integrable_angularTorusFormCurvatureDensity
      (cutoffPhysicalField m V) ha ha2
      (fun i => contDiff_pi.mp
        (contDiff_cutoffPhysicalField m hV) i)
      (fun i d z => congrFun
        (cutoffPhysicalField_periodic m hVp d z) i)
      (cutoffPhysicalField_coordinate_hasCompactSupport m V)
  rw [complexLp_norm_sq_eq_integral]
  change
    (∫ q : LogTorus n,
      ‖(angularSmoothCompactHessianRootVector_memLp
        ha ha2 hH V hV hVp m).toLp
          (angularSmoothCompactHessianRootVector a V m) q‖ ^ 2
      ∂(angularWeightedTorusMeasure a)) =
    (∫ q : LogTorus n,
      angularTorusFormCurvatureDensity a
        (cutoffPhysicalField m V) q
      ∂(angularWeightedTorusMeasure a)).re
  calc
    (∫ q : LogTorus n,
      ‖(angularSmoothCompactHessianRootVector_memLp
        ha ha2 hH V hV hVp m).toLp
          (angularSmoothCompactHessianRootVector a V m) q‖ ^ 2
      ∂(angularWeightedTorusMeasure a)) =
      ∫ q : LogTorus n,
        (angularTorusFormCurvatureDensity a
          (cutoffPhysicalField m V) q).re
        ∂(angularWeightedTorusMeasure a) := by
          apply integral_congr_ae
          filter_upwards
            [(angularSmoothCompactHessianRootVector_memLp
              ha ha2 hH V hV hVp m).coeFn_toLp]
            with q hq
          rw [hq]
          exact
            (angularCurvatureDensity_re_eq_squareRoot_norm_sq
              hH (cutoffPhysicalField m V) q).symm
    _ = (∫ q : LogTorus n,
      angularTorusFormCurvatureDensity a
        (cutoffPhysicalField m V) q
      ∂(angularWeightedTorusMeasure a)).re := by
        simpa only [RCLike.re_to_complex] using (integral_re hcurv)

private theorem angularSmoothCompactHessianRootVector_norm_sq_le_adjoint_add_exterior
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (V : LogSpace n → LogSpace n)
    (hV : ContDiff ℝ 2 V)
    (hVp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d))
    (m : ℕ) :
    ‖(angularSmoothCompactHessianRootVector_memLp
      ha ha2 hH V hV hVp m).toLp
        (angularSmoothCompactHessianRootVector a V m)‖ ^ 2 ≤
    (∫ q : LogTorus n,
      angularTorusFormAdjoint a (cutoffPhysicalField m V) q *
      conj (angularTorusFormAdjoint a
        (cutoffPhysicalField m V) q)
      ∂(angularWeightedTorusMeasure a)).re +
    (∫ q : LogTorus n,
      sourceTorusFormExteriorDerivativeDensity
        (cutoffPhysicalField m V) q
      ∂(angularWeightedTorusMeasure a)).re := by
  rw [angularSmoothCompactHessianRootVector_L2_norm_sq
    ha ha2 hH V hV hVp m]
  exact angularTorus_compact_form_curvature_le_adjoint_add_exterior
    (cutoffPhysicalField m V) ha ha2
    (fun i => contDiff_pi.mp (contDiff_cutoffPhysicalField m hV) i)
    (fun i d z => congrFun
      (cutoffPhysicalField_periodic m hVp d z) i)
    (cutoffPhysicalField_coordinate_hasCompactSupport m V)

private def angularClosedMollifiedRootVectorL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) : angularWeightedFormL2 a :=
  (angularSmoothCompactHessianRootVector_memLp
    ha ha2 hH (angularGraphMollifiedPhysicalField W ℓ)
    (WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2)
    (angularGraphMollifiedPhysicalField_periodic W ℓ)
    m).toLp
      (angularSmoothCompactHessianRootVector a
        (angularGraphMollifiedPhysicalField W ℓ) m)

private theorem angularClosedGraphMollifiedRootBochner
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (f : angularWeightedScalarL2 a)
    (W : angularWeightedFormL2 a)
    (hgraph : WithLp.toLp 2 (f, W) ∈ angularDolbeaultGraph a)
    (ℓ m : ℕ) :
    ‖angularClosedMollifiedRootVectorL2
      ha ha2 hH W ℓ m‖ ^ 2 ≤
    (∫ q : LogTorus n,
      angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)) q *
      conj (angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)) q)
      ∂(angularWeightedTorusMeasure a)).re +
    (∫ q : LogTorus n,
      complexEuclideanAntisymmetricEnergy
        (sourceCutoffDerivativeCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q)
      ∂(angularWeightedTorusMeasure a)).re := by
  have hV : ContDiff ℝ 2
      (angularGraphMollifiedPhysicalField W ℓ) :=
    WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2
  have hp := angularGraphMollifiedPhysicalField_periodic W ℓ
  have hclosed :=
    WeightedTorusScalarCompactGreen.sourceTorusClosedForm_angularGraphMollifiedPhysicalField
      ha f W hgraph ℓ
  have hbochner :=
    angularSmoothCompactHessianRootVector_norm_sq_le_adjoint_add_exterior
      ha ha2 hH
      (angularGraphMollifiedPhysicalField W ℓ) hV hp m
  change
    ‖angularClosedMollifiedRootVectorL2
      ha ha2 hH W ℓ m‖ ^ 2 ≤ _ at hbochner
  simpa only
    [sourceTorusFormExteriorDerivativeDensity_cutoff_eq_antisymmetric
      hV hclosed m] using hbochner

private theorem angularWeakResolventClosedMollifiedRootBochner
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (g : angularWeightedScalarL2 a)
    (ℓ m : ℕ) :
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    ‖angularClosedMollifiedRootVectorL2
      ha ha2 hH W ℓ m‖ ^ 2 ≤
    (∫ q : LogTorus n,
      angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)) q *
      conj (angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)) q)
      ∂(angularWeightedTorusMeasure a)).re +
    (∫ q : LogTorus n,
      complexEuclideanAntisymmetricEnergy
        (sourceCutoffDerivativeCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q)
      ∂(angularWeightedTorusMeasure a)).re := by
  dsimp only
  exact angularClosedGraphMollifiedRootBochner
    ha ha2 hH (angularWeakScalarResolventCLM a g)
    (WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a))
    (angularWeakDolbeaultResolvent_components_mem_graph a g)
    ℓ m

end TorusHomogeneousSmoothRootBochner

namespace TorusHomogeneousRadialAdjoint

open Set Function Filter MeasureTheory Matrix
open EqualitySaturatingKillingPaths TorusCharacters WeightedTorusHilbert WeightedBrascampLieb
open WeightedResolventConstantCore MatrixTorusBochnerCoreApproximation
open MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault TorusMollifiedBochner
open TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator TorusWeakRadialExteriorMollification
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  Matrix.Norms.L2Operator Topology ContDiff

private theorem angularClosedMollifiedRadialAdjointCommutator_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) :
    MemLp
      (angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ))
      2 (angularWeightedTorusMeasure a) := by
  let : IsLocallyFiniteMeasure (angularWeightedTorusMeasure a) :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts (angularWeightedTorusMeasure a) :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hc : Continuous
      (angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ)) :=
    continuous_angularSourceCutoffAdjointCommutator m
      (WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
        ha W ℓ 2)
      (angularGraphMollifiedPhysicalField_periodic W ℓ)
  have hs : HasCompactSupport
      (angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ)) := by
    apply (sourceCutoffBarGradient_hasCompactSupport m).mono
    intro q hq
    change sourceCutoffBarGradient m q ≠ 0
    intro hz
    apply hq
    simp only [angularSourceCutoffAdjointCommutator, hz, inner_zero_left]
  exact hc.memLp_of_hasCompactSupport hs

private def angularClosedMollifiedRadialAdjointCommutatorL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) : angularWeightedScalarL2 a :=
  (angularClosedMollifiedRadialAdjointCommutator_memLp
    ha W ℓ m).toLp
      (angularSourceCutoffAdjointCommutator m
        (angularGraphMollifiedPhysicalField W ℓ))

private theorem angularClosedMollifiedRadialAdjointCommutatorL2_sub_norm_sq_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    (ℓ m : ℕ)
    {B : ℝ}
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B) :
    ‖angularClosedMollifiedRadialAdjointCommutatorL2
        ha W ℓ m -
      (angularWeakSourceCutoffAdjointCommutator_memLp
        W hB m).toLp
        (angularWeakSourceCutoffAdjointCommutator W m)‖ ^ 2 ≤
      (((m : ℝ) + 1)⁻¹ * B) ^ 2 *
        (∫ q in tsupport (sourceCutoffBarGradient (n := n) m),
          ‖torusFormRepresentative
              (angularGraphMollifiedPhysicalField W ℓ) q - W q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) := by
  let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
  let S : Set (LogTorus n) :=
    tsupport (sourceCutoffBarGradient (n := n) m)
  let V : LogSpace n → LogSpace n :=
    angularGraphMollifiedPhysicalField W ℓ
  let A : ℝ := ((m : ℝ) + 1)⁻¹ * B
  let M : angularWeightedScalarL2 a :=
    angularClosedMollifiedRadialAdjointCommutatorL2 ha W ℓ m
  let R : angularWeightedScalarL2 a :=
    (angularWeakSourceCutoffAdjointCommutator_memLp
      W hB m).toLp
        (angularWeakSourceCutoffAdjointCommutator W m)
  have hB₀ : 0 ≤ B :=
    (norm_nonneg
      (euclideanGradient (fun y : Space n => unitBump y)
        (0 : Space n))).trans
      (hB (0 : Space n))
  have hA : 0 ≤ A := mul_nonneg (by positivity) hB₀
  let : IsLocallyFiniteMeasure μ :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts μ :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hS : IsCompact S :=
    (sourceCutoffBarGradient_hasCompactSupport m).isCompact
  have hV : ContDiff ℝ 2 V :=
    WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2
  have hp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d) :=
    angularGraphMollifiedPhysicalField_periodic W ℓ
  have hVc : Continuous (torusFormRepresentative V) :=
    continuous_torusFormRepresentative_of_smooth_periodic hV hp
  have hVm : MemLp (torusFormRepresentative V) 2
      (μ.restrict S) := by
    apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (hVc.aestronglyMeasurable.mono_measure
        Measure.restrict_le_self)).mpr
    exact (hVc.norm.pow 2).continuousOn.integrableOn_compact hS
  have hWm : MemLp (fun q : LogTorus n => W q) 2
      (μ.restrict S) :=
    (MeasureTheory.Lp.memLp W).mono_measure
      Measure.restrict_le_self
  have hdiff : IntegrableOn
      (fun q : LogTorus n =>
        ‖torusFormRepresentative V q - W q‖ ^ 2) S μ :=
    (hVm.sub hWm).norm.integrable_sq
  have hMmem := angularClosedMollifiedRadialAdjointCommutator_memLp
    ha W ℓ m
  have hRmem := angularWeakSourceCutoffAdjointCommutator_memLp
    W hB m
  have hM :
      (fun q : LogTorus n => M q) =ᵐ[μ]
        angularSourceCutoffAdjointCommutator m V := by
    simpa [M, μ, V,
      angularClosedMollifiedRadialAdjointCommutatorL2]
      using hMmem.coeFn_toLp
  have hR :
      (fun q : LogTorus n => R q) =ᵐ[μ]
        angularWeakSourceCutoffAdjointCommutator W m := by
    simpa only using hRmem.coeFn_toLp
  have hnorm :
      ‖M - R‖ ^ 2 =
        ∫ q : LogTorus n,
          ‖angularSourceCutoffAdjointCommutator m V q -
            angularWeakSourceCutoffAdjointCommutator W m q‖ ^ 2
          ∂μ := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Lp.coeFn_sub M R, hM, hR]
      with q hsub hm hr
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hm, hr]
  have hleft : Integrable
      (fun q : LogTorus n =>
        ‖angularSourceCutoffAdjointCommutator m V q -
          angularWeakSourceCutoffAdjointCommutator W m q‖ ^ 2)
      μ :=
    (hMmem.sub hRmem).norm.integrable_sq
  have hright : Integrable
      (S.indicator
        (fun q : LogTorus n =>
          A ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2)) μ :=
    (MeasureTheory.integrable_indicator_iff hS.measurableSet).mpr
      (hdiff.const_mul (A ^ 2))
  have hpoint (q : LogTorus n) :
      ‖angularSourceCutoffAdjointCommutator m V q -
        angularWeakSourceCutoffAdjointCommutator W m q‖ ^ 2 ≤
      S.indicator
        (fun r : LogTorus n =>
          A ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q := by
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      have hb :
          ‖angularSourceCutoffAdjointCommutator m V q -
            angularWeakSourceCutoffAdjointCommutator W m q‖ ≤
            A * ‖torusFormRepresentative V q - W q‖ := by
        change
          ‖angularSourceCutoffAdjointCommutator m
            (angularGraphMollifiedPhysicalField W ℓ) q -
            angularWeakSourceCutoffAdjointCommutator W m q‖ ≤
            A * ‖torusFormRepresentative V q - W q‖
        rw [TorusStrongWeightedCutoffAdjoint.angularClosedMollifiedRadialAdjointCommutator_sub_weak]
        exact (norm_inner_le_norm _ _).trans
          (mul_le_mul_of_nonneg_right
            (sourceCutoffBarGradient_norm_le hB m q)
            (norm_nonneg _))
      calc
        _ ≤ (A * ‖torusFormRepresentative V q - W q‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg hA (norm_nonneg _))).mpr hb
        _ = _ := by rw [mul_pow]
    · rw [Set.indicator_of_notMem hq]
      have hz : sourceCutoffBarGradient m q = 0 :=
        image_eq_zero_of_notMem_tsupport hq
      change
        ‖angularSourceCutoffAdjointCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q -
          angularWeakSourceCutoffAdjointCommutator W m q‖ ^ 2 ≤ 0
      rw [TorusStrongWeightedCutoffAdjoint.angularClosedMollifiedRadialAdjointCommutator_sub_weak,
        hz]
      simp only [CStarModule.inner_sub_right, inner_zero_left, sub_self, norm_zero, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, Std.le_refl]
  change ‖M - R‖ ^ 2 ≤
    A ^ 2 *
      (∫ q in S,
        ‖torusFormRepresentative V q - W q‖ ^ 2 ∂μ)
  rw [hnorm]
  calc
    _ ≤ ∫ q : LogTorus n,
      S.indicator
        (fun r : LogTorus n =>
          A ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q
      ∂μ := integral_mono hleft hright hpoint
    _ = ∫ q in S,
      A ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2
      ∂μ := MeasureTheory.integral_indicator hS.measurableSet
    _ = _ := integral_const_mul (A ^ 2) _

private theorem angularClosedMollifiedRadialAdjointCommutatorL2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a) (W : angularWeightedFormL2 a)
    {B : ℝ}
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B)
    (m : ℕ) :
    Tendsto
      (fun ℓ : ℕ =>
        angularClosedMollifiedRadialAdjointCommutatorL2
          ha W ℓ m)
      atTop
      (nhds
        ((angularWeakSourceCutoffAdjointCommutator_memLp
          W hB m).toLp
            (angularWeakSourceCutoffAdjointCommutator W m))) := by
  have hS := (sourceCutoffBarGradient_hasCompactSupport
    (n := n) m).isCompact
  have hlocal :=
    TorusHomogeneousCutoffAdjoint.graphField_mollification_L2_tendsto_zero
      ha W hS
  have hsq :
      Tendsto
        (fun ℓ : ℕ =>
          ‖angularClosedMollifiedRadialAdjointCommutatorL2
              ha W ℓ m -
            (angularWeakSourceCutoffAdjointCommutator_memLp
              W hB m).toLp
                (angularWeakSourceCutoffAdjointCommutator W m)‖ ^ 2)
        atTop (nhds 0) := by
    apply squeeze_zero (fun ℓ => sq_nonneg _)
      (fun ℓ =>
        angularClosedMollifiedRadialAdjointCommutatorL2_sub_norm_sq_le
          ha W ℓ m hB)
    simpa only [mul_zero] using hlocal.const_mul
      ((((m : ℝ) + 1)⁻¹ * B) ^ 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_nonneg, Real.sqrt_sq, Real.sqrt_zero] using hsq.sqrt

end TorusHomogeneousRadialAdjoint

namespace TorusHomogeneousWeakResolventRootCoercivity

open Set Function Filter MeasureTheory Matrix
open TorusCharacters WeightedTorusHilbert WeightedBrascampLieb WeightedResolventConstantCore
open JetEnvelopeRightDerivative EqualitySaturatingKillingPaths ComplexKillingSaturationBridge
open WeightedTorusDistributionBridge MatrixTorusBochnerCoreDensity
open MatrixTorusBochnerCoreApproximation MatrixTorusBochnerCoreConvergence WeightedTorusDolbeault
open WeightedTorusBochner WeightedTorusBrascampLieb MatrixTorusDolbeaultGraph TorusNoncompactBochner
open RadialPhysicalResolventRootCutoffPairing TorusWeakDolbeaultMollification TorusMollifiedBochner
open TorusWeightedAdjointMollification TorusFriedrichsCutoff TorusWeakRadialCutoffCommutator
open TorusWeakRadialExteriorEnergy TorusWeakRadialBochnerUpperBound
open TorusWeakRadialExteriorMollification TorusClosedMollifiedRootBochner
open TorusStrongWeightedCutoffAdjoint TorusWeakResolventRootBochner
open RadialPhysicalResolventRootCutoffUniformExtraction TorusHomogeneousSmoothRootBochner
open scoped BigOperators ENNReal ComplexConjugate InnerProductSpace
  MatrixOrder ComplexOrder Matrix.Norms.L2Operator Topology ContDiff

private theorem exists_angularHessianSquareRoot_fiber_bound_on_compact
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    {s : Set (LogTorus n)} (hs : IsCompact s) :
    ∃ B : ℝ, 0 < B ∧
      ∀ q ∈ s, ∀ v : EuclideanSpace ℂ (Fin n),
        ‖Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q) v‖ ≤ B * ‖v‖ := by
  have hbdd : BddAbove
      ((fun q : LogTorus n =>
        ‖angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q‖) '' s) :=
    hs.bddAbove_image
      (continuous_angularMatrixSquareRoot
        (continuous_angularTorusComplexHessianMatrix ha2)
        hH).norm.continuousOn
  obtain ⟨C, hC⟩ := hbdd
  refine ⟨max 1 C,
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro q hq v
  have hroot :
      ‖angularMatrixSquareRoot
        (angularTorusComplexHessianMatrix a) q‖ ≤ max 1 C :=
    (hC ⟨q, hq, rfl⟩).trans (le_max_right _ _)
  change
    ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
      (angularMatrixSquareRoot
        (angularTorusComplexHessianMatrix a) q) v‖ ≤
      max 1 C * ‖v‖
  calc
    _ ≤ ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)‖ * ‖v‖ :=
      (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
        (angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q)).le_opNorm v
    _ = ‖angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q‖ * ‖v‖ := by
      rw [Matrix.l2_opNorm_toEuclideanCLM]
    _ ≤ _ := mul_le_mul_of_nonneg_right hroot (norm_nonneg _)

private def angularPhysicalResolventRootCutoffField
    {n : ℕ} (a : LogTorus n → ℝ)
    (W : angularWeightedFormL2 a)
    (m : ℕ) (q : LogTorus n) : EuclideanSpace ℂ (Fin n) :=
  (sourceRadialCutoff m q : ℂ) •
    Matrix.toEuclideanLin
      (angularMatrixSquareRoot
        (angularTorusComplexHessianMatrix a) q)
      (angularEuclideanConjugation (W q))

private theorem angularPhysicalResolventRootCutoffField_aestronglyMeasurable
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a) (m : ℕ) :
    AEStronglyMeasurable
      (angularPhysicalResolventRootCutoffField a W m)
      (angularWeightedTorusMeasure a) := by
  change AEStronglyMeasurable
    (fun q : LogTorus n =>
      (sourceRadialCutoff m q : ℂ) •
        Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation (W q)))
    (angularWeightedTorusMeasure a)
  apply (Complex.continuous_ofReal.comp
    (continuous_sourceRadialCutoff m)).aestronglyMeasurable.smul
  apply aestronglyMeasurable_complexEuclideanConjugatedMatrixAction
  · exact
      (continuous_angularMatrixSquareRoot
        (continuous_angularTorusComplexHessianMatrix ha2)
        hH).aestronglyMeasurable
  · exact (MeasureTheory.Lp.memLp W).aestronglyMeasurable

private theorem angularPhysicalResolventRootCutoffField_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a) (m : ℕ) :
    MemLp
      (angularPhysicalResolventRootCutoffField a W m)
      2 (angularWeightedTorusMeasure a) := by
  obtain ⟨B, hB, hb⟩ :=
    exists_angularHessianSquareRoot_fiber_bound_on_compact
      ha2 hH (sourceRadialCutoff_hasCompactSupport m).isCompact
  apply (MeasureTheory.Lp.memLp W).of_le_mul
    (c := B)
    (angularPhysicalResolventRootCutoffField_aestronglyMeasurable
      ha2 hH W m)
  filter_upwards [] with q
  by_cases hq : q ∈ tsupport (sourceRadialCutoff (n := n) m)
  · rw [angularPhysicalResolventRootCutoffField,
      norm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
    calc
      sourceRadialCutoff m q *
        ‖Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation (W q))‖ ≤
        ‖Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation (W q))‖ :=
        mul_le_of_le_one_left (norm_nonneg _)
          (sourceRadialCutoff_le_one m q)
      _ ≤ B * ‖angularEuclideanConjugation (W q)‖ :=
        hb q hq _
      _ = B * ‖W q‖ := by
        rw [norm_angularEuclideanConjugation]
  · have hz : sourceRadialCutoff m q = 0 :=
      image_eq_zero_of_notMem_tsupport hq
    simp only [angularPhysicalResolventRootCutoffField, hz, Complex.ofReal_zero, zero_smul,
      norm_zero,
      mul_nonneg hB.le (norm_nonneg _)]

private def angularPhysicalResolventRootCutoffL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a) (m : ℕ) :
    angularWeightedFormL2 a :=
  (angularPhysicalResolventRootCutoffField_memLp
    ha2 hH W m).toLp
      (angularPhysicalResolventRootCutoffField a W m)

private theorem angularClosedMollifiedRootVector_sub_pointwise
    {n : ℕ} {a : LogTorus n → ℝ}
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) (q : LogTorus n) :
    angularSmoothCompactHessianRootVector a
        (angularGraphMollifiedPhysicalField W ℓ) m q -
      angularPhysicalResolventRootCutoffField a W m q =
      (sourceRadialCutoff m q : ℂ) •
        Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation
            (torusFormRepresentative
                (angularGraphMollifiedPhysicalField W ℓ) q - W q)) := by
  rw [angularSmoothCompactHessianRootVector,
    angularPhysicalResolventRootCutoffField]
  change
    Matrix.toEuclideanLin
        (angularMatrixSquareRoot
          (angularTorusComplexHessianMatrix a) q)
        (angularEuclideanConjugation
          (torusFormRepresentative
            (cutoffPhysicalField m
              (angularGraphMollifiedPhysicalField W ℓ)) q)) -
      (sourceRadialCutoff m q : ℂ) •
        Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q)
          (angularEuclideanConjugation (W q)) = _
  rw [torusFormRepresentative_cutoffPhysicalField,
    angularEuclideanConjugation_real_smul,
    map_smul, ← smul_sub, ← map_sub,
    ← angularEuclideanConjugation_sub]

private theorem angularClosedMollifiedRootVectorL2_sub_norm_sq_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ q ∈ tsupport (sourceRadialCutoff (n := n) m),
      ∀ v : EuclideanSpace ℂ (Fin n),
        ‖Matrix.toEuclideanLin
          (angularMatrixSquareRoot
            (angularTorusComplexHessianMatrix a) q) v‖ ≤ B * ‖v‖) :
    ‖angularClosedMollifiedRootVectorL2
        ha ha2 hH W ℓ m -
      angularPhysicalResolventRootCutoffL2
        ha2 hH W m‖ ^ 2 ≤
      B ^ 2 *
        (∫ q in tsupport (sourceRadialCutoff (n := n) m),
          ‖torusFormRepresentative
              (angularGraphMollifiedPhysicalField W ℓ) q - W q‖ ^ 2
          ∂(angularWeightedTorusMeasure a)) := by
  let μ : Measure (LogTorus n) := angularWeightedTorusMeasure a
  let S : Set (LogTorus n) :=
    tsupport (sourceRadialCutoff (n := n) m)
  let V : LogSpace n → LogSpace n :=
    angularGraphMollifiedPhysicalField W ℓ
  let U : angularWeightedFormL2 a :=
    angularClosedMollifiedRootVectorL2 ha ha2 hH W ℓ m
  let R : angularWeightedFormL2 a :=
    angularPhysicalResolventRootCutoffL2 ha2 hH W m
  let : IsLocallyFiniteMeasure μ :=
    angularWeightedTorusMeasure_isLocallyFinite ha
  have : IsFiniteMeasureOnCompacts μ :=
    isFiniteMeasureOnCompacts_of_isLocallyFiniteMeasure
  have hS : IsCompact S :=
    (sourceRadialCutoff_hasCompactSupport m).isCompact
  have hV : ContDiff ℝ 2 V :=
    WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2
  have hp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d) :=
    angularGraphMollifiedPhysicalField_periodic W ℓ
  have hVc : Continuous (torusFormRepresentative V) :=
    continuous_torusFormRepresentative_of_smooth_periodic hV hp
  have hVm : MemLp (torusFormRepresentative V) 2
      (μ.restrict S) := by
    apply (MeasureTheory.memLp_two_iff_integrable_sq_norm
      (hVc.aestronglyMeasurable.mono_measure
        Measure.restrict_le_self)).mpr
    exact (hVc.norm.pow 2).continuousOn.integrableOn_compact hS
  have hWm : MemLp (fun q : LogTorus n => W q) 2
      (μ.restrict S) :=
    (MeasureTheory.Lp.memLp W).mono_measure
      Measure.restrict_le_self
  have hdiff : IntegrableOn
      (fun q : LogTorus n =>
        ‖torusFormRepresentative V q - W q‖ ^ 2) S μ :=
    (hVm.sub hWm).norm.integrable_sq
  have hsmooth := angularSmoothCompactHessianRootVector_memLp
    ha ha2 hH V hV hp m
  have hweak := angularPhysicalResolventRootCutoffField_memLp
    ha2 hH W m
  have hU :
      (fun q : LogTorus n => U q) =ᵐ[μ]
        angularSmoothCompactHessianRootVector a V m := by
    simpa [U, V, μ, angularClosedMollifiedRootVectorL2]
      using hsmooth.coeFn_toLp
  have hR :
      (fun q : LogTorus n => R q) =ᵐ[μ]
        angularPhysicalResolventRootCutoffField a W m := by
    simpa [R, μ, angularPhysicalResolventRootCutoffL2]
      using hweak.coeFn_toLp
  have hroot :
      ‖U - R‖ ^ 2 =
        ∫ q : LogTorus n,
          ‖angularSmoothCompactHessianRootVector a V m q -
            angularPhysicalResolventRootCutoffField a W m q‖ ^ 2 ∂μ := by
    rw [complexLp_norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [MeasureTheory.Lp.coeFn_sub U R, hU, hR]
      with q hsub hu hr
    rw [hsub]
    simp only [Pi.sub_apply]
    rw [hu, hr]
  have hleft : Integrable
      (fun q : LogTorus n =>
        ‖angularSmoothCompactHessianRootVector a V m q -
          angularPhysicalResolventRootCutoffField a W m q‖ ^ 2) μ :=
    (hsmooth.sub hweak).norm.integrable_sq
  have hright : Integrable
      (S.indicator
        (fun q : LogTorus n =>
          B ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2)) μ :=
    (MeasureTheory.integrable_indicator_iff hS.measurableSet).mpr
      (hdiff.const_mul (B ^ 2))
  have hpoint (q : LogTorus n) :
      ‖angularSmoothCompactHessianRootVector a V m q -
        angularPhysicalResolventRootCutoffField a W m q‖ ^ 2 ≤
        S.indicator
          (fun r : LogTorus n =>
            B ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q := by
    by_cases hq : q ∈ S
    · rw [Set.indicator_of_mem hq]
      have he := angularClosedMollifiedRootVector_sub_pointwise
        W ℓ m q
      have hnorm :
          ‖angularSmoothCompactHessianRootVector a V m q -
            angularPhysicalResolventRootCutoffField a W m q‖ ≤
          B * ‖torusFormRepresentative V q - W q‖ := by
        rw [he, norm_smul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
        calc
          sourceRadialCutoff m q *
              ‖Matrix.toEuclideanLin
                (angularMatrixSquareRoot
                  (angularTorusComplexHessianMatrix a) q)
                (angularEuclideanConjugation
                  (torusFormRepresentative V q - W q))‖ ≤
            ‖Matrix.toEuclideanLin
                (angularMatrixSquareRoot
                  (angularTorusComplexHessianMatrix a) q)
                (angularEuclideanConjugation
                  (torusFormRepresentative V q - W q))‖ :=
              mul_le_of_le_one_left (norm_nonneg _)
                (sourceRadialCutoff_le_one m q)
          _ ≤ B * ‖angularEuclideanConjugation
              (torusFormRepresentative V q - W q)‖ :=
            hB q hq _
          _ = B * ‖torusFormRepresentative V q - W q‖ := by
            rw [norm_angularEuclideanConjugation]
      calc
        _ ≤ (B * ‖torusFormRepresentative V q - W q‖) ^ 2 :=
          (sq_le_sq₀ (norm_nonneg _)
            (mul_nonneg hB₀ (norm_nonneg _))).mpr hnorm
        _ = _ := by rw [mul_pow]
    · rw [Set.indicator_of_notMem hq]
      have hz : sourceRadialCutoff m q = 0 :=
        image_eq_zero_of_notMem_tsupport hq
      have he := angularClosedMollifiedRootVector_sub_pointwise
        W ℓ m q
      rw [he, hz]
      simp only [Complex.ofReal_zero, zero_smul, norm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow, Std.le_refl]
  change ‖U - R‖ ^ 2 ≤
    B ^ 2 *
      (∫ q in S, ‖torusFormRepresentative V q - W q‖ ^ 2 ∂μ)
  rw [hroot]
  calc
    _ ≤ ∫ q : LogTorus n,
      S.indicator
        (fun r : LogTorus n =>
          B ^ 2 * ‖torusFormRepresentative V r - W r‖ ^ 2) q
        ∂μ := integral_mono hleft hright hpoint
    _ = ∫ q in S,
      B ^ 2 * ‖torusFormRepresentative V q - W q‖ ^ 2
        ∂μ := MeasureTheory.integral_indicator hS.measurableSet
    _ = _ := integral_const_mul (B ^ 2) _

private theorem angularClosedMollifiedRootVectorL2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a) (m : ℕ) :
    Tendsto
      (fun ℓ : ℕ =>
        angularClosedMollifiedRootVectorL2 ha ha2 hH W ℓ m)
      atTop
      (nhds
        (angularPhysicalResolventRootCutoffL2 ha2 hH W m)) := by
  have hS := (sourceRadialCutoff_hasCompactSupport
    (n := n) m).isCompact
  obtain ⟨B, hBpos, hB⟩ :=
    exists_angularHessianSquareRoot_fiber_bound_on_compact
      ha2 hH hS
  have hlocal :=
    TorusHomogeneousCutoffAdjoint.graphField_mollification_L2_tendsto_zero
      ha W hS
  have hsq :
      Tendsto
        (fun ℓ : ℕ =>
          ‖angularClosedMollifiedRootVectorL2
              ha ha2 hH W ℓ m -
            angularPhysicalResolventRootCutoffL2
              ha2 hH W m‖ ^ 2)
        atTop (nhds 0) := by
    apply squeeze_zero (fun ℓ => sq_nonneg _)
      (fun ℓ => angularClosedMollifiedRootVectorL2_sub_norm_sq_le
        ha ha2 hH W ℓ m hBpos.le hB)
    simpa only [mul_zero] using hlocal.const_mul (B ^ 2)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simpa only [norm_nonneg, Real.sqrt_sq, Real.sqrt_zero] using hsq.sqrt

private theorem angularClosedMollifiedRadialAdjoint_memLp
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a) (ℓ m : ℕ) :
    MemLp
      (angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)))
      2 (angularWeightedTorusMeasure a) := by
  let V : LogSpace n → LogSpace n :=
    angularGraphMollifiedPhysicalField W ℓ
  have hV : ContDiff ℝ 2 V :=
    WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha W ℓ 2
  have hp : ∀ d : Fin n → ℤ,
      Function.Periodic V (imaginaryShift d) :=
    angularGraphMollifiedPhysicalField_periodic W ℓ
  have hc : Continuous
      (angularTorusFormAdjoint a (cutoffPhysicalField m V)) := by
    unfold angularTorusFormAdjoint
    apply continuous_finsetSum
    intro i _
    exact continuous_angularTorusWeightedHolomorphicDerivative ha2
      (contDiff_pi.mp (contDiff_cutoffPhysicalField m hV) i)
      (fun d z => congrFun
        (cutoffPhysicalField_periodic m hp d z) i) i
  have hprod := integrable_angularTorusFormAdjoint_mul_conj
    (cutoffPhysicalField m V) ha ha2
    (fun i => contDiff_pi.mp (contDiff_cutoffPhysicalField m hV) i)
    (fun i d z => congrFun
      (cutoffPhysicalField_periodic m hp d z) i)
    (cutoffPhysicalField_coordinate_hasCompactSupport m V)
  have hsquare : Integrable
      (fun q : LogTorus n =>
        ‖angularTorusFormAdjoint a
          (cutoffPhysicalField m V) q‖ ^ 2)
      (angularWeightedTorusMeasure a) := by
    refine hprod.re.congr ?_
    filter_upwards [] with q
    change
      (angularTorusFormAdjoint a
          (cutoffPhysicalField m V) q *
        conj (angularTorusFormAdjoint a
          (cutoffPhysicalField m V) q)).re =
        ‖angularTorusFormAdjoint a
          (cutoffPhysicalField m V) q‖ ^ 2
    rw [Complex.mul_conj]
    simp only [Complex.normSq_eq_norm_sq, pow_two, Complex.ofReal_mul, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm
    hc.aestronglyMeasurable).mpr hsquare

private def angularClosedMollifiedRadialAdjointL2
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (W : angularWeightedFormL2 a)
    (ℓ m : ℕ) : angularWeightedScalarL2 a :=
  (angularClosedMollifiedRadialAdjoint_memLp
    ha ha2 W ℓ m).toLp
      (angularTorusFormAdjoint a
        (cutoffPhysicalField m
          (angularGraphMollifiedPhysicalField W ℓ)))

private theorem angularTorusFormAdjoint_cutoff_closedWeakResolventMollifier
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (g : angularWeightedScalarL2 a)
    (ℓ m : ℕ) (q : LogTorus n) :
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    angularTorusFormAdjoint a
      (cutoffPhysicalField m
        (angularGraphMollifiedPhysicalField W ℓ)) q =
      (sourceRadialCutoff m q : ℂ) *
        (-normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n =>
              (g - angularWeakScalarResolventCLM a g) r))
          ℓ (sourceTorusCoverPoint q) +
          angularMollifiedPhysicalAdjointDriftCommutator
            W ℓ (sourceTorusCoverPoint q)) +
        angularSourceCutoffAdjointCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q := by
  dsimp only
  rw [angularTorusFormAdjoint_cutoffPhysicalField a m
    (WeightedTorusScalarCompactGreen.contDiff_angularGraphMollifiedPhysicalField
      ha
      (WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)) ℓ 2) q,
    angularTorusFormAdjoint_eq_coverFormAdjoint,
    TorusHomogeneousClosedResolventAdjoint.coverFormAdjoint_mollifiedWeakResolvent_eq
      ha ha3 g ℓ (sourceTorusCoverPoint q)]

private theorem angularClosedMollifiedRadialAdjointL2_eq_defect_drift_commutator
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (g : angularWeightedScalarL2 a)
    (ℓ m : ℕ) :
    let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
      ha3.of_le (by norm_num)
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    let d : angularWeightedScalarL2 a :=
      g - angularWeakScalarResolventCLM a g
    angularClosedMollifiedRadialAdjointL2 ha ha2 W ℓ m =
      -(TorusHomogeneousCutoffAdjoint.fixedRadialCutoff_mollification_memLp
          ha d m ℓ).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (normalizedCoverMollification
                  (complexTorusCoverLift
                    (fun r : LogTorus n => d r)) ℓ) q) +
        (TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_memLp
          ha ha2 W ℓ m).toLp
          (fun q : LogTorus n =>
            (sourceRadialCutoff m q : ℂ) •
              torusScalarRepresentative
                (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q) +
        TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutatorL2
          ha W ℓ m := by
  dsimp only
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  let U : angularWeightedScalarL2 a :=
    angularClosedMollifiedRadialAdjointL2 ha ha2 W ℓ m
  let P : angularWeightedScalarL2 a :=
    (TorusHomogeneousCutoffAdjoint.fixedRadialCutoff_mollification_memLp
      ha d m ℓ).toLp
        (fun q : LogTorus n =>
          (sourceRadialCutoff m q : ℂ) •
            torusScalarRepresentative
              (normalizedCoverMollification
                (complexTorusCoverLift
                  (fun r : LogTorus n => d r)) ℓ) q)
  let T : angularWeightedScalarL2 a :=
    (TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_memLp
      ha ha2 W ℓ m).toLp
        (fun q : LogTorus n =>
          (sourceRadialCutoff m q : ℂ) •
            torusScalarRepresentative
              (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q)
  let J : angularWeightedScalarL2 a :=
    TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutatorL2
      ha W ℓ m
  change U = -P + T + J
  apply MeasureTheory.Lp.ext
  have hU :=
    (angularClosedMollifiedRadialAdjoint_memLp
      ha ha2 W ℓ m).coeFn_toLp
  have hP :=
    (TorusHomogeneousCutoffAdjoint.fixedRadialCutoff_mollification_memLp
      ha d m ℓ).coeFn_toLp
  have hT :=
    (TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_memLp
      ha ha2 W ℓ m).coeFn_toLp
  have hJ :=
    (TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutator_memLp
      ha W ℓ m).coeFn_toLp
  filter_upwards
    [hU, hP, hT, hJ,
     MeasureTheory.Lp.coeFn_neg P,
     MeasureTheory.Lp.coeFn_add (-P) T,
     MeasureTheory.Lp.coeFn_add (-P + T) J]
    with q hu hp ht hj hneg hinner houter
  change U q =
    angularTorusFormAdjoint a
      (cutoffPhysicalField m
        (angularGraphMollifiedPhysicalField W ℓ)) q at hu
  change P q =
    (sourceRadialCutoff m q : ℂ) •
      torusScalarRepresentative
        (normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n => d r)) ℓ) q at hp
  change T q =
    (sourceRadialCutoff m q : ℂ) •
      torusScalarRepresentative
        (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q at ht
  change J q =
    angularSourceCutoffAdjointCommutator m
      (angularGraphMollifiedPhysicalField W ℓ) q at hj
  rw [hu, houter, Pi.add_apply, hinner, Pi.add_apply,
    hneg, Pi.neg_apply, hp, ht, hj]
  have hpoint :=
    angularTorusFormAdjoint_cutoff_closedWeakResolventMollifier
      ha ha3 g ℓ m q
  change
    angularTorusFormAdjoint a
      (cutoffPhysicalField m
        (angularGraphMollifiedPhysicalField W ℓ)) q =
      (sourceRadialCutoff m q : ℂ) *
        (-normalizedCoverMollification
          (complexTorusCoverLift
            (fun r : LogTorus n => d r)) ℓ
            (sourceTorusCoverPoint q) +
          angularMollifiedPhysicalAdjointDriftCommutator
            W ℓ (sourceTorusCoverPoint q)) +
        angularSourceCutoffAdjointCommutator m
          (angularGraphMollifiedPhysicalField W ℓ) q
    at hpoint
  rw [hpoint]
  simp only [torusScalarRepresentative_eq_sourceTorusCoverPoint,
    smul_eq_mul]
  ring

private theorem angularClosedMollifiedRadialAdjointL2_tendsto
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (g : angularWeightedScalarL2 a)
    {B : ℝ}
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B)
    (m : ℕ) :
    let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
      ha3.of_le (by norm_num)
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    let d : angularWeightedScalarL2 a :=
      g - angularWeakScalarResolventCLM a g
    Tendsto
      (fun ℓ : ℕ =>
        angularClosedMollifiedRadialAdjointL2
          ha ha2 W ℓ m)
      atTop
      (nhds
        (angularWeakSourceCutoffAdjointDefectL2
          d W hB m)) := by
  dsimp only
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  change Tendsto
    (fun ℓ : ℕ =>
      angularClosedMollifiedRadialAdjointL2
        ha ha2 W ℓ m)
    atTop
    (nhds
      (angularWeakSourceCutoffAdjointDefectL2 d W hB m))
  have hscalar :=
    TorusHomogeneousCutoffAdjoint.angularWeightedScalar_fixedRadialCutoff_mollification_L2_tendsto
      ha d m
  have hdrift :=
    TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_L2_tendsto_zero
      ha ha2 W m
  have hcomm :=
    TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutatorL2_tendsto
      ha W hB m
  have hcombined := (hscalar.neg.add hdrift).add hcomm
  have hlimit :
      Tendsto
        (fun ℓ : ℕ =>
          -(TorusHomogeneousCutoffAdjoint.fixedRadialCutoff_mollification_memLp
              ha d m ℓ).toLp
              (fun q : LogTorus n =>
                (sourceRadialCutoff m q : ℂ) •
                  torusScalarRepresentative
                    (normalizedCoverMollification
                      (complexTorusCoverLift
                        (fun r : LogTorus n => d r)) ℓ) q) +
            (TorusHomogeneousCutoffAdjoint.angularClosedMollifiedDrift_fixedRadialCutoff_memLp
              ha ha2 W ℓ m).toLp
              (fun q : LogTorus n =>
                (sourceRadialCutoff m q : ℂ) •
                  torusScalarRepresentative
                    (angularMollifiedPhysicalAdjointDriftCommutator W ℓ) q) +
            TorusHomogeneousRadialAdjoint.angularClosedMollifiedRadialAdjointCommutatorL2
              ha W ℓ m)
        atTop
        (nhds
          (angularWeakSourceCutoffAdjointDefectL2 d W hB m)) := by
    simpa only [smul_eq_mul, angularWeakSourceCutoffAdjointDefectL2, add_zero] using hcombined
  apply Filter.Tendsto.congr' _ hlimit
  filter_upwards [] with ℓ
  exact (angularClosedMollifiedRadialAdjointL2_eq_defect_drift_commutator
    ha ha3 g ℓ m).symm

private theorem angularWeakResolventClosedMollifiedRootBochner_le_adjoint_matrix
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (g : angularWeightedScalarL2 a)
    (ℓ m : ℕ) :
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    ‖angularClosedMollifiedRootVectorL2
        ha ha2 hH W ℓ m‖ ^ 2 ≤
      ‖angularClosedMollifiedRadialAdjointL2
          ha ha2 W ℓ m‖ ^ 2 +
        2 * ‖TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutatorL2
          ha W ℓ m‖ ^ 2 := by
  dsimp only
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  have hadj := angularClosedMollifiedRadialAdjoint_memLp
    ha ha2 W ℓ m
  have hmatrix :=
    TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutator_memLp
      ha W ℓ m
  have hboch :=
    TorusHomogeneousSmoothRootBochner.angularWeakResolventClosedMollifiedRootBochner
      ha ha2 hH g ℓ m
  change
    ‖angularClosedMollifiedRootVectorL2
      ha ha2 hH W ℓ m‖ ^ 2 ≤ _ at hboch ⊢
  calc
    _ ≤
        (∫ q : LogTorus n,
          angularTorusFormAdjoint a
            (cutoffPhysicalField m
              (angularGraphMollifiedPhysicalField W ℓ)) q *
            conj (angularTorusFormAdjoint a
              (cutoffPhysicalField m
                (angularGraphMollifiedPhysicalField W ℓ)) q)
          ∂(angularWeightedTorusMeasure a)).re +
        (∫ q : LogTorus n,
          complexEuclideanAntisymmetricEnergy
            (sourceCutoffDerivativeCommutator m
              (angularGraphMollifiedPhysicalField W ℓ) q)
          ∂(angularWeightedTorusMeasure a)).re := hboch
    _ ≤
        (∫ q : LogTorus n,
          angularTorusFormAdjoint a
            (cutoffPhysicalField m
              (angularGraphMollifiedPhysicalField W ℓ)) q *
            conj (angularTorusFormAdjoint a
              (cutoffPhysicalField m
                (angularGraphMollifiedPhysicalField W ℓ)) q)
          ∂(angularWeightedTorusMeasure a)).re +
        2 * ‖hmatrix.toLp
          (sourceCutoffDerivativeCommutator m
            (angularGraphMollifiedPhysicalField W ℓ))‖ ^ 2 :=
      add_le_add le_rfl
        (integral_complexEuclideanAntisymmetricEnergy_le_of_memLp
          hmatrix)
    _ = _ := by
      rw [complexScalar_integral_mul_conj_re_eq_L2_norm_sq hadj]
      rfl

private theorem angularPhysicalWeakResolventRootCutoff_sq_le_adjoint_matrix
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (g : angularWeightedScalarL2 a)
    {B : ℝ} (hB₀ : 0 ≤ B)
    (hB : ∀ x : Space n,
      ‖euclideanGradient (fun y => unitBump y) x‖ ≤ B)
    (m : ℕ) :
    let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
      ha3.of_le (by norm_num)
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    let d : angularWeightedScalarL2 a :=
      g - angularWeakScalarResolventCLM a g
    ‖angularPhysicalResolventRootCutoffL2
        ha2 hH W m‖ ^ 2 ≤
      ‖angularWeakSourceCutoffAdjointDefectL2 d W hB m‖ ^ 2 +
        2 * ‖(angularWeakSourceCutoffDerivativeCommutator_memLp
          W hB m).toLp
            (angularWeakSourceCutoffDerivativeCommutator W m)‖ ^ 2 := by
  dsimp only
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  let R : angularWeightedFormL2 a :=
    angularPhysicalResolventRootCutoffL2 ha2 hH W m
  let J : angularWeightedScalarL2 a :=
    angularWeakSourceCutoffAdjointDefectL2 d W hB m
  let M : MeasureTheory.Lp
      (EuclideanSpace ℂ (Fin n × Fin n)) 2
      (angularWeightedTorusMeasure a) :=
    (angularWeakSourceCutoffDerivativeCommutator_memLp
      W hB m).toLp
        (angularWeakSourceCutoffDerivativeCommutator W m)
  have hroot := angularClosedMollifiedRootVectorL2_tendsto
    ha ha2 hH W m
  have hrootnorm :
      Tendsto
        (fun ℓ : ℕ =>
          ‖angularClosedMollifiedRootVectorL2
            ha ha2 hH W ℓ m‖ ^ 2)
        atTop (nhds (‖R‖ ^ 2)) := by
    exact ((continuous_norm.tendsto R).comp hroot).pow 2
  have hadj := angularClosedMollifiedRadialAdjointL2_tendsto
    ha ha3 g hB m
  have hadjnorm :
      Tendsto
        (fun ℓ : ℕ =>
          ‖angularClosedMollifiedRadialAdjointL2
            ha ha2 W ℓ m‖ ^ 2)
        atTop (nhds (‖J‖ ^ 2)) := by
    exact ((continuous_norm.tendsto J).comp hadj).pow 2
  have hmatrix :=
    TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutatorL2_tendsto
      ha W hB₀ hB m
  have hmatrixnorm :
      Tendsto
        (fun ℓ : ℕ =>
          2 * ‖TorusHomogeneousRadialMatrix.angularClosedMollifiedRadialMatrixCommutatorL2
            ha W ℓ m‖ ^ 2)
        atTop (nhds (2 * ‖M‖ ^ 2)) := by
    exact (((continuous_norm.tendsto M).comp hmatrix).pow 2).const_mul 2
  have hlimit := (hadjnorm.add hmatrixnorm).sub hrootnorm
  have hnonneg : 0 ≤ ‖J‖ ^ 2 + 2 * ‖M‖ ^ 2 - ‖R‖ ^ 2 := by
    apply ge_of_tendsto hlimit
    filter_upwards [] with ℓ
    exact sub_nonneg.mpr
      (angularWeakResolventClosedMollifiedRootBochner_le_adjoint_matrix
        ha ha2 hH g ℓ m)
  exact sub_nonneg.mp hnonneg

private theorem angularPhysicalResolventRootCutoffL2_norm_le_of_one_on_support
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a)
    (m M : ℕ)
    (hone : ∀ q ∈ tsupport (sourceRadialCutoff (n := n) m),
      sourceRadialCutoff M q = 1) :
    ‖angularPhysicalResolventRootCutoffL2 ha2 hH W m‖ ≤
      ‖angularPhysicalResolventRootCutoffL2 ha2 hH W M‖ := by
  let hm := angularPhysicalResolventRootCutoffField_memLp
    ha2 hH W m
  let hM := angularPhysicalResolventRootCutoffField_memLp
    ha2 hH W M
  change
    ‖hm.toLp (angularPhysicalResolventRootCutoffField a W m)‖ ≤
      ‖hM.toLp (angularPhysicalResolventRootCutoffField a W M)‖
  have hcomp := complexLp_norm_le_of_ae_norm_le
    hm hM (C := (1 : ℝ)) zero_le_one
      (by
        filter_upwards [] with q
        by_cases hq :
            q ∈ tsupport (sourceRadialCutoff (n := n) m)
        · have hMq := hone q hq
          unfold angularPhysicalResolventRootCutoffField
          rw [hMq]
          simp only [Complex.ofReal_one, one_smul, one_mul,
            norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (sourceRadialCutoff_nonneg m q)]
          exact mul_le_of_le_one_left (norm_nonneg _)
            (sourceRadialCutoff_le_one m q)
        · have hmq : sourceRadialCutoff m q = 0 :=
            image_eq_zero_of_notMem_tsupport hq
          simp only [angularPhysicalResolventRootCutoffField, hmq, Complex.ofReal_zero, zero_smul,
            norm_zero, Complex.coe_smul, one_mul, norm_nonneg])
  simpa only [one_mul] using hcomp

private theorem eventually_angularPhysicalResolventRootCutoffL2_norm_le
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha2 : ContDiff ℝ 2 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (W : angularWeightedFormL2 a)
    (m : ℕ) :
    ∀ᶠ M : ℕ in atTop,
      ‖angularPhysicalResolventRootCutoffL2 ha2 hH W m‖ ≤
        ‖angularPhysicalResolventRootCutoffL2 ha2 hH W M‖ := by
  filter_upwards
    [sourceRadialCutoff_eventually_one_on_compact
      (sourceRadialCutoff_hasCompactSupport m).isCompact]
    with M hM
  exact angularPhysicalResolventRootCutoffL2_norm_le_of_one_on_support
    ha2 hH W m M hM

private theorem angularPhysicalWeakResolventRootCutoffCoercivity
    {n : ℕ} {a : LogTorus n → ℝ}
    (ha : Continuous a)
    (ha3 : ContDiff ℝ 3 (angularCoverPotential a))
    (hH : ∀ q : LogTorus n,
      (angularTorusComplexHessianMatrix a q).PosDef)
    (g : angularWeightedScalarL2 a)
    (m : ℕ) :
    let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
      ha3.of_le (by norm_num)
    let W : angularWeightedFormL2 a :=
      WithLp.snd
        (angularWeakDolbeaultResolvent a g :
          angularDolbeaultGraphAmbient a)
    ‖angularPhysicalResolventRootCutoffL2
      ha2 hH W m‖ ≤
      ‖g - angularWeakScalarResolventCLM a g‖ := by
  dsimp only
  let ha2 : ContDiff ℝ 2 (angularCoverPotential a) :=
    ha3.of_le (by norm_num)
  let W : angularWeightedFormL2 a :=
    WithLp.snd
      (angularWeakDolbeaultResolvent a g :
        angularDolbeaultGraphAmbient a)
  let d : angularWeightedScalarL2 a :=
    g - angularWeakScalarResolventCLM a g
  change ‖angularPhysicalResolventRootCutoffL2 ha2 hH W m‖ ≤ ‖d‖
  obtain ⟨B, hB₀, hB⟩ :=
    unitBump_euclideanGradient_bound (n := n)
  have hadj :=
    angularWeakSourceCutoffAdjointDefectL2_tendsto
      d W hB₀ hB
  have hadjnorm :=
    ((continuous_norm.tendsto
      (-d : angularWeightedScalarL2 a)).comp hadj).pow 2
  have hmatrix :=
    angularWeakSourceCutoffDerivativeCommutator_L2_tendsto_zero
      W hB₀ hB
  have hmatrixnorm :=
    (((continuous_norm.tendsto
      (0 : MeasureTheory.Lp
        (EuclideanSpace ℂ (Fin n × Fin n)) 2
        (angularWeightedTorusMeasure a))).comp hmatrix).pow 2).const_mul
      (2 : ℝ)
  have htail :
      Tendsto
        (fun M : ℕ =>
          ‖angularWeakSourceCutoffAdjointDefectL2
            d W hB M‖ ^ 2 +
          2 * ‖(angularWeakSourceCutoffDerivativeCommutator_memLp
            W hB M).toLp
              (angularWeakSourceCutoffDerivativeCommutator W M)‖ ^ 2)
        atTop (nhds (‖d‖ ^ 2)) := by
    simpa only [Function.comp_apply, norm_neg, norm_zero, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero] using hadjnorm.add hmatrixnorm
  have hbound :
      ∀ᶠ M : ℕ in atTop,
        ‖angularPhysicalResolventRootCutoffL2
          ha2 hH W m‖ ^ 2 ≤
          ‖angularWeakSourceCutoffAdjointDefectL2
            d W hB M‖ ^ 2 +
          2 * ‖(angularWeakSourceCutoffDerivativeCommutator_memLp
            W hB M).toLp
              (angularWeakSourceCutoffDerivativeCommutator W M)‖ ^ 2 := by
    filter_upwards
      [eventually_angularPhysicalResolventRootCutoffL2_norm_le
        ha2 hH W m]
      with M hmono
    calc
      ‖angularPhysicalResolventRootCutoffL2
          ha2 hH W m‖ ^ 2 ≤
        ‖angularPhysicalResolventRootCutoffL2
          ha2 hH W M‖ ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hmono
      _ ≤ _ :=
        angularPhysicalWeakResolventRootCutoff_sq_le_adjoint_matrix
          ha ha3 hH g hB₀ hB M
  have hsquare :
      ‖angularPhysicalResolventRootCutoffL2
        ha2 hH W m‖ ^ 2 ≤ ‖d‖ ^ 2 :=
    ge_of_tendsto htail hbound
  exact
    (sq_le_sq₀
      (norm_nonneg
        (angularPhysicalResolventRootCutoffL2 ha2 hH W m))
      (norm_nonneg d)).mp hsquare

end TorusHomogeneousWeakResolventRootCoercivity

end Ehrhart

end
