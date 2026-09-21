/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import LeanPool.ParameterFreeGradient.V7.Proofs.Stage5AboveTwoLowerS5A2Envelope.KernelHessianStructure
import LeanPool.ParameterFreeGradient.V7.Proofs.Shared
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
A positive semidefinite Hessian bound yields cocoercivity of the kernel gradient.
-/

open scoped Interval

namespace V7.Stage5AboveTwoLowerS5A2Envelope

open Stage5AboveTwoLower
open Stage5AboveTwoLower.S5ARepair
open Stage5AboveTwoLower.S5AGlobalC2

/-- Cauchy--Schwarz for scalar integration on the unit interval, proved from
nonnegativity of the integrated centred square. -/
lemma sq_intervalIntegral_le_integral_sq (X : ℝ → ℝ)
    (hX : Continuous X) :
    (∫ t in (0 : ℝ)..1, X t) ^ (2 : ℕ) ≤
      ∫ t in (0 : ℝ)..1, (X t) ^ (2 : ℕ) := by
  let I : ℝ := ∫ t in (0 : ℝ)..1, X t
  have hcenter : Continuous (fun t ↦ (X t - I) ^ (2 : ℕ)) :=
    (hX.sub continuous_const).pow 2
  have hnon : 0 ≤ ∫ t in (0 : ℝ)..1, (X t - I) ^ (2 : ℕ) :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun t ↦ sq_nonneg (X t - I))
  have hXint : IntervalIntegrable X MeasureTheory.volume 0 1 :=
    hX.intervalIntegrable _ _
  have hXsqint : IntervalIntegrable (fun t ↦ (X t) ^ (2 : ℕ))
      MeasureTheory.volume 0 1 := hX.pow 2 |>.intervalIntegrable _ _
  have hconstint : IntervalIntegrable (fun _ : ℝ ↦ I)
      MeasureTheory.volume 0 1 := intervalIntegrable_const
  have hcrossint : IntervalIntegrable (fun t ↦ 2 * I * X t)
      MeasureTheory.volume 0 1 := hXint.const_mul (2 * I)
  have hrewrite : (fun t ↦ (X t - I) ^ (2 : ℕ)) =
      fun t ↦ X t ^ (2 : ℕ) - 2 * I * X t + I ^ (2 : ℕ) := by
    funext t
    ring
  rw [hrewrite, intervalIntegral.integral_add
      (hXsqint.sub hcrossint)
      (intervalIntegrable_const : IntervalIntegrable
        (fun _ : ℝ ↦ I ^ (2 : ℕ)) MeasureTheory.volume 0 1),
    intervalIntegral.integral_sub hXsqint hcrossint,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hnon
  dsimp [I] at hnon ⊢
  norm_num at hnon ⊢
  nlinarith

/-- Exact unit-ball cocoercivity of the concrete kernel gradient, derived
from the genuine Hessian, its PSD Cauchy--Schwarz inequality, and the frozen
quadratic Hessian bound. -/
theorem kernelGradient_cocoercive_on_unit_of_hessian_bound
    {p r theta M : ℝ}
    (hp : 1 < p) (hr : 2 < r) (htheta : 1 < theta)
    (htr : 2 * theta < r) {d : ℕ}
    (hbound : ∀ z e : Point d, lpNorm p z ≤ 1 →
      O3.pairing e (kernelHessian r theta z e) ≤
        M * lpNorm p e ^ (2 : ℕ)) :
    KernelCocoerciveOnUnit p M (kernelGradientVector (d := d) r theta) := by
  intro u w hu hw
  let h : Point d := u - w
  let D : Point d := kernelGradientVector r theta u -
    kernelGradientVector r theta w
  let G : ℝ := lpNorm (conjugateExponent p) D
  by_cases hD : D = 0
  · change G ^ (2 : ℕ) ≤ M * O3.pairing D h
    rw [hD]
    simp [G, hD, h, O3.pairing, O3.lpNorm_zero
      (lt_trans zero_lt_one (O3.one_lt_conjugateExponent hp))]
  · have hG : 0 < G := O3.lpNorm_pos_of_ne_zero hD
    let e : Point d := normingDirection (conjugateExponent p) D
    have heData := normingDirection_correct p hp d D hG
    have heNorm : lpNorm p e = 1 := by simpa [e] using heData.1
    have hePair : O3.pairing D e = G := by simpa [e, G] using heData.2
    let path : ℝ → Point d := AffineMap.lineMap w u
    let X : ℝ → ℝ := fun t ↦
      O3.pairing e (kernelHessian r theta (path t) h)
    let A : ℝ → ℝ := fun t ↦
      O3.pairing h (kernelHessian r theta (path t) h)
    let Fe : ℝ → ℝ := fun t ↦
      O3.pairing e (kernelGradientVector r theta (path t))
    let Fh : ℝ → ℝ := fun t ↦
      O3.pairing h (kernelGradientVector r theta (path t))
    have hpath : Continuous path := by
      dsimp [path]
      fun_prop
    have hH : Continuous (fun t ↦ kernelHessian r theta (path t)) :=
      (continuous_kernelHessian hr htheta htr).comp hpath
    have hHh : Continuous (fun t ↦ kernelHessian r theta (path t) h) :=
      hH.clm_apply continuous_const
    have hX : Continuous X := by
      simpa [X, Function.comp_def, pairingCLM_apply] using
        (pairingCLM e).continuous.comp hHh
    have hA : Continuous A := by
      simpa [A, Function.comp_def, pairingCLM_apply] using
        (pairingCLM h).continuous.comp hHh
    have hpathUnit : ∀ t ∈ Set.Icc (0 : ℝ) 1, lpNorm p (path t) ≤ 1 := by
      intro t ht
      have hn := (convexOn_lpNorm (d := d) hp.le).2
        (Set.mem_univ w) (Set.mem_univ u) (sub_nonneg.mpr ht.2)
        ht.1 (by ring : (1 - t) + t = 1)
      have hline : path t = (1 - t) • w + t • u := by
        funext i
        simp [path, AffineMap.lineMap_apply]
        ring
      rw [hline]
      calc
        lpNorm p ((1 - t) • w + t • u) ≤
            (1 - t) * lpNorm p w + t * lpNorm p u := by
          simpa [smul_eq_mul] using hn
        _ ≤ (1 - t) * 1 + t * 1 := by
          gcongr
          · exact sub_nonneg.mpr ht.2
          · exact ht.1
        _ = 1 := by ring
    have hpoint : ∀ t ∈ Set.Icc (0 : ℝ) 1,
        X t ^ (2 : ℕ) ≤ M * A t := by
      intro t ht
      have hcs := kernelHessian_cauchy_schwarz hr htheta htr
        (path t) e h
      have hdiag := hbound (path t) e (hpathUnit t ht)
      have hAnonneg := kernelHessian_quadratic_nonneg hr htheta htr
        (path t) h
      change X t ^ (2 : ℕ) ≤
        O3.pairing e (kernelHessian r theta (path t) e) * A t at hcs
      change O3.pairing e (kernelHessian r theta (path t) e) ≤
        M * lpNorm p e ^ (2 : ℕ) at hdiag
      change 0 ≤ A t at hAnonneg
      rw [heNorm] at hdiag
      norm_num at hdiag
      nlinarith [mul_le_mul_of_nonneg_right hdiag hAnonneg]
    have hXsqInt : IntervalIntegrable (fun t ↦ X t ^ (2 : ℕ))
        MeasureTheory.volume 0 1 := hX.pow 2 |>.intervalIntegrable _ _
    have hAInt : IntervalIntegrable A MeasureTheory.volume 0 1 :=
      hA.intervalIntegrable _ _
    have hintMono : (∫ t in (0 : ℝ)..1, X t ^ (2 : ℕ)) ≤
        ∫ t in (0 : ℝ)..1, M * A t := by
      exact intervalIntegral.integral_mono_on (by norm_num) hXsqInt
        (hAInt.const_mul M) hpoint
    have hlineDeriv (t : ℝ) := AffineMap.hasDerivAt_lineMap
      (a := w) (b := u) (x := t)
    have hFeDeriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt Fe (X t) t := by
      intro t _
      have hg := (hasFDerivAt_kernelGradientVector hr htheta htr (path t)).comp
        t (hlineDeriv t).hasFDerivAt
      have hpj := (pairingCLM e).hasFDerivAt.comp t hg
      simpa [Fe, X, path, h, Function.comp_def, pairingCLM_apply,
        ContinuousLinearMap.toSpanSingleton_apply] using hpj.hasDerivAt
    have hFhDeriv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
        HasDerivAt Fh (A t) t := by
      intro t _
      have hg := (hasFDerivAt_kernelGradientVector hr htheta htr (path t)).comp
        t (hlineDeriv t).hasFDerivAt
      have hpj := (pairingCLM h).hasFDerivAt.comp t hg
      simpa [Fh, A, path, h, Function.comp_def, pairingCLM_apply,
        ContinuousLinearMap.toSpanSingleton_apply] using hpj.hasDerivAt
    have hXIntegral : (∫ t in (0 : ℝ)..1, X t) = G := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFeDeriv
        (hX.intervalIntegrable _ _)]
      have hePair' : O3.pairing e D = G := by
        rw [O3.pairing_comm]
        exact hePair
      simpa [Fe, path, AffineMap.lineMap_apply, D, O3.pairing,
        Pi.sub_apply, Finset.sum_sub_distrib, mul_sub] using hePair'
    have hAIntegral : (∫ t in (0 : ℝ)..1, A t) =
        O3.pairing D h := by
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hFhDeriv hAInt]
      have hpair : O3.pairing h D = O3.pairing D h := O3.pairing_comm h D
      simpa [Fh, path, AffineMap.lineMap_apply, D, O3.pairing,
        Pi.sub_apply, Finset.sum_sub_distrib, mul_sub] using hpair
    have hjensen := sq_intervalIntegral_le_integral_sq X hX
    rw [hXIntegral] at hjensen
    rw [intervalIntegral.integral_const_mul, hAIntegral] at hintMono
    change G ^ (2 : ℕ) ≤ M * O3.pairing D h
    exact hjensen.trans hintMono

end V7.Stage5AboveTwoLowerS5A2Envelope
