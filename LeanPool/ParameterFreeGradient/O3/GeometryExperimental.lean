/-
Copyright (c) 2026 Yuning Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuning Yang
-/

import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import LeanPool.ParameterFreeGradient.O3.Geometry

namespace O3.Experimental

noncomputable def scalarJ (p u : ℝ) : ℝ := |u| ^ (p - 2) * u

lemma scalarJ_nonneg {p u : ℝ} (hp : 2 < p) (hu : 0 ≤ u) :
    scalarJ p u = u ^ (p - 1) := by
  rw [scalarJ, abs_of_nonneg hu]
  rw [← Real.rpow_add_one' hu (by linarith : p - 2 + 1 ≠ 0)]
  congr 1
  ring

lemma scalarJ_nonpos {p u : ℝ} (hp : 2 < p) (hu : u ≤ 0) :
    scalarJ p u = -((-u) ^ (p - 1)) := by
  rw [scalarJ, abs_of_nonpos hu]
  have hnu : 0 ≤ -u := neg_nonneg.mpr hu
  calc
    (-u) ^ (p - 2) * u = -((-u) ^ (p - 2) * (-u)) := by ring
    _ = -((-u) ^ (p - 1)) := by
      rw [← Real.rpow_add_one' hnu (by linarith : p - 2 + 1 ≠ 0)]
      congr 2
      ring

lemma scalarJ_strongMonotone_ordered {p u v : ℝ} (hp : 2 < p) (huv : v ≤ u) :
    (2 : ℝ) ^ (2 - p) * |u - v| ^ p ≤ (scalarJ p u - scalarJ p v) * (u - v) := by
  have hr : 1 ≤ p - 1 := by linarith
  have hc1 : (2 : ℝ) ^ (2 - p) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by norm_num) (by linarith)
  rcases le_total 0 v with hv | hv
  · have hu : 0 ≤ u := hv.trans huv
    rw [scalarJ_nonneg hp hu, scalarJ_nonneg hp hv, abs_of_nonneg (sub_nonneg.mpr huv)]
    have hpow := Real.add_rpow_le_rpow_add hv (sub_nonneg.mpr huv) hr
    have huvsum : v + (u - v) = u := by ring
    rw [huvsum] at hpow
    have hdiff : (u - v) ^ (p - 1) ≤ u ^ (p - 1) - v ^ (p - 1) := by linarith
    have hd0 : 0 ≤ u - v := sub_nonneg.mpr huv
    have hmul := mul_le_mul_of_nonneg_right hdiff hd0
    have hrpow : (u - v) ^ (p - 1) * (u - v) = (u - v) ^ p := by
      rw [← Real.rpow_add_one' hd0 (by linarith : p - 1 + 1 ≠ 0)]
      congr 1
      ring
    rw [hrpow] at hmul
    have hcpow := mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hd0 p)
    calc
      2 ^ (2 - p) * (u - v) ^ p ≤ 1 * (u - v) ^ p := hcpow
      _ = (u - v) ^ p := one_mul _
      _ ≤ (u ^ (p - 1) - v ^ (p - 1)) * (u - v) := hmul
  · rcases le_total u 0 with hu | hu
    · have hnv : 0 ≤ -u := neg_nonneg.mpr hu
      have hv0 : v ≤ 0 := huv.trans hu
      rw [scalarJ_nonpos hp hu, scalarJ_nonpos hp hv0,
        abs_of_nonneg (sub_nonneg.mpr huv)]
      ring_nf
      have hpow := Real.add_rpow_le_rpow_add hnv (sub_nonneg.mpr huv) hr
      have hsum : -u + (u - v) = -v := by ring
      rw [hsum] at hpow
      have hdiff : (u - v) ^ (p - 1) ≤ (-v) ^ (p - 1) - (-u) ^ (p - 1) := by linarith
      have hd0 : 0 ≤ u - v := sub_nonneg.mpr huv
      have hmul := mul_le_mul_of_nonneg_right hdiff hd0
      have hrpow : (u - v) ^ (p - 1) * (u - v) = (u - v) ^ p := by
        rw [← Real.rpow_add_one' hd0 (by linarith : p - 1 + 1 ≠ 0)]
        congr 1
        ring
      rw [hrpow] at hmul
      ring_nf at hmul
      have hcpow := mul_le_mul_of_nonneg_right hc1 (Real.rpow_nonneg hd0 p)
      have hcpow' : 2 ^ (2 - p) * (u - v) ^ p ≤ (u - v) ^ p := by
        simpa only [one_mul] using hcpow
      have hfinal := hcpow'.trans hmul
      ring_nf at hfinal
      linarith [hfinal]
    · have hu0 : 0 ≤ u := hu
      have hv0 : v ≤ 0 := hv
      rw [scalarJ_nonneg hp hu0, scalarJ_nonpos hp hv0,
        abs_of_nonneg (sub_nonneg.mpr huv)]
      let a : NNReal := ⟨u, hu0⟩
      let b : NNReal := ⟨-v, neg_nonneg.mpr hv0⟩
      have hnn := NNReal.rpow_add_le_mul_rpow_add_rpow a b (p := p - 1) hr
      have hcast : (↑((a + b) ^ (p - 1)) : ℝ) ≤
          ↑((2 : NNReal) ^ (p - 1 - 1) * (a ^ (p - 1) + b ^ (p - 1))) := by
        exact_mod_cast hnn
      simp only [NNReal.coe_rpow, NNReal.coe_mul, NNReal.coe_add, NNReal.coe_ofNat] at hcast
      have hreal' : ((a : ℝ) + (b : ℝ)) ^ (p - 1) ≤
          (2 : ℝ) ^ (p - 2) * ((a : ℝ) ^ (p - 1) + (b : ℝ) ^ (p - 1)) := by
        convert hcast using 1
        ring_nf
      change (u + (-v)) ^ (p - 1) ≤
        (2 : ℝ) ^ (p - 2) * (u ^ (p - 1) + (-v) ^ (p - 1)) at hreal'
      have hreal : (u + (-v)) ^ (p - 1) ≤
          (2 : ℝ) ^ (p - 2) * (u ^ (p - 1) + (-v) ^ (p - 1)) := by
        exact hreal'
      have hd : u - v = u + (-v) := by ring
      rw [hd]
      have hd0 : 0 ≤ u + -v := add_nonneg hu0 (neg_nonneg.mpr hv0)
      have hcpos : 0 < (2 : ℝ) ^ (p - 2) := Real.rpow_pos_of_pos (by norm_num) _
      have hcancel :
          (2 : ℝ) ^ (2 - p) * (u + -v) ^ (p - 1) ≤
            u ^ (p - 1) + (-v) ^ (p - 1) := by
        have hinv : (2 : ℝ) ^ (2 - p) = ((2 : ℝ) ^ (p - 2))⁻¹ := by
          rw [← Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          congr 2
          ring
        rw [hinv, inv_mul_le_iff₀ hcpos]
        simpa [mul_comm] using hreal
      have hmul := mul_le_mul_of_nonneg_right hcancel hd0
      have hrpow : (u + -v) ^ (p - 1) * (u + -v) = (u + -v) ^ p := by
        rw [← Real.rpow_add_one' hd0 (by linarith : p - 1 + 1 ≠ 0)]
        congr 1
        ring
      rw [mul_assoc, hrpow] at hmul
      nlinarith

lemma scalarJ_strongMonotone {p u v : ℝ} (hp : 2 < p) :
    (2 : ℝ) ^ (2 - p) * |u - v| ^ p ≤ (scalarJ p u - scalarJ p v) * (u - v) := by
  rcases le_total v u with huv | huv
  · exact scalarJ_strongMonotone_ordered hp huv
  · have h := scalarJ_strongMonotone_ordered hp huv
    calc
      2 ^ (2 - p) * |u - v| ^ p = 2 ^ (2 - p) * |v - u| ^ p := by rw [abs_sub_comm]
      _ ≤ (scalarJ p v - scalarJ p u) * (v - u) := h
      _ = (scalarJ p u - scalarJ p v) * (u - v) := by ring

lemma powerDualityMap_strongMonotone {p : ℝ} (hp : 2 < p) {d : ℕ}
    (u v : Point d) :
    (2 : ℝ) ^ (2 - p) * lpPower p (u - v) ≤
      pairing (powerDualityMap p u - powerDualityMap p v) (u - v) := by
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦
    scalarJ_strongMonotone (u := u i) (v := v i) hp
  simpa only [lpPower, pairing, powerDualityMap, scalarJ, Pi.sub_apply,
    Finset.mul_sum] using hsum

noncomputable def scalarEnergy (p x : ℝ) : ℝ := |x| ^ p / p

lemma hasDerivAt_scalarEnergy {p : ℝ} (hp : 2 < p) (x : ℝ) :
    HasDerivAt (scalarEnergy p) (scalarJ p x) x := by
  have h := (hasDerivAt_abs_rpow x (by linarith : 1 < p)).div_const p
  have heq : scalarJ p x = p * |x| ^ (p - 2) * x / p := by
    unfold scalarJ
    field_simp
  rw [heq]
  exact h

lemma continuous_scalarJ {p : ℝ} (hp : 2 < p) : Continuous (scalarJ p) := by
  unfold scalarJ
  fun_prop (discharger := linarith)

lemma scalarUniformConvexity_of_le {p x y : ℝ} (hp : 2 < p) (hxy : x ≤ y) :
    scalarEnergy p y ≥ scalarEnergy p x + scalarJ p x * (y - x) +
      ((2 : ℝ) ^ (2 - p) / p) * |y - x| ^ p := by
  let c : ℝ := (2 : ℝ) ^ (2 - p)
  have hc0 : 0 ≤ c := Real.rpow_nonneg (by norm_num) _
  have hJint : IntervalIntegrable (scalarJ p) MeasureTheory.volume x y :=
    (continuous_scalarJ hp).intervalIntegrable _ _
  have hdiffcont : Continuous (fun t : ℝ ↦ scalarJ p t - scalarJ p x) :=
    (continuous_scalarJ hp).sub continuous_const
  have hdiffint : IntervalIntegrable (fun t : ℝ ↦ scalarJ p t - scalarJ p x)
      MeasureTheory.volume x y := hdiffcont.intervalIntegrable _ _
  have hlowercont : Continuous (fun t : ℝ ↦ c * scalarJ p (t - x)) := by
    exact continuous_const.mul
      ((continuous_scalarJ hp).comp (continuous_id.sub continuous_const))
  have hlowerint : IntervalIntegrable (fun t : ℝ ↦ c * scalarJ p (t - x))
      MeasureTheory.volume x y := hlowercont.intervalIntegrable _ _
  have hpoint : ∀ t ∈ Set.Icc x y,
      c * scalarJ p (t - x) ≤ scalarJ p t - scalarJ p x := by
    intro t ht
    by_cases htx : t = x
    · subst t
      simp [scalarJ]
    · have htxpos : 0 < t - x := sub_pos.mpr (lt_of_le_of_ne ht.1 (Ne.symm htx))
      have hs := scalarJ_strongMonotone (p := p) (u := t) (v := x) hp
      have hjmul : scalarJ p (t - x) * (t - x) = |t - x| ^ p := by
        rw [scalarJ_nonneg hp htxpos.le, abs_of_pos htxpos]
        rw [← Real.rpow_add_one' htxpos.le (by linarith : p - 1 + 1 ≠ 0)]
        congr 1
        ring
      have hmul : (c * scalarJ p (t - x)) * (t - x) ≤
          (scalarJ p t - scalarJ p x) * (t - x) := by
        rw [mul_assoc, hjmul]
        exact hs
      exact (le_of_mul_le_mul_right hmul htxpos)
  have hmono := intervalIntegral.integral_mono_on hxy hlowerint hdiffint hpoint
  have henergy : ∫ t in x..y, scalarJ p t = scalarEnergy p y - scalarEnergy p x :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t _ ↦ hasDerivAt_scalarEnergy hp t) hJint
  have hlowerDeriv : ∀ t ∈ Set.uIcc x y,
      HasDerivAt (fun s : ℝ ↦ c * scalarEnergy p (s - x))
        (c * scalarJ p (t - x)) t := by
    intro t _
    simpa only [Function.comp_apply, id_eq, one_mul, mul_one] using
      ((hasDerivAt_scalarEnergy hp (t - x)).comp t
        ((hasDerivAt_id t).sub_const x) |>.const_mul c)
  have hlower : ∫ t in x..y, c * scalarJ p (t - x) =
      c * scalarEnergy p (y - x) - c * scalarEnergy p (x - x) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hlowerDeriv hlowerint
  rw [hlower, intervalIntegral.integral_sub hJint
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ ↦ scalarJ p x)
      MeasureTheory.volume x y), henergy, intervalIntegral.integral_const] at hmono
  have hp0 : p ≠ 0 := by linarith
  simp [scalarEnergy, scalarJ, c, hp0] at hmono ⊢
  ring_nf at hmono ⊢
  linarith

lemma scalarJ_neg (p x : ℝ) : scalarJ p (-x) = -scalarJ p x := by
  simp only [scalarJ, abs_neg]
  ring

lemma scalarEnergy_neg (p x : ℝ) : scalarEnergy p (-x) = scalarEnergy p x := by
  simp only [scalarEnergy, abs_neg]

lemma scalarUniformConvexity {p x y : ℝ} (hp : 2 < p) :
    scalarEnergy p y ≥ scalarEnergy p x + scalarJ p x * (y - x) +
      ((2 : ℝ) ^ (2 - p) / p) * |y - x| ^ p := by
  rcases le_total x y with hxy | hyx
  · exact scalarUniformConvexity_of_le hp hxy
  · have hneg := scalarUniformConvexity_of_le hp (neg_le_neg hyx)
    rw [scalarEnergy_neg, scalarEnergy_neg, scalarJ_neg] at hneg
    simp only [neg_sub_neg, neg_mul] at hneg
    rw [abs_sub_comm] at hneg
    convert hneg using 1
    ring_nf

lemma lpNorm_rpow_eq_lpPower {p : ℝ} (hp : p ≠ 0) {d : ℕ} (z : Point d) :
    (lpNorm p z) ^ p = lpPower p z := by
  unfold lpNorm
  rw [one_div]
  exact Real.rpow_inv_rpow (lpPower_nonneg p z) hp

theorem pUniformConvexity {p : ℝ} (hp : 2 < p) {d : ℕ}
    (x y c : Point d) :
    uniformRegularizer p c y ≥
      uniformRegularizer p c x + pairing (powerDualityMap p (x - c)) (y - x) +
        (2 ^ (2 - p) / p) * (lpNorm p (y - x)) ^ p := by
  have hsum := Finset.sum_le_sum fun i (_hi : i ∈ Finset.univ) ↦
    scalarUniformConvexity (p := p) (x := (x - c) i) (y := (y - c) i) hp
  rw [lpNorm_rpow_eq_lpPower (by linarith : p ≠ 0)]
  simpa only [uniformRegularizer, lpPower, pairing, powerDualityMap,
    scalarEnergy, scalarJ, Pi.sub_apply, Finset.sum_add_distrib,
    Finset.sum_mul, Finset.mul_sum, div_eq_mul_inv,
    sub_sub_sub_cancel_right, mul_comm, mul_left_comm, mul_assoc,
    one_mul, mul_one, add_comm, add_left_comm, add_assoc] using hsum

end O3.Experimental

namespace O3

/-- Frozen TeX Lemma `lem:puniform`, proved for every real `p > 2` and every
finite dimension with the source-exact constant. -/
theorem pUniformConvexity : PUniformConvexityStatement := by
  intro p hp d x y c
  exact Experimental.pUniformConvexity hp x y c

end O3
