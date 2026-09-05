/-
Copyright (c) 2024 Sidharth Hariharan and 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Sidharth Hariharan, Gareth Ma, Dean Cureton
-/

module

import all LeanPool.SpherePacking.Foundations
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Real.Pi.Wallis
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.TotallySplit
import Mathlib.Tactic.Monotonicity.Lemmas
import Mathlib.Topology.Sheaves.Presheaf

/-!
# MellinAnalysis

Mellin inversion and lower-contour estimates.
-/

namespace CohnElkies

section

open Filter Set MeasureTheory intervalIntegral
open scoped Interval Topology

private theorem saddleCauchyPole_symmetric_intervalIntegral_tendsto_pos
    {a : ℝ} (ha : 0 < a) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹)
      Filter.atTop (𝓝 (Real.pi : ℂ)) := by
  have hdiv : Tendsto (fun T : ℝ => T / a)
      Filter.atTop Filter.atTop :=
    (tendsto_div_const_atTop_of_pos ha).2 tendsto_id
  have hatan : Tendsto
      (fun T : ℝ => Real.arctan (T / a))
      Filter.atTop (𝓝 (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atTop).comp hdiv
  have hreal : Tendsto
      (fun T : ℝ => 2 * Real.arctan (T / a))
      Filter.atTop (𝓝 Real.pi) := by
    convert! (tendsto_const_nhds.mul hatan) using 1
    all_goals ring_nf
  have hcomplex : Tendsto
      (fun T : ℝ =>
        ((2 * Real.arctan (T / a) : ℝ) : ℂ))
      Filter.atTop (𝓝 (Real.pi : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hreal
  exact hcomplex.congr'
    (Filter.Eventually.of_forall
      (fun T : ℝ =>
        (saddleCauchyPole_symmetric_intervalIntegral
          ha.ne' T).symm))

private theorem saddleCauchyPole_symmetric_intervalIntegral_tendsto_neg
    {a : ℝ} (ha : a < 0) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          ((a : ℂ) + (t : ℂ) * Complex.I)⁻¹)
      Filter.atTop (𝓝 (-(Real.pi : ℂ))) := by
  have hdiv : Tendsto (fun T : ℝ => T / a)
      Filter.atTop Filter.atBot :=
    (tendsto_div_const_atBot_of_neg ha).2 tendsto_id
  have hatan : Tendsto
      (fun T : ℝ => Real.arctan (T / a))
      Filter.atTop (𝓝 (-(Real.pi / 2))) :=
    (tendsto_nhds_of_tendsto_nhdsWithin
      Real.tendsto_arctan_atBot).comp hdiv
  have hreal : Tendsto
      (fun T : ℝ => 2 * Real.arctan (T / a))
      Filter.atTop (𝓝 (-Real.pi)) := by
    convert! (tendsto_const_nhds.mul hatan) using 1
    all_goals ring_nf
  have hcomplex : Tendsto
      (fun T : ℝ =>
        ((2 * Real.arctan (T / a) : ℝ) : ℂ))
      Filter.atTop (𝓝 (-(Real.pi : ℂ))) := by
    simpa only [Function.comp_apply, Complex.ofReal_neg] using!
      (Complex.continuous_ofReal.continuousAt.tendsto.comp
        hreal)
  exact hcomplex.congr'
    (Filter.Eventually.of_forall
      (fun T : ℝ =>
        (saddleCauchyPole_symmetric_intervalIntegral
          ha.ne T).symm))

private theorem saddleShiftedCauchyPole_symmetric_intervalIntegral_tendsto_pos
    (n : ℕ) {a : ℝ}
    (ha : -((2 * n : ℕ) : ℝ) < a) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          (((a : ℂ) + (t : ℂ) * Complex.I +
            ((2 * n : ℕ) : ℂ))⁻¹))
      Filter.atTop (𝓝 (Real.pi : ℂ)) := by
  have hshift : 0 < a + ((2 * n : ℕ) : ℝ) := by
    linarith
  have hlimit :=
    saddleCauchyPole_symmetric_intervalIntegral_tendsto_pos
      hshift
  apply hlimit.congr'
  filter_upwards [] with T
  apply intervalIntegral.integral_congr
  intro t _
  push_cast
  ring

private theorem saddleShiftedCauchyPole_symmetric_intervalIntegral_tendsto_neg
    (n : ℕ) {a : ℝ}
    (ha : a < -((2 * n : ℕ) : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          (((a : ℂ) + (t : ℂ) * Complex.I +
            ((2 * n : ℕ) : ℂ))⁻¹))
      Filter.atTop (𝓝 (-(Real.pi : ℂ))) := by
  have hshift : a + ((2 * n : ℕ) : ℝ) < 0 := by
    linarith
  have hlimit :=
    saddleCauchyPole_symmetric_intervalIntegral_tendsto_neg
      hshift
  apply hlimit.congr'
  filter_upwards [] with T
  apply intervalIntegral.integral_congr
  intro t _
  push_cast
  ring

private theorem saddleGaussianPoleRepresentative_eq_inv_add_slope
    (n : ℕ) {z : ℂ}
    (hz : z + ((2 * n : ℕ) : ℂ) ≠ 0) :
    saddleGaussianPoleRepresentative n z =
      (z + ((2 * n : ℕ) : ℂ))⁻¹ +
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ)) := by
  rw [saddleGaussianPoleSlope_eq_of_ne hz]
  unfold saddleGaussianPoleRepresentative
  field_simp [hz]
  all_goals ring

private theorem saddleGaussianPoleShiftedSlope_differentiable
    (n : ℕ) :
    Differentiable ℂ
      (fun z : ℂ =>
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ))) :=
  saddleGaussianPoleSlope_differentiable.comp
    (by fun_prop)

private theorem saddleGaussianPoleShiftedSlope_boundary_rectangle
    (n : ℕ) (A B T : ℝ) :
    (∫ a in A..B,
      saddleGaussianPoleSlope
        ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ))) -
    (∫ a in A..B,
      saddleGaussianPoleSlope
        ((a : ℂ) + (T : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ))) +
    Complex.I *
      (∫ t in -T..T,
        saddleGaussianPoleSlope
          ((B : ℂ) + (t : ℂ) * Complex.I +
            ((2 * n : ℕ) : ℂ))) -
    Complex.I *
      (∫ t in -T..T,
        saddleGaussianPoleSlope
          ((A : ℂ) + (t : ℂ) * Complex.I +
            ((2 * n : ℕ) : ℂ))) = 0 := by
  have hrectangle :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (fun z : ℂ =>
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ)))
      ((A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
      ((B : ℂ) + (T : ℂ) * Complex.I)
      (saddleGaussianPoleShiftedSlope_differentiable
        n).differentiableOn
  simpa only [Complex.ofReal_neg, neg_mul, Nat.cast_mul, Nat.cast_ofNat, Complex.add_im,
    Complex.ofReal_im,
    Complex.neg_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re,
      mul_zero, add_zero,
    zero_add, Complex.add_re, Complex.neg_re, Complex.mul_re, sub_self, neg_zero,
      smul_eq_mul] using! hrectangle

private theorem saddleGaussianPoleShiftedSlope_horizontalIntegral_tendsto_zero
    {A B : ℝ} (hAB : A ≤ B)
    (n : ℕ) (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleSlope
            ((a : ℂ) +
              ((s * T : ℝ) : ℂ) * Complex.I +
                ((2 * n : ℕ) : ℂ)))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hgaussian⟩ :=
    saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
      (r := 1) (by norm_num : (0 : ℝ) < 1) hAB n
  apply saddleHorizontalIntegral_tendsto_zero
    (F := fun z : ℂ =>
      saddleGaussianPoleSlope
        (z + ((2 * n : ℕ) : ℂ)))
    hAB (C := C + 1) ?_ s hs
  intro a ha t ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let q : ℂ := z + ((2 * n : ℕ) : ℂ)
  have hden : |t| ≤ ‖q‖ := by
    try dsimp [q, z]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
        Complex.re_ofNat,
      Complex.natCast_im, Complex.im_ofNat, Complex.natCast_re, zero_mul] using!
      (Complex.abs_im_le_norm
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)))
  have hqpos : 0 < ‖q‖ :=
    (lt_of_lt_of_le zero_lt_one ht).trans_le hden
  have hq : q ≠ 0 := norm_pos_iff.mp hqpos
  have hpole : |t| * ‖q⁻¹‖ ≤ 1 := by
    rw [norm_inv, ← div_eq_mul_inv]
    exact (div_le_one hqpos).2 hden
  have hgaussian' :
      |t| * ‖saddleGaussianPoleRepresentative n z‖ ≤ C := by
    simpa only [saddleMellinInversePower, Complex.ofReal_one, neg_add_rev, Complex.one_cpow,
      one_mul] using!
      hgaussian a ha t ht
  have hslope :
      saddleGaussianPoleSlope q =
        saddleGaussianPoleRepresentative n z - q⁻¹ := by
    have hsplit :=
      saddleGaussianPoleRepresentative_eq_inv_add_slope
        n (z := z)
        (show z + ((2 * n : ℕ) : ℂ) ≠ 0 from hq)
    change saddleGaussianPoleRepresentative n z =
      q⁻¹ + saddleGaussianPoleSlope q at hsplit
    apply (eq_sub_iff_add_eq).2
    simpa only [Nat.cast_mul, Nat.cast_ofNat, add_comm] using! hsplit.symm
  change |t| * ‖saddleGaussianPoleSlope q‖ ≤ C + 1
  rw [hslope]
  calc
    |t| *
        ‖saddleGaussianPoleRepresentative n z - q⁻¹‖ ≤
      |t| *
        (‖saddleGaussianPoleRepresentative n z‖ +
          ‖q⁻¹‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = |t| * ‖saddleGaussianPoleRepresentative n z‖ +
      |t| * ‖q⁻¹‖ := by
        ring
    _ ≤ C + 1 := add_le_add hgaussian' hpole

private theorem saddleInfiniteRectangle_vertical_limit_eq
    {F : ℂ → ℂ} {A B : ℝ} {u v : ℂ}
    (hleft : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          F ((A : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (𝓝 u))
    (hright : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          F ((B : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (𝓝 v))
    (hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0))
    (hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0))
    (hrectangle : ∀ T : ℝ,
      (∫ a in A..B,
        F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
      (∫ a in A..B,
        F ((a : ℂ) + (T : ℂ) * Complex.I)) +
      Complex.I *
        (∫ t in -T..T,
          F ((B : ℂ) + (t : ℂ) * Complex.I)) -
      Complex.I *
        (∫ t in -T..T,
          F ((A : ℂ) + (t : ℂ) * Complex.I)) = 0) :
    v = u := by
  have hlimit : Tendsto
      (fun T : ℝ =>
        (∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        (∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I *
          (∫ t in -T..T,
            F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
          (∫ t in -T..T,
            F ((A : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop (𝓝 (Complex.I * v - Complex.I * u)) := by
    simpa only [Complex.ofReal_neg, neg_mul, sub_self, zero_add] using!
      (((hlower.sub hupper).add
        (tendsto_const_nhds.mul hright)).sub
          (tendsto_const_nhds.mul hleft))
  have hzero : Tendsto
      (fun T : ℝ =>
        (∫ a in A..B,
          F ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
        (∫ a in A..B,
          F ((a : ℂ) + (T : ℂ) * Complex.I)) +
        Complex.I *
          (∫ t in -T..T,
            F ((B : ℂ) + (t : ℂ) * Complex.I)) -
        Complex.I *
          (∫ t in -T..T,
            F ((A : ℂ) + (t : ℂ) * Complex.I)))
      Filter.atTop (𝓝 0) :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℝ => (0 : ℂ))
        Filter.atTop (𝓝 0)).congr'
          (Filter.Eventually.of_forall
            (fun T : ℝ => (hrectangle T).symm))
  have hidentity : Complex.I * (v - u) = 0 := by
    simpa only [mul_sub] using!
      (tendsto_nhds_unique hlimit hzero)
  exact sub_eq_zero.mp
    ((mul_eq_zero.mp hidentity).resolve_left
      Complex.I_ne_zero)

private theorem saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral
    (n : ℕ) {a : ℝ}
    (ha : a ≠ -((2 * n : ℕ) : ℝ)) (T : ℝ) :
    (∫ t in -T..T,
      saddleGaussianPoleSlope
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ))) =
    (∫ t in -T..T,
      saddleGaussianPoleRepresentative n
        ((a : ℂ) + (t : ℂ) * Complex.I)) -
    (∫ t in -T..T,
      (((a : ℂ) + (t : ℂ) * Complex.I +
        ((2 * n : ℕ) : ℂ))⁻¹)) := by
  have hline : Continuous
      (fun t : ℝ =>
        (a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)) := by
    fun_prop
  have hnonzero : ∀ t : ℝ,
      (a : ℂ) + (t : ℂ) * Complex.I +
        ((2 * n : ℕ) : ℂ) ≠ 0 := by
    intro t hzero
    apply ha
    have hre := congrArg Complex.re hzero
    norm_num [Complex.mul_re] at hre
    push_cast
    linarith
  have hgaussian : IntervalIntegrable
      (fun t : ℝ =>
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I))
      volume (-T) T :=
    (saddleGaussianPoleRepresentative_shiftedLine_continuous
      n ha).intervalIntegrable _ _
  have hpole : IntervalIntegrable
      (fun t : ℝ =>
        (((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ))⁻¹))
      volume (-T) T :=
    (hline.inv₀ hnonzero).intervalIntegrable _ _
  rw [← intervalIntegral.integral_sub hgaussian hpole]
  apply intervalIntegral.integral_congr
  intro t _
  have hsplit :=
    saddleGaussianPoleRepresentative_eq_inv_add_slope
      n (hnonzero t)
  apply (eq_sub_iff_add_eq).2
  simpa only [Nat.cast_mul, Nat.cast_ofNat, add_comm] using! hsplit.symm

private theorem saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral_tendsto_pos
    (n : ℕ) {a : ℝ}
    (ha : -((2 * n : ℕ) : ℝ) < a) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          saddleGaussianPoleSlope
            ((a : ℂ) + (t : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)))
      Filter.atTop
      (𝓝 ((∫ t : ℝ,
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) -
        (Real.pi : ℂ))) := by
  have hane : a ≠ -((2 * n : ℕ) : ℝ) :=
    ne_of_gt ha
  have hgaussian : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (𝓝 (∫ t : ℝ,
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral
      (saddleGaussianPoleRepresentative_shiftedLine_integrable
        n hane)
      tendsto_neg_atTop_atBot tendsto_id
  have hpole :=
    saddleShiftedCauchyPole_symmetric_intervalIntegral_tendsto_pos
      n ha
  exact (hgaussian.sub hpole).congr'
    (Filter.Eventually.of_forall
      (fun T : ℝ =>
        (saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral
          n hane T).symm))

private theorem saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral_tendsto_neg
    (n : ℕ) {a : ℝ}
    (ha : a < -((2 * n : ℕ) : ℝ)) :
    Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          saddleGaussianPoleSlope
            ((a : ℂ) + (t : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)))
      Filter.atTop
      (𝓝 ((∫ t : ℝ,
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) -
        (-(Real.pi : ℂ)))) := by
  have hane : a ≠ -((2 * n : ℕ) : ℝ) :=
    ne_of_lt ha
  have hgaussian : Tendsto
      (fun T : ℝ =>
        ∫ t in -T..T,
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop
      (𝓝 (∫ t : ℝ,
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I))) :=
    intervalIntegral_tendsto_integral
      (saddleGaussianPoleRepresentative_shiftedLine_integrable
        n hane)
      tendsto_neg_atTop_atBot tendsto_id
  have hpole :=
    saddleShiftedCauchyPole_symmetric_intervalIntegral_tendsto_neg
      n ha
  exact (hgaussian.sub hpole).congr'
    (Filter.Eventually.of_forall
      (fun T : ℝ =>
        (saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral
          n hane T).symm))

private theorem saddleGaussianPoleRepresentative_vertical_integral_jump
    (n : ℕ) {A B : ℝ}
    (hA : A < -((2 * n : ℕ) : ℝ))
    (hB : -((2 * n : ℕ) : ℝ) < B) :
    (∫ t : ℝ,
      saddleGaussianPoleRepresentative n
        ((B : ℂ) + (t : ℂ) * Complex.I)) -
    (∫ t : ℝ,
      saddleGaussianPoleRepresentative n
        ((A : ℂ) + (t : ℂ) * Complex.I)) =
      ((2 * Real.pi : ℝ) : ℂ) := by
  have hAB : A ≤ B := (hA.trans hB).le
  have hleft :=
    saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral_tendsto_neg
      n hA
  have hright :=
    saddleGaussianPoleShiftedSlope_symmetric_intervalIntegral_tendsto_pos
      n hB
  have hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleSlope
            ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)))
      Filter.atTop (𝓝 0) := by
    simpa only [Complex.ofReal_neg, neg_mul, Nat.cast_mul, Nat.cast_ofNat, one_mul] using!
      saddleGaussianPoleShiftedSlope_horizontalIntegral_tendsto_zero
        hAB n (-1) (by norm_num)
  have hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleSlope
            ((a : ℂ) + (T : ℂ) * Complex.I +
              ((2 * n : ℕ) : ℂ)))
      Filter.atTop (𝓝 0) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, one_mul] using!
      saddleGaussianPoleShiftedSlope_horizontalIntegral_tendsto_zero
        hAB n 1 (by norm_num)
  have hidentity :=
    saddleInfiniteRectangle_vertical_limit_eq
      (F := fun z : ℂ =>
        saddleGaussianPoleSlope
          (z + ((2 * n : ℕ) : ℂ)))
      hleft hright hlower hupper
      (fun T : ℝ =>
        saddleGaussianPoleShiftedSlope_boundary_rectangle
          n A B T)
  push_cast
  linear_combination hidentity

private theorem saddleMellinInversePower_negativeEvenPole
    (r : ℝ) (n : ℕ) :
    saddleMellinInversePower r
      (-((2 * n : ℕ) : ℂ)) =
      ((r ^ (2 * n) : ℝ) : ℂ) := by
  unfold saddleMellinInversePower
  rw [neg_neg, Complex.cpow_natCast]
  exact (Complex.ofReal_pow r (2 * n)).symm

private noncomputable def saddleMellinInversePowerPoleSlope
    (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  dslope (saddleMellinInversePower r)
    (-((2 * n : ℕ) : ℂ)) z

private theorem saddleMellinInversePowerPoleSlope_differentiable
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Differentiable ℂ
      (saddleMellinInversePowerPoleSlope r n) := by
  unfold saddleMellinInversePowerPoleSlope
  exact differentiableOn_univ.mp
    ((Complex.differentiableOn_dslope
      (s := Set.univ)
      (c := -((2 * n : ℕ) : ℂ))
      (show Set.univ ∈ 𝓝 (-((2 * n : ℕ) : ℂ))
        from univ_mem)).mpr
      (saddleMellinInversePower_differentiable
        hr).differentiableOn)

private noncomputable def saddleGaussianPoleWeightedCorrection
    (r : ℝ) (n : ℕ) (z : ℂ) : ℂ :=
  Complex.exp ((z + ((2 * n : ℕ) : ℂ)) ^ 2) *
    saddleMellinInversePowerPoleSlope r n z

private theorem saddleGaussianPoleWeightedCorrection_differentiable
    {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Differentiable ℂ
      (saddleGaussianPoleWeightedCorrection r n) := by
  unfold saddleGaussianPoleWeightedCorrection
  have hgaussian : Differentiable ℂ
      (fun z : ℂ =>
        Complex.exp ((z + ((2 * n : ℕ) : ℂ)) ^ 2)) := by
    fun_prop
  exact hgaussian.mul
    (saddleMellinInversePowerPoleSlope_differentiable
      hr n)

private theorem saddleGaussianPoleWeightedRepresentative_eq_pole_add_correction
    {r : ℝ} (n : ℕ) {z : ℂ}
    (hz : z + ((2 * n : ℕ) : ℂ) ≠ 0) :
    saddleMellinInversePower r z *
        saddleGaussianPoleRepresentative n z =
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        saddleGaussianPoleRepresentative n z +
      saddleGaussianPoleWeightedCorrection r n z := by
  let p : ℂ := -((2 * n : ℕ) : ℂ)
  let q : ℂ := z + ((2 * n : ℕ) : ℂ)
  have hslope :=
    sub_smul_dslope (saddleMellinInversePower r) p z
  have hcoordinate : z - p = q := by
    try dsimp [p, q]
    ring
  rw [hcoordinate, smul_eq_mul] at hslope
  have hdiv :
      saddleMellinInversePowerPoleSlope r n z =
        (saddleMellinInversePower r z -
          saddleMellinInversePower r p) / q := by
    apply (eq_div_iff (show q ≠ 0 from hz)).2
    unfold saddleMellinInversePowerPoleSlope
    change dslope (saddleMellinInversePower r) p z * q =
      saddleMellinInversePower r z -
        saddleMellinInversePower r p
    simpa only [mul_comm] using! hslope
  unfold saddleGaussianPoleRepresentative
    saddleGaussianPoleWeightedCorrection
  change saddleMellinInversePower r z *
      (Complex.exp (q ^ 2) / q) =
    saddleMellinInversePower r p *
        (Complex.exp (q ^ 2) / q) +
      Complex.exp (q ^ 2) *
        saddleMellinInversePowerPoleSlope r n z
  rw [hdiv]
  field_simp [hz]
  all_goals ring

private theorem saddleGaussianPole_shiftedLine_ne_zero
    (n : ℕ) {a : ℝ}
    (ha : a ≠ -((2 * n : ℕ) : ℝ))
    (t : ℝ) :
    (a : ℂ) + (t : ℂ) * Complex.I +
      ((2 * n : ℕ) : ℂ) ≠ 0 := by
  intro hzero
  apply ha
  have hre := congrArg Complex.re hzero
  norm_num [Complex.mul_re] at hre
  push_cast
  linarith

private theorem saddleGaussianPoleWeightedCorrection_eq_sub
    {r : ℝ} (n : ℕ) {z : ℂ}
    (hz : z + ((2 * n : ℕ) : ℂ) ≠ 0) :
    saddleGaussianPoleWeightedCorrection r n z =
      saddleMellinInversePower r z *
        saddleGaussianPoleRepresentative n z -
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        saddleGaussianPoleRepresentative n z := by
  have hsplit :=
    saddleGaussianPoleWeightedRepresentative_eq_pole_add_correction
      (r := r) n hz
  apply (eq_sub_iff_add_eq).2
  simpa only [Nat.cast_mul, Nat.cast_ofNat, add_comm] using! hsplit.symm

private theorem saddleGaussianPoleWeightedCorrection_shiftedLine_integrable
    {r a : ℝ} (hr : 0 < r)
    (n : ℕ) (ha : a ≠ -((2 * n : ℕ) : ℝ)) :
    Integrable (fun t : ℝ =>
      saddleGaussianPoleWeightedCorrection r n
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hweighted :=
    saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
      n ha hr
  have hunweighted :=
    saddleGaussianPoleRepresentative_shiftedLine_integrable n ha
  have hconstant :=
    hunweighted.const_mul
      (saddleMellinInversePower r
        (-((2 * n : ℕ) : ℂ)))
  apply (hweighted.sub hconstant).congr
  filter_upwards [] with t
  exact
    (saddleGaussianPoleWeightedCorrection_eq_sub
      n (saddleGaussianPole_shiftedLine_ne_zero
        n ha t)).symm

private theorem saddleGaussianPoleWeightedCorrection_horizontalStrip_bound
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B)
    (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ a ∈ Set.Icc A B, ∀ t : ℝ,
        1 ≤ |t| →
          |t| *
            ‖saddleGaussianPoleWeightedCorrection r n
              ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C := by
  obtain ⟨Cw, hCw, hweighted⟩ :=
    saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
      hr hAB n
  obtain ⟨Cu, hCu, hunweighted⟩ :=
    saddleGaussianPoleRepresentative_weighted_horizontalStrip_bound
      (r := 1) (by norm_num : (0 : ℝ) < 1) hAB n
  let p : ℂ := -((2 * n : ℕ) : ℂ)
  refine ⟨Cw + ‖saddleMellinInversePower r p‖ * Cu,
    by positivity, ?_⟩
  intro a ha t ht
  let z : ℂ := (a : ℂ) + (t : ℂ) * Complex.I
  let q : ℂ := z + ((2 * n : ℕ) : ℂ)
  have hden : |t| ≤ ‖q‖ := by
    try dsimp [q, z]
    simpa only [Nat.cast_mul, Nat.cast_ofNat, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
        Complex.re_ofNat,
      Complex.natCast_im, Complex.im_ofNat, Complex.natCast_re, zero_mul] using!
      (Complex.abs_im_le_norm
        ((a : ℂ) + (t : ℂ) * Complex.I +
          ((2 * n : ℕ) : ℂ)))
  have hqpos : 0 < ‖q‖ :=
    (lt_of_lt_of_le zero_lt_one ht).trans_le hden
  have hq : q ≠ 0 := norm_pos_iff.mp hqpos
  have hweighted' :
      |t| *
        ‖saddleMellinInversePower r z *
          saddleGaussianPoleRepresentative n z‖ ≤ Cw := by
    simpa only [Complex.norm_mul] using! hweighted a ha t ht
  have hunweighted' :
      |t| * ‖saddleGaussianPoleRepresentative n z‖ ≤ Cu := by
    simpa only [saddleMellinInversePower, Complex.ofReal_one, neg_add_rev, Complex.one_cpow,
      one_mul] using!
      hunweighted a ha t ht
  have hscaled :
      |t| *
        ‖saddleMellinInversePower r p *
          saddleGaussianPoleRepresentative n z‖ ≤
        ‖saddleMellinInversePower r p‖ * Cu := by
    rw [norm_mul]
    calc
      |t| *
          (‖saddleMellinInversePower r p‖ *
            ‖saddleGaussianPoleRepresentative n z‖) =
        ‖saddleMellinInversePower r p‖ *
          (|t| * ‖saddleGaussianPoleRepresentative n z‖) := by
          ring
      _ ≤ ‖saddleMellinInversePower r p‖ * Cu :=
        mul_le_mul_of_nonneg_left hunweighted'
          (norm_nonneg _)
  have hcorrection :=
    saddleGaussianPoleWeightedCorrection_eq_sub
      (r := r) n (z := z)
      (show z + ((2 * n : ℕ) : ℂ) ≠ 0 from hq)
  change |t| * ‖saddleGaussianPoleWeightedCorrection r n z‖ ≤
    Cw + ‖saddleMellinInversePower r p‖ * Cu
  rw [hcorrection]
  change |t| *
      ‖saddleMellinInversePower r z *
        saddleGaussianPoleRepresentative n z -
        saddleMellinInversePower r p *
          saddleGaussianPoleRepresentative n z‖ ≤
    Cw + ‖saddleMellinInversePower r p‖ * Cu
  calc
    |t| *
        ‖saddleMellinInversePower r z *
          saddleGaussianPoleRepresentative n z -
          saddleMellinInversePower r p *
            saddleGaussianPoleRepresentative n z‖ ≤
      |t| *
        (‖saddleMellinInversePower r z *
            saddleGaussianPoleRepresentative n z‖ +
          ‖saddleMellinInversePower r p *
            saddleGaussianPoleRepresentative n z‖) := by
        gcongr
        exact norm_sub_le _ _
    _ = |t| *
          ‖saddleMellinInversePower r z *
            saddleGaussianPoleRepresentative n z‖ +
        |t| *
          ‖saddleMellinInversePower r p *
            saddleGaussianPoleRepresentative n z‖ := by
        ring
    _ ≤ Cw + ‖saddleMellinInversePower r p‖ * Cu :=
      add_le_add hweighted' hscaled

private theorem saddleGaussianPoleWeightedCorrection_horizontalIntegral_tendsto_zero
    {r A B : ℝ} (hr : 0 < r) (hAB : A ≤ B)
    (n : ℕ) (s : ℝ) (hs : |s| = 1) :
    Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) +
              ((s * T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ :=
    saddleGaussianPoleWeightedCorrection_horizontalStrip_bound
      hr hAB n
  exact saddleHorizontalIntegral_tendsto_zero
    (F := saddleGaussianPoleWeightedCorrection r n)
    hAB hbound s hs

private theorem saddleGaussianPoleWeightedCorrection_boundary_rectangle
    {r : ℝ} (hr : 0 < r)
    (n : ℕ) (A B T : ℝ) :
    (∫ a in A..B,
      saddleGaussianPoleWeightedCorrection r n
        ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)) -
    (∫ a in A..B,
      saddleGaussianPoleWeightedCorrection r n
        ((a : ℂ) + (T : ℂ) * Complex.I)) +
    Complex.I *
      (∫ t in -T..T,
        saddleGaussianPoleWeightedCorrection r n
          ((B : ℂ) + (t : ℂ) * Complex.I)) -
    Complex.I *
      (∫ t in -T..T,
        saddleGaussianPoleWeightedCorrection r n
          ((A : ℂ) + (t : ℂ) * Complex.I)) = 0 := by
  have hrectangle :=
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn
      (saddleGaussianPoleWeightedCorrection r n)
      ((A : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
      ((B : ℂ) + (T : ℂ) * Complex.I)
      (saddleGaussianPoleWeightedCorrection_differentiable
        hr n).differentiableOn
  simpa only [Complex.ofReal_neg, neg_mul, Complex.add_im, Complex.ofReal_im, Complex.neg_im,
    Complex.mul_im,
    Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add,
      Complex.add_re,
    Complex.neg_re, Complex.mul_re, sub_self, neg_zero, smul_eq_mul] using! hrectangle

private theorem saddleGaussianPoleWeightedCorrection_vertical_integral_eq
    {r A B : ℝ} (hr : 0 < r)
    (n : ℕ) (hAB : A ≤ B)
    (hA : A ≠ -((2 * n : ℕ) : ℝ))
    (hB : B ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      saddleGaussianPoleWeightedCorrection r n
        ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleGaussianPoleWeightedCorrection r n
        ((A : ℂ) + (t : ℂ) * Complex.I)) := by
  have hleft :=
    saddleGaussianPoleWeightedCorrection_shiftedLine_integrable
      hr n hA
  have hright :=
    saddleGaussianPoleWeightedCorrection_shiftedLine_integrable
      hr n hB
  have hlower : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) + ((-T : ℝ) : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa only [Complex.ofReal_neg, neg_mul, one_mul] using!
      saddleGaussianPoleWeightedCorrection_horizontalIntegral_tendsto_zero
        hr hAB n (-1) (by norm_num)
  have hupper : Tendsto
      (fun T : ℝ =>
        ∫ a in A..B,
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) + (T : ℂ) * Complex.I))
      Filter.atTop (𝓝 0) := by
    simpa only [one_mul] using!
      saddleGaussianPoleWeightedCorrection_horizontalIntegral_tendsto_zero
        hr hAB n 1 (by norm_num)
  exact saddleInfiniteRectangle_vertical_integral_eq
    hleft hright hlower hupper
    (fun T : ℝ =>
      saddleGaussianPoleWeightedCorrection_boundary_rectangle
        hr n A B T)

private theorem saddleGaussianPoleWeightedRepresentative_shiftedLine_integral_eq
    {r a : ℝ} (hr : 0 < r)
    (n : ℕ) (ha : a ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) =
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        (∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I)) +
        (∫ t : ℝ,
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hrepresentative :=
    saddleGaussianPoleRepresentative_shiftedLine_integrable n ha
  have hconstant :=
    hrepresentative.const_mul
      (saddleMellinInversePower r
        (-((2 * n : ℕ) : ℂ)))
  have hcorrection :=
    saddleGaussianPoleWeightedCorrection_shiftedLine_integrable
      hr n ha
  calc
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ,
        saddleMellinInversePower r
            (-((2 * n : ℕ) : ℂ)) *
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I) +
          saddleGaussianPoleWeightedCorrection r n
            ((a : ℂ) + (t : ℂ) * Complex.I) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with t
          exact
            saddleGaussianPoleWeightedRepresentative_eq_pole_add_correction
              (r := r) n
              (saddleGaussianPole_shiftedLine_ne_zero
                n ha t)
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
            (-((2 * n : ℕ) : ℂ)) *
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ t : ℝ,
        saddleGaussianPoleWeightedCorrection r n
          ((a : ℂ) + (t : ℂ) * Complex.I)) :=
      integral_add hconstant hcorrection
    _ =
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        (∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I)) +
      (∫ t : ℝ,
        saddleGaussianPoleWeightedCorrection r n
          ((a : ℂ) + (t : ℂ) * Complex.I)) := by
        rw [integral_const_mul_of_integrable hrepresentative]

private theorem saddleGaussianPoleWeightedRepresentative_vertical_integral_jump
    {r A B : ℝ} (hr : 0 < r)
    (n : ℕ)
    (hA : A < -((2 * n : ℕ) : ℝ))
    (hB : -((2 * n : ℕ) : ℝ) < B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((B : ℂ) + (t : ℂ) * Complex.I)) -
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((A : ℂ) + (t : ℂ) * Complex.I) *
        saddleGaussianPoleRepresentative n
          ((A : ℂ) + (t : ℂ) * Complex.I)) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ((r ^ (2 * n) : ℝ) : ℂ) := by
  have hAB : A ≤ B := (hA.trans hB).le
  have hAne : A ≠ -((2 * n : ℕ) : ℝ) :=
    ne_of_lt hA
  have hBne : B ≠ -((2 * n : ℕ) : ℝ) :=
    ne_of_gt hB
  rw [saddleGaussianPoleWeightedRepresentative_shiftedLine_integral_eq
    hr n hBne,
    saddleGaussianPoleWeightedRepresentative_shiftedLine_integral_eq
      hr n hAne]
  have hcorrection :=
    saddleGaussianPoleWeightedCorrection_vertical_integral_eq
      hr n hAB hAne hBne
  have hgaussian :=
    saddleGaussianPoleRepresentative_vertical_integral_jump
      n hA hB
  calc
    saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        (∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((B : ℂ) + (t : ℂ) * Complex.I)) +
        (∫ t : ℝ,
          saddleGaussianPoleWeightedCorrection r n
            ((B : ℂ) + (t : ℂ) * Complex.I)) -
      (saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        (∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
        (∫ t : ℝ,
          saddleGaussianPoleWeightedCorrection r n
            ((A : ℂ) + (t : ℂ) * Complex.I))) =
      saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        ((∫ t : ℝ,
          saddleGaussianPoleRepresentative n
            ((B : ℂ) + (t : ℂ) * Complex.I)) -
          (∫ t : ℝ,
            saddleGaussianPoleRepresentative n
              ((A : ℂ) + (t : ℂ) * Complex.I))) := by
        rw [hcorrection]
        ring
    _ = saddleMellinInversePower r
          (-((2 * n : ℕ) : ℂ)) *
        ((2 * Real.pi : ℝ) : ℂ) := by
        rw [hgaussian]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ((r ^ (2 * n) : ℝ) : ℂ) := by
        rw [saddleMellinInversePower_negativeEvenPole]
        ring

private theorem saddleFiniteGaussianPoleWeighted_shiftedLine_integrable
    {r a : ℝ} (hr : 0 < r)
    (c : ℕ → ℂ) (N : ℕ)
    (ha : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    Integrable (fun t : ℝ =>
      ∑ n ∈ Finset.range (N + 1),
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (c n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) := by
  apply integrable_finsetSum
  intro n _
  have hterm :=
    (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
      n (ha n) hr).const_mul (c n)
  exact hterm.congr
    (Filter.Eventually.of_forall
      (fun t : ℝ => by ring))

private theorem saddleFiniteGaussianPoleWeighted_shiftedLine_integral
    {r a : ℝ} (hr : 0 < r)
    (c : ℕ → ℂ) (N : ℕ)
    (ha : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      ∑ n ∈ Finset.range (N + 1),
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (c n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) =
      ∑ n ∈ Finset.range (N + 1),
        c n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hterm (n : ℕ) :
      Integrable (fun t : ℝ =>
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          (c n *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I))) := by
    have h :=
      (saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
        n (ha n) hr).const_mul (c n)
    exact h.congr
      (Filter.Eventually.of_forall
        (fun t : ℝ => by ring))
  rw [MeasureTheory.integral_finsetSum
    (Finset.range (N + 1))
      (fun n _ => hterm n)]
  apply Finset.sum_congr rfl
  intro n _
  have hweighted :=
    saddleGaussianPoleRepresentative_shiftedLine_weighted_integrable
      n (ha n) hr
  calc
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        (c n *
          saddleGaussianPoleRepresentative n
            ((a : ℂ) + (t : ℂ) * Complex.I))) =
      ∫ t : ℝ,
        c n *
          (saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        ring
    _ = c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((a : ℂ) + (t : ℂ) * Complex.I)) :=
      integral_const_mul_of_integrable hweighted

private theorem plusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
    {ε ℓ a r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < a)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hdata :=
    plusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder hpole hr
  have hsum :=
    saddleFiniteGaussianPoleWeighted_shiftedLine_integrable
      hr (plusSaddlePoleResidue ε ℓ) N hpole
  calc
    (∫ t : ℝ,
      plusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ,
        saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I) -
        ∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            (plusSaddlePoleResidue ε ℓ n *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with t
          have hz :
              (a : ℂ) + (t : ℂ) * Complex.I ∈
                saddleFinitePoleHalfPlane N := by
            change -(2 * ((N : ℝ) + 1)) <
              ((a : ℂ) + (t : ℂ) * Complex.I).re
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
              mul_zero, Complex.ofReal_im,
              Complex.I_im, mul_one, sub_self, add_zero] using! hhalf
          unfold plusSaddleFiniteRapidContourIntegrand
          rw [plusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
            hε horder ℓ N hz
              (saddleShiftedLine_ne_pole hpole t)]
          unfold plusSaddleFiniteRapidPoleSubtraction
          rw [mul_sub, Finset.mul_sum]
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ,
        ∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            (plusSaddlePoleResidue ε ℓ n *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I))) :=
      MeasureTheory.integral_sub hdata hsum
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
        rw [saddleFiniteGaussianPoleWeighted_shiftedLine_integral
          hr (plusSaddlePoleResidue ε ℓ) N hpole]

private theorem minusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
    {ε ℓ a r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < a)
    (hpole : ∀ n : ℕ, a ≠ -((2 * n : ℕ) : ℝ)) :
    (∫ t : ℝ,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
  have hdata :=
    minusSaddleMellinData_shiftedLine_weighted_integrable
      hε hℓ horder hpole hr
  have hsum :=
    saddleFiniteGaussianPoleWeighted_shiftedLine_integrable
      hr (minusSaddlePoleResidue ε ℓ) N hpole
  calc
    (∫ t : ℝ,
      minusSaddleFiniteRapidContourIntegrand ε ℓ N r
        ((a : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t : ℝ,
        saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I) -
        ∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            (minusSaddlePoleResidue ε ℓ n *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [] with t
          have hz :
              (a : ℂ) + (t : ℂ) * Complex.I ∈
                saddleFinitePoleHalfPlane N := by
            change -(2 * ((N : ℝ) + 1)) <
              ((a : ℂ) + (t : ℂ) * Complex.I).re
            simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
              mul_zero, Complex.ofReal_im,
              Complex.I_im, mul_one, sub_self, add_zero] using! hhalf
          unfold minusSaddleFiniteRapidContourIntegrand
          rw [minusSaddleFiniteRapidPoleRegularPart_eq_subtraction_of_not_pole
            hε horder ℓ N hz
              (saddleShiftedLine_ne_pole hpole t)]
          unfold minusSaddleFiniteRapidPoleSubtraction
          rw [mul_sub, Finset.mul_sum]
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      (∫ t : ℝ,
        ∑ n ∈ Finset.range (N + 1),
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
            (minusSaddlePoleResidue ε ℓ n *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I))) :=
      MeasureTheory.integral_sub hdata hsum
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((a : ℂ) + (t : ℂ) * Complex.I)) -
      ∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((a : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((a : ℂ) + (t : ℂ) * Complex.I)) := by
        rw [saddleFiniteGaussianPoleWeighted_shiftedLine_integral
          hr (minusSaddlePoleResidue ε ℓ) N hpole]

private theorem saddleFiniteGaussianPoleWeighted_vertical_integral_jump
    {r A B : ℝ} (hr : 0 < r)
    (c : ℕ → ℂ) (N : ℕ)
    (hcross : ∀ n ∈ Finset.range (N + 1),
      A < -((2 * n : ℕ) : ℝ) ∧
        -((2 * n : ℕ) : ℝ) < B) :
    (∑ n ∈ Finset.range (N + 1),
      c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((B : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((B : ℂ) + (t : ℂ) * Complex.I))) -
    (∑ n ∈ Finset.range (N + 1),
      c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((A : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((A : ℂ) + (t : ℂ) * Complex.I))) =
      ((2 * Real.pi : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (N + 1),
          c n * ((r ^ (2 * n) : ℝ) : ℂ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ n ∈ Finset.range (N + 1),
      (c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((B : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((B : ℂ) + (t : ℂ) * Complex.I)) -
       c n *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((A : ℂ) + (t : ℂ) * Complex.I) *
            saddleGaussianPoleRepresentative n
              ((A : ℂ) + (t : ℂ) * Complex.I)))) =
      ∑ n ∈ Finset.range (N + 1),
        c n *
          ((∫ t : ℝ,
            saddleMellinInversePower r
              ((B : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((B : ℂ) + (t : ℂ) * Complex.I)) -
           (∫ t : ℝ,
            saddleMellinInversePower r
              ((A : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((A : ℂ) + (t : ℂ) * Complex.I))) := by
        apply Finset.sum_congr rfl
        intro n _
        ring
    _ =
      ∑ n ∈ Finset.range (N + 1),
        c n *
          (((2 * Real.pi : ℝ) : ℂ) *
            ((r ^ (2 * n) : ℝ) : ℂ)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [saddleGaussianPoleWeightedRepresentative_vertical_integral_jump
          hr n (hcross n hn).1 (hcross n hn).2]
    _ = ((2 * Real.pi : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (N + 1),
          c n * ((r ^ (2 * n) : ℝ) : ℂ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring

private theorem plusSaddleMellinData_vertical_integral_residue_expansion
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -((2 * n : ℕ) : ℝ))
    (hBpole : ∀ n : ℕ, B ≠ -((2 * n : ℕ) : ℝ))
    (hcross : ∀ n ∈ Finset.range (N + 1),
      A < -((2 * n : ℕ) : ℝ) ∧
        -((2 * n : ℕ) : ℝ) < B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((A : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((A : ℂ) + (t : ℂ) * Complex.I)) +
      ((2 * Real.pi : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (N + 1),
          plusSaddlePoleResidue ε ℓ n *
            ((r ^ (2 * n) : ℝ) : ℂ) := by
  have hhalfB : -(2 * ((N : ℝ) + 1)) < B :=
    hhalf.trans_le hAB
  have hcontour :=
    plusSaddleFiniteRapidContourIntegrand_vertical_integral_eq
      hε hℓ horder hr N hhalf hAB hApole hBpole
  rw [plusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
        hε hℓ horder hr N hhalfB hBpole,
      plusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
        hε hℓ horder hr N hhalf hApole]
    at hcontour
  have hsum :=
    saddleFiniteGaussianPoleWeighted_vertical_integral_jump
      hr (plusSaddlePoleResidue ε ℓ) N hcross
  calc
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
      ((∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((B : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((B : ℂ) + (t : ℂ) * Complex.I))) -
       (∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((A : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((A : ℂ) + (t : ℂ) * Complex.I)))) := by
        linear_combination hcontour
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
          plusSaddleMellinData ε ℓ
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
        ((2 * Real.pi : ℝ) : ℂ) *
          ∑ n ∈ Finset.range (N + 1),
            plusSaddlePoleResidue ε ℓ n *
              ((r ^ (2 * n) : ℝ) : ℂ) := by
          rw [hsum]

private theorem minusSaddleMellinData_vertical_integral_residue_expansion
    {ε ℓ r A B : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ)
    (hhalf : -(2 * ((N : ℝ) + 1)) < A)
    (hAB : A ≤ B)
    (hApole : ∀ n : ℕ, A ≠ -((2 * n : ℕ) : ℝ))
    (hBpole : ∀ n : ℕ, B ≠ -((2 * n : ℕ) : ℝ))
    (hcross : ∀ n ∈ Finset.range (N + 1),
      A < -((2 * n : ℕ) : ℝ) ∧
        -((2 * n : ℕ) : ℝ) < B) :
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((A : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((A : ℂ) + (t : ℂ) * Complex.I)) +
      ((2 * Real.pi : ℝ) : ℂ) *
        ∑ n ∈ Finset.range (N + 1),
          minusSaddlePoleResidue ε ℓ n *
            ((r ^ (2 * n) : ℝ) : ℂ) := by
  have hhalfB : -(2 * ((N : ℝ) + 1)) < B :=
    hhalf.trans_le hAB
  have hcontour :=
    minusSaddleFiniteRapidContourIntegrand_vertical_integral_eq
      hε hℓ horder hr N hhalf hAB hApole hBpole
  rw [minusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
        hε hℓ horder hr N hhalfB hBpole,
      minusSaddleFiniteRapidContourIntegrand_shiftedLine_integral_eq
        hε hℓ horder hr N hhalf hApole]
    at hcontour
  have hsum :=
    saddleFiniteGaussianPoleWeighted_vertical_integral_jump
      hr (minusSaddlePoleResidue ε ℓ) N hcross
  calc
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((B : ℂ) + (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((B : ℂ) + (t : ℂ) * Complex.I)) =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
      ((∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((B : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((B : ℂ) + (t : ℂ) * Complex.I))) -
       (∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          (∫ t : ℝ,
            saddleMellinInversePower r
              ((A : ℂ) + (t : ℂ) * Complex.I) *
              saddleGaussianPoleRepresentative n
                ((A : ℂ) + (t : ℂ) * Complex.I)))) := by
        linear_combination hcontour
    _ =
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((A : ℂ) + (t : ℂ) * Complex.I) *
          minusSaddleMellinData ε ℓ
            ((A : ℂ) + (t : ℂ) * Complex.I)) +
        ((2 * Real.pi : ℝ) : ℂ) *
          ∑ n ∈ Finset.range (N + 1),
            minusSaddlePoleResidue ε ℓ n *
              ((r ^ (2 * n) : ℝ) : ℂ) := by
          rw [hsum]

private noncomputable def saddleTaylorContour (N : ℕ) : ℝ :=
  -((2 * N + 1 : ℕ) : ℝ)

private theorem saddleTaylorContour_mem_halfPlane (N : ℕ) :
    -(2 * ((N : ℝ) + 1)) < saddleTaylorContour N := by
  unfold saddleTaylorContour
  push_cast
  linarith

private theorem saddleTaylorContour_ne_pole (N n : ℕ) :
    saddleTaylorContour N ≠ -((2 * n : ℕ) : ℝ) := by
  intro heq
  unfold saddleTaylorContour at heq
  have hcast :
      ((2 * N + 1 : ℕ) : ℝ) =
        ((2 * n : ℕ) : ℝ) :=
    neg_injective heq
  have hnat : 2 * N + 1 = 2 * n := by
    exact_mod_cast hcast
  omega

private theorem saddlePositiveContour_ne_pole
    {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) :
    ℓ ≠ -((2 * n : ℕ) : ℝ) := by
  have hnonpos : -((2 * n : ℕ) : ℝ) ≤ 0 := by
    exact neg_nonpos.mpr (Nat.cast_nonneg (2 * n))
  exact ne_of_gt (hnonpos.trans_lt hℓ)

private theorem saddleTaylorContour_crosses_poles
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    ∀ n ∈ Finset.range (N + 1),
      saddleTaylorContour N < -((2 * n : ℕ) : ℝ) ∧
        -((2 * n : ℕ) : ℝ) < ℓ := by
  intro n hn
  have hnle : n ≤ N := by
    have hnlt := Finset.mem_range.mp hn
    omega
  constructor
  · unfold saddleTaylorContour
    apply neg_lt_neg
    exact_mod_cast (show 2 * n < 2 * N + 1 by omega)
  · have hnonpos : -((2 * n : ℕ) : ℝ) ≤ 0 := by
      exact neg_nonpos.mpr (Nat.cast_nonneg (2 * n))
    exact hnonpos.trans_lt hℓ

private theorem saddleTaylorContour_le_positive
    {ℓ : ℝ} (hℓ : 0 < ℓ) (N : ℕ) :
    saddleTaylorContour N ≤ ℓ := by
  have hnonpos : saddleTaylorContour N ≤ 0 := by
    unfold saddleTaylorContour
    exact neg_nonpos.mpr (Nat.cast_nonneg (2 * N + 1))
  exact hnonpos.trans hℓ.le

private theorem plusSaddleProfile_eq_normalized_vertical_integral
    {ε ℓ r : ℝ} (hr : 0 < r) :
    plusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((ℓ : ℂ) + (t : ℂ) * Complex.I) *
            plusSaddleMellinData ε ℓ
              ((ℓ : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold plusSaddleProfile
  rw [ite_eq_right hr.ne']
  unfold mellinInv
  simp only [smul_eq_mul, Complex.real_smul]
  rfl

private theorem minusSaddleProfile_eq_normalized_vertical_integral
    {ε ℓ r : ℝ} (hr : 0 < r) :
    minusSaddleProfile ε ℓ r =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          saddleMellinInversePower r
            ((ℓ : ℂ) + (t : ℂ) * Complex.I) *
            minusSaddleMellinData ε ℓ
              ((ℓ : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold minusSaddleProfile
  rw [ite_eq_right hr.ne']
  unfold mellinInv
  simp only [smul_eq_mul, Complex.real_smul]
  rfl

private noncomputable def plusSaddleTaylorRemainder
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) *
        plusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I))

private noncomputable def minusSaddleTaylorRemainder
    (ε ℓ : ℝ) (N : ℕ) (r : ℝ) : ℂ :=
  ((1 / (2 * Real.pi) : ℝ) : ℂ) *
    (∫ t : ℝ,
      saddleMellinInversePower r
        ((saddleTaylorContour N : ℂ) +
          (t : ℂ) * Complex.I) *
        minusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (t : ℂ) * Complex.I))

private theorem plusSaddlePoleResidue_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    plusSaddlePoleResidue ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by
  simpa only [plusSaddlePoleResidue, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
    div_one, mul_zero,
    CharP.cast_eq_zero, neg_zero] using!
    (two_mul_plusSaddleRegularMellinFactor_zero
      (ε := ε) hℓ)

private theorem minusSaddlePoleResidue_zero
    {ε ℓ : ℝ} (hℓ : 0 < ℓ) :
    minusSaddlePoleResidue ε ℓ 0 =
      (saddleOriginValue ε ℓ : ℂ) := by
  simpa only [minusSaddlePoleResidue, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
    div_one, mul_zero,
    CharP.cast_eq_zero, neg_zero] using!
    (two_mul_minusSaddleRegularMellinFactor_zero
      (ε := ε) hℓ)

private theorem plusSaddleProfile_eq_residue_sum_add_remainder
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ) :
    plusSaddleProfile ε ℓ r =
      (∑ n ∈ Finset.range (N + 1),
        plusSaddlePoleResidue ε ℓ n *
          ((r ^ (2 * n) : ℝ) : ℂ)) +
      plusSaddleTaylorRemainder ε ℓ N r := by
  have hcontour :=
    plusSaddleMellinData_vertical_integral_residue_expansion
      hε hℓ horder hr N
      (saddleTaylorContour_mem_halfPlane N)
      (saddleTaylorContour_le_positive hℓ N)
      (fun n : ℕ => saddleTaylorContour_ne_pole N n)
      (fun n : ℕ => saddlePositiveContour_ne_pole hℓ n)
      (saddleTaylorContour_crosses_poles hℓ N)
  have hnormal :
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [plusSaddleProfile_eq_normalized_vertical_integral hr,
    hcontour]
  unfold plusSaddleTaylorRemainder
  rw [mul_add, ← mul_assoc, hnormal, one_mul]
  ring

private theorem minusSaddleProfile_eq_residue_sum_add_remainder
    {ε ℓ r : ℝ}
    (hε : 0 < ε) (hℓ : 0 < ℓ)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)))
    (hr : 0 < r) (N : ℕ) :
    minusSaddleProfile ε ℓ r =
      (∑ n ∈ Finset.range (N + 1),
        minusSaddlePoleResidue ε ℓ n *
          ((r ^ (2 * n) : ℝ) : ℂ)) +
      minusSaddleTaylorRemainder ε ℓ N r := by
  have hcontour :=
    minusSaddleMellinData_vertical_integral_residue_expansion
      hε hℓ horder hr N
      (saddleTaylorContour_mem_halfPlane N)
      (saddleTaylorContour_le_positive hℓ N)
      (fun n : ℕ => saddleTaylorContour_ne_pole N n)
      (fun n : ℕ => saddlePositiveContour_ne_pole hℓ n)
      (saddleTaylorContour_crosses_poles hℓ N)
  have hnormal :
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((2 * Real.pi : ℝ) : ℂ) = 1 := by
    push_cast
    field_simp [Real.pi_ne_zero]
  rw [minusSaddleProfile_eq_normalized_vertical_integral hr,
    hcontour]
  unfold minusSaddleTaylorRemainder
  rw [mul_add, ← mul_assoc, hnormal, one_mul]
  ring

private theorem saddleMellinInversePower_shiftedLine_integral_norm
    {r a : ℝ} (hr : 0 < r)
    (F : ℂ → ℂ)
    (hF : Integrable
      (fun t : ℝ => F ((a : ℂ) + (t : ℂ) * Complex.I))) :
    (∫ t : ℝ,
      ‖saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        F ((a : ℂ) + (t : ℂ) * Complex.I)‖) =
      r ^ (-a) *
        (∫ t : ℝ,
          ‖F ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by
  calc
    (∫ t : ℝ,
      ‖saddleMellinInversePower r
        ((a : ℂ) + (t : ℂ) * Complex.I) *
        F ((a : ℂ) + (t : ℂ) * Complex.I)‖) =
      ∫ t : ℝ,
        r ^ (-a) *
          ‖F ((a : ℂ) + (t : ℂ) * Complex.I)‖ := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards [] with t
        rw [norm_mul,
          saddleMellinInversePower_shiftedLine_norm hr a t]
    _ = r ^ (-a) *
        (∫ t : ℝ,
          ‖F ((a : ℂ) + (t : ℂ) * Complex.I)‖) :=
      integral_const_mul_of_integrable hF.norm

private theorem saddleTaylorContour_rpow
    (r : ℝ) (N : ℕ) :
    r ^ (-(saddleTaylorContour N)) =
      r ^ (2 * N + 1) := by
  unfold saddleTaylorContour
  rw [neg_neg, Real.rpow_natCast]

end

section

open Filter
open scoped Topology

private theorem tendsto_log_wallisProduct :
    Tendsto (fun n : ℕ => Real.log (Real.Wallis.W n))
      atTop (nhds (Real.log (Real.pi / 2))) := by
  exact (Real.continuousAt_log (by positivity)).tendsto.comp
    Real.Wallis.tendsto_W_nhds_pi_div_two

end

section

open Filter MeasureTheory Set
open scoped Topology

private noncomputable def frullaniKernel (a b x : ℝ) : ℝ :=
  (Real.exp (-a * x) - Real.exp (-b * x)) / x

private theorem laplaceKernel_integrable {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun x : ℝ => Real.exp (-a * x)) (Ioi 0) := by
  exact integrableOn_exp_mul_Ioi (by linarith : -a < 0) 0

private theorem integral_laplaceKernel {a : ℝ} (ha : 0 < a) :
    (∫ x : ℝ in Ioi 0, Real.exp (-a * x)) = a⁻¹ := by
  simpa only [neg_mul, mul_zero, Real.exp_zero, neg_div_neg_eq,
    one_div] using! (integral_exp_mul_Ioi (by linarith : -a < 0) 0)

private theorem intervalIntegral_laplaceKernel {x : ℝ} (hx : x ≠ 0)
    (a b : ℝ) :
    (∫ s in a..b, Real.exp (-s * x)) = frullaniKernel a b x := by
  have hderiv (s : ℝ) :
      HasDerivAt (fun u : ℝ => -Real.exp (-u * x) / x)
        (Real.exp (-s * x)) s := by
    convert! (((Real.hasDerivAt_exp (-s * x)).comp s
      ((hasDerivAt_id s).neg.mul_const x)).neg.div_const x)
      using 1; field_simp [hx]
  have hint :
      IntervalIntegrable (fun s : ℝ => Real.exp (-s * x))
        volume a b :=
    ((Real.continuous_exp.comp
      (continuous_id.neg.mul continuous_const)).intervalIntegrable a b)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s _ => hderiv s) hint]
  unfold frullaniKernel
  ring

private theorem laplaceParameter_integrable {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    Integrable
      (Function.uncurry (fun s x : ℝ => Real.exp (-s * x)))
      ((volume.restrict (Set.uIoc a b)).prod
        (volume.restrict (Ioi 0))) := by
  have hmeas :
      AEStronglyMeasurable
        (Function.uncurry (fun s x : ℝ => Real.exp (-s * x)))
        ((volume.restrict (Set.uIoc a b)).prod
          (volume.restrict (Ioi 0))) := by
    fun_prop
  apply (integrable_prod_iff hmeas).2
  constructor
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hspos : 0 < s := by
      rw [Set.uIoc_of_le hab] at hs
      linarith [hs.1]
    exact laplaceKernel_integrable hspos
  · have hnonzero :
        ∀ s ∈ Set.uIcc a b, s ≠ 0 := by
      intro s hs
      rw [Set.uIcc_of_le hab] at hs
      exact ne_of_gt (lt_of_lt_of_le ha hs.1)
    have hcont : ContinuousOn (fun s : ℝ => s⁻¹) (Set.uIcc a b) :=
      continuousOn_id.inv₀ hnonzero
    have hinv :
        Integrable (fun s : ℝ => s⁻¹)
          (volume.restrict (Set.uIoc a b)) :=
      intervalIntegrable_iff.mp hcont.intervalIntegrable
    apply hinv.congr
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with s hs
    have hspos : 0 < s := by
      rw [Set.uIoc_of_le hab] at hs
      linarith [hs.1]
    symm
    change (∫ y : ℝ in Ioi 0, ‖Real.exp (-s * y)‖) = s⁻¹
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using!
      integral_laplaceKernel hspos

private theorem integral_frullaniKernel {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    (∫ x : ℝ in Ioi 0, frullaniKernel a b x) =
      Real.log (b / a) := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  calc
    (∫ x : ℝ in Ioi 0, frullaniKernel a b x) =
        ∫ x : ℝ in Ioi 0, ∫ s in a..b, Real.exp (-s * x) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact (intervalIntegral_laplaceKernel (ne_of_gt hx) a b).symm
    _ = ∫ s in a..b, ∫ x : ℝ in Ioi 0, Real.exp (-s * x) :=
      (intervalIntegral_integral_swap
        (laplaceParameter_integrable ha hab)).symm
    _ = ∫ s in a..b, s⁻¹ := by
      apply intervalIntegral.integral_congr
      intro s hs
      have hspos : 0 < s := by
        rw [Set.uIcc_of_le hab] at hs
        exact lt_of_lt_of_le ha hs.1
      exact integral_laplaceKernel hspos
    _ = Real.log (b / a) :=
      integral_inv_of_pos ha hb

private theorem frullaniKernel_integrable {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) :
    IntegrableOn (frullaniKernel a b) (Ioi 0) := by
  have hprod := (laplaceParameter_integrable ha hab).integral_prod_right
  apply hprod.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  change (∫ s in Set.uIoc a b, Real.exp (-s * x)) =
    frullaniKernel a b x
  rw [Set.uIoc_of_le hab, ← intervalIntegral.integral_of_le hab]
  exact intervalIntegral_laplaceKernel (ne_of_gt hx) a b

private noncomputable def wallisPairKernel (n : ℕ) (x : ℝ) : ℝ :=
  frullaniKernel (2 * (n : ℝ) + 1) (2 * (n : ℝ) + 2) x -
    frullaniKernel (2 * (n : ℝ) + 2) (2 * (n : ℝ) + 3) x

private theorem wallisPairKernel_eq (n : ℕ) (x : ℝ) :
    wallisPairKernel n x =
      Real.exp (-(2 * (n : ℝ) + 1) * x) *
        (1 - Real.exp (-x)) ^ 2 / x := by
  have htwo :
      Real.exp (-(2 * (n : ℝ) + 2) * x) =
        Real.exp (-(2 * (n : ℝ) + 1) * x) * Real.exp (-x) := by
    rw [show -(2 * (n : ℝ) + 2) * x =
      -(2 * (n : ℝ) + 1) * x + -x by ring, Real.exp_add]
  have hthree :
      Real.exp (-(2 * (n : ℝ) + 3) * x) =
        Real.exp (-(2 * (n : ℝ) + 1) * x) *
          Real.exp (-x) ^ 2 := by
    rw [show -(2 * (n : ℝ) + 3) * x =
      (-(2 * (n : ℝ) + 1) * x + -x) + -x by ring,
      Real.exp_add, Real.exp_add]
    ring
  unfold wallisPairKernel frullaniKernel
  rw [htwo, hthree]
  ring

private theorem wallisPairKernel_integrable (n : ℕ) :
    IntegrableOn (wallisPairKernel n) (Ioi 0) := by
  unfold wallisPairKernel
  apply Integrable.sub
  · exact frullaniKernel_integrable (by positivity) (by linarith)
  · exact frullaniKernel_integrable (by positivity) (by linarith)

private noncomputable def wallisPairFactor (n : ℕ) : ℝ :=
  ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 1)) *
    ((2 * (n : ℝ) + 2) / (2 * (n : ℝ) + 3))

private theorem integral_wallisPairKernel (n : ℕ) :
    (∫ x : ℝ in Ioi 0, wallisPairKernel n x) =
      Real.log (wallisPairFactor n) := by
  unfold wallisPairKernel
  rw [integral_sub
    (frullaniKernel_integrable (by positivity) (by linarith))
    (frullaniKernel_integrable (by positivity) (by linarith)),
    integral_frullaniKernel (by positivity) (by linarith),
    integral_frullaniKernel (by positivity) (by linarith)]
  unfold wallisPairFactor
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity),
    Real.log_div (by positivity) (by positivity)]
  ring

private theorem wallisPairFactor_pos (n : ℕ) : 0 < wallisPairFactor n := by
  unfold wallisPairFactor
  positivity

private theorem wallisProduct_succ (n : ℕ) :
    Real.Wallis.W (n + 1) =
      Real.Wallis.W n * wallisPairFactor n := by
  simpa only [wallisPairFactor] using! Real.Wallis.W_succ n

private noncomputable def wallisPartialKernel (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, wallisPairKernel k x

private theorem wallisPartialKernel_integrable (n : ℕ) :
    IntegrableOn (wallisPartialKernel n) (Ioi 0) := by
  unfold wallisPartialKernel
  exact integrable_finsetSum _ fun k _ => wallisPairKernel_integrable k

private theorem integral_wallisPartialKernel (n : ℕ) :
    (∫ x : ℝ in Ioi 0, wallisPartialKernel n x) =
      Real.log (Real.Wallis.W n) := by
  induction n with
  | zero =>
      simp only [wallisPartialKernel, Finset.range_zero, Finset.sum_empty, integral_zero,
        Real.Wallis.W, Finset.prod_empty, Real.log_one]
  | succ n ih =>
      have hpartial :
          (fun x : ℝ => wallisPartialKernel (n + 1) x) =
            fun x : ℝ =>
              wallisPartialKernel n x + wallisPairKernel n x := by
        funext x
        simp only [wallisPartialKernel, Finset.sum_range_succ]
      rw [hpartial, integral_add (wallisPartialKernel_integrable n)
        (wallisPairKernel_integrable n), ih,
        integral_wallisPairKernel, wallisProduct_succ,
        Real.log_mul (Real.Wallis.W_pos n).ne'
          (wallisPairFactor_pos n).ne']

private noncomputable def wallisLaplaceKernel (x : ℝ) : ℝ :=
  Real.exp (-x) * (1 - Real.exp (-x)) /
    (x * (1 + Real.exp (-x)))

private theorem wallisPartialKernel_eq (n : ℕ) {x : ℝ} (hx : x ≠ 0) :
    wallisPartialKernel n x =
      wallisLaplaceKernel x *
        (1 - Real.exp (-(2 * (n : ℝ)) * x)) := by
  induction n with
  | zero => simp only [wallisPartialKernel, Finset.range_zero, Finset.sum_empty,
    CharP.cast_eq_zero, mul_zero, neg_zero,
              zero_mul, Real.exp_zero, sub_self]
  | succ n ih =>
      rw [show wallisPartialKernel (n + 1) x =
          wallisPartialKernel n x + wallisPairKernel n x by
        simp only [wallisPartialKernel, Finset.sum_range_succ],
        ih, wallisPairKernel_eq]
      have htwo :
          Real.exp (-(2 * ((n + 1 : ℕ) : ℝ)) * x) =
            Real.exp (-(2 * (n : ℝ)) * x) *
              Real.exp (-x) ^ 2 := by
        push_cast
        rw [show -(2 * ((n : ℝ) + 1)) * x =
          (-(2 * (n : ℝ)) * x + -x) + -x by ring,
          Real.exp_add, Real.exp_add]
        ring
      have hone :
          Real.exp (-(2 * (n : ℝ) + 1) * x) =
            Real.exp (-(2 * (n : ℝ)) * x) *
              Real.exp (-x) := by
        rw [show -(2 * (n : ℝ) + 1) * x =
          -(2 * (n : ℝ)) * x + -x by ring, Real.exp_add]
      rw [htwo, hone]
      unfold wallisLaplaceKernel
      have hden : 1 + Real.exp (-x) ≠ 0 := by positivity
      field_simp [hx, hden]
      ring

private theorem wallisLaplaceKernel_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ wallisLaplaceKernel x := by
  unfold wallisLaplaceKernel
  have hq : Real.exp (-x) ≤ 1 :=
    (Real.exp_le_one_iff).2 (neg_nonpos.mpr hx.le)
  exact div_nonneg
    (mul_nonneg (Real.exp_pos _).le (sub_nonneg.mpr hq))
    (mul_nonneg hx.le (by positivity))

private theorem wallisLaplaceKernel_abs_le {x : ℝ} (hx : 0 < x) :
    |wallisLaplaceKernel x| ≤ Real.exp (-x) := by
  rw [abs_of_nonneg (wallisLaplaceKernel_nonneg hx)]
  unfold wallisLaplaceKernel
  have hq : 0 < Real.exp (-x) := Real.exp_pos _
  have hsub : 1 - Real.exp (-x) ≤ x := by
    linarith [Real.add_one_le_exp (-x)]
  have hden : 0 < x * (1 + Real.exp (-x)) := by positivity
  apply (div_le_iff₀ hden).2
  have hmul : 0 ≤ x * Real.exp (-x) :=
    mul_nonneg hx.le hq.le
  nlinarith

private theorem wallisLaplaceKernel_integrable :
    IntegrableOn wallisLaplaceKernel (Ioi 0) := by
  have hbound :
      IntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) := by
    simpa only [neg_mul, one_mul] using! laplaceKernel_integrable (a := (1 : ℝ)) zero_lt_one
  refine hbound.mono' ?_ ?_
  · unfold wallisLaplaceKernel
    exact (by fun_prop : Measurable
      (fun x : ℝ => Real.exp (-x) * (1 - Real.exp (-x)) /
        (x * (1 + Real.exp (-x))))).aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  simpa only [Real.norm_eq_abs] using! wallisLaplaceKernel_abs_le hx

private theorem wallisPartialKernel_abs_le (n : ℕ) {x : ℝ} (hx : 0 < x) :
    |wallisPartialKernel n x| ≤ wallisLaplaceKernel x := by
  rw [wallisPartialKernel_eq n hx.ne']
  have hexp : Real.exp (-(2 * (n : ℝ)) * x) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
    nlinarith
  have hfactor : 0 ≤ 1 - Real.exp (-(2 * (n : ℝ)) * x) :=
    sub_nonneg.mpr hexp
  have hfactor_le : 1 - Real.exp (-(2 * (n : ℝ)) * x) ≤ 1 := by
    linarith [Real.exp_pos (-(2 * (n : ℝ)) * x)]
  rw [abs_of_nonneg
    (mul_nonneg (wallisLaplaceKernel_nonneg hx) hfactor)]
  exact mul_le_of_le_one_right (wallisLaplaceKernel_nonneg hx) hfactor_le

private theorem tendsto_wallisPartialKernel {x : ℝ} (hx : 0 < x) :
    Tendsto (fun n : ℕ => wallisPartialKernel n x)
      atTop (nhds (wallisLaplaceKernel x)) := by
  have hlinear :
      Tendsto (fun n : ℕ => (2 * x) * (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
  have hexp :
      Tendsto (fun n : ℕ =>
        Real.exp (-(2 * (n : ℝ)) * x)) atTop (nhds 0) := by
    convert! Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear using 1
    funext n
    congr 1
    ring
  have hfactor :
      Tendsto (fun n : ℕ =>
        1 - Real.exp (-(2 * (n : ℝ)) * x)) atTop (nhds 1) := by
    simpa only [neg_mul, sub_zero] using! tendsto_const_nhds.sub hexp
  have hproduct :=
    (tendsto_const_nhds (x := wallisLaplaceKernel x)).mul hfactor
  simpa only [mul_one, wallisPartialKernel_eq _ hx.ne'] using! hproduct

private theorem tendsto_integral_wallisPartialKernel :
    Tendsto
      (fun n : ℕ => ∫ x : ℝ in Ioi 0, wallisPartialKernel n x)
      atTop (nhds (∫ x : ℝ in Ioi 0, wallisLaplaceKernel x)) := by
  apply tendsto_integral_of_dominated_convergence
    wallisLaplaceKernel
    (fun n => (wallisPartialKernel_integrable n).aestronglyMeasurable)
    wallisLaplaceKernel_integrable
  · intro n
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simpa only [Real.norm_eq_abs] using!
      wallisPartialKernel_abs_le n hx
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact tendsto_wallisPartialKernel hx

private theorem integral_wallisLaplaceKernel :
    (∫ x : ℝ in Ioi 0, wallisLaplaceKernel x) =
      Real.log (Real.pi / 2) := by
  have hproduct :
      Tendsto
        (fun n : ℕ => ∫ x : ℝ in Ioi 0, wallisPartialKernel n x)
        atTop (nhds (Real.log (Real.pi / 2))) := by
    simpa only [integral_wallisPartialKernel] using!
      tendsto_log_wallisProduct
  exact tendsto_nhds_unique tendsto_integral_wallisPartialKernel
    hproduct

end

section

open Filter MeasureTheory
open scoped Topology

private theorem tendsto_cubic_gaussian_atTop :
    Tendsto (fun x : ℝ => (x ^ 3 + 1) * Real.exp (-(x ^ 2) / 8))
      atTop (nhds 0) := by
  have hpoly :
      Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-(1 / 8 : ℝ) * x))
        atTop (nhds 0) := by
    simpa only [one_div, neg_mul, Real.rpow_ofNat] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (3 : ℝ) (1 / 8 : ℝ) (by norm_num))
  have hone :
      Tendsto (fun x : ℝ => Real.exp (-(1 / 8 : ℝ) * x))
        atTop (nhds 0) := by
    simpa only [one_div, neg_mul, Real.tendsto_exp_comp_nhds_zero, tendsto_neg_atBot_iff,
      Real.rpow_zero,
      one_mul] using!
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (0 : ℝ) (1 / 8 : ℝ) (by norm_num))
  have hlinear :
      Tendsto
        (fun x : ℝ => (x ^ 3 + 1) * Real.exp (-(1 / 8 : ℝ) * x))
        atTop (nhds 0) := by
    convert! hpoly.add hone using 1
    · ext x
      ring
    · norm_num
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ))) hlinear ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hxpoly : 0 ≤ x ^ 3 + 1 := by positivity
    apply mul_le_mul_of_nonneg_left _ hxpoly
    apply Real.exp_le_exp.mpr
    linarith [mul_nonneg (by linarith : 0 ≤ x)
      (by linarith : 0 ≤ x - 1)]

private noncomputable def shellRadiusMajorant (ε : ℝ) : ℝ :=
  ((ε⁻¹ ^ 3) + 1) * shellWeight ε *
    Real.exp ((ε / 4) * ((ε⁻¹ ^ 3) + 1))

private theorem shellRadiusMajorant_inv {x : ℝ} (hx : x ≠ 0) :
    shellRadiusMajorant x⁻¹ =
      ((x ^ 3 + 1) * Real.exp (-(x ^ 2) / 8)) *
        Real.exp (x⁻¹ / 4) := by
  unfold shellRadiusMajorant shellWeight
  simp only [inv_inv]
  simp only [mul_assoc]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

private theorem tendsto_shellRadiusMajorant :
    Tendsto shellRadiusMajorant (𝓝[>] (0 : ℝ)) (nhds 0) := by
  apply tendsto_nhdsGT_zero_of_comp_inv_tendsto_atTop
  have hsmall :
      Tendsto (fun x : ℝ => x⁻¹ / 4) atTop (nhds 0) := by
    convert! tendsto_inv_atTop_zero.div_const (4 : ℝ) using 1; norm_num
  have hexp :
      Tendsto (fun x : ℝ => Real.exp (x⁻¹ / 4)) atTop (nhds 1) := by
    simpa only [Real.exp_zero] using! hsmall.rexp
  have hproduct := tendsto_cubic_gaussian_atTop.mul hexp
  have hzero :
      Tendsto
        (fun x : ℝ =>
          ((x ^ 3 + 1) * Real.exp (-(x ^ 2) / 8)) *
            Real.exp (x⁻¹ / 4))
        atTop (nhds 0) := by
    simpa only [mul_one] using! hproduct
  refine hzero.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with x hx
  exact (shellRadiusMajorant_inv hx).symm

private theorem tendsto_positiveShellRadiusContribution :
    Tendsto positiveShellRadiusContribution
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (tendsto_const_nhds (x := (0 : ℝ)))
    tendsto_shellRadiusMajorant ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (positiveShellRadiusContribution_bounds hε).1
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (positiveShellRadiusContribution_bounds hε).2

private theorem sinh_le_mul_cosh {a : ℝ} (ha : 0 ≤ a) :
    Real.sinh a ≤ a * Real.cosh a := by
  let f : ℝ → ℝ := fun x => x * Real.cosh x - Real.sinh x
  have hderiv (x : ℝ) :
      HasDerivAt f (x * Real.sinh x) x := by
    try dsimp [f]
    convert! ((hasDerivAt_id x).mul
      (Real.hasDerivAt_cosh x)).sub
      (Real.hasDerivAt_sinh x) using 1;
      simp only [one_mul, id, add_sub_cancel_left]
  have hdiff : Differentiable ℝ f :=
    fun x => (hderiv x).differentiableAt
  have hmono : MonotoneOn f (Set.Ici (0 : ℝ)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici (0 : ℝ))
      hdiff.continuous.continuousOn hdiff.differentiableOn
    intro x hx
    rw [interior_Ici] at hx
    rw [(hderiv x).deriv]
    exact mul_nonneg hx.le (Real.sinh_nonneg_iff.mpr hx.le)
  have h := hmono (show (0 : ℝ) ∈ Set.Ici 0 by simp only [Set.mem_Ici, Std.le_refl])
    (show a ∈ Set.Ici 0 from ha) ha
  try dsimp [f] at h
  norm_num at h
  linarith

private noncomputable def shortShellRadiusIntegrand (ε a : ℝ) : ℝ :=
  shortShellDensity ε a * a * Real.sinh ((1 + ε / 4) * a)

private noncomputable def wallisRadiusIntegrand (a : ℝ) : ℝ :=
  -(Real.exp (-2 * a) * Real.tanh a / (2 * a))

private theorem tendsto_shortShellRadiusIntegrand {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => shortShellRadiusIntegrand ε a)
      (𝓝[>] (0 : ℝ)) (nhds (wallisRadiusIntegrand a)) := by
  have hc : Continuous (fun ε : ℝ => shortShellRadiusIntegrand ε a) := by
    unfold shortShellRadiusIntegrand shortShellDensity
    fun_prop
  have ht :
      Tendsto (fun ε : ℝ => shortShellRadiusIntegrand ε a)
        (𝓝[>] (0 : ℝ)) (nhds (shortShellRadiusIntegrand 0 a)) :=
    (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left
      (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hvalue : shortShellRadiusIntegrand 0 a =
      wallisRadiusIntegrand a := by
    unfold shortShellRadiusIntegrand shortShellDensity
      wallisRadiusIntegrand
    rw [Real.tanh_eq_sinh_div_cosh]
    field_simp [ha.ne', (Real.cosh_pos a).ne']
    ring_nf
  simpa only [hvalue] using! ht

private theorem shortMargin_abs_le_exp {ε a : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a) :
    |(1 - 10 * ε * (1 + a))| ≤ 11 * Real.exp a := by
  have hterm : 0 ≤ 10 * ε * (1 + a) := by positivity
  calc
    |(1 - 10 * ε * (1 + a))| = |1 - 10 * ε * (1 + a)| := rfl
    _ ≤ |(1 : ℝ)| + |10 * ε * (1 + a)| := abs_sub _ _
    _ = 1 + 10 * ε * (1 + a) := by
      rw [abs_of_pos (by norm_num : (0 : ℝ) < 1),
        abs_of_nonneg hterm]
    _ ≤ 11 * (1 + a) := by
      linarith [mul_le_mul_of_nonneg_right hε1
        (show 0 ≤ 1 + a by linarith)]
    _ ≤ 11 * Real.exp a := by
      gcongr
      linarith [Real.add_one_le_exp a]

private theorem shortShellHyperbolicRatio_le {ε a : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 ≤ a) :
    Real.sinh ((1 + ε / 4) * a) / Real.cosh a ≤
      (5 / 4 : ℝ) * a * Real.exp (a / 4) := by
  have hδ : 0 ≤ ε / 4 := by positivity
  have harg : 0 ≤ (1 + ε / 4) * a := by positivity
  calc
    Real.sinh ((1 + ε / 4) * a) / Real.cosh a
        ≤ ((1 + ε / 4) * a) *
          (Real.cosh ((1 + ε / 4) * a) / Real.cosh a) := by
          rw [← mul_div_assoc]
          exact (div_le_div_iff_of_pos_right (Real.cosh_pos a)).2
            (sinh_le_mul_cosh harg)
    _ ≤ ((5 / 4 : ℝ) * a) * Real.exp ((ε / 4) * a) := by
          gcongr
          · linarith
          · exact cosh_ratio_upper ha hδ
    _ ≤ ((5 / 4 : ℝ) * a) * Real.exp (a / 4) := by
          gcongr
          linarith [mul_le_mul_of_nonneg_right hε1 ha]

private theorem shortShellRadiusIntegrand_eq_ratio {ε a : ℝ} (ha : a ≠ 0) :
    shortShellRadiusIntegrand ε a =
      -((1 - 10 * ε * (1 + a)) * Real.exp (-2 * a) *
        (Real.sinh ((1 + ε / 4) * a) / Real.cosh a) /
          (2 * a)) := by
  unfold shortShellRadiusIntegrand shortShellDensity
  field_simp [ha, (Real.cosh_pos a).ne']

private theorem shortShellRadiusIntegrand_abs_le {ε a : ℝ}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (ha : 0 < a) :
    |shortShellRadiusIntegrand ε a| ≤
      7 * Real.exp (-(3 / 4 : ℝ) * a) := by
  have harg : 0 ≤ (1 + ε / 4) * a := by positivity
  have hratio0 :
      0 ≤ Real.sinh ((1 + ε / 4) * a) / Real.cosh a :=
    div_nonneg (Real.sinh_nonneg_iff.mpr harg)
      (Real.cosh_pos a).le
  rw [shortShellRadiusIntegrand_eq_ratio ha.ne', abs_neg,
    abs_div, abs_mul, abs_mul,
    abs_of_pos (Real.exp_pos (-2 * a)), abs_of_nonneg hratio0,
    abs_of_pos (by positivity : 0 < (2 : ℝ) * a)]
  calc
    |(1 - 10 * ε * (1 + a))| * Real.exp (-2 * a) *
        (Real.sinh ((1 + ε / 4) * a) / Real.cosh a) / (2 * a)
      ≤ (11 * Real.exp a) * Real.exp (-2 * a) *
          ((5 / 4 : ℝ) * a * Real.exp (a / 4)) / (2 * a) := by
            gcongr
            · exact shortMargin_abs_le_exp hε0 hε1 ha.le
            · exact shortShellHyperbolicRatio_le hε0 hε1 ha.le
    _ = (55 / 8 : ℝ) * Real.exp (-(3 / 4 : ℝ) * a) := by
          rw [show -(3 / 4 : ℝ) * a =
            (a + -2 * a) + a / 4 by ring,
            Real.exp_add, Real.exp_add]
          field_simp [ha.ne']
          ring
    _ ≤ 7 * Real.exp (-(3 / 4 : ℝ) * a) :=
          mul_le_mul_of_nonneg_right (by norm_num)
            (Real.exp_pos _).le

private noncomputable def shortShellRadiusMajorant (a : ℝ) : ℝ :=
  7 * Real.exp (-(3 / 4 : ℝ) * a)

private theorem shortShellRadiusMajorant_integrable :
    IntegrableOn shortShellRadiusMajorant (Set.Ioi (0 : ℝ)) := by
  change Integrable
    (fun a : ℝ => 7 * Real.exp (-(3 / 4 : ℝ) * a))
    (volume.restrict (Set.Ioi (0 : ℝ)))
  simpa only [neg_div] using!
    (integrableOn_exp_mul_Ioi (a := (-3 / 4 : ℝ))
      (by norm_num) 0).const_mul 7

private theorem shortShellRadiusIntegrand_measurable (ε : ℝ) :
    Measurable (shortShellRadiusIntegrand ε) := by
  have hn : Measurable (fun a : ℝ =>
      (1 - 10 * ε * (1 + a)) * Real.exp (-2 * a)) := by
    fun_prop
  have hd : Measurable (fun a : ℝ =>
      2 * a ^ 2 * Real.cosh a) := by
    fun_prop
  have hs : Measurable (fun a : ℝ =>
      Real.sinh ((1 + ε / 4) * a)) := by
    fun_prop
  exact ((hn.div hd).neg.mul measurable_id).mul hs

private theorem tendsto_shortCutoff :
    Tendsto (fun ε : ℝ => ε ^ 3) (𝓝[>] (0 : ℝ)) (nhds 0) := by
  have ht : Tendsto (fun ε : ℝ => ε)
      (𝓝[>] (0 : ℝ)) (nhds 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  simpa only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow] using! ht.pow 3

private theorem tendsto_shortEndpoint :
    Tendsto (fun ε : ℝ => 10 * Real.log (1 / ε)) (𝓝[>] (0 : ℝ)) atTop := by
  have ht : Tendsto (fun ε : ℝ => Real.log ε⁻¹)
      (𝓝[>] (0 : ℝ)) atTop :=
    Real.tendsto_log_atTop.comp tendsto_inv_nhdsGT_zero
  change Tendsto (fun ε : ℝ => 10 * Real.log (1 / ε))
    (𝓝[>] (0 : ℝ)) atTop
  simpa only [one_div] using!
    ht.const_mul_atTop (by norm_num : (0 : ℝ) < 10)

private noncomputable def shortShellRadiusContribution (ε : ℝ) : ℝ :=
  ∫ a in (ε ^ 3)..(10 * Real.log (1 / ε)),
    shortShellRadiusIntegrand ε a

private noncomputable def supportedShortShellRadiusIntegrand (ε a : ℝ) : ℝ :=
  (Set.Ioc (ε ^ 3) (10 * Real.log (1 / ε))).indicator
    (shortShellRadiusIntegrand ε) a

private theorem supportedShortShellRadiusIntegrand_measurable (ε : ℝ) :
    Measurable (supportedShortShellRadiusIntegrand ε) := by
  exact (shortShellRadiusIntegrand_measurable ε).indicator
    measurableSet_Ioc

private theorem tendsto_supportedShortShellRadiusIntegrand {a : ℝ} (ha : 0 < a) :
    Tendsto (fun ε : ℝ => supportedShortShellRadiusIntegrand ε a)
      (𝓝[>] (0 : ℝ)) (nhds (wallisRadiusIntegrand a)) := by
  refine (tendsto_shortShellRadiusIntegrand ha).congr' ?_
  filter_upwards
    [tendsto_shortCutoff.eventually (Iio_mem_nhds ha),
      tendsto_shortEndpoint.eventually_ge_atTop a]
    with ε hlower hupper
  have hmem : a ∈ Set.Ioc (ε ^ 3) (10 * Real.log (1 / ε)) :=
    ⟨hlower, hupper⟩
  simp only [supportedShortShellRadiusIntegrand, Set.indicator_of_mem hmem]

private theorem tendsto_supportedShortShellRadiusIntegral :
    Tendsto
      (fun ε : ℝ => ∫ a in Set.Ioi (0 : ℝ),
        supportedShortShellRadiusIntegrand ε a)
      (𝓝[>] (0 : ℝ))
      (nhds (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (μ := volume.restrict (Set.Ioi (0 : ℝ)))
    shortShellRadiusMajorant
  · exact Eventually.of_forall fun ε =>
      (supportedShortShellRadiusIntegrand_measurable ε).aestronglyMeasurable
  · filter_upwards
      [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))]
      with ε hε hsmall
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    by_cases hmem : a ∈ Set.Ioc (ε ^ 3) (10 * Real.log (1 / ε))
    · rw [show supportedShortShellRadiusIntegrand ε a =
        shortShellRadiusIntegrand ε a by
          exact Set.indicator_of_mem hmem (shortShellRadiusIntegrand ε)]
      rw [Real.norm_eq_abs]
      exact shortShellRadiusIntegrand_abs_le hε.le hsmall.le ha
    · rw [show supportedShortShellRadiusIntegrand ε a = 0 by
        exact Set.indicator_of_notMem hmem (shortShellRadiusIntegrand ε),
        norm_zero]
      unfold shortShellRadiusMajorant
      positivity
  · exact shortShellRadiusMajorant_integrable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
    exact tendsto_supportedShortShellRadiusIntegrand ha

private theorem shortShellRadiusContribution_eq_supported {ε : ℝ}
    (hε : 0 < ε)
    (horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε))) :
    shortShellRadiusContribution ε =
      ∫ a in Set.Ioi (0 : ℝ),
        supportedShortShellRadiusIntegrand ε a := by
  have hcutoff : 0 ≤ (ε ^ 3) := by
    positivity
  have hsubset :
      Set.Ioc (ε ^ 3) (10 * Real.log (1 / ε)) ⊆
        Set.Ioi (0 : ℝ) := by
    intro a ha
    exact lt_of_le_of_lt hcutoff ha.1
  unfold shortShellRadiusContribution supportedShortShellRadiusIntegrand
  rw [intervalIntegral.integral_of_le horder,
    MeasureTheory.integral_indicator measurableSet_Ioc,
    Measure.restrict_restrict_of_subset hsubset]

private theorem tendsto_shortShellRadiusContribution :
    Tendsto shortShellRadiusContribution
      (𝓝[>] (0 : ℝ))
      (nhds (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a)) := by
  refine tendsto_supportedShortShellRadiusIntegral.congr' ?_
  filter_upwards
    [self_mem_nhdsWithin,
      tendsto_shortCutoff.eventually
        (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      tendsto_shortEndpoint.eventually_ge_atTop (1 : ℝ)]
    with ε hε hcutoff hendpoint
  have horder : (ε ^ 3) ≤ (10 * Real.log (1 / ε)) :=
    hcutoff.le.trans hendpoint
  exact (shortShellRadiusContribution_eq_supported hε horder).symm

private theorem wallisRadiusIntegrand_eq_laplace (a : ℝ) :
    wallisRadiusIntegrand a = -wallisLaplaceKernel (2 * a) := by
  by_cases ha : a = 0
  · simp only [wallisRadiusIntegrand, ha, mul_zero, Real.exp_zero, Real.tanh_zero, div_zero,
    neg_zero,
      wallisLaplaceKernel, sub_self, zero_mul]
  · have hexp :
        Real.exp (-2 * a) = Real.exp (-a) / Real.exp a := by
        rw [← Real.exp_sub]
        congr 1
        ring
    have hplus : Real.exp a + Real.exp (-a) ≠ 0 := by
      positivity
    have hratio : 1 + Real.exp (-a) / Real.exp a ≠ 0 := by
      positivity
    unfold wallisRadiusIntegrand wallisLaplaceKernel
    rw [Real.tanh_eq a]
    simp only [show -(2 * a) = -2 * a by ring]
    rw [hexp]
    field_simp [ha, (Real.exp_pos a).ne', hplus, hratio]

private theorem integral_wallisRadiusIntegrand :
    (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a) =
      -(1 / 2 : ℝ) * Real.log (Real.pi / 2) := by
  have hscale :
      (∫ a in Set.Ioi (0 : ℝ), wallisLaplaceKernel (2 * a)) =
        (2 : ℝ)⁻¹ * Real.log (Real.pi / 2) := by
    simpa only [mul_zero, integral_wallisLaplaceKernel, smul_eq_mul] using!
      (integral_comp_mul_left_Ioi wallisLaplaceKernel 0
        (by norm_num : (0 : ℝ) < 2))
  calc
    (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a) =
        ∫ a in Set.Ioi (0 : ℝ), -wallisLaplaceKernel (2 * a) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro a _
          exact wallisRadiusIntegrand_eq_laplace a
    _ = -(∫ a in Set.Ioi (0 : ℝ), wallisLaplaceKernel (2 * a)) := by
          rw [integral_neg]
    _ = -(1 / 2 : ℝ) * Real.log (Real.pi / 2) := by
          rw [hscale]
          ring

private noncomputable def limitingSaddleRadius (ε : ℝ) : ℝ :=
  Real.sqrt ((2 + ε / 4) / (4 * Real.pi)) *
    Real.exp (shortShellRadiusContribution ε +
      positiveShellRadiusContribution ε)

private theorem tendsto_limitingSaddleRadius_wallisIntegral :
    Tendsto limitingSaddleRadius (𝓝[>] (0 : ℝ))
      (nhds (Real.sqrt (1 / (2 * Real.pi)) *
        Real.exp (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a))) := by
  have hε : Tendsto (fun ε : ℝ => ε)
      (𝓝[>] (0 : ℝ)) (nhds 0) :=
    tendsto_id.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
  have hnum : Tendsto (fun ε : ℝ => 2 + ε / 4)
      (𝓝[>] (0 : ℝ)) (nhds (2 : ℝ)) := by
    simpa only [zero_div, add_zero] using! (tendsto_const_nhds (x := (2 : ℝ))).add
      (hε.div_const 4)
  have hratio : Tendsto
      (fun ε : ℝ => (2 + ε / 4) / (4 * Real.pi))
      (𝓝[>] (0 : ℝ)) (nhds (1 / (2 * Real.pi))) := by
    have hvalue : (2 : ℝ) / (4 * Real.pi) =
        1 / (2 * Real.pi) := by
      field_simp [Real.pi_ne_zero]
      norm_num
    simpa only [hvalue] using! hnum.div_const (4 * Real.pi)
  have hfactor : Tendsto
      (fun ε : ℝ => Real.sqrt ((2 + ε / 4) / (4 * Real.pi)))
      (𝓝[>] (0 : ℝ)) (nhds (Real.sqrt (1 / (2 * Real.pi)))) :=
    Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  have hshell : Tendsto
      (fun ε : ℝ => shortShellRadiusContribution ε +
        positiveShellRadiusContribution ε)
      (𝓝[>] (0 : ℝ))
      (nhds (∫ a in Set.Ioi (0 : ℝ), wallisRadiusIntegrand a)) := by
    simpa only [add_zero] using! tendsto_shortShellRadiusContribution.add
      tendsto_positiveShellRadiusContribution
  exact hfactor.mul hshell.rexp

private theorem saddleRadius_wallis_constant :
    Real.sqrt (1 / (2 * Real.pi)) *
      Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2)) =
        Real.pi⁻¹ := by
  have hhalfpi : 0 < Real.pi / 2 := by positivity
  have hexpsq :
      (Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2))) ^ 2 =
        (Real.pi / 2)⁻¹ := by
    calc
      (Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2))) ^ 2 =
          Real.exp
            (-(1 / 2 : ℝ) * Real.log (Real.pi / 2) +
              -(1 / 2 : ℝ) * Real.log (Real.pi / 2)) := by
            rw [Real.exp_add]
            ring
      _ = Real.exp (-Real.log (Real.pi / 2)) := by
            congr 1
            ring
      _ = (Real.pi / 2)⁻¹ := by
            rw [Real.exp_neg, Real.exp_log hhalfpi]
  have hsquare :
      (Real.sqrt (1 / (2 * Real.pi)) *
        Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2))) ^ 2 =
          (Real.pi⁻¹) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hexpsq]
    field_simp [Real.pi_ne_zero]
  have hleft : 0 ≤
      Real.sqrt (1 / (2 * Real.pi)) *
        Real.exp (-(1 / 2 : ℝ) * Real.log (Real.pi / 2)) := by
    positivity
  have hright : 0 ≤ Real.pi⁻¹ := (inv_pos.mpr Real.pi_pos).le
  nlinarith

private theorem tendsto_limitingSaddleRadius :
    Tendsto limitingSaddleRadius (𝓝[>] (0 : ℝ))
      (nhds Real.pi⁻¹) := by
  have h := tendsto_limitingSaddleRadius_wallisIntegral
  rw [integral_wallisRadiusIntegrand] at h
  simpa only [saddleRadius_wallis_constant] using! h

end

section

open Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology ENNReal

private noncomputable def radialL1Mass {d : ℕ} (g : TestFunction d) : ℝ :=
  ∫ x : Euclidean d, ‖g x‖

private theorem radialL1Mass_pos {d : ℕ} (g : TestFunction d)
    (hg : g ≠ 0) : 0 < radialL1Mass g := by
  obtain ⟨x, hx⟩ : ∃ x : Euclidean d, g x ≠ 0 := by
    by_contra h
    push Not at h
    apply hg
    ext x
    simpa only [zero_apply] using! h x
  unfold radialL1Mass
  exact integral_pos_of_integrable_nonneg_nonzero
    g.continuous.norm g.integrable.norm (fun _ => norm_nonneg _)
    (norm_ne_zero_iff.mpr hx)

private theorem integral_scaled_exp_change_Ioi {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) :
    (∫ r : ℝ in Ioi 0, f r) =
      ∫ v : ℝ, (R * Real.exp v) • f (R * Real.exp v) := by
  let F : ℝ → ℝ := fun v => R * Real.exp v
  have himage : F '' (Set.univ : Set ℝ) = Ioi 0 := by
    ext r
    constructor
    · rintro ⟨v, _, rfl⟩
      exact mul_pos hR (Real.exp_pos v)
    · intro hr
      refine ⟨Real.log (r / R), Set.mem_univ _, ?_⟩
      try dsimp [F]
      rw [Real.exp_log (div_pos hr hR)]
      field_simp
  have hderiv :
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivWithinAt F (R * Real.exp x) Set.univ x := by
    intro x _
    exact ((Real.hasDerivAt_exp x).const_mul R).hasDerivWithinAt
  have hinj : Set.InjOn F (Set.univ : Set ℝ) := by
    intro x _ y _ hxy
    exact Real.exp_injective (mul_left_cancel₀ hR.ne' hxy)
  have h :=
    integral_image_eq_integral_abs_deriv_smul
      (f := F) (f' := fun x => R * Real.exp x)
      MeasurableSet.univ hderiv hinj f
  simpa only [himage, Measure.restrict_univ, abs_of_pos (mul_pos hR (Real.exp_pos _))] using! h

private theorem integrable_scaled_exp_change_Ioi {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {R : ℝ} (hR : 0 < R) (f : ℝ → E) :
    IntegrableOn f (Ioi 0) ↔
      Integrable (fun v : ℝ =>
        (R * Real.exp v) • f (R * Real.exp v)) := by
  let F : ℝ → ℝ := fun v => R * Real.exp v
  have himage : F '' (Set.univ : Set ℝ) = Ioi 0 := by
    ext r
    constructor
    · rintro ⟨v, _, rfl⟩
      exact mul_pos hR (Real.exp_pos v)
    · intro hr
      refine ⟨Real.log (r / R), Set.mem_univ _, ?_⟩
      try dsimp [F]
      rw [Real.exp_log (div_pos hr hR)]
      field_simp
  have hderiv :
      ∀ x ∈ (Set.univ : Set ℝ),
        HasDerivWithinAt F (R * Real.exp x) Set.univ x := by
    intro x _
    exact ((Real.hasDerivAt_exp x).const_mul R).hasDerivWithinAt
  have hinj : Set.InjOn F (Set.univ : Set ℝ) := by
    intro x _ y _ hxy
    exact Real.exp_injective (mul_left_cancel₀ hR.ne' hxy)
  simpa only [himage, abs_of_pos (mul_pos hR (Real.exp_pos _)), integrableOn_univ] using!
      (integrableOn_image_iff_integrableOn_abs_deriv_smul
        (f := F) (f' := fun x => R * Real.exp x)
        MeasurableSet.univ hderiv hinj f)

private theorem radialL1Mass_eq {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRadial g) :
    radialL1Mass g =
      radialSurfaceArea d *
        ∫ r : ℝ in Ioi 0,
          r ^ (d - 1) * ‖radialProfile hd g r‖ := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  unfold radialL1Mass
  calc
    (∫ x : Euclidean d, ‖g x‖) =
        ∫ x : Euclidean d, ‖radialProfile hd g ‖x‖‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [radialProfile_norm hd g hg x]
    _ = radialSurfaceArea d *
        ∫ r : ℝ in Ioi 0,
          r ^ (d - 1) * ‖radialProfile hd g r‖ := by
      simpa only [radialSurfaceArea, mul_assoc, finrank_euclideanSpace, Fintype.card_fin,
        volume_real_unitBall hd,
        smul_eq_mul, nsmul_eq_mul] using!
        (integral_fun_norm_addHaar
          (volume : Measure (Euclidean d))
          (fun r : ℝ => ‖radialProfile hd g r‖))

private noncomputable def normalizedRadialLogProfile {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (R v : ℝ) : ℝ :=
  radialSurfaceArea d / radialL1Mass g *
    (R * Real.exp v) ^ d *
    (radialProfile hd g (R * Real.exp v)).re

private theorem norm_radialProfile_eq_abs_re {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRealValued g) (r : ℝ) :
    ‖radialProfile hd g r‖ =
      |(radialProfile hd g r).re| := by
  have hvalue :
      radialProfile hd g r =
        ((radialProfile hd g r).re : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using! radialProfile_real hd g hg r
  calc
    ‖radialProfile hd g r‖ =
        ‖((radialProfile hd g r).re : ℂ)‖ :=
      congrArg Norm.norm hvalue
    _ = |(radialProfile hd g r).re| := by
      simp only [Complex.norm_real, Real.norm_eq_abs]

private theorem radialProfile_re_weight_integrable {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRadial g) :
    IntegrableOn
      (fun r : ℝ => r ^ (d - 1) * (radialProfile hd g r).re)
      (Ioi 0) := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hre :
      Integrable
        (fun x : Euclidean d => (radialProfile hd g ‖x‖).re) := by
    apply g.integrable.re.congr
    filter_upwards [] with x
    change (g x).re = (radialProfile hd g ‖x‖).re
    rw [radialProfile_norm hd g hg x]
  simpa only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul] using!
    (integrable_fun_norm_addHaar
      (volume : Measure (Euclidean d))
      (f := fun r : ℝ => (radialProfile hd g r).re)).mp hre

private theorem integral_radialProfile_re {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRadial g) :
    (∫ x : Euclidean d, (g x).re) =
      radialSurfaceArea d *
        ∫ r : ℝ in Ioi 0,
          r ^ (d - 1) * (radialProfile hd g r).re := by
  let : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  calc
    (∫ x : Euclidean d, (g x).re) =
        ∫ x : Euclidean d, (radialProfile hd g ‖x‖).re := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [radialProfile_norm hd g hg x]
    _ = radialSurfaceArea d *
        ∫ r : ℝ in Ioi 0,
          r ^ (d - 1) * (radialProfile hd g r).re := by
      simpa only [radialSurfaceArea, mul_assoc, finrank_euclideanSpace, Fintype.card_fin,
        volume_real_unitBall hd,
        smul_eq_mul, nsmul_eq_mul] using!
        (integral_fun_norm_addHaar
          (volume : Measure (Euclidean d))
          (fun r : ℝ => (radialProfile hd g r).re))

private theorem radialLogRadius_pow {d : ℕ} (hd : 0 < d) (r : ℝ) :
    r ^ d = r * r ^ (d - 1) := by
  have hindex : d - 1 + 1 = d := Nat.sub_add_cancel hd
  conv_lhs => rw [← hindex, pow_succ]
  ring

private theorem normalizedRadialLogProfile_eq {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (R v : ℝ) :
    normalizedRadialLogProfile hd g R v =
      (radialSurfaceArea d / radialL1Mass g) *
        ((R * Real.exp v) *
          ((R * Real.exp v) ^ (d - 1) *
            (radialProfile hd g (R * Real.exp v)).re)) := by
  unfold normalizedRadialLogProfile
  rw [radialLogRadius_pow hd]
  ring

private theorem normalizedRadialLogProfile_integrable {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRadial g)
    {R : ℝ} (hR : 0 < R) :
    Integrable (normalizedRadialLogProfile hd g R) := by
  have hweight := radialProfile_re_weight_integrable hd g hg
  have hexp :=
    (integrable_scaled_exp_change_Ioi hR
      (fun r : ℝ => r ^ (d - 1) *
        (radialProfile hd g r).re)).mp hweight
  have hscaled :=
    hexp.const_mul (radialSurfaceArea d / radialL1Mass g)
  apply hscaled.congr
  filter_upwards [] with v
  simpa only [smul_eq_mul] using!
    (normalizedRadialLogProfile_eq hd g R v).symm

private theorem integral_normalizedRadialLogProfile {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hg : IsRadial g)
    {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, normalizedRadialLogProfile hd g R v) =
      (∫ x : Euclidean d, (g x).re) / radialL1Mass g := by
  calc
    (∫ v : ℝ, normalizedRadialLogProfile hd g R v) =
        ∫ v : ℝ,
          (radialSurfaceArea d / radialL1Mass g) *
            ((R * Real.exp v) *
              ((R * Real.exp v) ^ (d - 1) *
                (radialProfile hd g (R * Real.exp v)).re)) := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact normalizedRadialLogProfile_eq hd g R v
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ∫ v : ℝ,
            (R * Real.exp v) *
              ((R * Real.exp v) ^ (d - 1) *
                (radialProfile hd g (R * Real.exp v)).re) := by
      rw [integral_const_mul]
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ∫ r : ℝ in Ioi 0,
            r ^ (d - 1) * (radialProfile hd g r).re := by
      rw [integral_scaled_exp_change_Ioi hR
        (fun r : ℝ => r ^ (d - 1) *
          (radialProfile hd g r).re)]
      simp only [smul_eq_mul]
    _ = (∫ x : Euclidean d, (g x).re) / radialL1Mass g := by
      rw [integral_radialProfile_re hd g hg]
      ring

private theorem abs_normalizedRadialLogProfile {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hreal : IsRealValued g)
    (hnonzero : g ≠ 0) {R : ℝ} (hR : 0 < R) (v : ℝ) :
    |normalizedRadialLogProfile hd g R v| =
      (radialSurfaceArea d / radialL1Mass g) *
        ((R * Real.exp v) *
          ((R * Real.exp v) ^ (d - 1) *
            ‖radialProfile hd g (R * Real.exp v)‖)) := by
  have hcoefficient : 0 < radialSurfaceArea d / radialL1Mass g :=
    div_pos (radialSurfaceArea_pos hd) (radialL1Mass_pos g hnonzero)
  have hradius : 0 < R * Real.exp v :=
    mul_pos hR (Real.exp_pos v)
  calc
    |normalizedRadialLogProfile hd g R v| =
        |radialSurfaceArea d / radialL1Mass g| *
          |(R * Real.exp v) ^ d| *
            |(radialProfile hd g (R * Real.exp v)).re| := by
      simp only [normalizedRadialLogProfile, mul_assoc, abs_mul, abs_pow, Real.abs_exp]
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ((R * Real.exp v) *
            ((R * Real.exp v) ^ (d - 1) *
              ‖radialProfile hd g (R * Real.exp v)‖)) := by
      rw [abs_of_pos hcoefficient, abs_pow, abs_of_pos hradius,
        ← norm_radialProfile_eq_abs_re hd g hreal,
        radialLogRadius_pow hd]
      ring

private theorem integral_abs_normalizedRadialLogProfile {d : ℕ} (hd : 0 < d)
    (g : TestFunction d) (hradial : IsRadial g)
    (hreal : IsRealValued g) (hnonzero : g ≠ 0)
    {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, |normalizedRadialLogProfile hd g R v|) = 1 := by
  have hmass : 0 < radialL1Mass g := radialL1Mass_pos g hnonzero
  calc
    (∫ v : ℝ, |normalizedRadialLogProfile hd g R v|) =
        ∫ v : ℝ,
          (radialSurfaceArea d / radialL1Mass g) *
            ((R * Real.exp v) *
              ((R * Real.exp v) ^ (d - 1) *
                ‖radialProfile hd g (R * Real.exp v)‖)) := by
      apply integral_congr_ae
      filter_upwards [] with v
      exact abs_normalizedRadialLogProfile hd g hreal hnonzero hR v
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ∫ v : ℝ,
            (R * Real.exp v) *
              ((R * Real.exp v) ^ (d - 1) *
                ‖radialProfile hd g (R * Real.exp v)‖) := by
      rw [integral_const_mul]
    _ = (radialSurfaceArea d / radialL1Mass g) *
          ∫ r : ℝ in Ioi 0,
            r ^ (d - 1) * ‖radialProfile hd g r‖ := by
      rw [integral_scaled_exp_change_Ioi hR
        (fun r : ℝ => r ^ (d - 1) * ‖radialProfile hd g r‖)]
      simp only [smul_eq_mul]
    _ = (radialSurfaceArea d *
          ∫ r : ℝ in Ioi 0,
            r ^ (d - 1) * ‖radialProfile hd g r‖) /
            radialL1Mass g := by
      ring
    _ = 1 := by
      rw [← radialL1Mass_eq hd g hradial]
      exact div_self hmass.ne'

private theorem integral_re_eq_zero_of_antiFourier {d : ℕ}
    (g : TestFunction d)
    (hanti : (𝓕 g : TestFunction d) = -g)
    (hzero : g (0 : Euclidean d) = 0) :
    (∫ x : Euclidean d, (g x).re) = 0 := by
  have hfourierzero :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) = 0 := by
    rw [hanti]
    simpa only [neg_apply, neg_eq_zero] using! hzero
  have hfourier_integral :
      ((𝓕 g : TestFunction d) (0 : Euclidean d)) =
        ∫ x : Euclidean d, g x := by
    change (𝓕 (g : Euclidean d → ℂ)) 0 = _
    rw [Real.fourier_eq']
    simp only [neg_mul, inner_zero_right, mul_zero, Complex.ofReal_zero, zero_mul,
      Complex.exp_zero, smul_eq_mul,
      one_mul]
  calc
    (∫ x : Euclidean d, (g x).re) =
        (∫ x : Euclidean d, g x).re :=
      integral_re g.integrable
    _ = ((𝓕 g : TestFunction d) (0 : Euclidean d)).re := by
      rw [hfourier_integral]
    _ = 0 := by
      rw [hfourierzero]
      rfl

private theorem integral_normalizedRadialLogProfile_eq_zero_of_antiFourier
    {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hradial : IsRadial g)
    (hanti : (𝓕 g : TestFunction d) = -g)
    (hzero : g (0 : Euclidean d) = 0)
    {R : ℝ} (hR : 0 < R) :
    (∫ v : ℝ, normalizedRadialLogProfile hd g R v) = 0 := by
  rw [integral_normalizedRadialLogProfile hd g hradial hR,
    integral_re_eq_zero_of_antiFourier g hanti hzero]
  simp only [zero_div]

private theorem normalizedRadialLogProfile_nonneg_of_exterior
    {d : ℕ} (hd : 0 < d) (g : TestFunction d)
    (hnonzero : g ≠ 0) {R : ℝ} (hR : 0 < R)
    (houtside : ∀ x : Euclidean d,
      R ≤ ‖x‖ → 0 ≤ (g x).re)
    (v : ℝ) (hv : 0 ≤ v) :
    0 ≤ normalizedRadialLogProfile hd g R v := by
  have hexp : 1 ≤ Real.exp v := Real.one_le_exp_iff.mpr hv
  have hradius : 0 < R * Real.exp v :=
    mul_pos hR (Real.exp_pos v)
  have hpoint :
      R ≤ ‖(R * Real.exp v) • radialUnitDirection hd‖ := by
    rw [norm_smul, norm_radialUnitDirection hd, mul_one,
      Real.norm_eq_abs, abs_of_pos hradius]
    calc
      R = R * 1 := (mul_one R).symm
      _ ≤ R * Real.exp v :=
        mul_le_mul_of_nonneg_left hexp hR.le
  unfold normalizedRadialLogProfile
  refine mul_nonneg (mul_nonneg ?_ (pow_nonneg hradius.le _)) ?_
  · exact (div_pos (radialSurfaceArea_pos hd)
      (radialL1Mass_pos g hnonzero)).le
  · exact houtside _ hpoint

private theorem antiFourierWitness_normalizedRadialLogProfile
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) :
    let φ := normalizedRadialLogProfile hd w.function R
    Integrable φ ∧
      (∫ v : ℝ, φ v) = 0 ∧
      (∫ v : ℝ, |φ v|) = 1 ∧
      (∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) := by
  try dsimp
  refine ⟨normalizedRadialLogProfile_integrable
      hd w.function w.radial hR, ?_, ?_, ?_⟩
  · exact integral_normalizedRadialLogProfile_eq_zero_of_antiFourier
      hd w.function w.radial w.anti_fourier w.zero_value hR
  · exact integral_abs_normalizedRadialLogProfile hd w.function
      w.radial w.real w.nonzero hR
  · intro v hv
    exact normalizedRadialLogProfile_nonneg_of_exterior
      hd w.function w.nonzero hR w.eventually_nonneg v hv

end

section

open Asymptotics Filter Function MeasureTheory Metric Set
open scoped FourierTransform SchwartzMap Topology

private noncomputable def radialLineIsometry {d : ℕ} (hd : 0 < d) :
    ℝ →ₗᵢ[ℝ] Euclidean d :=
  LinearIsometry.toSpanSingleton ℝ (Euclidean d)
    (norm_radialUnitDirection hd)

private noncomputable def radialSchwartzProfile {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    (radialLineIsometry hd).toContinuousLinearMap.hasTemperateGrowth
    (radialLineIsometry hd).isometry.antilipschitz f

@[simp] private theorem radialSchwartzProfile_apply {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (r : ℝ) :
    radialSchwartzProfile hd f r = radialProfile hd f r := by
  rfl

private theorem radialProfile_smooth {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (n : ℕ∞) :
    ContDiff ℝ n (radialProfile hd f) := by
  simpa only  using! (radialSchwartzProfile hd f).smooth n

private theorem radialProfile_deriv_zero {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f) :
    deriv (radialProfile hd f) 0 = 0 := by
  have heven :
      (fun r : ℝ => radialProfile hd f (-r)) =
        radialProfile hd f := by
    funext r
    exact radialProfile_neg hd f hf r
  have hderiv := congrArg (fun h : ℝ → ℂ => deriv h 0) heven
  rw [deriv_comp_neg] at hderiv
  simp only [neg_zero] at hderiv
  linear_combination -hderiv / 2

private theorem radialProfile_quadratic_bound {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    ∃ C : ℝ, ∀ r : ℝ, 0 ≤ r → r ≤ 1 →
      ‖radialProfile hd f r‖ ≤ C * r ^ 2 := by
  have hsmooth :
      ContDiffOn ℝ (2 : ℕ∞)
        (radialProfile hd f) (Icc (0 : ℝ) 1) :=
    (radialProfile_smooth hd f 2).contDiffOn
  obtain ⟨C, hC⟩ :=
    exists_taylor_mean_remainder_bound
      (f := radialProfile hd f)
      (a := (0 : ℝ)) (b := (1 : ℝ)) (n := 1)
      zero_le_one hsmooth
  refine ⟨C, ?_⟩
  intro r hr hrone
  have hderivWithin :
      derivWithin (radialProfile hd f)
        (Icc (0 : ℝ) 1) 0 = 0 := by
    rw [DifferentiableAt.derivWithin
      ((radialProfile_smooth hd f 1).differentiable
        one_ne_zero 0)
      (uniqueDiffOn_Icc_zero_one 0 (by simp only [mem_Icc, Std.le_refl, zero_le_one, and_self]))]
    exact radialProfile_deriv_zero hd f hf
  have htaylor :
      taylorWithinEval (radialProfile hd f) 1
        (Icc (0 : ℝ) 1) 0 r = 0 := by
    rw [show (1 : ℕ) = 0 + 1 by rfl,
      taylorWithinEval_succ]
    simp only [taylor_within_zero_eval, radialProfile_zero, hzero, CharP.cast_eq_zero, zero_add,
      Nat.factorial_zero, Nat.cast_one, mul_one, inv_one, sub_zero, pow_one, one_mul,
        iteratedDerivWithin_one,
      hderivWithin, smul_zero, add_zero]
  calc
    ‖radialProfile hd f r‖ =
        ‖radialProfile hd f r -
          taylorWithinEval (radialProfile hd f) 1
            (Icc (0 : ℝ) 1) 0 r‖ := by
      rw [htaylor, sub_zero]
    _ ≤ C * r ^ 2 := by
      simpa only [sub_zero, Nat.reduceAdd] using!
        hC r ⟨hr, hrone⟩

private theorem radialProfile_isBigO_rpow_two_zero {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    radialProfile hd f =O[𝓝[>] (0 : ℝ)]
      (fun r : ℝ => r ^ (2 : ℝ)) := by
  obtain ⟨C, hC⟩ := radialProfile_quadratic_bound hd f hf hzero
  apply IsBigO.of_bound C
  filter_upwards
    [eventually_mem_nhdsWithin,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono
        nhdsWithin_le_nhds] with r hr hrone
  rw [Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hr.le 2), Real.rpow_two]
  exact hC r hr.le hrone.le

private theorem radialProfile_isBigO_rpow_atTop {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (a : ℝ) :
    radialProfile hd f =O[atTop]
      (fun r : ℝ => r ^ (-a)) := by
  have hschwartz :=
    (radialSchwartzProfile hd f).isBigO_cocompact_rpow (-a)
  have htop := hschwartz.mono atTop_le_cocompact
  refine htop.congr'
    (Eventually.of_forall
      (fun r : ℝ => radialSchwartzProfile_apply hd f r)) ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
  simp only [Real.norm_eq_abs, abs_of_pos hr]

private theorem radialProfile_locallyIntegrableOn {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) :
    LocallyIntegrableOn
      (radialProfile hd f) (Ioi (0 : ℝ)) :=
  (radialProfile_continuous hd f).locallyIntegrable.locallyIntegrableOn _

private theorem radialProfile_mellinConvergent {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (s : ℂ) (hs : -2 < s.re) :
    MellinConvergent (radialProfile hd f) s := by
  apply mellinConvergent_of_isBigO_rpow
    (a := s.re + 1) (b := (-2 : ℝ))
    (radialProfile_locallyIntegrableOn hd f)
    (radialProfile_isBigO_rpow_atTop hd f (s.re + 1))
    (by linarith)
  · simpa only [neg_neg, Real.rpow_ofNat] using! radialProfile_isBigO_rpow_two_zero hd f hf hzero
  · exact hs

private theorem radialProfile_mellin_differentiableAt {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (s : ℂ) (hs : -2 < s.re) :
    DifferentiableAt ℂ (mellin (radialProfile hd f)) s := by
  apply mellin_differentiableAt_of_isBigO_rpow
    (a := s.re + 1) (b := (-2 : ℝ))
    (radialProfile_locallyIntegrableOn hd f)
    (radialProfile_isBigO_rpow_atTop hd f (s.re + 1))
    (by linarith)
  · simpa only [neg_neg, Real.rpow_ofNat] using! radialProfile_isBigO_rpow_two_zero hd f hf hzero
  · exact hs

private noncomputable def radialMellinStrip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (z : ℂ) : ℂ :=
  mellin (radialProfile hd f)
    ((d : ℂ) / 2 - Complex.I * z)

private theorem radialMellinStrip_differentiableAt {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (z : ℂ) (hz : -(d : ℝ) / 2 - 2 < z.im) :
    DifferentiableAt ℂ (radialMellinStrip hd f) z := by
  have hs :
      -2 < (((d : ℂ) / 2 - Complex.I * z).re) := by
    norm_num
    linarith
  change
    DifferentiableAt ℂ
      (fun w : ℂ =>
        mellin (radialProfile hd f)
          ((d : ℂ) / 2 - Complex.I * w)) z
  let F : ℂ → ℂ := mellin (radialProfile hd f)
  let A : ℂ → ℂ := fun w => (d : ℂ) / 2 - Complex.I * w
  have houter : DifferentiableAt ℂ F (A z) :=
    radialProfile_mellin_differentiableAt
      hd f hf hzero
      ((d : ℂ) / 2 - Complex.I * z) hs
  have hinner : DifferentiableAt ℂ A z := by
    try dsimp [A]
    fun_prop
  have hcomp : DifferentiableAt ℂ (F ∘ A) z :=
    houter.comp z hinner
  exact hcomp

private theorem radialMellinStrip_diffContOnCl {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    DiffContOnCl ℂ (radialMellinStrip hd f)
      (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hhalf : 0 < (d : ℝ) / 2 := by
    exact half_pos (Nat.cast_pos.mpr hd)
  apply DifferentiableOn.diffContOnCl
  intro z hz
  rw [Complex.closure_preimage_im,
    closure_Ioo (ne_of_lt (neg_lt_self hhalf))] at hz
  apply
    (radialMellinStrip_differentiableAt
      hd f hf hzero z (by linarith [hz.1])).differentiableWithinAt

private noncomputable def normalizedRadialMellinStrip {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (R : ℝ) (z : ℂ) : ℂ :=
  (radialSurfaceArea d / radialL1Mass f : ℝ) *
    Complex.exp
      (((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ)) *
      radialMellinStrip hd f z

private theorem normalizedRadialMellinStrip_diffContOnCl {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) (R : ℝ) :
    DiffContOnCl ℂ (normalizedRadialMellinStrip hd f R)
      (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) := by
  have hstrip := radialMellinStrip_diffContOnCl hd f hf hzero
  have hfactor :
      Differentiable ℂ
        (fun z : ℂ =>
          (radialSurfaceArea d / radialL1Mass f : ℝ) *
            Complex.exp
              (((d : ℂ) / 2 + Complex.I * z) *
                (Real.log R : ℂ))) := by
    fun_prop
  exact
    ⟨hfactor.differentiableOn.mul hstrip.differentiableOn,
      hfactor.continuous.continuousOn.mul hstrip.continuousOn⟩

private theorem norm_nonnegative_imaginary_cpow_le_one
    (r t : ℝ) (hr : 0 ≤ r) :
    ‖(r : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1 := by
  rcases eq_or_lt_of_le hr with rfl | hrpos
  · by_cases ht : t = 0
    · simp only [Complex.ofReal_zero, ht, mul_zero, neg_zero, Complex.cpow_zero, norm_one,
      Std.le_refl]
    · have hexponent :
          -(Complex.I * (t : ℂ)) ≠ 0 := by
        exact neg_ne_zero.mpr
          (mul_ne_zero Complex.I_ne_zero
            (Complex.ofReal_ne_zero.mpr ht))
      change ‖(0 : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤ 1
      rw [Complex.zero_cpow hexponent]
      simp only [norm_zero, zero_le_one]
  · rw [Complex.norm_cpow_eq_rpow_re_of_pos hrpos]
    norm_num

private theorem schwartz_imaginaryRiesz_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    Integrable
      (fun x : Euclidean d =>
        f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))) := by
  apply schwartz_mul_norm_cpow_integrable
    hd f (-(Complex.I * (t : ℂ)))
  · norm_num
    exact Nat.cast_pos.mpr hd
  · norm_num

private theorem norm_schwartz_imaginaryRiesz_integral_le_L1 {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (t : ℝ) :
    ‖∫ x : Euclidean d,
      f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
      radialL1Mass f := by
  calc
    ‖∫ x : Euclidean d,
      f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
        ∫ x : Euclidean d,
          ‖f x * (‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x : Euclidean d, ‖f x‖ := by
      apply integral_mono
        (schwartz_imaginaryRiesz_integrable hd f t).norm
        f.integrable.norm
      intro x
      try dsimp
      rw [norm_mul]
      calc
        ‖f x‖ *
            ‖(‖x‖ : ℂ) ^ (-(Complex.I * (t : ℂ)))‖ ≤
          ‖f x‖ * 1 :=
            mul_le_mul_of_nonneg_left
              (norm_nonnegative_imaginary_cpow_le_one
                ‖x‖ t (norm_nonneg x))
              (norm_nonneg _)
        _ = ‖f x‖ := mul_one _
    _ = radialL1Mass f := rfl

private theorem normalizedRadialMellinStrip_top_norm_le_one {d : ℕ}
    (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hnonzero : f ≠ 0)
    (R : ℝ) (y : ℝ) :
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) +
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤ 1 := by
  let z : ℂ :=
    (y : ℂ) + Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)
  let s : ℂ := (d : ℂ) - Complex.I * (y : ℂ)
  have hmass : 0 < radialL1Mass f :=
    radialL1Mass_pos f hnonzero
  have hsurface : 0 < radialSurfaceArea d :=
    radialSurfaceArea_pos hd
  have hmellin :
      (d : ℂ) / 2 - Complex.I * z = s := by
    try dsimp [z, s]
    push_cast
    simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul]; ring
  have hphase :
      ((((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ))).re = 0 := by
    try dsimp [z]
    push_cast
    norm_num
  have hpolar :
      (∫ x : Euclidean d,
        f x * (‖x‖ : ℂ) ^ (-(Complex.I * (y : ℂ)))) =
        radialSurfaceArea d • mellin (radialProfile hd f) s := by
    have hexponent : s - (d : ℂ) =
        -(Complex.I * (y : ℂ)) := by
      try dsimp [s]
      ring
    simpa only [hexponent] using!
      integral_radialProfile_cpow hd f hf s
  have hbound :
      radialSurfaceArea d * ‖mellin (radialProfile hd f) s‖ ≤
        radialL1Mass f := by
    calc
      radialSurfaceArea d * ‖mellin (radialProfile hd f) s‖ =
          ‖radialSurfaceArea d •
            mellin (radialProfile hd f) s‖ := by
        rw [norm_smul, Real.norm_eq_abs,
          abs_of_pos hsurface]
      _ = ‖∫ x : Euclidean d,
          f x * (‖x‖ : ℂ) ^
            (-(Complex.I * (y : ℂ)))‖ := by
        rw [hpolar]
      _ ≤ radialL1Mass f :=
        norm_schwartz_imaginaryRiesz_integral_le_L1 hd f y
  change ‖normalizedRadialMellinStrip hd f R z‖ ≤ 1
  calc
    ‖normalizedRadialMellinStrip hd f R z‖ =
        (radialSurfaceArea d / radialL1Mass f) *
          ‖mellin (radialProfile hd f) s‖ := by
      unfold normalizedRadialMellinStrip radialMellinStrip
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs,
        abs_of_pos (div_pos hsurface hmass),
        Complex.norm_exp, hphase, Real.exp_zero,
        hmellin]
      ring
    _ = (radialSurfaceArea d *
          ‖mellin (radialProfile hd f) s‖) /
            radialL1Mass f := by
      ring
    _ ≤ 1 := (div_le_one hmass).mpr hbound

private theorem radial_fourier_mellin_regularized_closed {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hhatZero : (𝓕 f : TestFunction d) (0 : Euclidean d) = 0)
    (s : ℂ) (hs : 0 ≤ s.re) (hsd : s.re ≤ (d : ℝ)) :
    mellin (radialProfile hd (𝓕 f : TestFunction d)) s *
        (Complex.Gamma (s / 2))⁻¹ =
      (Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
        (mellin (radialProfile hd f) ((d : ℂ) - s) *
          (Complex.Gamma (((d : ℂ) - s) / 2))⁻¹) := by
  let U : Set ℂ := Complex.re ⁻¹' Ioo (0 : ℝ) (d : ℝ)
  let T : Set ℂ := Complex.re ⁻¹' Icc (0 : ℝ) (d : ℝ)
  let L : ℂ → ℂ := fun w =>
    mellin (radialProfile hd (𝓕 f : TestFunction d)) w *
      (Complex.Gamma (w / 2))⁻¹
  let G : ℂ → ℂ := fun w =>
    (Real.pi : ℂ) ^ ((d : ℂ) / 2 - w) *
      (mellin (radialProfile hd f) ((d : ℂ) - w) *
        (Complex.Gamma (((d : ℂ) - w) / 2))⁻¹)
  have hinv : Continuous (fun w : ℂ => (Complex.Gamma w)⁻¹) :=
    Complex.differentiable_one_div_Gamma.continuous
  have hhat : ContinuousOn
      (fun w : ℂ =>
        mellin (radialProfile hd (𝓕 f : TestFunction d)) w) T := by
    intro w hw
    change 0 ≤ w.re ∧ w.re ≤ (d : ℝ) at hw
    exact
      (radialProfile_mellin_differentiableAt hd
        (𝓕 f : TestFunction d)
        (gaussianMellin_fourier_radial hf) hhatZero w
        (by linarith [hw.1])).continuousAt.continuousWithinAt
  have hprimal : ContinuousOn
      (fun w : ℂ =>
        mellin (radialProfile hd f) ((d : ℂ) - w)) T := by
    intro w hw
    change 0 ≤ w.re ∧ w.re ≤ (d : ℝ) at hw
    have hinner : ContinuousAt (fun v : ℂ => (d : ℂ) - v) w := by
      fun_prop
    have hre : -2 < (((d : ℂ) - w).re) := by
      norm_num
      linarith [hw.2]
    exact
      ((radialProfile_mellin_differentiableAt hd f hf hzero
        ((d : ℂ) - w) hre).continuousAt.comp
        hinner).continuousWithinAt
  have hL : ContinuousOn L T := by
    try dsimp [L]
    exact hhat.mul
      (hinv.comp (continuous_id.div_const (2 : ℂ))).continuousOn
  have hpi :
      Continuous (fun w : ℂ =>
        (Real.pi : ℂ) ^ ((d : ℂ) / 2 - w)) := by
    exact (continuous_const.sub continuous_id).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hG : ContinuousOn G T := by
    try dsimp [G]
    exact hpi.continuousOn.mul
      (hprimal.mul
        (hinv.comp
          ((continuous_const.sub continuous_id).div_const
            (2 : ℂ))).continuousOn)
  have heq : Set.EqOn L G U := by
    intro w hw
    change 0 < w.re ∧ w.re < (d : ℝ) at hw
    have hg₁ : Complex.Gamma (w / 2) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      norm_num
      linarith [hw.1]
    have hg₂ : Complex.Gamma (((d : ℂ) - w) / 2) ≠ 0 := by
      apply Complex.Gamma_ne_zero_of_re_pos
      norm_num
      linarith [hw.2]
    try dsimp [L, G]
    rw [radial_fourier_mellin_strip hd f hf w hw.1 hw.2]
    field_simp
  have hUT : U ⊆ T := by
    intro w hw
    exact ⟨hw.1.le, hw.2.le⟩
  have hdreal : (0 : ℝ) < (d : ℝ) := Nat.cast_pos.mpr hd
  have hTU : T ⊆ closure U := by
    try dsimp [T, U]
    rw [Complex.closure_preimage_re,
      closure_Ioo (ne_of_lt hdreal)]
  exact heq.of_subset_closure hL hG hUT hTU ⟨hs, hsd⟩

private theorem radial_fourier_mellin_antifourier_boundary {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hanti : (𝓕 f : TestFunction d) = -f)
    (y : ℝ) (hy : y ≠ 0) :
    Complex.Gamma
        (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2) *
        mellin (radialProfile hd f) (-(Complex.I * (y : ℂ))) =
      -((Real.pi : ℂ) ^
          (((d : ℂ) / 2) + Complex.I * (y : ℂ)) *
        Complex.Gamma (-(Complex.I * (y : ℂ)) / 2) *
        mellin (radialProfile hd f)
          ((d : ℂ) + Complex.I * (y : ℂ))) := by
  let s : ℂ := -(Complex.I * (y : ℂ))
  have hhatZero :
      (𝓕 f : TestFunction d) (0 : Euclidean d) = 0 := by
    rw [hanti]
    simpa only [neg_apply, neg_eq_zero, neg_zero] using! congrArg Neg.neg hzero
  have hs : 0 ≤ s.re := by
    try dsimp [s]
    norm_num
  have hsd : s.re ≤ (d : ℝ) := by
    try dsimp [s]
    norm_num
  have hnum : Complex.Gamma (s / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    try dsimp [s] at him
    norm_num at him
    apply hy
    linarith
  have hden : Complex.Gamma (((d : ℂ) - s) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    try dsimp [s]
    norm_num
    exact Nat.cast_pos.mpr hd
  have heq := radial_fourier_mellin_regularized_closed
    hd f hf hzero hhatZero s hs hsd
  have hprofile :
      mellin (radialProfile hd (𝓕 f : TestFunction d)) s =
        -(mellin (radialProfile hd f) s) := by
    rw [hanti]
    simp only [mellin, radialProfile, neg_apply, smul_eq_mul, mul_neg, integral_neg]
  rw [hprofile] at heq
  have hcross :
      Complex.Gamma (((d : ℂ) - s) / 2) *
          mellin (radialProfile hd f) s =
        -((Real.pi : ℂ) ^ ((d : ℂ) / 2 - s) *
          Complex.Gamma (s / 2) *
          mellin (radialProfile hd f) ((d : ℂ) - s)) := by
    field_simp [hnum, hden] at heq ⊢
    linear_combination -heq
  convert! hcross using 1 <;> dsimp [s] <;>
    push_cast <;> ring_nf

private theorem radial_fourier_mellin_antifourier_boundary_norm {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hanti : (𝓕 f : TestFunction d) = -f)
    (y : ℝ) (hy : y ≠ 0) :
    ‖mellin (radialProfile hd f) (-(Complex.I * (y : ℂ)))‖ =
      Real.pi ^ ((d : ℝ) / 2) *
        (‖Complex.Gamma (-(Complex.I * (y : ℂ)) / 2)‖ /
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2)‖) *
          ‖mellin (radialProfile hd f)
            ((d : ℂ) + Complex.I * (y : ℂ))‖ := by
  have hdenGamma :
      Complex.Gamma
        (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
    exact Nat.cast_pos.mpr hd
  have hden :
      ‖Complex.Gamma
        (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hdenGamma
  have hnorm := congrArg norm
    (radial_fourier_mellin_antifourier_boundary
      hd f hf hzero hanti y hy)
  simp only [norm_mul, norm_neg,
    Complex.norm_cpow_eq_rpow_re_of_pos Real.pi_pos] at hnorm
  norm_num at hnorm
  calc
    ‖mellin (radialProfile hd f) (-(Complex.I * (y : ℂ)))‖ =
        (Real.pi ^ ((d : ℝ) / 2) *
          ‖Complex.Gamma (-(Complex.I * (y : ℂ)) / 2)‖ *
          ‖mellin (radialProfile hd f)
            ((d : ℂ) + Complex.I * (y : ℂ))‖) /
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2)‖ := by
      apply (eq_div_iff hden).2
      push_cast
      convert! hnorm using 1; ring
    _ = Real.pi ^ ((d : ℝ) / 2) *
        (‖Complex.Gamma (-(Complex.I * (y : ℂ)) / 2)‖ /
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) + Complex.I * (y : ℂ) / 2)‖) *
          ‖mellin (radialProfile hd f)
            ((d : ℂ) + Complex.I * (y : ℂ))‖ := by
      ring

private theorem normalizedRadialMellinStrip_top_norm_eq {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hnonzero : f ≠ 0)
    (R : ℝ) (y : ℝ) :
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) +
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ =
      (radialSurfaceArea d / radialL1Mass f) *
        ‖mellin (radialProfile hd f)
          ((d : ℂ) - Complex.I * (y : ℂ))‖ := by
  let z : ℂ :=
    (y : ℂ) + Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)
  have hmass : 0 < radialL1Mass f :=
    radialL1Mass_pos f hnonzero
  have hsurface : 0 < radialSurfaceArea d :=
    radialSurfaceArea_pos hd
  have hmellin :
      (d : ℂ) / 2 - Complex.I * z =
        (d : ℂ) - Complex.I * (y : ℂ) := by
    try dsimp [z]
    push_cast
    simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul]; ring
  have hphase :
      ((((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ))).re = 0 := by
    try dsimp [z]
    push_cast
    norm_num
  change ‖normalizedRadialMellinStrip hd f R z‖ = _
  unfold normalizedRadialMellinStrip radialMellinStrip
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (div_pos hsurface hmass),
    Complex.norm_exp, hphase, Real.exp_zero, hmellin]
  ring

private theorem normalizedRadialMellinStrip_bottom_norm_eq {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hnonzero : f ≠ 0)
    (R : ℝ) (y : ℝ) :
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ =
      (radialSurfaceArea d / radialL1Mass f) *
        Real.exp ((d : ℝ) * Real.log R) *
        ‖mellin (radialProfile hd f)
          (-(Complex.I * (y : ℂ)))‖ := by
  let z : ℂ :=
    (y : ℂ) - Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ)
  have hmass : 0 < radialL1Mass f :=
    radialL1Mass_pos f hnonzero
  have hsurface : 0 < radialSurfaceArea d :=
    radialSurfaceArea_pos hd
  have hmellin :
      (d : ℂ) / 2 - Complex.I * z =
        -(Complex.I * (y : ℂ)) := by
    try dsimp [z]
    push_cast
    simp only [mul_sub, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, sub_neg_eq_add,
      sub_add_cancel_right]
  have hphase :
      ((((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ))).re =
          (d : ℝ) * Real.log R := by
    try dsimp [z]
    push_cast
    norm_num
  change ‖normalizedRadialMellinStrip hd f R z‖ = _
  unfold normalizedRadialMellinStrip radialMellinStrip
  rw [norm_mul, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (div_pos hsurface hmass),
    Complex.norm_exp, hphase, hmellin]

private theorem radialGammaBoundaryExponent_exp
    (d : ℕ) (R A B : ℝ)
    (hR : 0 < R) (hA : 0 < A) (hB : 0 < B) :
    Real.exp
        (((d : ℝ) / 2) * Real.log (Real.pi * R ^ 2) +
          Real.log A - Real.log B) =
      Real.exp ((d : ℝ) * Real.log R) *
        Real.pi ^ ((d : ℝ) / 2) * (A / B) := by
  have hlog :
      Real.log (Real.pi * R ^ 2) =
        Real.log Real.pi + 2 * Real.log R := by
    rw [Real.log_mul Real.pi_ne_zero
      (pow_ne_zero 2 hR.ne'), Real.log_pow]
    norm_num
  have hscale :
      Real.exp (((d : ℝ) / 2) *
        Real.log (Real.pi * R ^ 2)) =
      Real.exp ((d : ℝ) * Real.log R) *
        Real.pi ^ ((d : ℝ) / 2) := by
    rw [hlog, mul_add, Real.exp_add,
      Real.rpow_def_of_pos Real.pi_pos]
    have hdouble :
        ((d : ℝ) / 2) * (2 * Real.log R) =
          (d : ℝ) * Real.log R := by
      ring
    rw [hdouble]
    rw [show ((d : ℝ) / 2) * Real.log Real.pi =
      Real.log Real.pi * ((d : ℝ) / 2) by ring]
    ring
  rw [Real.exp_sub, Real.exp_add,
    Real.exp_log hA, Real.exp_log hB, hscale]
  ring

private theorem normalizedRadialMellinStrip_bottom_norm_le_gamma {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0)
    (hanti : (𝓕 f : TestFunction d) = -f)
    (hnonzero : f ≠ 0)
    (R : ℝ) (hR : 0 < R) (y : ℝ) (hy : y ≠ 0) :
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
      Real.exp
        (((d : ℝ) / 2) * Real.log (Real.pi * R ^ 2) +
          Real.log
            ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma
              (((d : ℝ) / 2 : ℝ) +
                Complex.I * (y : ℂ) / 2)‖) := by
  have hnumGamma :
      Complex.Gamma (-Complex.I * (y : ℂ) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero
    intro n hn
    have him := congrArg Complex.im hn
    norm_num at him
    apply hy
    linarith
  have hdenGamma :
      Complex.Gamma
        (((d : ℝ) / 2 : ℝ) +
          Complex.I * (y : ℂ) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
    exact Nat.cast_pos.mpr hd
  have hnum :
      0 < ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ :=
    norm_pos_iff.mpr hnumGamma
  have hden :
      0 < ‖Complex.Gamma
        (((d : ℝ) / 2 : ℝ) +
          Complex.I * (y : ℂ) / 2)‖ :=
    norm_pos_iff.mpr hdenGamma
  have htop :=
    normalizedRadialMellinStrip_top_norm_le_one
      hd f hf hnonzero R (-y)
  rw [normalizedRadialMellinStrip_top_norm_eq
    hd f hnonzero R (-y)] at htop
  have hdual :
      (radialSurfaceArea d / radialL1Mass f) *
        ‖mellin (radialProfile hd f)
          ((d : ℂ) + Complex.I * (y : ℂ))‖ ≤ 1 := by
    simpa only [Complex.ofReal_neg, mul_neg, sub_neg_eq_add] using! htop
  have hboundary :=
    radial_fourier_mellin_antifourier_boundary_norm
      hd f hf hzero hanti y hy
  have harg :
      -(Complex.I * (y : ℂ)) / 2 =
        -Complex.I * (y : ℂ) / 2 := by
    ring
  rw [harg] at hboundary
  have hfactor :
      0 ≤ Real.exp ((d : ℝ) * Real.log R) *
        Real.pi ^ ((d : ℝ) / 2) *
        (‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ /
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) +
              Complex.I * (y : ℂ) / 2)‖) := by
    positivity
  calc
    ‖normalizedRadialMellinStrip hd f R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ =
        (radialSurfaceArea d / radialL1Mass f) *
          Real.exp ((d : ℝ) * Real.log R) *
          ‖mellin (radialProfile hd f)
            (-(Complex.I * (y : ℂ)))‖ :=
      normalizedRadialMellinStrip_bottom_norm_eq
        hd f hnonzero R y
    _ = (Real.exp ((d : ℝ) * Real.log R) *
          Real.pi ^ ((d : ℝ) / 2) *
          (‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ /
            ‖Complex.Gamma
              (((d : ℝ) / 2 : ℝ) +
                Complex.I * (y : ℂ) / 2)‖)) *
          ((radialSurfaceArea d / radialL1Mass f) *
            ‖mellin (radialProfile hd f)
              ((d : ℂ) + Complex.I * (y : ℂ))‖) := by
      rw [hboundary]
      ring
    _ ≤ (Real.exp ((d : ℝ) * Real.log R) *
          Real.pi ^ ((d : ℝ) / 2) *
          (‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ /
            ‖Complex.Gamma
              (((d : ℝ) / 2 : ℝ) +
                Complex.I * (y : ℂ) / 2)‖)) * 1 :=
      mul_le_mul_of_nonneg_left hdual hfactor
    _ = Real.exp
        (((d : ℝ) / 2) * Real.log (Real.pi * R ^ 2) +
          Real.log
            ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma
              (((d : ℝ) / 2 : ℝ) +
                Complex.I * (y : ℂ) / 2)‖) := by
      rw [mul_one]
      exact
        (radialGammaBoundaryExponent_exp d R
          ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖
          ‖Complex.Gamma
            (((d : ℝ) / 2 : ℝ) +
              Complex.I * (y : ℂ) / 2)‖
          hR hnum hden).symm

private theorem radialProfile_mellin_uniform_strip_bound {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ s : ℂ, 0 ≤ s.re → s.re ≤ (d : ℝ) →
        ‖mellin (radialProfile hd f) s‖ ≤ C := by
  have hmeas :
      AEStronglyMeasurable (radialProfile hd f)
        (volume.restrict (Ioi (0 : ℝ))) :=
    (radialProfile_continuous hd f).aestronglyMeasurable
  have hzeroWeight : IntegrableOn
      (fun r : ℝ => r ^ (-(1 : ℝ)) *
        ‖radialProfile hd f r‖) (Ioi (0 : ℝ)) := by
    have hconv := radialProfile_mellinConvergent
      hd f hf hzero (0 : ℂ) (by norm_num)
    simpa only [Complex.zero_re, zero_sub] using!
      (mellin_convergent_iff_norm
        (T := Ioi (0 : ℝ)) Subset.rfl
        measurableSet_Ioi hmeas).mp hconv
  have hdimensionWeight : IntegrableOn
      (fun r : ℝ => r ^ ((d : ℝ) - 1) *
        ‖radialProfile hd f r‖) (Ioi (0 : ℝ)) := by
    have hre : -2 < ((d : ℂ).re) := by
      norm_num
      linarith [show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d]
    have hconv := radialProfile_mellinConvergent
      hd f hf hzero (d : ℂ) hre
    simpa only [Complex.natCast_re] using!
      (mellin_convergent_iff_norm
        (T := Ioi (0 : ℝ)) Subset.rfl
        measurableSet_Ioi hmeas).mp hconv
  have hmajor : IntegrableOn
      (fun r : ℝ =>
        (r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1)) *
          ‖radialProfile hd f r‖) (Ioi (0 : ℝ)) := by
    simpa only [add_mul] using!
      hzeroWeight.add hdimensionWeight
  let B : ℝ :=
    ∫ r : ℝ in Ioi (0 : ℝ),
      (r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1)) *
        ‖radialProfile hd f r‖
  refine ⟨max 0 B, le_max_left _ _, ?_⟩
  intro s hs hsd
  have hconv : MellinConvergent (radialProfile hd f) s :=
    radialProfile_mellinConvergent hd f hf hzero s (by linarith)
  have hbound : ‖mellin (radialProfile hd f) s‖ ≤ B := by
    calc
      ‖mellin (radialProfile hd f) s‖ ≤
          ∫ r : ℝ in Ioi (0 : ℝ),
            ‖(r : ℂ) ^ (s - 1) • radialProfile hd f r‖ :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ r : ℝ in Ioi (0 : ℝ),
          (r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1)) *
            ‖radialProfile hd f r‖ := by
        apply integral_mono_ae hconv.norm hmajor
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
        change 0 < r at hr
        rw [norm_smul,
          Complex.norm_cpow_eq_rpow_re_of_pos hr]
        norm_num
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        by_cases hone : r ≤ 1
        · calc
            r ^ (s.re - 1) ≤ r ^ (-(1 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_ge hr hone
                (by linarith)
            _ ≤ r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1) := by
              exact le_add_of_nonneg_right
                (Real.rpow_nonneg hr.le _)
        · have hlarge : 1 ≤ r := le_of_not_ge hone
          calc
            r ^ (s.re - 1) ≤ r ^ ((d : ℝ) - 1) :=
              Real.rpow_le_rpow_of_exponent_le hlarge
                (by linarith)
            _ ≤ r ^ (-(1 : ℝ)) + r ^ ((d : ℝ) - 1) := by
              exact le_add_of_nonneg_left
                (Real.rpow_nonneg hr.le _)
      _ = B := rfl
  exact hbound.trans (le_max_right _ _)

private theorem normalizedRadialMellinStrip_uniform_bound {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hf : IsRadial f)
    (hzero : f (0 : Euclidean d) = 0) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ,
        -((d : ℝ) / 2) ≤ z.im →
        z.im ≤ (d : ℝ) / 2 →
          ‖normalizedRadialMellinStrip hd f R z‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ :=
    radialProfile_mellin_uniform_strip_bound hd f hf hzero
  let B : ℝ :=
    |radialSurfaceArea d / radialL1Mass f| *
      Real.exp ((d : ℝ) * |Real.log R|) * C
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro z hzlower hzupper
  have hsnonneg :
      0 ≤ (((d : ℂ) / 2 - Complex.I * z).re) := by
    norm_num
    linarith
  have hsupper :
      (((d : ℂ) / 2 - Complex.I * z).re) ≤ (d : ℝ) := by
    norm_num
    linarith
  have hphase :
      ((((d : ℂ) / 2 + Complex.I * z) *
        (Real.log R : ℂ))).re ≤
        (d : ℝ) * |Real.log R| := by
    norm_num
    have hcoefnonneg :
        0 ≤ (d : ℝ) / 2 - z.im := by
      linarith
    have hcoefupper :
        (d : ℝ) / 2 - z.im ≤ (d : ℝ) := by
      linarith
    calc
      ((d : ℝ) / 2 - z.im) * Real.log R ≤
          ((d : ℝ) / 2 - z.im) * |Real.log R| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) hcoefnonneg
      _ ≤ (d : ℝ) * |Real.log R| :=
        mul_le_mul_of_nonneg_right hcoefupper (abs_nonneg _)
  change ‖normalizedRadialMellinStrip hd f R z‖ ≤ B
  calc
    ‖normalizedRadialMellinStrip hd f R z‖ =
        |radialSurfaceArea d / radialL1Mass f| *
          Real.exp
            ((((d : ℂ) / 2 + Complex.I * z) *
              (Real.log R : ℂ))).re *
          ‖mellin (radialProfile hd f)
            ((d : ℂ) / 2 - Complex.I * z)‖ := by
      unfold normalizedRadialMellinStrip radialMellinStrip
      rw [norm_mul, norm_mul, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_exp]
    _ ≤ |radialSurfaceArea d / radialL1Mass f| *
          Real.exp ((d : ℝ) * |Real.log R|) * C := by
      gcongr
      exact hbound _ hsnonneg hsupper
    _ = B := rfl

private theorem normalizedRadialLogProfile_ofReal {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hreal : IsRealValued f)
    (R v : ℝ) :
    (normalizedRadialLogProfile hd f R v : ℂ) =
      ((radialSurfaceArea d / radialL1Mass f : ℝ) : ℂ) *
        (((R * Real.exp v) ^ d : ℝ) : ℂ) *
        radialProfile hd f (R * Real.exp v) := by
  have hvalue :
      radialProfile hd f (R * Real.exp v) =
        (((radialProfile hd f (R * Real.exp v)).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp only [Complex.ofReal_re]
    · simpa only [Complex.ofReal_im] using! radialProfile_real hd f hreal (R * Real.exp v)
  unfold normalizedRadialLogProfile
  rw [hvalue]
  simp only [Complex.ofReal_re]
  push_cast
  ring

private theorem normalizedRadialLogProfile_weighted_ofReal {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hreal : IsRealValued f)
    (R a v : ℝ) :
    (Real.exp (-a * v) : ℂ) *
        (normalizedRadialLogProfile hd f R v : ℂ) =
      ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ) *
        (Real.exp (((d : ℝ) - a) * v) : ℂ) *
        radialProfile hd f (R * Real.exp v) := by
  have hexp :
      Real.exp (-a * v) * (R * Real.exp v) ^ d =
        R ^ d * Real.exp (((d : ℝ) - a) * v) := by
    rw [mul_pow, ← Real.exp_nat_mul]
    calc
      Real.exp (-a * v) *
          (R ^ d * Real.exp ((d : ℝ) * v)) =
        R ^ d *
          (Real.exp (-a * v) * Real.exp ((d : ℝ) * v)) := by
        ring
      _ = R ^ d * Real.exp (-a * v + (d : ℝ) * v) := by
        rw [← Real.exp_add]
      _ = R ^ d * Real.exp (((d : ℝ) - a) * v) := by
        congr 1
        ring_nf
  rw [normalizedRadialLogProfile_ofReal hd f hreal R v]
  have hcomplex := congrArg (fun x : ℝ => (x : ℂ)) hexp
  push_cast at hcomplex ⊢
  linear_combination
    (((radialSurfaceArea d : ℝ) : ℂ) /
      ((radialL1Mass f : ℝ) : ℂ) *
      radialProfile hd f (R * Real.exp v)) * hcomplex

private theorem normalizedRadialMellinStrip_shifted_eq_fourier {d : ℕ}
    (hd : 0 < d) (f : TestFunction d) (hreal : IsRealValued f)
    (R : ℝ) (hR : 0 < R) (a t : ℝ) :
    normalizedRadialMellinStrip hd f R
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ))) =
      (𝓕 (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) :
          ℝ → ℂ) (t / (2 * Real.pi)) := by
  let s : ℂ := (((d : ℝ) - a : ℝ) : ℂ) -
    Complex.I * (t : ℂ)
  let g : ℝ → ℂ := fun u =>
    Real.exp (-((d : ℝ) - a) * u) •
      radialProfile hd f (R * Real.exp (-u))
  let c : ℂ :=
    ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ)
  have hweight :
      (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) =
        c • (fun v : ℝ => g (-v)) := by
    funext v
    have hv :=
      normalizedRadialLogProfile_weighted_ofReal
        hd f hreal R a v
    change _ = c * g (-v)
    calc
      (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ) =
          ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ) *
            (Real.exp (((d : ℝ) - a) * v) : ℂ) *
            radialProfile hd f (R * Real.exp v) := hv
      _ = c * g (-v) := by
        simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow,
          Complex.ofReal_exp, Complex.ofReal_sub,
          Complex.ofReal_natCast, neg_sub, Complex.real_smul, Complex.ofReal_neg, mul_neg,
            neg_neg, c, g]
        ring_nf
  have hmellin :
      mellin (fun r : ℝ => radialProfile hd f (R * r)) s =
        (𝓕 g : ℝ → ℂ) (-(t / (2 * Real.pi))) := by
    simpa [s, g, neg_div] using!
      (mellin_eq_fourier
        (fun r : ℝ => radialProfile hd f (R * r))
        (s := s))
  have hscalar (F : ℝ → ℂ) (x : ℝ) :
      (𝓕 (c • F) : ℝ → ℂ) x =
        c * (𝓕 F : ℝ → ℂ) x := by
    rw [Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    ring
  have hfourier :
      (𝓕 (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) :
          ℝ → ℂ) (t / (2 * Real.pi)) =
        c * mellin (fun r : ℝ =>
          radialProfile hd f (R * r)) s := by
    calc
      (𝓕 (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) :
          ℝ → ℂ) (t / (2 * Real.pi)) =
          c * (𝓕 (fun v : ℝ => g (-v)) :
            ℝ → ℂ) (t / (2 * Real.pi)) := by
        rw [hweight,
          hscalar (fun v : ℝ => g (-v))]
      _ = c * (𝓕 g : ℝ → ℂ)
            (-(t / (2 * Real.pi))) := by
        congr 1
        rw [← Real.fourierInv_eq_fourier_comp_neg g,
          Real.fourierInv_eq_fourier_neg]
      _ = c * mellin (fun r : ℝ =>
          radialProfile hd f (R * r)) s := by
        rw [hmellin]
  have hRcomplex : (R : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hR.ne'
  have hRpow :
      ((R ^ d : ℝ) : ℂ) = (R : ℂ) ^ (d : ℂ) := by
    push_cast
    rw [Complex.cpow_natCast]
  have hpower :
      ((R ^ d : ℝ) : ℂ) * (R : ℂ) ^ (-s) =
        Complex.exp
          ((((a : ℂ) + Complex.I * (t : ℂ)) *
            (Real.log R : ℂ))) := by
    rw [hRpow, ← Complex.cpow_add _ _ hRcomplex,
      Complex.cpow_def_of_ne_zero hRcomplex,
      ← Complex.ofReal_log hR.le]
    congr 1
    try dsimp [s]
    push_cast
    ring
  have hscale :
      c * mellin (fun r : ℝ =>
        radialProfile hd f (R * r)) s =
      ((radialSurfaceArea d / radialL1Mass f : ℝ) : ℂ) *
        Complex.exp
          ((((a : ℂ) + Complex.I * (t : ℂ)) *
            (Real.log R : ℂ))) *
        mellin (radialProfile hd f) s := by
    rw [mellin_comp_mul_left
      (radialProfile hd f) s hR]
    simp only [smul_eq_mul]
    try dsimp [c]
    push_cast
    have hc := hpower
    push_cast at hc
    linear_combination
      (((radialSurfaceArea d : ℝ) : ℂ) /
        ((radialL1Mass f : ℝ) : ℂ) *
          mellin (radialProfile hd f) s) * hc
  have harg :
      (d : ℂ) / 2 - Complex.I *
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ))) = s := by
    try dsimp [s]
    push_cast
    simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_sub]; ring
  have hphase :
      (d : ℂ) / 2 + Complex.I *
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ))) =
        (a : ℂ) + Complex.I * (t : ℂ) := by
    push_cast
    simp only [mul_add, ← mul_assoc, Complex.I_mul_I, neg_mul, one_mul, neg_sub]; ring
  unfold normalizedRadialMellinStrip radialMellinStrip
  rw [harg, hphase]
  exact hscale.symm.trans hfourier.symm

private theorem normalizedRadialLogProfile_weighted_integrable {d : ℕ}
    (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hreal : IsRealValued f)
    (hzero : f (0 : Euclidean d) = 0)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ) + 2) :
    Integrable (fun v : ℝ =>
      (Real.exp (-a * v) : ℂ) *
        (normalizedRadialLogProfile hd f R v : ℂ)) := by
  let κ : ℝ := (d : ℝ) - a
  have hκ : -2 < κ := by
    try dsimp [κ]
    linarith
  have hconv : MellinConvergent
      (radialProfile hd f) (κ : ℂ) := by
    apply radialProfile_mellinConvergent hd f hf hzero
    simpa only [Complex.ofReal_re] using! hκ
  have hscaled : MellinConvergent
      (fun r : ℝ => radialProfile hd f (R * r)) (κ : ℂ) :=
    (MellinConvergent.comp_mul_left hR).mpr hconv
  have hchange : Integrable (fun v : ℝ =>
      (1 * Real.exp v) •
        (((1 * Real.exp v : ℝ) : ℂ) ^
          ((κ : ℂ) - 1) •
            radialProfile hd f (R * (1 * Real.exp v)))) := by
    apply (integrable_scaled_exp_change_Ioi
      (R := (1 : ℝ)) (by norm_num)
      (fun r : ℝ =>
        (r : ℂ) ^ ((κ : ℂ) - 1) •
          radialProfile hd f (R * r))).mp
    exact hscaled
  have hpower (v : ℝ) :
      (Real.exp v : ℂ) *
        (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) =
          (Real.exp (κ * v) : ℂ) := by
    have hbase : (Real.exp v : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)
    calc
      (Real.exp v : ℂ) *
          (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) =
        (Real.exp v : ℂ) ^ (1 : ℂ) *
          (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) := by
        rw [Complex.cpow_one]
      _ = (Real.exp v : ℂ) ^
          ((1 : ℂ) + ((κ : ℂ) - 1)) := by
        rw [Complex.cpow_add _ _ hbase]
      _ =
        (Real.exp v : ℂ) ^ (κ : ℂ) := by
        congr 1
        ring
      _ = (Real.exp (κ * v) : ℂ) := by
        rw [Complex.cpow_def_of_ne_zero hbase,
          ← Complex.ofReal_log (Real.exp_pos v).le,
          Real.log_exp, Complex.ofReal_exp]
        congr 1
        push_cast
        ring
  have hplus : Integrable (fun v : ℝ =>
      (Real.exp (κ * v) : ℂ) *
        radialProfile hd f (R * Real.exp v)) := by
    apply hchange.congr
    filter_upwards [] with v
    simp only [one_mul, smul_eq_mul, Complex.real_smul]
    rw [← mul_assoc, hpower]
  have hfactor :=
    hplus.const_mul
      ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ)
  apply hfactor.congr
  filter_upwards [] with v
  rw [normalizedRadialLogProfile_weighted_ofReal
    hd f hreal R a v]
  try dsimp [κ]
  ring

private theorem integrable_fourier_of_integrable_two_derivatives
    (g : ℝ → ℂ) (hg : Integrable g)
    (hgdiff : Differentiable ℝ g)
    (hg' : Integrable (deriv g))
    (hg'diff : Differentiable ℝ (deriv g))
    (hg'' : Integrable (deriv (deriv g))) :
    Integrable (𝓕 g : ℝ → ℂ) := by
  let A : ℝ := ∫ v : ℝ, ‖g v‖
  let D : ℝ := ∫ v : ℝ, ‖deriv (deriv g) v‖
  let p : ℝ := 2 * Real.pi
  have hp : 0 < p := by
    try dsimp [p]
    positivity
  have hA : 0 ≤ A := by
    try dsimp [A]
    exact integral_nonneg (fun v => norm_nonneg _)
  have hD : 0 ≤ D := by
    try dsimp [D]
    exact integral_nonneg (fun v => norm_nonneg _)
  have hcont : Continuous (𝓕 g : ℝ → ℂ) := by
    exact VectorFourier.fourierIntegral_continuous
      Real.continuous_fourierChar
      (innerSL ℝ).continuous₂ hg
  have hzero (t : ℝ) :
      ‖(𝓕 g : ℝ → ℂ) t‖ ≤ A := by
    exact VectorFourier.norm_fourierIntegral_le_integral_norm
      Real.fourierChar volume (innerₗ ℝ) g t
  have hident (t : ℝ) :
      (𝓕 (deriv (deriv g)) : ℝ → ℂ) t =
        (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2 *
          (𝓕 g : ℝ → ℂ) t := by
    rw [congrFun
      (Real.fourier_deriv hg' hg'diff hg'') t,
      congrFun (Real.fourier_deriv hg hgdiff hg') t]
    simp only [smul_eq_mul]
    ring
  have hcoef (t : ℝ) :
      ‖(2 * (Real.pi : ℂ) * Complex.I * (t : ℂ)) ^ 2‖ =
        p ^ 2 * t ^ 2 := by
    try dsimp [p]
    simp only [norm_pow, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos Real.pi_pos, Complex.norm_I, mul_one]
    rw [mul_pow, sq_abs]
  have hsecond (t : ℝ) :
      p ^ 2 * t ^ 2 * ‖(𝓕 g : ℝ → ℂ) t‖ ≤ D := by
    calc
      p ^ 2 * t ^ 2 * ‖(𝓕 g : ℝ → ℂ) t‖ =
        ‖(𝓕 (deriv (deriv g)) : ℝ → ℂ) t‖ := by
        rw [hident, norm_mul, hcoef]
      _ ≤ D :=
        VectorFourier.norm_fourierIntegral_le_integral_norm
          Real.fourierChar volume (innerₗ ℝ)
          (deriv (deriv g)) t
  have hquadratic (t : ℝ) :
      t ^ 2 * ‖(𝓕 g : ℝ → ℂ) t‖ ≤ D / p ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hp)).2
    linarith [hsecond t]
  have hmajor : Integrable
      (fun t : ℝ => (A + D / p ^ 2) * (1 + t ^ 2)⁻¹) :=
    integrable_inv_one_add_sq.const_mul (A + D / p ^ 2)
  apply hmajor.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hconstant : 0 ≤ A + D / p ^ 2 := by positivity
  change ‖(𝓕 g : ℝ → ℂ) t‖ ≤
    (A + D / p ^ 2) / (1 + t ^ 2)
  apply (le_div_iff₀ hden).2
  linarith [hzero t, hquadratic t,
    norm_nonneg ((𝓕 g : ℝ → ℂ) t)]

private theorem schwartzRealLine_mellinConvergent_of_re_pos
    (g : 𝓢(ℝ, ℂ)) (s : ℂ) (hs : 0 < s.re) :
    MellinConvergent (g : ℝ → ℂ) s := by
  have hlocal : LocallyIntegrableOn
      (g : ℝ → ℂ) (Ioi (0 : ℝ)) :=
    g.continuous.locallyIntegrable.locallyIntegrableOn _
  have htop :
      (g : ℝ → ℂ) =O[atTop]
        (fun r : ℝ => r ^ (-(s.re + 1))) := by
    have h :=
      (g.isBigO_cocompact_rpow (-(s.re + 1))).mono
        atTop_le_cocompact
    refine h.congr' (Eventually.of_forall (fun _ => rfl)) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with r hr
    simp only [Real.norm_eq_abs, abs_of_pos hr, neg_add_rev]
  obtain ⟨C, _hC, hdecay⟩ := g.decay 0 0
  have hbounded (r : ℝ) : ‖g r‖ ≤ C := by
    simpa only [Real.norm_eq_abs, pow_zero, norm_iteratedFDeriv_zero, one_mul] using! hdecay r
  have hzero :
      (g : ℝ → ℂ) =O[𝓝[>] (0 : ℝ)]
        (fun r : ℝ => r ^ (-(0 : ℝ))) := by
    apply IsBigO.of_bound C
    filter_upwards [] with r
    simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using! hbounded r
  exact mellinConvergent_of_isBigO_rpow
    (a := s.re + 1) (b := (0 : ℝ)) hlocal htop
    (by linarith) hzero hs

private noncomputable def schwartzExponentialTilt
    (g : 𝓢(ℝ, ℂ)) (κ R v : ℝ) : ℂ :=
  (Real.exp (κ * v) : ℂ) * g (R * Real.exp v)

private theorem schwartzExponentialTilt_integrable
    (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (schwartzExponentialTilt g κ R) := by
  have hconv : MellinConvergent
      (g : ℝ → ℂ) (κ : ℂ) := by
    apply schwartzRealLine_mellinConvergent_of_re_pos
    simpa only [Complex.ofReal_re] using! hκ
  have hscaled : MellinConvergent
      (fun r : ℝ => g (R * r)) (κ : ℂ) :=
    (MellinConvergent.comp_mul_left hR).mpr hconv
  have hchange : Integrable (fun v : ℝ =>
      (1 * Real.exp v) •
        (((1 * Real.exp v : ℝ) : ℂ) ^
          ((κ : ℂ) - 1) •
            g (R * (1 * Real.exp v)))) := by
    apply (integrable_scaled_exp_change_Ioi
      (R := (1 : ℝ)) (by norm_num)
      (fun r : ℝ =>
        (r : ℂ) ^ ((κ : ℂ) - 1) • g (R * r))).mp
    exact hscaled
  have hpower (v : ℝ) :
      (Real.exp v : ℂ) *
        (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) =
          (Real.exp (κ * v) : ℂ) := by
    have hbase : (Real.exp v : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero v)
    calc
      (Real.exp v : ℂ) *
          (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) =
        (Real.exp v : ℂ) ^ (1 : ℂ) *
          (Real.exp v : ℂ) ^ ((κ : ℂ) - 1) := by
        rw [Complex.cpow_one]
      _ = (Real.exp v : ℂ) ^
          ((1 : ℂ) + ((κ : ℂ) - 1)) := by
        rw [Complex.cpow_add _ _ hbase]
      _ = (Real.exp v : ℂ) ^ (κ : ℂ) := by
        congr 1
        ring
      _ = (Real.exp (κ * v) : ℂ) := by
        rw [Complex.cpow_def_of_ne_zero hbase,
          ← Complex.ofReal_log (Real.exp_pos v).le,
          Real.log_exp, Complex.ofReal_exp]
        congr 1
        push_cast
        ring
  apply hchange.congr
  filter_upwards [] with v
  simp only [one_mul, smul_eq_mul, Complex.real_smul,
    schwartzExponentialTilt]
  rw [← mul_assoc, hpower]

private theorem schwartzExponentialTilt_differentiable
    (g : 𝓢(ℝ, ℂ)) (κ R : ℝ) :
    Differentiable ℝ (schwartzExponentialTilt g κ R) := by
  unfold schwartzExponentialTilt
  have hexpreal :
      Differentiable ℝ (fun v : ℝ => Real.exp (κ * v)) := by
    fun_prop
  have hexp :
      Differentiable ℝ (fun v : ℝ =>
        (Real.exp (κ * v) : ℂ)) :=
    Complex.ofRealCLM.differentiable.comp hexpreal
  have hg : Differentiable ℝ (g : ℝ → ℂ) :=
    (g.smooth 1).differentiable (by norm_num)
  have hradius :
      Differentiable ℝ (fun v : ℝ => R * Real.exp v) := by
    fun_prop
  exact hexp.mul (hg.comp hradius)

private theorem schwartzExponentialTilt_deriv
    (g : 𝓢(ℝ, ℂ)) (κ R v : ℝ) :
    deriv (schwartzExponentialTilt g κ R) v =
      (κ : ℂ) * schwartzExponentialTilt g κ R v +
        (R : ℂ) *
          schwartzExponentialTilt
            ((SchwartzMap.derivCLM ℂ ℂ) g)
            (κ + 1) R v := by
  have hlinear :
      HasDerivAt (fun u : ℝ => κ * u) κ v := by
    simpa only [id_eq, mul_one] using! (hasDerivAt_id v).const_mul κ
  have hexpreal :
      HasDerivAt (fun u : ℝ => Real.exp (κ * u))
        (κ * Real.exp (κ * v)) v := by
    convert! (Real.hasDerivAt_exp (κ * v)).comp v hlinear
      using 1; simp only [mul_comm]
  have hexp :
      HasDerivAt (fun u : ℝ =>
        (Real.exp (κ * u) : ℂ))
        ((κ * Real.exp (κ * v) : ℝ) : ℂ) v :=
    hexpreal.ofReal_comp
  have hradius :
      HasDerivAt (fun u : ℝ => R * Real.exp u)
        (R * Real.exp v) v :=
    (Real.hasDerivAt_exp v).const_mul R
  have hprofile :
      HasDerivAt (fun u : ℝ => g (R * Real.exp u))
        ((R * Real.exp v) •
          deriv (g : ℝ → ℂ) (R * Real.exp v)) v := by
    simpa only [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_exp, comp_def] using!
      (g.hasDerivAt (R * Real.exp v)).scomp v hradius
  have hder := (hexp.mul hprofile).deriv
  change deriv
      ((fun u : ℝ => (Real.exp (κ * u) : ℂ)) *
        (fun u : ℝ => g (R * Real.exp u))) v = _
  rw [hder]
  have hexpadd :
      Real.exp ((κ + 1) * v) =
        Real.exp (κ * v) * Real.exp v := by
    rw [← Real.exp_add]
    congr 1
    ring
  simp only [Complex.ofReal_mul, Complex.ofReal_exp, Complex.real_smul, schwartzExponentialTilt,
    hexpadd,
    SchwartzMap.derivCLM_apply]
  ring

private theorem schwartzExponentialTilt_deriv_integrable
    (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (deriv (schwartzExponentialTilt g κ R)) := by
  let g' : 𝓢(ℝ, ℂ) :=
    (SchwartzMap.derivCLM ℂ ℂ) g
  have hzero := schwartzExponentialTilt_integrable g hκ hR
  have hone := schwartzExponentialTilt_integrable
    g' (show 0 < κ + 1 by linarith) hR
  have hsum :=
    (hzero.const_mul (κ : ℂ)).add
      (hone.const_mul (R : ℂ))
  apply hsum.congr
  filter_upwards [] with v
  exact (schwartzExponentialTilt_deriv g κ R v).symm

private theorem schwartzExponentialTilt_deriv_deriv
    (g : 𝓢(ℝ, ℂ)) (κ R v : ℝ) :
    deriv (deriv (schwartzExponentialTilt g κ R)) v =
      (κ : ℂ) * deriv (schwartzExponentialTilt g κ R) v +
        (R : ℂ) * deriv
          (schwartzExponentialTilt
            ((SchwartzMap.derivCLM ℂ ℂ) g)
            (κ + 1) R) v := by
  let g' : 𝓢(ℝ, ℂ) :=
    (SchwartzMap.derivCLM ℂ ℂ) g
  have hderivfun :
      deriv (schwartzExponentialTilt g κ R) =
        (fun u : ℝ =>
          (κ : ℂ) * schwartzExponentialTilt g κ R u +
            (R : ℂ) *
              schwartzExponentialTilt g' (κ + 1) R u) := by
    funext u
    exact schwartzExponentialTilt_deriv g κ R u
  conv_lhs => rw [hderivfun]
  have hfirst :
      Differentiable ℝ
        (fun u : ℝ =>
          (κ : ℂ) * schwartzExponentialTilt g κ R u) :=
    (schwartzExponentialTilt_differentiable g κ R).const_mul
      (κ : ℂ)
  have hsecond :
      Differentiable ℝ
        (fun u : ℝ =>
          (R : ℂ) *
            schwartzExponentialTilt g' (κ + 1) R u) :=
    (schwartzExponentialTilt_differentiable
      g' (κ + 1) R).const_mul (R : ℂ)
  change deriv
      ((fun u : ℝ =>
        (κ : ℂ) * schwartzExponentialTilt g κ R u) +
        (fun u : ℝ =>
          (R : ℂ) *
            schwartzExponentialTilt g' (κ + 1) R u)) v = _
  rw [deriv_add hfirst.differentiableAt
    hsecond.differentiableAt,
    deriv_const_mul_field (κ : ℂ),
    deriv_const_mul_field (R : ℂ)]

private theorem schwartzExponentialTilt_deriv_deriv_integrable
    (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (deriv (deriv (schwartzExponentialTilt g κ R))) := by
  let g' : 𝓢(ℝ, ℂ) :=
    (SchwartzMap.derivCLM ℂ ℂ) g
  have hzero :=
    schwartzExponentialTilt_deriv_integrable g hκ hR
  have hone :=
    schwartzExponentialTilt_deriv_integrable
      g' (show 0 < κ + 1 by linarith) hR
  have hsum :=
    (hzero.const_mul (κ : ℂ)).add
      (hone.const_mul (R : ℂ))
  apply hsum.congr
  filter_upwards [] with v
  exact (schwartzExponentialTilt_deriv_deriv g κ R v).symm

private theorem schwartzExponentialTilt_deriv_differentiable
    (g : 𝓢(ℝ, ℂ)) (κ R : ℝ) :
    Differentiable ℝ
      (deriv (schwartzExponentialTilt g κ R)) := by
  let g' : 𝓢(ℝ, ℂ) :=
    (SchwartzMap.derivCLM ℂ ℂ) g
  have hderivfun :
      deriv (schwartzExponentialTilt g κ R) =
        (fun u : ℝ =>
          (κ : ℂ) * schwartzExponentialTilt g κ R u +
            (R : ℂ) *
              schwartzExponentialTilt g' (κ + 1) R u) := by
    funext u
    exact schwartzExponentialTilt_deriv g κ R u
  rw [hderivfun]
  exact
    ((schwartzExponentialTilt_differentiable
      g κ R).const_mul (κ : ℂ)).add
      ((schwartzExponentialTilt_differentiable
        g' (κ + 1) R).const_mul (R : ℂ))

private theorem schwartzExponentialTilt_fourier_integrable
    (g : 𝓢(ℝ, ℂ)) {κ R : ℝ}
    (hκ : 0 < κ) (hR : 0 < R) :
    Integrable (𝓕 (schwartzExponentialTilt g κ R) : ℝ → ℂ) :=
  integrable_fourier_of_integrable_two_derivatives
    (schwartzExponentialTilt g κ R)
    (schwartzExponentialTilt_integrable g hκ hR)
    (schwartzExponentialTilt_differentiable g κ R)
    (schwartzExponentialTilt_deriv_integrable g hκ hR)
    (schwartzExponentialTilt_deriv_differentiable g κ R)
    (schwartzExponentialTilt_deriv_deriv_integrable g hκ hR)

private theorem normalizedRadialLogProfile_weighted_fourier_integrable
    {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hreal : IsRealValued f)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ)) :
    Integrable
      (𝓕 (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) :
        ℝ → ℂ) := by
  let κ : ℝ := (d : ℝ) - a
  let g : 𝓢(ℝ, ℂ) := radialSchwartzProfile hd f
  let c : ℂ :=
    ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ)
  have hκ : 0 < κ := by
    try dsimp [κ]
    linarith
  have hweight :
      (fun v : ℝ =>
        (Real.exp (-a * v) : ℂ) *
          (normalizedRadialLogProfile hd f R v : ℂ)) =
        (fun v : ℝ =>
          c * schwartzExponentialTilt g κ R v) := by
    funext v
    rw [normalizedRadialLogProfile_weighted_ofReal
      hd f hreal R a v]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_exp,
      Complex.ofReal_sub,
      Complex.ofReal_natCast, schwartzExponentialTilt, radialSchwartzProfile_apply, c, κ, g]
    ring
  have hfourier :=
    (schwartzExponentialTilt_fourier_integrable
      g hκ hR).const_mul c
  have hscalar (t : ℝ) :
      (𝓕 (fun v : ℝ =>
        c * schwartzExponentialTilt g κ R v) :
        ℝ → ℂ) t =
        c *
          (𝓕 (schwartzExponentialTilt g κ R) :
            ℝ → ℂ) t := by
    rw [Real.fourier_real_eq_integral_exp_smul,
      Real.fourier_real_eq_integral_exp_smul]
    simp only [smul_eq_mul]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with v
    ring
  apply hfourier.congr
  filter_upwards [] with t
  rw [hweight]
  exact (hscalar t).symm

private theorem normalizedRadialMellinStrip_shifted_integrable
    {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hreal : IsRealValued f)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ)) :
    Integrable (fun t : ℝ =>
      normalizedRadialMellinStrip hd f R
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) := by
  have hfourier :=
    normalizedRadialLogProfile_weighted_fourier_integrable
      hd f hreal hR ha
  have hscale : (2 * Real.pi)⁻¹ ≠ 0 := by
    exact inv_ne_zero
      (mul_ne_zero (by norm_num) Real.pi_ne_zero)
  have hscaled := hfourier.comp_mul_right' hscale
  apply hscaled.congr
  filter_upwards [] with t
  simpa only [neg_mul, Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, mul_inv_rev,
    div_eq_mul_inv,
    Complex.ofReal_sub, Complex.ofReal_natCast, Complex.ofReal_inv, Complex.ofReal_ofNat] using!
    (normalizedRadialMellinStrip_shifted_eq_fourier
      hd f hreal R hR a t).symm

private theorem normalizedRadialMellinStrip_shifted_fourier_inversion
    {d : ℕ} (hd : 0 < d) (f : TestFunction d)
    (hf : IsRadial f) (hreal : IsRealValued f)
    (hzero : f (0 : Euclidean d) = 0)
    {R : ℝ} (hR : 0 < R) {a : ℝ}
    (ha : a < (d : ℝ)) (v : ℝ) :
    (normalizedRadialLogProfile hd f R v : ℂ) =
      (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ =>
          normalizedRadialMellinStrip hd f R
            (((2 * Real.pi * ξ : ℝ) : ℂ) +
              Complex.I *
                ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) :
            ℝ → ℂ) v) := by
  let W : ℝ → ℂ := fun u =>
    (Real.exp (-a * u) : ℂ) *
      (normalizedRadialLogProfile hd f R u : ℂ)
  let κ : ℝ := (d : ℝ) - a
  let g : 𝓢(ℝ, ℂ) := radialSchwartzProfile hd f
  let c : ℂ :=
    ((radialSurfaceArea d / radialL1Mass f * R ^ d : ℝ) : ℂ)
  have hW : Integrable W := by
    try dsimp [W]
    apply normalizedRadialLogProfile_weighted_integrable
      hd f hf hreal hzero hR
    linarith
  have hFW : Integrable (𝓕 W : ℝ → ℂ) := by
    try dsimp [W]
    exact normalizedRadialLogProfile_weighted_fourier_integrable
      hd f hreal hR ha
  have hweight :
      W = (fun u : ℝ =>
        c * schwartzExponentialTilt g κ R u) := by
    funext u
    try dsimp [W]
    rw [normalizedRadialLogProfile_weighted_ofReal
      hd f hreal R a u]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_exp,
      Complex.ofReal_sub,
      Complex.ofReal_natCast, schwartzExponentialTilt, radialSchwartzProfile_apply, c, κ, g]
    ring
  have hcontinuous : Continuous W := by
    rw [hweight]
    exact
      (schwartzExponentialTilt_differentiable
        g κ R).continuous.const_mul c
  have hfrequency :
      (fun ξ : ℝ =>
        normalizedRadialMellinStrip hd f R
          (((2 * Real.pi * ξ : ℝ) : ℂ) +
            Complex.I *
              ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) =
        (𝓕 W : ℝ → ℂ) := by
    funext ξ
    rw [normalizedRadialMellinStrip_shifted_eq_fourier
      hd f hreal R hR a (2 * Real.pi * ξ)]
    change
      (𝓕 W : ℝ → ℂ)
          ((2 * Real.pi * ξ) / (2 * Real.pi)) =
        (𝓕 W : ℝ → ℂ) ξ
    field_simp [Real.pi_ne_zero]
  have hinversion :
      (𝓕⁻ (𝓕 W : ℝ → ℂ) : ℝ → ℂ) v = W v :=
    hW.fourierInv_fourier_eq hFW hcontinuous.continuousAt
  have hcancel :
      (Real.exp (a * v) : ℂ) * W v =
        (normalizedRadialLogProfile hd f R v : ℂ) := by
    try dsimp [W]
    rw [← mul_assoc, ← Complex.ofReal_mul,
      ← Real.exp_add]
    have hsum : a * v + -a * v = 0 := by ring
    rw [hsum, Real.exp_zero]
    norm_num
  calc
    (normalizedRadialLogProfile hd f R v : ℂ) =
        (Real.exp (a * v) : ℂ) * W v := hcancel.symm
    _ = (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ =>
          normalizedRadialMellinStrip hd f R
            (((2 * Real.pi * ξ : ℝ) : ℂ) +
              Complex.I *
                ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) :
            ℝ → ℂ) v) := by
      rw [hfrequency, hinversion]

end

section

private noncomputable def stripAngle (σ : ℝ) : ℝ :=
  Real.pi * (1 + σ) / 2

private noncomputable def stripPoissonKernel (σ T : ℝ) : ℝ :=
  Real.sin (stripAngle σ) /
    (4 * (Real.cosh (Real.pi * T / 2) - Real.cos (stripAngle σ)))

private noncomputable def stripBottomMass (σ : ℝ) : ℝ :=
  (1 - σ) / 2

private theorem stripAngle_mem_Ioo {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    0 < stripAngle σ ∧ stripAngle σ < Real.pi := by
  unfold stripAngle
  constructor
  · exact div_pos (mul_pos Real.pi_pos (by linarith)) (by norm_num)
  · calc
      Real.pi * (1 + σ) / 2 < Real.pi * 2 / 2 := by
        gcongr
        linarith
      _ = Real.pi := by ring

private theorem stripBottomMass_pos {σ : ℝ} (hσ : σ < 1) :
    0 < stripBottomMass σ := by
  unfold stripBottomMass
  linarith

private theorem stripBottomMass_lt_one {σ : ℝ} (hσ : -1 < σ) :
    stripBottomMass σ < 1 := by
  unfold stripBottomMass
  linarith

private theorem stripPoissonKernel_pos {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    0 < stripPoissonKernel σ T := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hcos : Real.cos (stripAngle σ) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ) (by norm_num) hangle'.le hangle
    simpa only [gt_iff_lt, Real.cos_zero] using! h
  have hden : 0 < Real.cosh (Real.pi * T / 2) -
      Real.cos (stripAngle σ) := by
    linarith [Real.one_le_cosh (Real.pi * T / 2)]
  exact div_pos hsin (mul_pos (by norm_num) hden)

end

section

open Filter MeasureTheory Set
open scoped Interval Topology

private noncomputable def stripPoissonPrimitive (σ T : ℝ) : ℝ :=
  Real.arctan
      ((Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)) /
        Real.sin (stripAngle σ)) / Real.pi

private theorem stripPoissonKernel_neg (σ T : ℝ) :
    stripPoissonKernel σ (-T) = stripPoissonKernel σ T := by
  unfold stripPoissonKernel
  have hneg : Real.pi * (-T) / 2 = -(Real.pi * T / 2) := by ring
  rw [hneg, Real.cosh_neg]

private theorem stripPoissonKernel_abs (σ T : ℝ) :
    stripPoissonKernel σ |T| = stripPoissonKernel σ T := by
  rcases le_total 0 T with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_nonpos h, stripPoissonKernel_neg]

private theorem stripPoissonPrimitive_hasDerivAt {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    HasDerivAt (stripPoissonPrimitive σ)
      (stripPoissonKernel σ T) T := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hsin0 : Real.sin (stripAngle σ) ≠ 0 := hsin.ne'
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hexp : 0 < Real.exp (Real.pi * T / 2) := Real.exp_pos _
  have hderiv :
      HasDerivAt
        (fun x : ℝ =>
          (Real.exp (Real.pi * x / 2) - Real.cos (stripAngle σ)) /
            Real.sin (stripAngle σ))
        ((Real.exp (Real.pi * T / 2) * (Real.pi / 2)) /
          Real.sin (stripAngle σ)) T := by
    convert!
      (((Real.hasDerivAt_exp (Real.pi * T / 2)).comp T
        ((hasDerivAt_id T).const_mul Real.pi |>.div_const 2)).sub_const
        (Real.cos (stripAngle σ))).div_const (Real.sin (stripAngle σ)) using 1
    all_goals simp only [mul_comm, mul_one]
  convert!
    ((Real.hasDerivAt_arctan _).comp T hderiv).div_const Real.pi
      using 1
  unfold stripPoissonKernel
  rw [Real.cosh_eq, Real.exp_neg]
  have htrig := Real.sin_sq_add_cos_sq (stripAngle σ)
  have hden : 0 <
      Real.exp (Real.pi * T / 2) ^ 2 + 1 -
        2 * Real.exp (Real.pi * T / 2) * Real.cos (stripAngle σ) := by
    linarith [sq_nonneg
      (Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)),
      sq_pos_of_pos hsin]
  field_simp [hsin0, hpi, hexp.ne', hden.ne']
  linarith

private theorem stripPoissonPrimitive_zero {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    stripPoissonPrimitive σ 0 = stripAngle σ / (2 * Real.pi) := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hhalf : 0 < stripAngle σ / 2 := half_pos hangle
  have hhalf' : stripAngle σ / 2 < Real.pi / 2 := by linarith
  have hcos : 0 < Real.cos (stripAngle σ / 2) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hhalf'⟩
  have hsin : 0 < Real.sin (stripAngle σ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi hhalf (by linarith [Real.pi_pos])
  have hratio :
      (1 - Real.cos (stripAngle σ)) / Real.sin (stripAngle σ) =
        Real.tan (stripAngle σ / 2) := by
    conv_lhs =>
      arg 1
      arg 2
      rw [show stripAngle σ = 2 * (stripAngle σ / 2) by ring,
        Real.cos_two_mul_eq_one_sub]
    conv_lhs =>
      arg 2
      rw [show stripAngle σ = 2 * (stripAngle σ / 2) by ring,
        Real.sin_two_mul]
    rw [Real.tan_eq_sin_div_cos]
    field_simp [hsin.ne', hcos.ne']
    ring
  unfold stripPoissonPrimitive
  simp only [mul_zero, zero_div, Real.exp_zero]
  rw [hratio, Real.arctan_tan (by linarith [Real.pi_pos]) hhalf']
  ring

private theorem stripPoissonPrimitive_tendsto_atTop {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    Tendsto (stripPoissonPrimitive σ) atTop (nhds (1 / 2 : ℝ)) := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hscale : Tendsto (fun T : ℝ => Real.pi * T / 2) atTop atTop := by
    convert! tendsto_id.atTop_mul_const (half_pos Real.pi_pos) using 1
    ext T
    change Real.pi * T / 2 = T * (Real.pi / 2)
    ring
  have hexp : Tendsto (fun T : ℝ => Real.exp (Real.pi * T / 2))
      atTop atTop := Real.tendsto_exp_atTop.comp hscale
  have hshift : Tendsto
      (fun T : ℝ => Real.exp (Real.pi * T / 2) -
        Real.cos (stripAngle σ)) atTop atTop := by
    simpa only [sub_eq_add_neg] using!
      (tendsto_atTop_add_const_right atTop
        (-Real.cos (stripAngle σ)) hexp)
  have hratio : Tendsto
      (fun T : ℝ =>
        (Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)) /
          Real.sin (stripAngle σ)) atTop atTop :=
    (tendsto_div_const_atTop_of_pos hsin).2 hshift
  have hatan : Tendsto
      (fun T : ℝ =>
        Real.arctan
          ((Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)) /
            Real.sin (stripAngle σ)))
      atTop (nhds (Real.pi / 2)) :=
    (tendsto_nhds_of_tendsto_nhdsWithin Real.tendsto_arctan_atTop).comp
      hratio
  unfold stripPoissonPrimitive
  convert! hatan.div_const Real.pi using 1
  field_simp [Real.pi_ne_zero]

private theorem stripPoissonKernel_integrableOn_Ioi {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    IntegrableOn (stripPoissonKernel σ) (Ioi (0 : ℝ)) := by
  exact integrableOn_Ioi_deriv_of_nonneg'
    (fun T _ => stripPoissonPrimitive_hasDerivAt hbelow habove T)
    (fun T _ => (stripPoissonKernel_pos hbelow habove T).le)
    (stripPoissonPrimitive_tendsto_atTop hbelow habove)

private theorem stripPoissonKernel_integral_Ioi {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    (∫ T in Ioi (0 : ℝ), stripPoissonKernel σ T) =
      1 / 2 - stripAngle σ / (2 * Real.pi) := by
  calc
    (∫ T in Ioi (0 : ℝ), stripPoissonKernel σ T) =
        (1 / 2 : ℝ) - stripPoissonPrimitive σ 0 := by
      exact integral_Ioi_of_hasDerivAt_of_nonneg'
        (fun T _ => stripPoissonPrimitive_hasDerivAt hbelow habove T)
        (fun T _ => (stripPoissonKernel_pos hbelow habove T).le)
        (stripPoissonPrimitive_tendsto_atTop hbelow habove)
    _ = 1 / 2 - stripAngle σ / (2 * Real.pi) := by
      rw [stripPoissonPrimitive_zero hbelow habove]

private theorem stripPoissonKernel_integrable {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    Integrable (stripPoissonKernel σ) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  have hright := stripPoissonKernel_integrableOn_Ioi hbelow habove
  refine ⟨?_, hright⟩
  have hreflected :
      IntegrableOn
        ((stripPoissonKernel σ) ∘ (fun T : ℝ => -T))
        ((fun T : ℝ => -T) ⁻¹' Iio (0 : ℝ)) := by
    simpa only [Function.comp_def, neg_preimage, neg_Iio, neg_zero,
      stripPoissonKernel_neg] using! hright
  exact ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected

private theorem integral_stripPoissonKernel {σ : ℝ}
    (hbelow : -1 < σ) (habove : σ < 1) :
    (∫ T : ℝ, stripPoissonKernel σ T) = stripBottomMass σ := by
  calc
    (∫ T : ℝ, stripPoissonKernel σ T) =
        ∫ T : ℝ, stripPoissonKernel σ |T| := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall
        (fun T => (stripPoissonKernel_abs σ T).symm)
    _ = 2 * ∫ T in Ioi (0 : ℝ), stripPoissonKernel σ T :=
      integral_comp_abs
    _ = 2 * (1 / 2 - stripAngle σ / (2 * Real.pi)) := by
      rw [stripPoissonKernel_integral_Ioi hbelow habove]
    _ = stripBottomMass σ := by
      unfold stripAngle stripBottomMass
      field_simp [Real.pi_ne_zero]
      ring

private theorem stripPoissonKernel_antitone_abs
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {x y : ℝ} (hxy : |x| ≤ |y|) :
    stripPoissonKernel σ y ≤ stripPoissonKernel σ x := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hcos : Real.cos (stripAngle σ) < 1 := by
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi
      (x := 0) (y := stripAngle σ)
      (by norm_num) hangle'.le hangle
    simpa only [gt_iff_lt, Real.cos_zero] using! h
  have hxden :
      0 < 4 *
        (Real.cosh (Real.pi * x / 2) -
          Real.cos (stripAngle σ)) := by
    have hxcosh := Real.one_le_cosh (Real.pi * x / 2)
    linarith
  have hcosh :
      Real.cosh (Real.pi * x / 2) ≤
        Real.cosh (Real.pi * y / 2) := by
    apply Real.cosh_le_cosh.mpr
    rw [abs_div, abs_div, abs_mul, abs_mul]
    gcongr
  have hden :
      4 * (Real.cosh (Real.pi * x / 2) -
          Real.cos (stripAngle σ)) ≤
        4 * (Real.cosh (Real.pi * y / 2) -
          Real.cos (stripAngle σ)) := by
    linarith
  unfold stripPoissonKernel
  exact div_le_div_of_nonneg_left hsin.le hxden hden

private theorem stripPoissonPrimitive_centered_hasDerivAt
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (r x : ℝ) :
    HasDerivAt
      (fun s : ℝ =>
        stripPoissonPrimitive σ (s + r) -
          stripPoissonPrimitive σ (s - r))
      (stripPoissonKernel σ (x + r) -
        stripPoissonKernel σ (x - r)) x := by
  have hplus :=
    (stripPoissonPrimitive_hasDerivAt hbelow habove (x + r)).comp x
      ((hasDerivAt_id x).add_const r)
  have hminus :=
    (stripPoissonPrimitive_hasDerivAt hbelow habove (x - r)).comp x
      ((hasDerivAt_id x).sub_const r)
  convert! hplus.sub hminus using 1
  all_goals simp only [mul_one]

private theorem stripPoissonPrimitive_centered_antitoneOn
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) :
    AntitoneOn
      (fun s : ℝ =>
        stripPoissonPrimitive σ (s + r) -
          stripPoissonPrimitive σ (s - r))
      (Ici (0 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici 0)
  · intro x hx
    exact
      (stripPoissonPrimitive_centered_hasDerivAt
        hbelow habove r x).continuousAt.continuousWithinAt
  · intro x hx
    exact
      (stripPoissonPrimitive_centered_hasDerivAt
        hbelow habove r x).differentiableAt.differentiableWithinAt
  · intro x hx
    have hxpos : 0 ≤ x := by
      have hx' : 0 < x := by simpa only [nonempty_Iio, interior_Ici', mem_Ioi] using! hx
      exact hx'.le
    rw [(stripPoissonPrimitive_centered_hasDerivAt
      hbelow habove r x).deriv]
    apply sub_nonpos.mpr
    apply stripPoissonKernel_antitone_abs hbelow habove
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    rw [sq_abs, sq_abs]
    linarith [mul_nonneg hxpos hr]

private theorem intervalIntegral_stripPoissonKernel
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (a b : ℝ) :
    (∫ x in a..b, stripPoissonKernel σ x) =
      stripPoissonPrimitive σ b -
        stripPoissonPrimitive σ a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    exact stripPoissonPrimitive_hasDerivAt hbelow habove x
  · exact (stripPoissonKernel_integrable hbelow habove).intervalIntegrable

private theorem stripPoissonPrimitive_centered_neg
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    (r s : ℝ) :
    stripPoissonPrimitive σ (-s + r) -
        stripPoissonPrimitive σ (-s - r) =
      stripPoissonPrimitive σ (s + r) -
        stripPoissonPrimitive σ (s - r) := by
  have hneg := intervalIntegral.integral_comp_neg
    (f := stripPoissonKernel σ)
    (a := s - r) (b := s + r)
  simp_rw [stripPoissonKernel_neg] at hneg
  rw [intervalIntegral_stripPoissonKernel hbelow habove,
    intervalIntegral_stripPoissonKernel hbelow habove] at hneg
  convert! hneg.symm using 1
  all_goals ring_nf

private theorem stripPoissonPrimitive_centered_le
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    stripPoissonPrimitive σ (s + r) -
        stripPoissonPrimitive σ (s - r) ≤
      stripPoissonPrimitive σ r -
        stripPoissonPrimitive σ (-r) := by
  have hanti :=
    stripPoissonPrimitive_centered_antitoneOn
      hbelow habove hr
  by_cases hs : 0 ≤ s
  · convert! hanti (show (0 : ℝ) ∈ Ici 0 by simp only [mem_Ici, Std.le_refl])
      (show s ∈ Ici 0 from hs) hs using 1
    all_goals ring_nf
  · have hsneg : 0 ≤ -s := by linarith
    rw [← stripPoissonPrimitive_centered_neg
      hbelow habove r s]
    convert! hanti (show (0 : ℝ) ∈ Ici 0 by simp only [mem_Ici, Std.le_refl])
      (show -s ∈ Ici 0 from hsneg) hsneg using 1
    all_goals ring_nf

private theorem stripPoissonKernel_centered_interval_max
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1)
    {r : ℝ} (hr : 0 ≤ r) (s : ℝ) :
    (∫ x in Icc (s - r) (s + r), stripPoissonKernel σ x) ≤
      ∫ x in Icc (-r) r, stripPoissonKernel σ x := by
  rw [integral_Icc_eq_integral_Ioc,
    integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : s - r ≤ s + r),
    ← intervalIntegral.integral_of_le (by linarith : -r ≤ r),
    intervalIntegral_stripPoissonKernel hbelow habove,
    intervalIntegral_stripPoissonKernel hbelow habove]
  exact stripPoissonPrimitive_centered_le hbelow habove hr s

private noncomputable def stripComplexPoissonKernel (σ T : ℝ) : ℂ :=
  Complex.I *
      ((Complex.exp
          (((Real.pi * T / 2 : ℝ) : ℂ) +
            Complex.I * ((stripAngle σ : ℝ) : ℂ)) + 1) /
        (Complex.exp
          (((Real.pi * T / 2 : ℝ) : ℂ) +
            Complex.I * ((stripAngle σ : ℝ) : ℂ)) - 1)) /
    4

private theorem stripComplexPoissonKernel_re
    {σ : ℝ} (hbelow : -1 < σ) (habove : σ < 1) (T : ℝ) :
    (stripComplexPoissonKernel σ T).re =
      stripPoissonKernel σ T := by
  obtain ⟨hangle, hangle'⟩ := stripAngle_mem_Ioo hbelow habove
  have hsin : 0 < Real.sin (stripAngle σ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hexp : 0 < Real.exp (Real.pi * T / 2) := Real.exp_pos _
  have htrig := Real.sin_sq_add_cos_sq (stripAngle σ)
  have hden :
      0 < Real.exp (Real.pi * T / 2) ^ 2 + 1 -
        2 * Real.exp (Real.pi * T / 2) * Real.cos (stripAngle σ) := by
    linarith [sq_nonneg
      (Real.exp (Real.pi * T / 2) - Real.cos (stripAngle σ)),
      sq_pos_of_pos hsin]
  unfold stripComplexPoissonKernel stripPoissonKernel
  rw [Real.cosh_eq, Real.exp_neg]
  simp only [Complex.div_re, Complex.div_im, Complex.mul_re, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, Complex.add_re,
    Complex.sub_re, Complex.add_im, Complex.sub_im,
    Complex.one_re, Complex.one_im,
    Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.exp_im, Complex.mul_im,
    sub_self, add_zero, zero_add, mul_zero,
    Complex.normSq_apply]
  norm_num
  field_simp [hexp.ne', hden.ne']
  nlinarith

private noncomputable def stripSchwarzExponential (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  Complex.exp
    (((Real.pi : ℂ) *
      (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
        (2 * (ℓ : ℂ)))

private theorem stripSchwarzExponential_continuous (ℓ : ℝ) (z : ℂ) :
    Continuous (fun y : ℝ => stripSchwarzExponential ℓ z y) := by
  unfold stripSchwarzExponential
  fun_prop

private theorem stripSchwarzExponential_hasDerivAt
    (ℓ : ℝ) (z : ℂ) (y : ℝ) :
    HasDerivAt
      (fun w : ℂ => stripSchwarzExponential ℓ w y)
      (stripSchwarzExponential ℓ z y *
        ((Real.pi : ℂ) / (2 * (ℓ : ℂ)))) z := by
  have haffine :=
    ((((hasDerivAt_id z).sub_const (y : ℂ)).add_const
      (Complex.I * (ℓ : ℂ))).const_mul (Real.pi : ℂ)).div_const
      (2 * (ℓ : ℂ))
  unfold stripSchwarzExponential
  convert! haffine.cexp using 1
  all_goals simp only [id_eq, mul_one]

private theorem norm_stripSchwarzExponential (ℓ : ℝ) (z : ℂ) (y : ℝ) :
    ‖stripSchwarzExponential ℓ z y‖ =
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) := by
  unfold stripSchwarzExponential
  rw [Complex.norm_exp,
    show (2 * (ℓ : ℂ)) = ((2 * ℓ : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re]
  congr 1
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.add_re, Complex.sub_re, Complex.I_re,
    zero_mul,
    Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, add_zero, Complex.add_im,
      Complex.sub_im, sub_zero,
    Complex.mul_im, one_mul, zero_add]

private theorem stripSchwarzExponential_re (ℓ : ℝ) (z : ℂ) (y : ℝ) :
    (stripSchwarzExponential ℓ z y).re =
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
        Real.cos (Real.pi * (z.im + ℓ) / (2 * ℓ)) := by
  unfold stripSchwarzExponential
  rw [Complex.exp_re,
    show (2 * (ℓ : ℂ)) = ((2 * ℓ : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  congr 1 <;> simp [Complex.mul_re, Complex.mul_im]

private theorem stripSchwarzExponential_im (ℓ : ℝ) (z : ℂ) (y : ℝ) :
    (stripSchwarzExponential ℓ z y).im =
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
        Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) := by
  unfold stripSchwarzExponential
  rw [Complex.exp_im,
    show (2 * (ℓ : ℂ)) = ((2 * ℓ : ℝ) : ℂ) by push_cast; rfl,
    Complex.div_ofReal_re, Complex.div_ofReal_im]
  congr 1 <;> simp [Complex.mul_re, Complex.mul_im]

private theorem stripSchwarzAngle_mem_Ioo
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    0 < Real.pi * (z.im + ℓ) / (2 * ℓ) ∧
      Real.pi * (z.im + ℓ) / (2 * ℓ) < Real.pi := by
  change -ℓ < z.im ∧ z.im < ℓ at hz
  constructor
  · exact div_pos (mul_pos Real.pi_pos (by linarith))
      (mul_pos (by norm_num) hℓ)
  · apply (div_lt_iff₀ (mul_pos (by norm_num) hℓ)).2
    linarith [mul_pos Real.pi_pos (show 0 < ℓ - z.im by linarith)]

private theorem stripSchwarzExponential_sub_one_norm_ge_sin
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ≤
      ‖stripSchwarzExponential ℓ z y - 1‖ := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have htrig :=
    Real.sin_sq_add_cos_sq (Real.pi * (z.im + ℓ) / (2 * ℓ))
  have hsquare :
      Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ^ 2 ≤
        ‖stripSchwarzExponential ℓ z y - 1‖ ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, sub_zero,
      stripSchwarzExponential_re, stripSchwarzExponential_im]
    nlinarith [sq_nonneg
      (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) -
        Real.cos (Real.pi * (z.im + ℓ) / (2 * ℓ)))]
  nlinarith [norm_nonneg (stripSchwarzExponential ℓ z y - 1)]

private theorem stripSchwarzExponential_sub_one_norm_ge_exp_mul_sin
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
        Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ≤
      ‖stripSchwarzExponential ℓ z y - 1‖ := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  calc
    Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
        Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) =
      |(stripSchwarzExponential ℓ z y - 1).im| := by
        rw [Complex.sub_im, Complex.one_im, sub_zero,
          stripSchwarzExponential_im,
          abs_of_pos (mul_pos (Real.exp_pos _) hsin)]
    _ ≤ ‖stripSchwarzExponential ℓ z y - 1‖ :=
      Complex.abs_im_le_norm _

private noncomputable def stripHolomorphicPoissonKernel (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  (Complex.I *
      ((Complex.exp
          (((Real.pi : ℂ) *
            (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
              (2 * (ℓ : ℂ))) + 1) /
        (Complex.exp
          (((Real.pi : ℂ) *
            (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
              (2 * (ℓ : ℂ))) - 1)) /
    4) / (ℓ : ℂ)

private theorem stripHolomorphicPoissonKernel_denominator_ne_zero
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    Complex.exp
      (((Real.pi : ℂ) *
        (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
          (2 * (ℓ : ℂ))) - 1 ≠ 0 := by
  change -ℓ < z.im ∧ z.im < ℓ at hz
  have hargument :
      (((Real.pi : ℂ) *
        (z - (y : ℂ) + Complex.I * (ℓ : ℂ))) /
          (2 * (ℓ : ℂ))).im =
        Real.pi * (z.im + ℓ) / (2 * ℓ) := by
    rw [show (2 * (ℓ : ℂ)) = ((2 * ℓ : ℝ) : ℂ) by push_cast; rfl,
      Complex.div_ofReal_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.add_im, Complex.sub_im,
      Complex.ofReal_im, sub_zero,
      Complex.I_re, mul_zero, Complex.I_im, one_mul, zero_add, Complex.add_re, Complex.sub_re,
        Complex.mul_re, zero_mul,
      sub_self, add_zero]
  have hpositive : 0 < Real.pi * (z.im + ℓ) / (2 * ℓ) := by
    exact div_pos (mul_pos Real.pi_pos (by linarith))
      (mul_pos (by norm_num) hℓ)
  have hless : Real.pi * (z.im + ℓ) / (2 * ℓ) < Real.pi := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hℓ)).2
    linarith [mul_pos Real.pi_pos (show 0 < ℓ - z.im by linarith)]
  have hsin := Real.sin_pos_of_pos_of_lt_pi hpositive hless
  intro hzero
  have him := congrArg Complex.im hzero
  simp only [Complex.sub_im, Complex.one_im, sub_zero,
    Complex.exp_im, hargument] at him
  exact (mul_pos (Real.exp_pos _) hsin).ne' him

private theorem stripHolomorphicPoissonKernel_eq_scaled
    {ℓ : ℝ} (hℓ : 0 < ℓ) (σ s y : ℝ) :
    stripHolomorphicPoissonKernel ℓ
        ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y =
      stripComplexPoissonKernel σ ((s - y) / ℓ) / (ℓ : ℂ) := by
  have hℓc : (ℓ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hargument :
      ((Real.pi : ℂ) *
          (((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) -
            (y : ℂ) + Complex.I * (ℓ : ℂ))) /
            (2 * (ℓ : ℂ)) =
        ((Real.pi * ((s - y) / ℓ) / 2 : ℝ) : ℂ) +
          Complex.I * ((stripAngle σ : ℝ) : ℂ) := by
    unfold stripAngle
    push_cast
    field_simp [hℓc]
    ring
  unfold stripHolomorphicPoissonKernel stripComplexPoissonKernel
  rw [hargument]

private theorem stripHolomorphicPoissonKernel_re
    {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hbelow : -1 < σ) (habove : σ < 1) (s y : ℝ) :
    (stripHolomorphicPoissonKernel ℓ
      ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y).re =
      stripPoissonKernel σ ((s - y) / ℓ) / ℓ := by
  rw [stripHolomorphicPoissonKernel_eq_scaled hℓ,
    Complex.div_ofReal_re,
    stripComplexPoissonKernel_re hbelow habove]

private noncomputable def stripRegularizedHolomorphicPoissonKernel
    (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  stripHolomorphicPoissonKernel ℓ z y +
    (if 0 ≤ y then Complex.I else -Complex.I) /
      ((4 * ℓ : ℝ) : ℂ)

private theorem stripRegularizedHolomorphicPoissonKernel_hasDerivAt
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    HasDerivAt
      (fun w : ℂ => stripRegularizedHolomorphicPoissonKernel ℓ w y)
      (-(Complex.I * (Real.pi : ℂ) *
          stripSchwarzExponential ℓ z y) /
        (4 * (ℓ : ℂ) ^ 2 *
          (stripSchwarzExponential ℓ z y - 1) ^ 2)) z := by
  have hℓc : (ℓ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hden : stripSchwarzExponential ℓ z y - 1 ≠ 0 := by
    simpa only [stripSchwarzExponential, ne_eq] using!
      stripHolomorphicPoissonKernel_denominator_ne_zero hℓ hz y
  have hexp := stripSchwarzExponential_hasDerivAt ℓ z y
  have hratio :=
    (hexp.add_const 1).div (hexp.sub_const 1) hden
  have hkernel :=
    ((((hratio.const_mul Complex.I).div_const (4 : ℂ)).div_const
      (ℓ : ℂ))).add_const
      ((if 0 ≤ y then Complex.I else -Complex.I) /
        ((4 * ℓ : ℝ) : ℂ))
  unfold stripRegularizedHolomorphicPoissonKernel
    stripHolomorphicPoissonKernel
  convert! hkernel using 1
  field_simp [hℓc, hden]
  ring

private noncomputable def stripRegularizedHolomorphicPoissonKernelDeriv
    (ℓ : ℝ) (z : ℂ) (y : ℝ) : ℂ :=
  -(Complex.I * (Real.pi : ℂ) *
      stripSchwarzExponential ℓ z y) /
    (4 * (ℓ : ℂ) ^ 2 *
      (stripSchwarzExponential ℓ z y - 1) ^ 2)

private theorem stripRegularizedHolomorphicPoissonKernel_hasDerivAt_deriv
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) (y : ℝ) :
    HasDerivAt
      (fun w : ℂ => stripRegularizedHolomorphicPoissonKernel ℓ w y)
      (stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y) z := by
  simpa only [stripRegularizedHolomorphicPoissonKernelDeriv] using!
    stripRegularizedHolomorphicPoissonKernel_hasDerivAt hℓ hz y

private theorem norm_stripRegularizedHolomorphicPoissonKernelDeriv_pos
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (y : ℝ) :
    ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y‖ ≤
      Real.pi * Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (4 * ℓ ^ 2 *
          Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ^ 2) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hden :=
    stripSchwarzExponential_sub_one_norm_ge_sin hℓ hz y
  have hsq :
      Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ^ 2 ≤
        ‖stripSchwarzExponential ℓ z y - 1‖ ^ 2 := by
    nlinarith [norm_nonneg (stripSchwarzExponential ℓ z y - 1)]
  calc
    ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y‖ =
      Real.pi * Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (4 * ℓ ^ 2 *
          ‖stripSchwarzExponential ℓ z y - 1‖ ^ 2) := by
      unfold stripRegularizedHolomorphicPoissonKernelDeriv
      rw [norm_div, norm_neg, norm_mul, norm_mul,
        norm_mul, norm_mul, norm_pow, norm_pow,
        norm_stripSchwarzExponential]
      simp only [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        one_mul,
        Complex.norm_ofNat, abs_of_pos hℓ]
    _ ≤ Real.pi * Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (4 * ℓ ^ 2 *
          Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ^ 2) := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le)
        (by positivity)
      exact mul_le_mul_of_nonneg_left hsq (by positivity)

private theorem norm_stripRegularizedHolomorphicPoissonKernelDeriv_neg
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (y : ℝ) :
    ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y‖ ≤
      Real.pi * Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) /
        (4 * ℓ ^ 2 *
          Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ^ 2) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hexp :
      0 < Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) :=
    Real.exp_pos _
  have hden :=
    stripSchwarzExponential_sub_one_norm_ge_exp_mul_sin hℓ hz y
  have hsq :
      (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
          Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) ^ 2 ≤
        ‖stripSchwarzExponential ℓ z y - 1‖ ^ 2 := by
    exact
      (sq_le_sq₀ (mul_pos hexp hsin).le
        (norm_nonneg (stripSchwarzExponential ℓ z y - 1))).2 hden
  calc
    ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y‖ =
      Real.pi * Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (4 * ℓ ^ 2 *
          ‖stripSchwarzExponential ℓ z y - 1‖ ^ 2) := by
      unfold stripRegularizedHolomorphicPoissonKernelDeriv
      rw [norm_div, norm_neg, norm_mul, norm_mul,
        norm_mul, norm_mul, norm_pow, norm_pow,
        norm_stripSchwarzExponential]
      simp only [Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        one_mul,
        Complex.norm_ofNat, abs_of_pos hℓ]
    _ ≤ Real.pi * Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (4 * ℓ ^ 2 *
          (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
            Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) ^ 2) := by
      apply div_le_div_of_nonneg_left
        (mul_nonneg Real.pi_pos.le (Real.exp_pos _).le)
        (by positivity)
      exact mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = Real.pi * Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) /
        (4 * ℓ ^ 2 *
          Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) ^ 2) := by
      rw [Real.exp_neg]
      field_simp [hℓ.ne', hexp.ne', hsin.ne']

private theorem stripRegularizedHolomorphicPoissonKernelDeriv_continuous
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    Continuous
      (fun y : ℝ => stripRegularizedHolomorphicPoissonKernelDeriv ℓ z y) := by
  have hcoordinate := stripSchwarzExponential_continuous ℓ z
  unfold stripRegularizedHolomorphicPoissonKernelDeriv
  apply Continuous.div
  · exact
      ((continuous_const.mul continuous_const).mul hcoordinate).neg
  · exact continuous_const.mul
      ((hcoordinate.sub continuous_const).pow 2)
  · intro y
    apply mul_ne_zero
    · exact mul_ne_zero (by norm_num)
        (pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hℓ.ne'))
    · apply pow_ne_zero
      simpa only [stripSchwarzExponential, ne_eq] using!
        stripHolomorphicPoissonKernel_denominator_ne_zero hℓ hz y

private theorem stripRegularizedHolomorphicPoissonKernelDeriv_local_bound
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    ∃ S ∈ 𝓝 z, ∃ C : ℝ, 0 ≤ C ∧
      ∀ w ∈ S, ∀ y : ℝ,
        ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖ ≤
          C * Real.exp (-(Real.pi / (2 * ℓ)) * |y|) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  let a : ℝ := Real.pi / (2 * ℓ)
  let A : ℂ → ℝ :=
    fun w => Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ))
  let sin0 : ℝ := A z
  let D : ℝ := 4 * ℓ ^ 2 * (sin0 / 2) ^ 2
  let Cpos : ℝ := Real.pi * Real.exp (a * (z.re + 1)) / D
  let Cneg : ℝ := Real.pi * Real.exp (-a * (z.re - 1)) / D
  have ha : 0 < a := by
    try dsimp [a]
    exact div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)
  have hsin0 : 0 < sin0 := by
    try dsimp [sin0, A]
    exact Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hD : 0 < D := by
    try dsimp [D]
    positivity
  have hA : Continuous A := by
    try dsimp [A]
    fun_prop
  have hstrip :
      Complex.im ⁻¹' Ioo (-ℓ) ℓ ∈ 𝓝 z := by
    have him : Continuous (fun w : ℂ => w.im) := by
      fun_prop
    exact (isOpen_Ioo.preimage him).mem_nhds hz
  have hsinset : A ⁻¹' Ioi (sin0 / 2) ∈ 𝓝 z := by
    apply (isOpen_Ioi.preimage hA).mem_nhds
    change sin0 / 2 < sin0
    linarith
  have hCpos : 0 ≤ Cpos := by
    try dsimp [Cpos]
    positivity
  have hCneg : 0 ≤ Cneg := by
    try dsimp [Cneg]
    positivity
  refine ⟨Metric.ball z 1 ∩
      (Complex.im ⁻¹' Ioo (-ℓ) ℓ) ∩
      (A ⁻¹' Ioi (sin0 / 2)),
    inter_mem (inter_mem (Metric.ball_mem_nhds z (by norm_num))
      hstrip) hsinset,
    Cpos + Cneg, add_nonneg hCpos hCneg, ?_⟩
  intro w hw y
  obtain ⟨⟨hwball, hwstrip⟩, hwsin⟩ := hw
  have hdist : ‖w - z‖ < (1 : ℝ) := by
    simpa only [norm_sub_rev, Metric.mem_ball, dist_eq_norm] using! hwball
  have hreabs := Complex.abs_re_le_norm (w - z)
  simp only [Complex.sub_re] at hreabs
  have hreupper : w.re ≤ z.re + 1 := by
    linarith [le_abs_self (w.re - z.re)]
  have hrelower : z.re - 1 ≤ w.re := by
    linarith [neg_le_abs (w.re - z.re)]
  have hsinw : sin0 / 2 <
      Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ)) := by
    exact hwsin
  have hden :
      D ≤ 4 * ℓ ^ 2 *
        Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ)) ^ 2 := by
    try dsimp [D]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact
      (sq_le_sq₀ (by positivity) (le_trans
        (by positivity : 0 ≤ sin0 / 2) hsinw.le)).2 hsinw.le
  rcases le_total 0 y with hy | hy
  · have hnum :
        Real.pi * Real.exp (Real.pi * (w.re - y) / (2 * ℓ)) ≤
          Real.pi * Real.exp (a * (z.re + 1 - y)) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      apply Real.exp_le_exp.mpr
      calc
        Real.pi * (w.re - y) / (2 * ℓ) =
            a * (w.re - y) := by
          try dsimp [a]
          ring
        _ ≤ a * (z.re + 1 - y) :=
          mul_le_mul_of_nonneg_left (by linarith) ha.le
    calc
      ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖ ≤
          Real.pi * Real.exp (Real.pi * (w.re - y) / (2 * ℓ)) /
            (4 * ℓ ^ 2 *
              Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ)) ^ 2) :=
        norm_stripRegularizedHolomorphicPoissonKernelDeriv_pos
          hℓ hwstrip y
      _ ≤ Real.pi * Real.exp (a * (z.re + 1 - y)) / D := by
        exact div_le_div₀
          (by positivity) hnum hD hden
      _ = Cpos * Real.exp ((-a) * y) := by
        have hsplit :
            Real.exp (a * (z.re + 1 - y)) =
              Real.exp (a * (z.re + 1)) * Real.exp ((-a) * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hsplit]
        try dsimp [Cpos]
        ring
      _ ≤ (Cpos + Cneg) *
          Real.exp (-(Real.pi / (2 * ℓ)) * |y|) := by
        rw [abs_of_nonneg hy]
        change
          Cpos * Real.exp ((-a) * y) ≤
            (Cpos + Cneg) * Real.exp ((-a) * y)
        exact mul_le_mul_of_nonneg_right
          (by linarith) (Real.exp_pos _).le
  · have hnum :
        Real.pi * Real.exp (-(Real.pi * (w.re - y) / (2 * ℓ))) ≤
          Real.pi * Real.exp (-a * (z.re - 1 - y)) := by
      apply mul_le_mul_of_nonneg_left _ Real.pi_pos.le
      apply Real.exp_le_exp.mpr
      calc
        -(Real.pi * (w.re - y) / (2 * ℓ)) =
            -(a * (w.re - y)) := by
          try dsimp [a]
          ring
        _ ≤ -(a * (z.re - 1 - y)) := by
          apply neg_le_neg
          exact mul_le_mul_of_nonneg_left (by linarith) ha.le
        _ = -a * (z.re - 1 - y) := by ring
    calc
      ‖stripRegularizedHolomorphicPoissonKernelDeriv ℓ w y‖ ≤
          Real.pi *
            Real.exp (-(Real.pi * (w.re - y) / (2 * ℓ))) /
            (4 * ℓ ^ 2 *
              Real.sin (Real.pi * (w.im + ℓ) / (2 * ℓ)) ^ 2) :=
        norm_stripRegularizedHolomorphicPoissonKernelDeriv_neg
          hℓ hwstrip y
      _ ≤ Real.pi * Real.exp (-a * (z.re - 1 - y)) / D := by
        exact div_le_div₀
          (by positivity) hnum hD hden
      _ = Cneg * Real.exp (a * y) := by
        have hsplit :
            Real.exp (-a * (z.re - 1 - y)) =
              Real.exp (-a * (z.re - 1)) * Real.exp (a * y) := by
          rw [← Real.exp_add]
          congr 1
          ring
        rw [hsplit]
        try dsimp [Cneg]
        ring
      _ ≤ (Cpos + Cneg) *
          Real.exp (-(Real.pi / (2 * ℓ)) * |y|) := by
        rw [abs_of_nonpos hy]
        change
          Cneg * Real.exp (a * y) ≤
            (Cpos + Cneg) * Real.exp ((-a) * (-y))
        have hexp : Real.exp ((-a) * (-y)) = Real.exp (a * y) := by
          congr 1
          ring
        rw [hexp]
        exact mul_le_mul_of_nonneg_right
          (by linarith) (Real.exp_pos _).le

private theorem stripRegularizedHolomorphicPoissonKernel_of_nonneg
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    {y : ℝ} (hy : 0 ≤ y) :
    stripRegularizedHolomorphicPoissonKernel ℓ z y =
      Complex.I * stripSchwarzExponential ℓ z y /
        (2 * (ℓ : ℂ) * (stripSchwarzExponential ℓ z y - 1)) := by
  have hℓc : (ℓ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hden := stripHolomorphicPoissonKernel_denominator_ne_zero
    hℓ hz y
  let w := stripSchwarzExponential ℓ z y
  have hw : w - 1 ≠ 0 := by
    simpa only [stripSchwarzExponential, ne_eq] using! hden
  unfold stripRegularizedHolomorphicPoissonKernel
    stripHolomorphicPoissonKernel
  rw [ite_eq_left hy]
  change
    (Complex.I * ((w + 1) / (w - 1)) / 4) / (ℓ : ℂ) +
        Complex.I / ((4 * ℓ : ℝ) : ℂ) =
      Complex.I * w / (2 * (ℓ : ℂ) * (w - 1))
  rw [show ((4 * ℓ : ℝ) : ℂ) = 4 * (ℓ : ℂ) by push_cast; rfl]
  field_simp [hℓc, hw]
  ring

private theorem stripRegularizedHolomorphicPoissonKernel_of_neg
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    {y : ℝ} (hy : y < 0) :
    stripRegularizedHolomorphicPoissonKernel ℓ z y =
      Complex.I /
        (2 * (ℓ : ℂ) * (stripSchwarzExponential ℓ z y - 1)) := by
  have hℓc : (ℓ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hℓ.ne'
  have hden := stripHolomorphicPoissonKernel_denominator_ne_zero
    hℓ hz y
  let w := stripSchwarzExponential ℓ z y
  have hw : w - 1 ≠ 0 := by
    simpa only [stripSchwarzExponential, ne_eq] using! hden
  unfold stripRegularizedHolomorphicPoissonKernel
    stripHolomorphicPoissonKernel
  rw [ite_eq_right (not_le.mpr hy)]
  change
    (Complex.I * ((w + 1) / (w - 1)) / 4) / (ℓ : ℂ) +
        (-Complex.I) / ((4 * ℓ : ℝ) : ℂ) =
      Complex.I / (2 * (ℓ : ℂ) * (w - 1))
  rw [show ((4 * ℓ : ℝ) : ℂ) = 4 * (ℓ : ℂ) by push_cast; rfl]
  field_simp [hℓc, hw]
  ring

private theorem norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    {y : ℝ} (hy : 0 ≤ y) :
    ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hden :=
    stripSchwarzExponential_sub_one_norm_ge_sin hℓ hz y
  calc
    ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ =
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (2 * ℓ * ‖stripSchwarzExponential ℓ z y - 1‖) := by
      rw [stripRegularizedHolomorphicPoissonKernel_of_nonneg
        hℓ hz hy, norm_div, norm_mul, norm_mul,
        norm_stripSchwarzExponential]
      simp only [Complex.norm_I, one_mul, Complex.norm_mul, Complex.norm_ofNat,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hℓ]
    _ ≤ Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) /
        (2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) := by
      apply div_le_div_of_nonneg_left (Real.exp_pos _).le
        (mul_pos (mul_pos (by norm_num) hℓ) hsin)
      exact mul_le_mul_of_nonneg_left hden
        (mul_pos (by norm_num) hℓ).le

private theorem norm_stripRegularizedHolomorphicPoissonKernel_of_neg
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    {y : ℝ} (hy : y < 0) :
    ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
      Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) /
        (2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  have hexp : 0 < Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) :=
    Real.exp_pos _
  have hden :=
    stripSchwarzExponential_sub_one_norm_ge_exp_mul_sin hℓ hz y
  calc
    ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ =
      1 / (2 * ℓ * ‖stripSchwarzExponential ℓ z y - 1‖) := by
      rw [stripRegularizedHolomorphicPoissonKernel_of_neg
        hℓ hz hy, norm_div, norm_mul, norm_mul]
      simp only [Complex.norm_I, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hℓ, one_div,
        mul_inv_rev]
    _ ≤ 1 /
        (2 * ℓ *
          (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) *
            Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)))) := by
      apply div_le_div_of_nonneg_left (by norm_num)
        (mul_pos (mul_pos (by norm_num) hℓ)
          (mul_pos hexp hsin))
      exact mul_le_mul_of_nonneg_left hden
        (mul_pos (by norm_num) hℓ).le
    _ = Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) /
        (2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))) := by
      rw [Real.exp_neg]
      field_simp [hℓ.ne', hexp.ne', hsin.ne']

private theorem stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    ContinuousOn
      (fun y : ℝ => stripRegularizedHolomorphicPoissonKernel ℓ z y)
      (Ioi (0 : ℝ)) := by
  have hcoordinate := stripSchwarzExponential_continuous ℓ z
  have hden : ∀ y : ℝ,
      stripSchwarzExponential ℓ z y - 1 ≠ 0 := by
    intro y
    simpa only [stripSchwarzExponential, ne_eq] using!
      stripHolomorphicPoissonKernel_denominator_ne_zero hℓ hz y
  have hform :
      Continuous (fun y : ℝ =>
        Complex.I * stripSchwarzExponential ℓ z y /
          (2 * (ℓ : ℂ) *
            (stripSchwarzExponential ℓ z y - 1))) := by
    apply (continuous_const.mul hcoordinate).div
      (continuous_const.mul (hcoordinate.sub continuous_const))
    intro y
    exact mul_ne_zero
      (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (Complex.ofReal_ne_zero.mpr hℓ.ne'))
      (hden y)
  refine hform.continuousOn.congr ?_
  intro y hy
  exact stripRegularizedHolomorphicPoissonKernel_of_nonneg
    hℓ hz (mem_Ioi.mp hy).le

private theorem stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio
    {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ) :
    ContinuousOn
      (fun y : ℝ => stripRegularizedHolomorphicPoissonKernel ℓ z y)
      (Iio (0 : ℝ)) := by
  have hcoordinate := stripSchwarzExponential_continuous ℓ z
  have hden : ∀ y : ℝ,
      stripSchwarzExponential ℓ z y - 1 ≠ 0 := by
    intro y
    simpa only [stripSchwarzExponential, ne_eq] using!
      stripHolomorphicPoissonKernel_denominator_ne_zero hℓ hz y
  have hform :
      Continuous (fun y : ℝ =>
        Complex.I /
          (2 * (ℓ : ℂ) *
            (stripSchwarzExponential ℓ z y - 1))) := by
    apply continuous_const.div
      (continuous_const.mul (hcoordinate.sub continuous_const))
    intro y
    exact mul_ne_zero
      (mul_ne_zero (by norm_num : (2 : ℂ) ≠ 0)
        (Complex.ofReal_ne_zero.mpr hℓ.ne'))
      (hden y)
  refine hform.continuousOn.congr ?_
  intro y hy
  exact stripRegularizedHolomorphicPoissonKernel_of_neg
    hℓ hz (mem_Iio.mp hy)

private theorem strip_exp_abs_integrable {a : ℝ} (ha : 0 < a) :
    Integrable (fun y : ℝ => Real.exp ((-a) * |y|)) := by
  have hright :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * |y|))
        (Ioi (0 : ℝ)) := by
    refine
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0).congr_fun
        ?_ measurableSet_Ioi
    intro y hy
    try dsimp
    rw [abs_of_pos (mem_Ioi.mp hy)]
  have hreflected :
      IntegrableOn
        ((fun y : ℝ => Real.exp ((-a) * |y|)) ∘
          (fun y : ℝ => -y))
        ((fun y : ℝ => -y) ⁻¹' Iio (0 : ℝ)) := by
    simpa only [neg_mul, Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using! hright
  have hleft :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * |y|))
        (Iio (0 : ℝ)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩

private theorem strip_abs_log_le_add_rpow {x : ℝ} (hx : 0 < x) :
    |Real.log x| ≤ x + 2 * x ^ (-(1 / 2 : ℝ)) := by
  by_cases hlarge : 1 ≤ x
  · rw [abs_of_nonneg (Real.log_nonneg hlarge)]
    have hlog := Real.log_le_sub_one_of_pos hx
    have hpower := Real.rpow_pos_of_pos hx (-(1 / 2 : ℝ))
    linarith
  · have hsmall : x ≤ 1 := le_of_not_ge hlarge
    rw [abs_of_nonpos (Real.log_nonpos hx.le hsmall)]
    have hpower := Real.rpow_pos_of_pos hx (-(1 / 2 : ℝ))
    have hlog := Real.log_le_sub_one_of_pos hpower
    rw [Real.log_rpow hx] at hlog
    linarith

private theorem strip_exp_abs_log_integrableOn_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => Real.exp ((-a) * x) * |Real.log x|)
      (Ioi (0 : ℝ)) := by
  have hlinear :
      IntegrableOn (fun x : ℝ =>
        x * Real.exp ((-a) * x)) (Ioi (0 : ℝ)) := by
    simpa only [neg_mul, Real.rpow_one] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := a)
        (by norm_num) (by norm_num) ha)
  have hhalf :
      IntegrableOn (fun x : ℝ =>
        x ^ (-(1 / 2 : ℝ)) * Real.exp ((-a) * x))
        (Ioi (0 : ℝ)) := by
    simpa only [one_div, neg_mul, Real.rpow_one] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := -(1 / 2 : ℝ)) (b := a)
        (by norm_num) (by norm_num) ha)
  have hmajorant :
      IntegrableOn (fun x : ℝ =>
        x * Real.exp ((-a) * x) +
          2 * (x ^ (-(1 / 2 : ℝ)) * Real.exp ((-a) * x)))
        (Ioi (0 : ℝ)) := hlinear.add (hhalf.const_mul 2)
  have hlogcontinuous :
      ContinuousOn (fun x : ℝ => Real.log x) (Ioi (0 : ℝ)) :=
    continuousOn_id.log (fun x hx => (mem_Ioi.mp hx).ne')
  have hexpcontinuous :
      ContinuousOn (fun x : ℝ => Real.exp ((-a) * x))
        (Ioi (0 : ℝ)) := by
    fun_prop
  apply hmajorant.mono'
    ((hexpcontinuous.mul hlogcontinuous.abs).aestronglyMeasurable
      measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hlog := strip_abs_log_le_add_rpow (mem_Ioi.mp hx)
  change ‖Real.exp ((-a) * x) * |Real.log x|‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_abs]
  calc
    Real.exp ((-a) * x) * |Real.log x| ≤
        Real.exp ((-a) * x) *
          (x + 2 * x ^ (-(1 / 2 : ℝ))) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = x * Real.exp ((-a) * x) +
        2 * (x ^ (-(1 / 2 : ℝ)) * Real.exp ((-a) * x)) := by
      ring

private theorem strip_exp_abs_log_integrableOn_Iio {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun x : ℝ => Real.exp (a * x) * |Real.log (-x)|)
      (Iio (0 : ℝ)) := by
  have hright := strip_exp_abs_log_integrableOn_Ioi ha
  have hreflected :
      IntegrableOn
        ((fun x : ℝ => Real.exp (a * x) * |Real.log (-x)|) ∘
          (fun x : ℝ => -x))
        ((fun x : ℝ => -x) ⁻¹' Iio (0 : ℝ)) := by
    simpa only [Real.log_neg_eq_log, Function.comp_def, mul_neg, neg_preimage, neg_Iio,
      neg_zero, neg_mul] using! hright
  exact
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected

/-- The exponential strip weight times the absolute logarithm is integrable. -/
public
theorem strip_exp_abs_log_abs_integrable {a : ℝ} (ha : 0 < a) :
    Integrable
      (fun x : ℝ =>
        Real.exp ((-a) * |x|) * |Real.log (|x|)|) := by
  have hright :
      IntegrableOn
        (fun x : ℝ =>
          Real.exp ((-a) * |x|) * |Real.log (|x|)|)
        (Ioi (0 : ℝ)) := by
    refine (strip_exp_abs_log_integrableOn_Ioi ha).congr_fun ?_
      measurableSet_Ioi
    intro x hx
    try dsimp
    rw [abs_of_pos (mem_Ioi.mp hx)]
  have hleft :
      IntegrableOn
        (fun x : ℝ =>
          Real.exp ((-a) * |x|) * |Real.log (|x|)|)
        (Iio (0 : ℝ)) := by
    refine (strip_exp_abs_log_integrableOn_Iio ha).congr_fun ?_
      measurableSet_Iio
    intro x hx
    try dsimp
    rw [abs_of_neg (mem_Iio.mp hx)]
    simp only [Real.log_neg_eq_log, mul_neg, neg_mul, neg_neg]
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩

private theorem stripRegularizedHolomorphicPoissonKernel_re
    {ℓ σ : ℝ} (hℓ : 0 < ℓ)
    (hbelow : -1 < σ) (habove : σ < 1) (s y : ℝ) :
    (stripRegularizedHolomorphicPoissonKernel ℓ
      ((s : ℂ) + Complex.I * ((σ * ℓ : ℝ) : ℂ)) y).re =
      stripPoissonKernel σ ((s - y) / ℓ) / ℓ := by
  unfold stripRegularizedHolomorphicPoissonKernel
  rw [Complex.add_re, Complex.div_ofReal_re,
    stripHolomorphicPoissonKernel_re hℓ hbelow habove]
  split <;> simp

end

section

open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology

private noncomputable def profileNegativePart (φ : ℝ → ℝ) (v : ℝ) : ℝ :=
  max (-φ v) 0

private theorem profileNegativePart_integrable {φ : ℝ → ℝ}
    (hφ : Integrable φ) : Integrable (profileNegativePart φ) := by
  change Integrable ((-φ) ⊔ (0 : ℝ → ℝ))
  exact hφ.neg.sup (integrable_zero ℝ ℝ volume)

private theorem abs_sub_eq_two_profileNegativePart (φ : ℝ → ℝ) (v : ℝ) :
    |φ v| - φ v = 2 * profileNegativePart φ v := by
  unfold profileNegativePart
  rcases le_total 0 (φ v) with h | h
  · rw [abs_of_nonneg h, max_eq_right (by linarith)]
    ring
  · rw [abs_of_nonpos h, max_eq_left (by linarith)]
    ring

private theorem integral_profileNegativePart_eq_half {φ : ℝ → ℝ}
    (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0)
    (hmass : (∫ v : ℝ, |φ v|) = 1) :
    (∫ v : ℝ, profileNegativePart φ v) = (1 / 2 : ℝ) := by
  have hsigned : (∫ v : ℝ, (|φ v| - φ v)) = 1 := by
    rw [integral_sub hφ.abs hφ, hmass, hmean]
    norm_num
  have htwice :
      (∫ v : ℝ, (|φ v| - φ v)) =
        2 * ∫ v : ℝ, profileNegativePart φ v := by
    calc
      (∫ v : ℝ, (|φ v| - φ v)) =
          ∫ v : ℝ, 2 * profileNegativePart φ v := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall
          (abs_sub_eq_two_profileNegativePart φ)
      _ = 2 * ∫ v : ℝ, profileNegativePart φ v := by
        rw [integral_const_mul]
  linarith

private theorem profileNegativePart_setIntegral_Iic_eq_integral {φ : ℝ → ℝ}
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) :
    (∫ v in Iic (0 : ℝ), profileNegativePart φ v) =
      ∫ v : ℝ, profileNegativePart φ v := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro v hv
  have hvpos : 0 < v := by simpa only [mem_Iic, not_le] using! hv
  unfold profileNegativePart
  exact max_eq_right (by linarith [hsign v hvpos.le])

private theorem normalizedProfile_negativeHalfline_mass_ge_half {φ : ℝ → ℝ}
    (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0)
    (hmass : (∫ v : ℝ, |φ v|) = 1)
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v) :
    (1 / 2 : ℝ) ≤ ∫ v in Iic (0 : ℝ), |φ v| := by
  have hneg := profileNegativePart_integrable hφ
  calc
    (1 / 2 : ℝ) = ∫ v : ℝ, profileNegativePart φ v :=
      (integral_profileNegativePart_eq_half hφ hmean hmass).symm
    _ = ∫ v in Iic (0 : ℝ), profileNegativePart φ v :=
      (profileNegativePart_setIntegral_Iic_eq_integral hsign).symm
    _ ≤ ∫ v in Iic (0 : ℝ), |φ v| := by
      refine setIntegral_mono_on hneg.integrableOn hφ.abs.integrableOn
        measurableSet_Iic ?_
      intro v _
      unfold profileNegativePart
      exact max_le (neg_le_abs _) (abs_nonneg _)

private theorem normalizedProfile_negativeHalfline_le_of_exp_majorant
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    {a B : ℝ} (ha : 0 < a)
    (hbound : ∀ v : ℝ, v ≤ 0 → |φ v| ≤ B * Real.exp (a * v)) :
    (∫ v in Iic (0 : ℝ), |φ v|) ≤ B / a := by
  have hexp : IntegrableOn (fun v : ℝ => Real.exp (a * v))
      (Iic (0 : ℝ)) := integrableOn_exp_mul_Iic ha 0
  have hmajorant :
      IntegrableOn (fun v : ℝ => B * Real.exp (a * v))
        (Iic (0 : ℝ)) := hexp.const_mul B
  calc
    (∫ v in Iic (0 : ℝ), |φ v|) ≤
        ∫ v in Iic (0 : ℝ), B * Real.exp (a * v) := by
      exact setIntegral_mono_on hφ.abs.integrableOn hmajorant
        measurableSet_Iic (fun v hv => hbound v hv)
    _ = B / a := by
      rw [integral_const_mul, integral_exp_mul_Iic ha 0]
      simp only [mul_zero, Real.exp_zero, div_eq_mul_inv, one_mul]

private theorem norm_fourierInv_le_integral_norm (F : ℝ → ℂ) (v : ℝ) :
    ‖((𝓕⁻ F : ℝ → ℂ) v)‖ ≤ ∫ s : ℝ, ‖F s‖ := by
  exact VectorFourier.norm_fourierIntegral_le_integral_norm
    Real.fourierChar volume (-innerₗ ℝ) F v

private theorem norm_scaled_fourierInv_le_integral_norm (Z : ℝ → ℂ) (v : ℝ) :
    ‖((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)‖ ≤
      (2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖ := by
  calc
    ‖((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)‖ ≤
        ∫ ξ : ℝ, ‖Z (2 * Real.pi * ξ)‖ :=
      norm_fourierInv_le_integral_norm
        (fun ξ : ℝ => Z (2 * Real.pi * ξ)) v
    _ = (2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖ := by
      rw [Measure.integral_comp_mul_left
        (fun s : ℝ => ‖Z s‖) (2 * Real.pi)]
      change |(2 * Real.pi)⁻¹| * (∫ s : ℝ, ‖Z s‖) =
        (2 * Real.pi)⁻¹ * (∫ s : ℝ, ‖Z s‖)
      rw [abs_of_pos (inv_pos.mpr (mul_pos (by norm_num) Real.pi_pos))]

private theorem negativeHalfline_le_of_fourierInversion
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    {a : ℝ} (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ,
      (φ v : ℂ) = (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)) :
    (∫ v in Iic (0 : ℝ), |φ v|) ≤
      ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a := by
  apply normalizedProfile_negativeHalfline_le_of_exp_majorant hφ ha
  intro v _
  calc
    |φ v| = ‖(φ v : ℂ)‖ := by simp only [Complex.norm_real, Real.norm_eq_abs]
    _ = ‖(Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)‖ := by
      rw [hinversion v]
    _ = Real.exp (a * v) *
        ‖((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v)‖ := by
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
    _ ≤ Real.exp (a * v) *
        ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) := by
      exact mul_le_mul_of_nonneg_left
        (norm_scaled_fourierInv_le_integral_norm Z v)
        (Real.exp_pos _).le
    _ = ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) *
        Real.exp (a * v) := by ring

private theorem no_normalizedProfile_of_fourierInversion_lt_half
    {φ : ℝ → ℝ} (hφ : Integrable φ)
    (hmean : (∫ v : ℝ, φ v) = 0)
    (hmass : (∫ v : ℝ, |φ v|) = 1)
    (hsign : ∀ v : ℝ, 0 ≤ v → 0 ≤ φ v)
    {a : ℝ} (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ,
      (φ v : ℂ) = (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v))
    (hsmall : ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a <
      (1 / 2 : ℝ)) : False := by
  have hlower := normalizedProfile_negativeHalfline_mass_ge_half
    hφ hmean hmass hsign
  have hupper := negativeHalfline_le_of_fourierInversion
    hφ ha Z hinversion
  linarith

private theorem no_antiFourierWitness_of_fourierInversion_lt_half
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R)
    {a : ℝ} (ha : 0 < a) (Z : ℝ → ℂ)
    (hinversion : ∀ v : ℝ,
      (normalizedRadialLogProfile hd w.function R v : ℂ) =
        (Real.exp (a * v) : ℂ) *
          ((𝓕⁻ (fun ξ : ℝ => Z (2 * Real.pi * ξ)) : ℝ → ℂ) v))
    (hsmall : ((2 * Real.pi)⁻¹ * ∫ s : ℝ, ‖Z s‖) / a <
      (1 / 2 : ℝ)) : False := by
  obtain ⟨hintegrable, hmean, hmass, hsign⟩ :=
    antiFourierWitness_normalizedRadialLogProfile hd hR w
  exact no_normalizedProfile_of_fourierInversion_lt_half
    hintegrable hmean hmass hsign ha Z hinversion hsmall

private theorem antiFourierWitness_normalizedMellinStrip_diffContOnCl
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) :
    DiffContOnCl ℂ
      (normalizedRadialMellinStrip hd w.function R)
      (Complex.im ⁻¹'
        Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) :=
  normalizedRadialMellinStrip_diffContOnCl
    hd w.function w.radial w.zero_value R

private theorem antiFourierWitness_normalizedMellinStrip_top_norm_le_one
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) (y : ℝ) :
    ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) +
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤ 1 :=
  normalizedRadialMellinStrip_top_norm_le_one
    hd w.function w.radial w.nonzero R y

private theorem antiFourierWitness_normalizedMellinStrip_uniform_bound
    {d : ℕ} (hd : 0 < d) {R : ℝ}
    (w : AntiFourierWitness d R) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ z : ℂ,
        -((d : ℝ) / 2) ≤ z.im →
        z.im ≤ (d : ℝ) / 2 →
          ‖normalizedRadialMellinStrip hd w.function R z‖ ≤ C :=
  normalizedRadialMellinStrip_uniform_bound
    hd w.function w.radial w.zero_value R

private theorem antiFourierWitness_normalizedMellinStrip_shifted_integrable
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) {a : ℝ}
    (ha : a < (d : ℝ)) :
    Integrable (fun t : ℝ =>
      normalizedRadialMellinStrip hd w.function R
        ((t : ℂ) + Complex.I *
          ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) :=
  normalizedRadialMellinStrip_shifted_integrable
    hd w.function w.real hR ha

private theorem antiFourierWitness_normalizedMellinStrip_shifted_fourier_inversion
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) {a : ℝ}
    (ha : a < (d : ℝ)) (v : ℝ) :
    (normalizedRadialLogProfile hd w.function R v : ℂ) =
      (Real.exp (a * v) : ℂ) *
        ((𝓕⁻ (fun ξ : ℝ =>
          normalizedRadialMellinStrip hd w.function R
            (((2 * Real.pi * ξ : ℝ) : ℂ) +
              Complex.I *
                ((((d : ℝ) / 2 - a : ℝ) : ℂ)))) :
            ℝ → ℂ) v) :=
  normalizedRadialMellinStrip_shifted_fourier_inversion
    hd w.function w.radial w.real w.zero_value hR ha v

private theorem no_antiFourierWitness_of_shiftedMellinL1_lt_half
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R)
    {a : ℝ} (hapos : 0 < a) (haless : a < (d : ℝ))
    (hsmall :
      ((2 * Real.pi)⁻¹ *
        ∫ s : ℝ,
          ‖normalizedRadialMellinStrip hd w.function R
            ((s : ℂ) + Complex.I *
              ((((d : ℝ) / 2 - a : ℝ) : ℂ)))‖) / a <
        (1 / 2 : ℝ)) : False := by
  apply no_antiFourierWitness_of_fourierInversion_lt_half
    hd hR w hapos
    (fun s : ℝ => normalizedRadialMellinStrip hd w.function R
      ((s : ℂ) + Complex.I *
        ((((d : ℝ) / 2 - a : ℝ) : ℂ))))
  · intro v
    exact
      antiFourierWitness_normalizedMellinStrip_shifted_fourier_inversion
        hd hR w haless v
  · exact hsmall

private theorem no_antiFourierWitness_of_interiorMellinL1_lt_half
    {d : ℕ} (hd : 0 < d) {R σ : ℝ} (hR : 0 < R)
    (hσbelow : -1 < σ) (hσabove : σ < 1)
    (w : AntiFourierWitness d R)
    (hsmall :
      ((2 * Real.pi)⁻¹ *
        ∫ s : ℝ,
          ‖normalizedRadialMellinStrip hd w.function R
            ((s : ℂ) + Complex.I *
              (((σ * ((d : ℝ) / 2) : ℝ) : ℂ)))‖) /
          ((1 - σ) * ((d : ℝ) / 2)) <
        (1 / 2 : ℝ)) : False := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  have ha : 0 < (1 - σ) * ((d : ℝ) / 2) :=
    mul_pos (sub_pos.mpr hσabove) hℓ
  have haless :
      (1 - σ) * ((d : ℝ) / 2) < (d : ℝ) := by
    linarith [mul_pos (by linarith : 0 < 1 + σ) hℓ]
  have hheight :
      (d : ℝ) / 2 - (1 - σ) * ((d : ℝ) / 2) =
        σ * ((d : ℝ) / 2) := by
    ring
  apply no_antiFourierWitness_of_shiftedMellinL1_lt_half
    hd hR w ha haless
  simpa only [mul_inv_rev, hheight, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_natCast,
    Complex.ofReal_ofNat, one_div] using! hsmall

private noncomputable def lowerGammaBoundaryLog (ℓ R y : ℝ) : ℝ :=
  ℓ * Real.log (Real.pi * R ^ 2) +
    Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
    Real.log ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖

private theorem lowerGammaBoundaryLog_continuousOn
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) {S : Set ℝ}
    (hS : ∀ y ∈ S, y ≠ 0) :
    ContinuousOn (lowerGammaBoundaryLog ℓ R) S := by
  have hnumPole (y : ℝ) (hy : y ∈ S) :
      ∀ m : ℕ,
        -Complex.I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have him := congrArg Complex.im hm
    norm_num at him
    exact hS y hy (by linarith)
  have hdenPole (y : ℝ) :
      ∀ m : ℕ,
        (ℓ : ℂ) + Complex.I * (y : ℂ) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    norm_num at hre
    have hmnonneg : 0 ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hnum :
      ContinuousOn
        (fun y : ℝ => Complex.Gamma (-Complex.I * (y : ℂ) / 2)) S := by
    intro y hy
    have harg :
        ContinuousAt (fun u : ℝ => -Complex.I * (u : ℂ) / 2) y :=
      ((Complex.continuous_ofReal.const_mul (-Complex.I)).div_const 2).continuousAt
    apply ContinuousAt.continuousWithinAt
    simpa only [neg_mul, Function.comp_def] using!
      (Complex.continuousAt_Gamma
        (-Complex.I * (y : ℂ) / 2) (hnumPole y hy)).comp_of_eq
        harg (by rfl)
  have hden :
      ContinuousOn
        (fun y : ℝ =>
          Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)) S := by
    intro y hy
    have harg :
        ContinuousAt
          (fun u : ℝ => (ℓ : ℂ) + Complex.I * (u : ℂ) / 2) y :=
      (continuous_const.add
        ((Complex.continuous_ofReal.const_mul Complex.I).div_const 2)).continuousAt
    apply ContinuousAt.continuousWithinAt
    simpa only [Function.comp_def] using!
      (Complex.continuousAt_Gamma
        ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2) (hdenPole y)).comp_of_eq
        harg (by rfl)
  have hnumlog :
      ContinuousOn
        (fun y : ℝ =>
          Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖) S := by
    apply hnum.norm.log
    intro y hy
    exact norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero (hnumPole y hy))
  have hdenlog :
      ContinuousOn
        (fun y : ℝ =>
          Real.log
            ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) S := by
    apply hden.norm.log
    intro y hy
    exact norm_ne_zero_iff.mpr
      (Complex.Gamma_ne_zero (hdenPole y))
  change ContinuousOn
    (fun y : ℝ =>
      ℓ * Real.log (Real.pi * R ^ 2) +
        Real.log ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ -
        Real.log
          ‖Complex.Gamma ((ℓ : ℂ) + Complex.I * (y : ℂ) / 2)‖) S
  exact (continuousOn_const.add hnumlog).sub hdenlog

private theorem lowerGammaBoundaryLog_measurable
    {ℓ : ℝ} (hℓ : 0 < ℓ) (R : ℝ) :
    Measurable (lowerGammaBoundaryLog ℓ R) := by
  apply measurable_of_continuousOn_compl_singleton (0 : ℝ)
  apply lowerGammaBoundaryLog_continuousOn hℓ R
  intro y hy
  simpa only [ne_eq, mem_compl_iff, mem_singleton_iff] using! hy

private theorem antiFourierWitness_normalizedMellinStrip_bottom_norm_le_gamma
    {d : ℕ} (hd : 0 < d) {R : ℝ} (hR : 0 < R)
    (w : AntiFourierWitness d R) (y : ℝ) (hy : y ≠ 0) :
    ‖normalizedRadialMellinStrip hd w.function R
        ((y : ℂ) -
          Complex.I * (((d : ℝ) / 2 : ℝ) : ℂ))‖ ≤
      Real.exp (lowerGammaBoundaryLog ((d : ℝ) / 2) R y) := by
  simpa only [Complex.ofReal_div, Complex.ofReal_natCast, Complex.ofReal_ofNat,
    lowerGammaBoundaryLog,
    neg_mul] using!
    normalizedRadialMellinStrip_bottom_norm_le_gamma
      hd w.function w.radial w.zero_value
      w.anti_fourier w.nonzero R hR y hy

private noncomputable def lowerStripPoissonMajorant (ℓ R σ s : ℝ) : ℝ :=
  ∫ T : ℝ,
    stripPoissonKernel σ T *
      lowerGammaBoundaryLog ℓ R (s - ℓ * T)

private theorem stripPoisson_integral_changeVariables
    {ℓ : ℝ} (hℓ : 0 < ℓ) (σ s : ℝ) (h : ℝ → ℝ) :
    (∫ y : ℝ,
      stripPoissonKernel σ ((s - y) / ℓ) / ℓ * h y) =
      ∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T) := by
  let G : ℝ → ℝ :=
    fun y => stripPoissonKernel σ ((s - y) / ℓ) / ℓ * h y
  have hscale :
      (∫ T : ℝ, G (s - ℓ * T)) =
        ℓ⁻¹ * ∫ y : ℝ, G y := by
    have hraw := Measure.integral_comp_mul_left
      (fun u : ℝ => G (s + u)) (-ℓ)
    rw [integral_add_left_eq_self G s] at hraw
    simpa only [sub_eq_add_neg, neg_mul, inv_neg, abs_neg, abs_of_pos (inv_pos.mpr hℓ),
      smul_eq_mul] using! hraw
  have hrewrite :
      (∫ T : ℝ, G (s - ℓ * T)) =
        ℓ⁻¹ *
          ∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T) := by
    calc
      (∫ T : ℝ, G (s - ℓ * T)) =
          ∫ T : ℝ,
            ℓ⁻¹ *
              (stripPoissonKernel σ T * h (s - ℓ * T)) := by
        apply integral_congr_ae
        refine Filter.Eventually.of_forall (fun T => ?_)
        have hargument : (s - (s - ℓ * T)) / ℓ = T := by
          field_simp [hℓ.ne']
          ring
        try dsimp [G]
        rw [hargument]
        ring
      _ = ℓ⁻¹ *
          ∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T) := by
        rw [integral_const_mul]
  change (∫ y : ℝ, G y) =
    ∫ T : ℝ, stripPoissonKernel σ T * h (s - ℓ * T)
  exact mul_left_cancel₀ (inv_ne_zero hℓ.ne')
    (hscale.symm.trans hrewrite)

private theorem norm_integerGammaFactor (j : ℕ) (y : ℝ) :
    ‖(j : ℂ) + Complex.I * (y : ℂ) / 2‖ =
      Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [Complex.add_re, Complex.natCast_re, Complex.div_ofNat_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_re, zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, zero_div,
      add_zero,
    Complex.add_im, Complex.natCast_im, Complex.div_ofNat_im, Complex.mul_im, one_mul, zero_add]
  ring

private theorem integerGammaFactor_ne_zero
    (j : ℕ) {y : ℝ} (hy : y ≠ 0) :
    (j : ℂ) + Complex.I * (y : ℂ) / 2 ≠ 0 := by
  intro hz
  have him := congrArg Complex.im hz
  norm_num at him
  exact hy (by linarith)

private theorem gamma_imaginary_ne_zero {y : ℝ} (hy : y ≠ 0) :
    Complex.Gamma (Complex.I * (y : ℂ) / 2) ≠ 0 := by
  apply Complex.Gamma_ne_zero
  intro j hj
  have him := congrArg Complex.im hj
  norm_num at him
  exact hy (by linarith)

private theorem norm_gamma_neg_imaginary (y : ℝ) :
    ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ =
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ := by
  have harg :
      -Complex.I * (y : ℂ) / 2 =
        starRingEnd ℂ (Complex.I * (y : ℂ) / 2) := by
    simp only [map_div₀, map_mul, Complex.conj_ofReal,
      Complex.conj_I, Complex.conj_ofNat]
  rw [harg, Complex.Gamma_conj, RCLike.norm_conj]

private theorem lowerGammaBoundaryLog_integer
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R y =
      (k : ℝ) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
  have hbase :
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gamma_imaginary_ne_zero hy)
  have hproduct :
      (∏ j ∈ Finset.range k,
        ((j : ℂ) + Complex.I * (y : ℂ) / 2)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun j _ => integerGammaFactor_ne_zero j hy)
  have hproductnorm :
      ‖∏ j ∈ Finset.range k,
        ((j : ℂ) + Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hproduct
  have hlogproduct :
      Real.log
        ‖∏ j ∈ Finset.range k,
          ((j : ℂ) + Complex.I * (y : ℂ) / 2)‖ =
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
    rw [Complex.norm_prod]
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro j _
      rw [norm_integerGammaFactor]
    · intro j _
      exact norm_ne_zero_iff.mpr (integerGammaFactor_ne_zero j hy)
  have hcast : ((k : ℝ) : ℂ) = (k : ℂ) := by
    norm_cast
  unfold lowerGammaBoundaryLog
  rw [hcast, integer_gamma_product k hy, norm_mul,
    Real.log_mul hbase hproductnorm, norm_gamma_neg_imaginary,
    hlogproduct]
  ring

private theorem lower_sqrtFactor_ge_abs_half (c y : ℝ) :
    |y| / 2 ≤ Real.sqrt (c ^ 2 + (y / 2) ^ 2) := by
  apply (Real.le_sqrt (by positivity) (by positivity)).2
  linarith [sq_nonneg c, sq_abs y]

private theorem lowerGammaBoundaryLog_integer_log_tail
    (k : ℕ) {R y : ℝ} (hR : 0 < R) (hy : y ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R y ≤
      (k : ℝ) * Real.log
        (2 * Real.pi * R ^ 2 / |y|) := by
  have hyhalf : 0 < |y| / 2 := by positivity
  have hsum :
      (k : ℝ) * Real.log (|y| / 2) ≤
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
    calc
      (k : ℝ) * Real.log (|y| / 2) =
          ∑ j ∈ Finset.range k,
            Real.log (|y| / 2) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact Real.log_le_log hyhalf
          (lower_sqrtFactor_ge_abs_half (j : ℝ) y)
  have hlogratio :
      Real.log (Real.pi * R ^ 2) - Real.log (|y| / 2) =
        Real.log (2 * Real.pi * R ^ 2 / |y|) := by
    rw [← Real.log_div
      (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hR.ne'))
      hyhalf.ne']
    congr 1
    field_simp [abs_ne_zero.mpr hy]
  rw [lowerGammaBoundaryLog_integer k R hy]
  calc
    (k : ℝ) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) ≤
      (k : ℝ) * Real.log (Real.pi * R ^ 2) -
        (k : ℝ) * Real.log (|y| / 2) := by
        linarith
    _ = (k : ℝ) *
        (Real.log (Real.pi * R ^ 2) -
          Real.log (|y| / 2)) := by
      ring
    _ = (k : ℝ) * Real.log
        (2 * Real.pi * R ^ 2 / |y|) := by
      rw [hlogratio]

private theorem lower_abs_log_sqrtFactor_le
    {c y : ℝ} (hc : 0 ≤ c) (hy : 0 < y) :
    |Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))| ≤
      c + y / 2 + |Real.log (y / 2)| := by
  have ht : 0 < y / 2 := by positivity
  have hinside : 0 < c ^ 2 + (y / 2) ^ 2 := by
    linarith [sq_nonneg c, sq_pos_of_pos ht]
  have hsqrt : 0 < Real.sqrt (c ^ 2 + (y / 2) ^ 2) :=
    Real.sqrt_pos.2 hinside
  have hlower :
      y / 2 ≤ Real.sqrt (c ^ 2 + (y / 2) ^ 2) := by
    apply (Real.le_sqrt ht.le hinside.le).2
    linarith [sq_nonneg c]
  have hupper :
      Real.sqrt (c ^ 2 + (y / 2) ^ 2) ≤ c + y / 2 := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · linarith [mul_nonneg hc ht.le]
  by_cases hlarge : 1 ≤ Real.sqrt (c ^ 2 + (y / 2) ^ 2)
  · rw [abs_of_nonneg (Real.log_nonneg hlarge)]
    have hlog := Real.log_le_sub_one_of_pos hsqrt
    have habs := abs_nonneg (Real.log (y / 2))
    linarith
  · rw [abs_of_nonpos
      (Real.log_nonpos hsqrt.le (le_of_not_ge hlarge))]
    have hlog := Real.log_le_log ht hlower
    have habs := neg_le_abs (Real.log (y / 2))
    have hnonneg : 0 ≤ c + y / 2 := by positivity
    linarith

private theorem lower_exp_abs_log_div_two_integrableOn_Ioi
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun y : ℝ =>
        Real.exp ((-a) * y) * |Real.log (y / 2)|)
      (Ioi (0 : ℝ)) := by
  have hexponential :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  have hmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Real.exp ((-a) * y) * |Real.log y| +
            |Real.log (2 : ℝ)| * Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) :=
    (strip_exp_abs_log_integrableOn_Ioi ha).add
      (hexponential.const_mul |Real.log (2 : ℝ)|)
  have hcontinuous :
      ContinuousOn
        (fun y : ℝ =>
          Real.exp ((-a) * y) * |Real.log (y / 2)|)
        (Ioi (0 : ℝ)) := by
    apply ContinuousOn.mul
    · exact (continuous_id.const_mul (-a)).rexp.continuousOn
    · apply ContinuousOn.abs
      apply ContinuousOn.log
      · exact (continuous_id.div_const 2).continuousOn
      · intro y hy
        exact div_ne_zero (mem_Ioi.mp hy).ne' (by norm_num)
  apply hmajorant.mono'
    (hcontinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos := mem_Ioi.mp hy
  have hlog :
      |Real.log (y / 2)| ≤ |Real.log y| + |Real.log (2 : ℝ)| := by
    rw [Real.log_div hypos.ne' (by norm_num)]
    exact abs_sub _ _
  change ‖Real.exp ((-a) * y) * |Real.log (y / 2)|‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _), abs_abs]
  calc
    Real.exp ((-a) * y) * |Real.log (y / 2)| ≤
        Real.exp ((-a) * y) *
          (|Real.log y| + |Real.log (2 : ℝ)|) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = Real.exp ((-a) * y) * |Real.log y| +
        |Real.log (2 : ℝ)| * Real.exp ((-a) * y) := by
      ring

private theorem lower_exp_log_sqrtFactor_integrableOn_Ioi
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    IntegrableOn
      (fun y : ℝ => Real.exp ((-a) * y) *
        Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2)))
      (Ioi (0 : ℝ)) := by
  have hexponential :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  have hlinear :
      IntegrableOn
        (fun y : ℝ => y * Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) := by
    simpa only [neg_mul, Real.rpow_one] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := a)
        (by norm_num) (by norm_num) ha)
  have hmajorant :
      IntegrableOn
        (fun y : ℝ =>
          c * Real.exp ((-a) * y) +
            (1 / 2 : ℝ) * (y * Real.exp ((-a) * y)) +
            Real.exp ((-a) * y) * |Real.log (y / 2)|)
        (Ioi (0 : ℝ)) :=
    ((hexponential.const_mul c).add (hlinear.const_mul (1 / 2))).add
      (lower_exp_abs_log_div_two_integrableOn_Ioi ha)
  have hcontinuous :
      ContinuousOn
        (fun y : ℝ => Real.exp ((-a) * y) *
          Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2)))
        (Ioi (0 : ℝ)) := by
    apply ContinuousOn.mul
    · exact (continuous_id.const_mul (-a)).rexp.continuousOn
    · apply ContinuousOn.log
      · exact (continuous_const.add
          ((continuous_id.div_const 2).pow 2)).sqrt.continuousOn
      · intro y hy
        apply (Real.sqrt_pos.2 ?_).ne'
        have ht : 0 < y / 2 := by
          exact half_pos (mem_Ioi.mp hy)
        linarith [sq_nonneg c, sq_pos_of_pos ht]
  apply hmajorant.mono'
    (hcontinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hlog := lower_abs_log_sqrtFactor_le hc (mem_Ioi.mp hy)
  change ‖Real.exp ((-a) * y) *
      Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp ((-a) * y) *
        |Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))| ≤
      Real.exp ((-a) * y) *
        (c + y / 2 + |Real.log (y / 2)|) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = c * Real.exp ((-a) * y) +
          (1 / 2 : ℝ) * (y * Real.exp ((-a) * y)) +
          Real.exp ((-a) * y) * |Real.log (y / 2)| := by
      ring

private theorem lower_exp_log_sqrtFactor_integrable
    {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) :
    Integrable
      (fun y : ℝ => Real.exp ((-a) * |y|) *
        Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))) := by
  have hright :
      IntegrableOn
        (fun y : ℝ => Real.exp ((-a) * |y|) *
          Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2)))
        (Ioi (0 : ℝ)) := by
    refine (lower_exp_log_sqrtFactor_integrableOn_Ioi ha hc).congr_fun ?_
      measurableSet_Ioi
    intro y hy
    try dsimp
    rw [abs_of_pos (mem_Ioi.mp hy)]
  have hreflected :
      IntegrableOn
        ((fun y : ℝ => Real.exp ((-a) * |y|) *
          Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2))) ∘
            (fun y : ℝ => -y))
        ((fun y : ℝ => -y) ⁻¹' Iio (0 : ℝ)) := by
    simpa only [neg_mul, Function.comp_def, abs_neg, neg_div, even_two, Even.neg_pow,
      neg_preimage, neg_Iio,
      neg_zero] using! hright
  have hleft :
      IntegrableOn
        (fun y : ℝ => Real.exp ((-a) * |y|) *
          Real.log (Real.sqrt (c ^ 2 + (y / 2) ^ 2)))
        (Iio (0 : ℝ)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩

private theorem lowerGammaBoundaryLog_integer_exp_integrable
    {a : ℝ} (ha : 0 < a) (k : ℕ) (R : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryLog (k : ℝ) R y) := by
  have hconstant :
      Integrable
        (fun y : ℝ =>
          ((k : ℝ) * Real.log (Real.pi * R ^ 2)) *
            Real.exp ((-a) * |y|)) :=
    (strip_exp_abs_integrable ha).const_mul
      ((k : ℝ) * Real.log (Real.pi * R ^ 2))
  have hsum :
      Integrable
        (fun y : ℝ =>
          ∑ j ∈ Finset.range k,
            Real.exp ((-a) * |y|) *
              Real.log
                (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2))) := by
    exact integrable_finsetSum (Finset.range k)
      (fun j _ => lower_exp_log_sqrtFactor_integrable ha
        (Nat.cast_nonneg j))
  have hmodel :
      Integrable
        (fun y : ℝ =>
          Real.exp ((-a) * |y|) *
            ((k : ℝ) * Real.log (Real.pi * R ^ 2) -
              ∑ j ∈ Finset.range k,
                Real.log
                  (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)))) := by
    simpa only [mul_sub, Finset.mul_sum, mul_comm] using!
      hconstant.sub hsum
  refine hmodel.congr ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with y hy
  rw [lowerGammaBoundaryLog_integer k R hy]

private theorem lowerStripGammaOuter_integrable_of_exp_integrable
    {ℓ R : ℝ} (hℓ : 0 < ℓ) {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹' Ioo (-ℓ) ℓ)
    (hgamma : Integrable
      (fun y : ℝ =>
        Real.exp (-(Real.pi / (2 * ℓ)) * |y|) *
          lowerGammaBoundaryLog ℓ R y)) :
    Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel ℓ z y *
          (lowerGammaBoundaryLog ℓ R y : ℂ)) := by
  obtain ⟨hangle, hangle'⟩ := stripSchwarzAngle_mem_Ioo hℓ hz
  have hsin :
      0 < Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ)) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangle'
  let a : ℝ := Real.pi / (2 * ℓ)
  let D : ℝ :=
    2 * ℓ * Real.sin (Real.pi * (z.im + ℓ) / (2 * ℓ))
  let Cpos : ℝ := Real.exp (a * z.re) / D
  let Cneg : ℝ := Real.exp (-a * z.re) / D
  have ha : 0 < a := by
    try dsimp [a]
    exact div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)
  change Integrable
    (fun y : ℝ =>
      Real.exp ((-a) * |y|) * lowerGammaBoundaryLog ℓ R y)
    at hgamma
  have hgammaabs :
      Integrable
        (fun y : ℝ =>
          Real.exp ((-a) * |y|) * |lowerGammaBoundaryLog ℓ R y|) := by
    simpa only [neg_mul, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using! hgamma.norm
  have hposfactor (y : ℝ) :
      Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D =
        Cpos * Real.exp ((-a) * y) := by
    have hsplit :
        Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) =
          Real.exp (a * z.re) * Real.exp ((-a) * y) := by
      rw [← Real.exp_add]
      congr 1
      try dsimp [a]
      ring
    rw [hsplit]
    try dsimp [Cpos]
    ring
  have hnegfactor (y : ℝ) :
      Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D =
        Cneg * Real.exp (a * y) := by
    have hsplit :
        Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) =
          Real.exp (-a * z.re) * Real.exp (a * y) := by
      rw [← Real.exp_add]
      congr 1
      try dsimp [a]
      ring
    rw [hsplit]
    try dsimp [Cneg]
    ring
  have hgammaRight :
      ContinuousOn (lowerGammaBoundaryLog ℓ R) (Ioi (0 : ℝ)) :=
    lowerGammaBoundaryLog_continuousOn hℓ R
      (fun y hy => (mem_Ioi.mp hy).ne')
  have hcastRight :
      ContinuousOn
        (fun y : ℝ => (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Ioi (0 : ℝ)) := by
    simpa only [Function.comp_def] using!
      Complex.continuous_ofReal.comp_continuousOn hgammaRight
  have hcontinuousRight :
      ContinuousOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Ioi (0 : ℝ)) :=
    (stripRegularizedHolomorphicPoissonKernel_continuousOn_Ioi
      hℓ hz).mul hcastRight
  have hrightmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Cpos *
            (Real.exp ((-a) * |y|) *
              |lowerGammaBoundaryLog ℓ R y|))
        (Ioi (0 : ℝ)) :=
    hgammaabs.integrableOn.const_mul Cpos
  have hright :
      IntegrableOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Ioi (0 : ℝ)) := by
    apply hrightmajorant.mono'
      (hcontinuousRight.aestronglyMeasurable measurableSet_Ioi)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y *
        (lowerGammaBoundaryLog ℓ R y : ℂ)‖ ≤
        Cpos *
          (Real.exp ((-a) * |y|) *
            |lowerGammaBoundaryLog ℓ R y|)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hbound :=
      norm_stripRegularizedHolomorphicPoissonKernel_of_nonneg
        hℓ hz (mem_Ioi.mp hy).le
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
        Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D
      at hbound
    calc
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ *
          |lowerGammaBoundaryLog ℓ R y| ≤
        (Real.exp (Real.pi * (z.re - y) / (2 * ℓ)) / D) *
          |lowerGammaBoundaryLog ℓ R y| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
      _ = Cpos *
          (Real.exp ((-a) * |y|) *
            |lowerGammaBoundaryLog ℓ R y|) := by
        rw [abs_of_pos (mem_Ioi.mp hy), hposfactor]
        ring
  have hgammaLeft :
      ContinuousOn (lowerGammaBoundaryLog ℓ R) (Iio (0 : ℝ)) :=
    lowerGammaBoundaryLog_continuousOn hℓ R
      (fun y hy => (mem_Iio.mp hy).ne)
  have hcastLeft :
      ContinuousOn
        (fun y : ℝ => (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Iio (0 : ℝ)) := by
    simpa only [Function.comp_def] using!
      Complex.continuous_ofReal.comp_continuousOn hgammaLeft
  have hcontinuousLeft :
      ContinuousOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Iio (0 : ℝ)) :=
    (stripRegularizedHolomorphicPoissonKernel_continuousOn_Iio
      hℓ hz).mul hcastLeft
  have hleftmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Cneg *
            (Real.exp ((-a) * |y|) *
              |lowerGammaBoundaryLog ℓ R y|))
        (Iio (0 : ℝ)) :=
    hgammaabs.integrableOn.const_mul Cneg
  have hleft :
      IntegrableOn
        (fun y : ℝ =>
          stripRegularizedHolomorphicPoissonKernel ℓ z y *
            (lowerGammaBoundaryLog ℓ R y : ℂ))
        (Iio (0 : ℝ)) := by
    apply hleftmajorant.mono'
      (hcontinuousLeft.aestronglyMeasurable measurableSet_Iio)
    filter_upwards [ae_restrict_mem measurableSet_Iio] with y hy
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y *
        (lowerGammaBoundaryLog ℓ R y : ℂ)‖ ≤
        Cneg *
          (Real.exp ((-a) * |y|) *
            |lowerGammaBoundaryLog ℓ R y|)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hbound :=
      norm_stripRegularizedHolomorphicPoissonKernel_of_neg
        hℓ hz (mem_Iio.mp hy)
    change
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ ≤
        Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D
      at hbound
    calc
      ‖stripRegularizedHolomorphicPoissonKernel ℓ z y‖ *
          |lowerGammaBoundaryLog ℓ R y| ≤
        (Real.exp (-(Real.pi * (z.re - y) / (2 * ℓ))) / D) *
          |lowerGammaBoundaryLog ℓ R y| :=
        mul_le_mul_of_nonneg_right hbound (abs_nonneg _)
      _ = Cneg *
          (Real.exp ((-a) * |y|) *
            |lowerGammaBoundaryLog ℓ R y|) := by
        rw [abs_of_neg (mem_Iio.mp hy), hnegfactor]
        simp only [mul_neg, neg_mul, neg_neg]
        ring
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩

private theorem norm_halfIntegerGammaFactor (j : ℕ) (y : ℝ) :
    ‖(j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2‖ =
      Real.sqrt (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp only [one_div, Complex.add_re, Complex.natCast_re, Complex.inv_re, Complex.re_ofNat,
    Complex.normSq_ofNat, div_self_mul_self', Complex.div_ofNat_re, Complex.mul_re,
      Complex.I_re, Complex.ofReal_re,
    zero_mul, Complex.I_im, Complex.ofReal_im, mul_zero, sub_self, zero_div, add_zero,
      Complex.add_im,
    Complex.natCast_im, Complex.inv_im, Complex.im_ofNat, neg_zero, Complex.div_ofNat_im,
      Complex.mul_im, one_mul,
    zero_add]
  ring

private theorem norm_gamma_half_add_imaginary_sq (x : ℝ) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 =
      Real.pi / Real.cosh (Real.pi * x) := by
  let z : ℂ := (1 / 2 : ℂ) + Complex.I * (x : ℂ)
  have harg : 1 - z = starRingEnd ℂ z := by
    try dsimp [z]
    simp only [map_add, map_div₀, Complex.conj_ofReal,
      Complex.conj_I, Complex.conj_ofNat, map_mul, map_one]
    ring
  have hsin :
      Complex.sin ((Real.pi : ℂ) * z) =
        (Real.cosh (Real.pi * x) : ℂ) := by
    have hinput :
        (Real.pi : ℂ) * z =
          (Real.pi / 2 : ℝ) + (Real.pi * x : ℝ) * Complex.I := by
      try dsimp [z]
      push_cast
      ring
    have hsinhalf :
        Complex.sin ((Real.pi / 2 : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_sin, Real.sin_pi_div_two]
      norm_num
    have hcoshalf :
        Complex.cos ((Real.pi / 2 : ℝ) : ℂ) = 0 := by
      rw [← Complex.ofReal_cos, Real.cos_pi_div_two]
      norm_num
    rw [hinput, Complex.sin_add_mul_I, hsinhalf, hcoshalf]
    simp only [one_mul, zero_mul, add_zero]
    exact (Complex.ofReal_cosh (Real.pi * x)).symm
  have href := Complex.Gamma_mul_Gamma_one_sub z
  rw [harg, Complex.Gamma_conj, hsin] at href
  have hnorm :
      Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z) =
        (‖Complex.Gamma z‖ ^ 2 : ℝ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  rw [hnorm] at href
  have hre := congrArg Complex.re href
  change
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2 =
      (((Real.pi : ℝ) : ℂ) /
        (Real.cosh (Real.pi * x) : ℂ)).re at hre
  simpa only [Complex.div_ofReal_re] using! hre

private theorem norm_gamma_imaginary_sq {x : ℝ} (hx : x ≠ 0) :
    ‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2 =
      Real.pi / (x * Real.sinh (Real.pi * x)) := by
  let z : ℂ := Complex.I * (x : ℂ)
  have hz : -z ≠ 0 := by
    try dsimp [z]
    exact neg_ne_zero.mpr
      (mul_ne_zero Complex.I_ne_zero (Complex.ofReal_ne_zero.mpr hx))
  have hrec :
      Complex.Gamma (1 - z) = (-z) * Complex.Gamma (-z) := by
    convert! Complex.Gamma_add_one (-z) hz using 1; ring_nf
  have hconjarg : -z = starRingEnd ℂ z := by
    try dsimp [z]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hconj :
      Complex.Gamma (-z) =
        starRingEnd ℂ (Complex.Gamma z) := by
    rw [hconjarg, Complex.Gamma_conj]
  have hsin :
      Complex.sin ((Real.pi : ℂ) * z) =
        (Real.sinh (Real.pi * x) : ℂ) * Complex.I := by
    have hinput :
        (Real.pi : ℂ) * z =
          ((Real.pi * x : ℝ) : ℂ) * Complex.I := by
      try dsimp [z]
      push_cast
      ring
    rw [hinput, Complex.sin_mul_I, ← Complex.ofReal_sinh]
  have hsinh : Real.sinh (Real.pi * x) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
  have hden : (Real.sinh (Real.pi * x) : ℂ) * Complex.I ≠ 0 :=
    mul_ne_zero (Complex.ofReal_ne_zero.mpr hsinh) Complex.I_ne_zero
  have hprod :
      Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z) =
        (‖Complex.Gamma z‖ ^ 2 : ℝ) := by
    rw [mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  have href := Complex.Gamma_mul_Gamma_one_sub z
  rw [hrec, hconj, hsin] at href
  have hidentity :
      ((‖Complex.Gamma z‖ ^ 2 *
        (x * Real.sinh (Real.pi * x)) : ℝ) : ℂ) =
          (Real.pi : ℂ) := by
    calc
      ((‖Complex.Gamma z‖ ^ 2 *
        (x * Real.sinh (Real.pi * x)) : ℝ) : ℂ) =
          (Complex.Gamma z * starRingEnd ℂ (Complex.Gamma z)) *
            ((x * Real.sinh (Real.pi * x) : ℝ) : ℂ) := by
        rw [hprod]
        push_cast
        rfl
      _ =
          (Complex.Gamma z *
            (-z * starRingEnd ℂ (Complex.Gamma z))) *
              ((Real.sinh (Real.pi * x) : ℂ) * Complex.I) := by
        try dsimp [z]
        rw [Complex.ofReal_mul]
        ring_nf
        simp only [Complex.ofReal_sinh, Complex.ofReal_mul, Complex.I_sq, neg_mul, one_mul, neg_neg]
      _ = ((Real.pi : ℂ) /
          ((Real.sinh (Real.pi * x) : ℂ) * Complex.I)) *
            ((Real.sinh (Real.pi * x) : ℂ) * Complex.I) := by
        rw [href]
      _ = (Real.pi : ℂ) := div_mul_cancel₀ _ hden
  have hmul :
      ‖Complex.Gamma z‖ ^ 2 *
        (x * Real.sinh (Real.pi * x)) = Real.pi := by
    exact_mod_cast hidentity
  exact (eq_div_iff (mul_ne_zero hx hsinh)).2 hmul

private theorem halfIntegerGammaFactor_ne_zero (j : ℕ) (y : ℝ) :
    (j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2 ≠ 0 := by
  intro hz
  have hre := congrArg Complex.re hz
  norm_num at hre
  have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  linarith

private theorem lowerGammaBoundaryLog_halfInteger_factorized
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y =
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (Real.log ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖) := by
  have himaginary :
      ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (gamma_imaginary_ne_zero hy)
  have hreflection :
      ‖Complex.Gamma (-Complex.I * (y : ℂ) / 2)‖ =
        ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ := by
    apply (div_eq_one_iff_eq himaginary).mp
    rw [norm_gamma_neg_imaginary, div_self himaginary]
  have hbase :
      Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
  have hbasenorm :
      ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hbase
  have hproduct :
      (∏ j ∈ Finset.range k,
        ((j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)) ≠ 0 := by
    exact Finset.prod_ne_zero_iff.mpr
      (fun j _ => halfIntegerGammaFactor_ne_zero j y)
  have hproductnorm :
      ‖∏ j ∈ Finset.range k,
        ((j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr hproduct
  have hlogproduct :
      Real.log
        ‖∏ j ∈ Finset.range k,
          ((j : ℂ) + (1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖ =
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
    rw [Complex.norm_prod]
    rw [Real.log_prod]
    · apply Finset.sum_congr rfl
      intro j _
      rw [norm_halfIntegerGammaFactor]
    · intro j _
      exact norm_ne_zero_iff.mpr (halfIntegerGammaFactor_ne_zero j y)
  have hcast :
      (((k : ℝ) + 1 / 2 : ℝ) : ℂ) =
        (k : ℂ) + (1 / 2 : ℂ) := by
    push_cast
    rfl
  unfold lowerGammaBoundaryLog
  rw [hcast, half_integer_gamma_product k y, norm_mul,
    Real.log_mul hbasenorm hproductnorm,
    hreflection, hlogproduct]
  ring

private noncomputable def lowerCoth (x : ℝ) : ℝ :=
  Real.cosh x / Real.sinh x

private theorem lowerCoth_pos {x : ℝ} (hx : 0 < x) :
    0 < lowerCoth x := by
  unfold lowerCoth
  exact div_pos (Real.cosh_pos x) (Real.sinh_pos_iff.mpr hx)

private theorem lowerCoth_one_le {x : ℝ} (hx : 0 < x) :
    1 ≤ lowerCoth x := by
  have hsinh : 0 < Real.sinh x := Real.sinh_pos_iff.mpr hx
  unfold lowerCoth
  apply (le_div_iff₀ hsinh).2
  rw [one_mul, Real.sinh_eq, Real.cosh_eq]
  linarith [Real.exp_pos (-x)]

private theorem lowerCoth_log_nonneg {x : ℝ} (hx : 0 < x) :
    0 ≤ Real.log (lowerCoth x) :=
  Real.log_nonneg (lowerCoth_one_le hx)

private theorem lowerCoth_hasDerivAt {x : ℝ} (hx : 0 < x) :
    HasDerivAt lowerCoth
      (-(Real.sinh x)⁻¹ ^ 2) x := by
  have hsinh : Real.sinh x ≠ 0 :=
    (Real.sinh_pos_iff.mpr hx).ne'
  have hderiv :=
    (Real.hasDerivAt_cosh x).div
      (Real.hasDerivAt_sinh x) hsinh
  unfold lowerCoth
  convert! hderiv using 1
  rw [div_eq_mul_inv]
  have hidentity := Real.cosh_sq_sub_sinh_sq x
  field_simp [hsinh]
  linarith

private theorem lowerCoth_antitoneOn :
    AntitoneOn lowerCoth (Ioi (0 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ioi 0)
  · intro x hx
    exact (lowerCoth_hasDerivAt hx).continuousAt.continuousWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using! hx
    exact (lowerCoth_hasDerivAt hx').differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : 0 < x := by simpa only [interior_Ioi, mem_Ioi] using! hx
    rw [(lowerCoth_hasDerivAt hx').deriv]
    exact neg_nonpos.mpr (sq_nonneg _)

private theorem lowerCoth_log_antitoneOn :
    AntitoneOn (fun x : ℝ => Real.log (lowerCoth x))
      (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  exact Real.log_le_log (lowerCoth_pos hy)
    (lowerCoth_antitoneOn hx hy hxy)

private theorem lower_cosh_le_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x ≤ Real.exp x := by
  have hnegative : Real.exp (-x) ≤ Real.exp x :=
    Real.exp_le_exp.mpr (by linarith)
  rw [Real.cosh_eq]
  linarith

private theorem lower_sinh_le_exp (x : ℝ) :
    Real.sinh x ≤ Real.exp x := by
  have hpositive := Real.exp_pos (-x)
  have hpositive' := Real.exp_pos x
  rw [Real.sinh_eq]
  linarith

private theorem lower_abs_log_cosh_le {x : ℝ} (hx : 0 ≤ x) :
    |Real.log (Real.cosh x)| ≤ x := by
  rw [abs_of_nonneg (Real.log_nonneg (Real.one_le_cosh x))]
  have hlog := Real.log_le_log
    (Real.cosh_pos x) (lower_cosh_le_exp hx)
  simpa only [ge_iff_le, Real.log_exp] using! hlog

private theorem lower_abs_log_sinh_le {x : ℝ} (hx : 0 < x) :
    |Real.log (Real.sinh x)| ≤ x + |Real.log x| := by
  have hlower : x ≤ Real.sinh x :=
    Real.self_le_sinh_iff.mpr hx.le
  have hsinh : 0 < Real.sinh x := hx.trans_le hlower
  by_cases hlarge : 1 ≤ Real.sinh x
  · rw [abs_of_nonneg (Real.log_nonneg hlarge)]
    have hlog := Real.log_le_log hsinh
      (lower_sinh_le_exp x)
    have habs := abs_nonneg (Real.log x)
    rw [Real.log_exp] at hlog
    linarith
  · rw [abs_of_nonpos
      (Real.log_nonpos hsinh.le (le_of_not_ge hlarge))]
    have hlog := Real.log_le_log hx hlower
    have habs := neg_le_abs (Real.log x)
    linarith

private theorem lower_abs_log_coth_div_le {x : ℝ} (hx : 0 < x) :
    |Real.log (lowerCoth (Real.pi * x) / x)| ≤
      2 * (Real.pi * x) +
        |Real.log Real.pi| + 2 * |Real.log x| := by
  have ht : 0 < Real.pi * x := mul_pos Real.pi_pos hx
  have hsinh : Real.sinh (Real.pi * x) ≠ 0 :=
    Real.sinh_ne_zero.mpr ht.ne'
  have hcosh : Real.cosh (Real.pi * x) ≠ 0 :=
    (Real.cosh_pos _).ne'
  have hlogpi :
      |Real.log (Real.pi * x)| ≤
        |Real.log Real.pi| + |Real.log x| := by
    rw [Real.log_mul Real.pi_ne_zero hx.ne']
    simpa only [sub_neg_eq_add, abs_neg] using!
      (abs_sub (Real.log Real.pi) (-(Real.log x)))
  have hcoshbound := lower_abs_log_cosh_le ht.le
  have hsinhbound := lower_abs_log_sinh_le ht
  unfold lowerCoth
  rw [Real.log_div (div_ne_zero hcosh hsinh) hx.ne',
    Real.log_div hcosh hsinh]
  calc
    |(Real.log (Real.cosh (Real.pi * x)) -
        Real.log (Real.sinh (Real.pi * x))) - Real.log x| ≤
      (|Real.log (Real.cosh (Real.pi * x))| +
        |Real.log (Real.sinh (Real.pi * x))|) +
          |Real.log x| := by
      have hfirst :=
        abs_sub
          (Real.log (Real.cosh (Real.pi * x)))
          (Real.log (Real.sinh (Real.pi * x)))
      have hsecond :=
        abs_sub
          (Real.log (Real.cosh (Real.pi * x)) -
            Real.log (Real.sinh (Real.pi * x)))
          (Real.log x)
      linarith
    _ ≤ 2 * (Real.pi * x) +
        |Real.log Real.pi| + 2 * |Real.log x| := by
      linarith

private theorem lowerCoth_sub_one_eq
    {x : ℝ} (hx : 0 < x) :
    lowerCoth x - 1 = Real.exp (-x) / Real.sinh x := by
  have hsinh : Real.sinh x ≠ 0 :=
    (Real.sinh_pos_iff.mpr hx).ne'
  unfold lowerCoth
  field_simp [hsinh]
  rw [Real.cosh_eq, Real.sinh_eq]
  ring

private theorem lower_sinh_ge_exp_quarter
    {x : ℝ} (hx : 1 ≤ x) :
    Real.exp x / 4 ≤ Real.sinh x := by
  have hbig : 2 ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x]
  have hsmall : Real.exp (-x) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by linarith)
  rw [Real.sinh_eq]
  linarith

private theorem lowerCoth_log_le_four_exp_neg_two
    {x : ℝ} (hx : 1 ≤ x) :
    Real.log (lowerCoth x) ≤
      4 * Real.exp (-2 * x) := by
  have hxpos : 0 < x := by linarith
  have hsinh : 0 < Real.sinh x :=
    Real.sinh_pos_iff.mpr hxpos
  calc
    Real.log (lowerCoth x) ≤ lowerCoth x - 1 :=
      Real.log_le_sub_one_of_pos (lowerCoth_pos hxpos)
    _ = Real.exp (-x) / Real.sinh x :=
      lowerCoth_sub_one_eq hxpos
    _ ≤ Real.exp (-x) / (Real.exp x / 4) :=
      div_le_div_of_nonneg_left (Real.exp_pos _).le
        (by positivity) (lower_sinh_ge_exp_quarter hx)
    _ = 4 * Real.exp (-2 * x) := by
      rw [show -2 * x = -x - x by ring,
        Real.exp_sub]
      field_simp [Real.exp_ne_zero x]

private theorem lowerCoth_log_small_abs_bound
    {y : ℝ} (hy : y ≠ 0) (hsmall : |y| ≤ 1) :
    Real.log (lowerCoth (Real.pi * |y| / 2)) ≤
      Real.pi + |Real.log Real.pi| +
        3 * (|Real.log (|y|)| + |Real.log (2 : ℝ)|) := by
  have hu : 0 < |y| / 2 := by positivity
  have hpiu : 0 < Real.pi * (|y| / 2) :=
    mul_pos Real.pi_pos hu
  have hcoth : 0 < lowerCoth (Real.pi * (|y| / 2)) :=
    lowerCoth_pos hpiu
  have hloghalf :
      |Real.log (|y| / 2)| ≤
        |Real.log (|y|)| + |Real.log (2 : ℝ)| := by
    rw [Real.log_div (abs_ne_zero.mpr hy) (by norm_num)]
    exact abs_sub _ _
  have hbase := lower_abs_log_coth_div_le hu
  have hdecomp :
      Real.log (lowerCoth (Real.pi * (|y| / 2))) =
        Real.log
          (lowerCoth (Real.pi * (|y| / 2)) / (|y| / 2)) +
            Real.log (|y| / 2) := by
    rw [Real.log_div hcoth.ne' hu.ne']
    ring
  rw [show Real.pi * |y| / 2 =
    Real.pi * (|y| / 2) by ring]
  rw [hdecomp]
  have hlogdiv := le_abs_self
    (Real.log (lowerCoth (Real.pi * (|y| / 2)) / (|y| / 2)))
  have hlogu := le_abs_self (Real.log (|y| / 2))
  have hpibound : 2 * (Real.pi * (|y| / 2)) ≤ Real.pi := by
    linarith [mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hsmall)]
  linarith

private theorem lowerCoth_log_abs_integrable :
    Integrable (fun y : ℝ =>
      Real.log (lowerCoth (Real.pi * |y| / 2))) := by
  let A : ℝ :=
    Real.pi + |Real.log Real.pi| + 3 * |Real.log (2 : ℝ)|
  have hA : 0 ≤ A := by
    try dsimp [A]
    positivity
  have hbase := strip_exp_abs_integrable
    (by norm_num : 0 < (1 : ℝ))
  have hlog := strip_exp_abs_log_abs_integrable
    (by norm_num : 0 < (1 : ℝ))
  have hnear : Integrable (fun y : ℝ =>
      A * Real.exp ((-1 : ℝ) * |y|) +
        3 * (Real.exp ((-1 : ℝ) * |y|) *
          |Real.log (|y|)|)) :=
    (hbase.const_mul A).add (hlog.const_mul 3)
  have hfar : Integrable (fun y : ℝ =>
      4 * Real.exp ((-Real.pi) * |y|)) :=
    (strip_exp_abs_integrable Real.pi_pos).const_mul 4
  have hmajor : Integrable (fun y : ℝ =>
      Real.exp 1 *
        (A * Real.exp ((-1 : ℝ) * |y|) +
          3 * (Real.exp ((-1 : ℝ) * |y|) *
            |Real.log (|y|)|)) +
        4 * Real.exp ((-Real.pi) * |y|)) :=
    (hnear.const_mul (Real.exp 1)).add hfar
  apply hmajor.mono'
  · have harg : Measurable (fun y : ℝ => Real.pi * |y| / 2) := by
      fun_prop
    have hcoth : Measurable (fun y : ℝ =>
        lowerCoth (Real.pi * |y| / 2)) := by
      unfold lowerCoth
      exact
        (Real.continuous_cosh.measurable.comp harg).div
          (Real.continuous_sinh.measurable.comp harg)
    exact hcoth.log.aestronglyMeasurable
  · filter_upwards [] with y
    by_cases hy : y = 0
    · subst y
      simp only [lowerCoth, abs_zero, mul_zero, zero_div, Real.cosh_zero, Real.sinh_zero,
        div_zero, Real.log_zero,
        norm_zero, Real.exp_zero, mul_one, add_zero, A]
      positivity
    · have hlognonneg :
          0 ≤ Real.log (lowerCoth (Real.pi * |y| / 2)) :=
        lowerCoth_log_nonneg (by positivity)
      rw [Real.norm_eq_abs, abs_of_nonneg hlognonneg]
      have hfar_nonneg : 0 ≤
          4 * Real.exp ((-Real.pi) * |y|) := by positivity
      have hnear_nonneg : 0 ≤
          Real.exp 1 *
            (A * Real.exp ((-1 : ℝ) * |y|) +
              3 * (Real.exp ((-1 : ℝ) * |y|) *
                |Real.log (|y|)|)) := by positivity
      by_cases hsmall : |y| ≤ 1
      · have hsmallbound :=
          lowerCoth_log_small_abs_bound hy hsmall
        have hfactor :
            1 ≤ Real.exp 1 * Real.exp ((-1 : ℝ) * |y|) := by
          rw [← Real.exp_add]
          exact (Real.one_le_exp_iff).2 (by linarith)
        have hpolynonneg : 0 ≤ A + 3 * |Real.log (|y|)| := by
          positivity
        have hproduct :
            A + 3 * |Real.log (|y|)| ≤
              (Real.exp 1 * Real.exp ((-1 : ℝ) * |y|)) *
                (A + 3 * |Real.log (|y|)|) := by
          linarith [mul_nonneg
            (sub_nonneg.mpr hfactor) hpolynonneg]
        have hrewrite :
            (Real.exp 1 * Real.exp ((-1 : ℝ) * |y|)) *
                (A + 3 * |Real.log (|y|)|) =
              Real.exp 1 *
                (A * Real.exp ((-1 : ℝ) * |y|) +
                  3 * (Real.exp ((-1 : ℝ) * |y|) *
                    |Real.log (|y|)|)) := by
          ring
        try dsimp [A] at hsmallbound ⊢
        try dsimp [A] at hproduct hrewrite
        linarith
      · have hylarge : 1 < |y| := lt_of_not_ge hsmall
        have harg : 1 ≤ Real.pi * |y| / 2 := by
          linarith [Real.pi_gt_three,
            mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 2)
              (sub_nonneg.mpr hylarge.le)]
        have hbound := lowerCoth_log_le_four_exp_neg_two harg
        have hexp :
            Real.exp (-2 * (Real.pi * |y| / 2)) =
              Real.exp ((-Real.pi) * |y|) := by
          congr 1
          ring
        rw [hexp] at hbound
        linarith

private theorem lower_exp_log_coth_div_integrableOn_Ioi
    {a : ℝ} (ha : 0 < a) :
    IntegrableOn
      (fun y : ℝ =>
        Real.exp ((-a) * y) *
          Real.log (lowerCoth (Real.pi * y / 2) / (y / 2)))
      (Ioi (0 : ℝ)) := by
  have hexponential :
      IntegrableOn (fun y : ℝ => Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) :=
    integrableOn_exp_mul_Ioi (neg_lt_zero.mpr ha) 0
  have hlinear :
      IntegrableOn
        (fun y : ℝ => y * Real.exp ((-a) * y))
        (Ioi (0 : ℝ)) := by
    simpa only [neg_mul, Real.rpow_one] using!
      (integrableOn_rpow_mul_exp_neg_mul_rpow
        (p := (1 : ℝ)) (s := (1 : ℝ)) (b := a)
        (by norm_num) (by norm_num) ha)
  have hmajorant :
      IntegrableOn
        (fun y : ℝ =>
          Real.pi * (y * Real.exp ((-a) * y)) +
            |Real.log Real.pi| * Real.exp ((-a) * y) +
            2 * (Real.exp ((-a) * y) * |Real.log (y / 2)|))
        (Ioi (0 : ℝ)) :=
    ((hlinear.const_mul Real.pi).add
      (hexponential.const_mul |Real.log Real.pi|)).add
        ((lower_exp_abs_log_div_two_integrableOn_Ioi ha).const_mul 2)
  have hargument :
      ContinuousOn
        (fun y : ℝ =>
          lowerCoth (Real.pi * y / 2) / (y / 2))
        (Ioi (0 : ℝ)) := by
    unfold lowerCoth
    apply ContinuousOn.div
    · apply ContinuousOn.div
      · exact (Real.continuous_cosh.comp
          ((continuous_id.const_mul Real.pi).div_const 2)).continuousOn
      · exact (Real.continuous_sinh.comp
          ((continuous_id.const_mul Real.pi).div_const 2)).continuousOn
      · intro y hy
        apply Real.sinh_ne_zero.mpr
        have hypos := mem_Ioi.mp hy
        positivity
    · exact (continuous_id.div_const 2).continuousOn
    · intro y hy
      have hypos := mem_Ioi.mp hy
      positivity
  have hargument_nonzero :
      ∀ y ∈ Ioi (0 : ℝ),
        lowerCoth (Real.pi * y / 2) / (y / 2) ≠ 0 := by
    intro y hy
    have hypos := mem_Ioi.mp hy
    unfold lowerCoth
    apply div_ne_zero
    · apply div_ne_zero
      · exact (Real.cosh_pos _).ne'
      · apply Real.sinh_ne_zero.mpr
        positivity
    · positivity
  have hcontinuous :
      ContinuousOn
        (fun y : ℝ =>
          Real.exp ((-a) * y) *
            Real.log (lowerCoth (Real.pi * y / 2) / (y / 2)))
        (Ioi (0 : ℝ)) := by
    apply ContinuousOn.mul
    · fun_prop
    · exact hargument.log hargument_nonzero
  apply hmajorant.mono'
    (hcontinuous.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
  have hypos := mem_Ioi.mp hy
  have hlog :
      |Real.log (lowerCoth (Real.pi * y / 2) / (y / 2))| ≤
        Real.pi * y + |Real.log Real.pi| +
          2 * |Real.log (y / 2)| := by
    convert! lower_abs_log_coth_div_le (half_pos hypos) using 1 <;>
      ring_nf
  change
    ‖Real.exp ((-a) * y) *
      Real.log (lowerCoth (Real.pi * y / 2) / (y / 2))‖ ≤ _
  rw [Real.norm_eq_abs, abs_mul,
    abs_of_pos (Real.exp_pos _)]
  calc
    Real.exp ((-a) * y) *
        |Real.log (lowerCoth (Real.pi * y / 2) / (y / 2))| ≤
      Real.exp ((-a) * y) *
        (Real.pi * y + |Real.log Real.pi| +
          2 * |Real.log (y / 2)|) :=
      mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = Real.pi * (y * Real.exp ((-a) * y)) +
          |Real.log Real.pi| * Real.exp ((-a) * y) +
          2 * (Real.exp ((-a) * y) * |Real.log (y / 2)|) := by
      ring

private theorem lower_exp_log_coth_div_integrable
    {a : ℝ} (ha : 0 < a) :
    Integrable
      (fun y : ℝ =>
        Real.exp ((-a) * |y|) *
          Real.log
            (lowerCoth (Real.pi * |y| / 2) / (|y| / 2))) := by
  have hright :
      IntegrableOn
        (fun y : ℝ =>
          Real.exp ((-a) * |y|) *
            Real.log
              (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)))
        (Ioi (0 : ℝ)) := by
    refine (lower_exp_log_coth_div_integrableOn_Ioi ha).congr_fun
      ?_ measurableSet_Ioi
    intro y hy
    try dsimp
    rw [abs_of_pos (mem_Ioi.mp hy)]
  have hreflected :
      IntegrableOn
        ((fun y : ℝ =>
          Real.exp ((-a) * |y|) *
            Real.log
              (lowerCoth (Real.pi * |y| / 2) / (|y| / 2))) ∘
          (fun y : ℝ => -y))
        ((fun y : ℝ => -y) ⁻¹' Iio (0 : ℝ)) := by
    simpa only [neg_mul, Function.comp_def, abs_neg, neg_preimage, neg_Iio, neg_zero] using! hright
  have hleft :
      IntegrableOn
        (fun y : ℝ =>
          Real.exp ((-a) * |y|) *
            Real.log
              (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)))
        (Iio (0 : ℝ)) :=
    ((Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding).mp hreflected
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ),
    integrableOn_union, integrableOn_Ici_iff_integrableOn_Ioi]
  exact ⟨hleft, hright⟩

private theorem gamma_log_coth_ratio {x : ℝ} (hx : x ≠ 0) :
    Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ -
        Real.log
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ =
      (1 / 2 : ℝ) *
        Real.log (lowerCoth (Real.pi * |x|) / |x|) := by
  have hsinh : Real.sinh (Real.pi * x) ≠ 0 :=
    Real.sinh_ne_zero.mpr (mul_ne_zero Real.pi_ne_zero hx)
  have hden : x * Real.sinh (Real.pi * x) ≠ 0 :=
    mul_ne_zero hx hsinh
  have hcosh : Real.cosh (Real.pi * x) ≠ 0 :=
    (Real.cosh_pos _).ne'
  have himaginary :
      2 * Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ =
        Real.log Real.pi -
          Real.log (x * Real.sinh (Real.pi * x)) := by
    calc
      2 * Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ =
          Real.log (‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2) := by
        rw [Real.log_pow]
        norm_num
      _ = Real.log (Real.pi / (x * Real.sinh (Real.pi * x))) := by
        rw [norm_gamma_imaginary_sq hx]
      _ = Real.log Real.pi -
          Real.log (x * Real.sinh (Real.pi * x)) :=
        Real.log_div Real.pi_ne_zero hden
  have hhalf :
      2 * Real.log
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ =
        Real.log Real.pi - Real.log (Real.cosh (Real.pi * x)) := by
    calc
      2 * Real.log
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ =
          Real.log
            (‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ ^ 2) := by
        rw [Real.log_pow]
        norm_num
      _ = Real.log (Real.pi / Real.cosh (Real.pi * x)) := by
        rw [norm_gamma_half_add_imaginary_sq]
      _ = Real.log Real.pi - Real.log (Real.cosh (Real.pi * x)) :=
        Real.log_div Real.pi_ne_zero hcosh
  have hcoth :
      lowerCoth (Real.pi * |x|) / |x| =
        Real.cosh (Real.pi * x) /
          (x * Real.sinh (Real.pi * x)) := by
    rcases lt_or_gt_of_ne hx with hnegative | hpositive
    · rw [abs_of_neg hnegative]
      unfold lowerCoth
      have harg : Real.pi * -x = -(Real.pi * x) := by ring
      rw [harg, Real.cosh_neg, Real.sinh_neg]
      field_simp [hx, hsinh]
    · rw [abs_of_pos hpositive]
      unfold lowerCoth
      field_simp [hx, hsinh]
  have hlogcoth :
      Real.log (Real.cosh (Real.pi * x)) -
          Real.log (x * Real.sinh (Real.pi * x)) =
        Real.log (lowerCoth (Real.pi * |x|) / |x|) := by
    rw [hcoth, Real.log_div hcosh hden]
  calc
    Real.log ‖Complex.Gamma (Complex.I * (x : ℂ))‖ -
        Real.log
          ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (x : ℂ))‖ =
      (1 / 2 : ℝ) *
        ((Real.log Real.pi -
            Real.log (x * Real.sinh (Real.pi * x))) -
          (Real.log Real.pi - Real.log (Real.cosh (Real.pi * x)))) := by
        linarith
    _ = (1 / 2 : ℝ) *
          (Real.log (Real.cosh (Real.pi * x)) -
            Real.log (x * Real.sinh (Real.pi * x))) := by
        ring
    _ = (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |x|) / |x|) := by
        rw [hlogcoth]

private theorem lowerGammaBoundaryLog_halfInteger
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y =
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (1 / 2 : ℝ) *
          Real.log
            (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)) := by
  calc
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y =
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (Real.log ‖Complex.Gamma (Complex.I * (y : ℂ) / 2)‖ -
          Real.log
            ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (y : ℂ) / 2)‖) :=
      lowerGammaBoundaryLog_halfInteger_factorized k R hy
    _ = ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (1 / 2 : ℝ) *
          Real.log
            (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)) := by
      congr 1
      simpa only [mul_div_assoc, one_div, Complex.ofReal_div, Complex.ofReal_ofNat, abs_div,
        Nat.abs_ofNat] using!
        (gamma_log_coth_ratio
          (x := y / 2) (div_ne_zero hy (by norm_num)))

private theorem lowerGammaBoundaryLog_halfInteger_log_tail
    (k : ℕ) {R y : ℝ} (hR : 0 < R) (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y ≤
      ((k : ℝ) + 1 / 2) * Real.log
        (2 * Real.pi * R ^ 2 / |y|) +
      (1 / 2 : ℝ) *
        Real.log (lowerCoth (Real.pi * |y| / 2)) := by
  have hyhalf : 0 < |y| / 2 := by positivity
  have hsum :
      (k : ℝ) * Real.log (|y| / 2) ≤
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt
              (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
    calc
      (k : ℝ) * Real.log (|y| / 2) =
          ∑ j ∈ Finset.range k,
            Real.log (|y| / 2) := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt
              (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
        apply Finset.sum_le_sum
        intro j hj
        exact Real.log_le_log hyhalf
          (lower_sqrtFactor_ge_abs_half
            ((j : ℝ) + 1 / 2) y)
  have hlogratio :
      Real.log (Real.pi * R ^ 2) - Real.log (|y| / 2) =
        Real.log (2 * Real.pi * R ^ 2 / |y|) := by
    rw [← Real.log_div
      (mul_ne_zero Real.pi_ne_zero (pow_ne_zero 2 hR.ne'))
      hyhalf.ne']
    congr 1
    field_simp [abs_ne_zero.mpr hy]
  have hcoth : 0 < lowerCoth (Real.pi * |y| / 2) := by
    apply lowerCoth_pos
    positivity
  have hlogcoth :
      Real.log
        (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)) =
      Real.log (lowerCoth (Real.pi * |y| / 2)) -
        Real.log (|y| / 2) :=
    Real.log_div hcoth.ne' hyhalf.ne'
  rw [lowerGammaBoundaryLog_halfInteger k R hy, hlogcoth]
  calc
    ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        ∑ j ∈ Finset.range k,
          Real.log
            (Real.sqrt
              (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) +
        (1 / 2 : ℝ) *
          (Real.log (lowerCoth (Real.pi * |y| / 2)) -
            Real.log (|y| / 2)) ≤
      ((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2) -
        (k : ℝ) * Real.log (|y| / 2) +
        (1 / 2 : ℝ) *
          (Real.log (lowerCoth (Real.pi * |y| / 2)) -
            Real.log (|y| / 2)) := by
      linarith
    _ = ((k : ℝ) + 1 / 2) *
          (Real.log (Real.pi * R ^ 2) -
            Real.log (|y| / 2)) +
          (1 / 2 : ℝ) *
            Real.log (lowerCoth (Real.pi * |y| / 2)) := by
      ring
    _ = ((k : ℝ) + 1 / 2) * Real.log
          (2 * Real.pi * R ^ 2 / |y|) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |y| / 2)) := by
      rw [hlogratio]

private theorem lowerGammaBoundaryLog_dimension_log_tail
    {d : ℕ} (_hd : 0 < d) {R y : ℝ}
    (hR : 0 < R) (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R y ≤
      ((d : ℝ) / 2) * Real.log
        (2 * Real.pi * R ^ 2 / |y|) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |y| / 2)) := by
  have hcoth : 0 ≤ Real.log
      (lowerCoth (Real.pi * |y| / 2)) := by
    apply lowerCoth_log_nonneg
    positivity
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    have htail := lowerGammaBoundaryLog_integer_log_tail k hR hy
    linarith
  · have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_halfInteger_log_tail k hR hy

private theorem lowerGammaBoundaryLog_dimension_scaled_log_tail
    {d : ℕ} (hd : 0 < d) {c Y : ℝ}
    (hc : 0 < c) (hY : Y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤
      ((d : ℝ) / 2) *
        Real.log (4 * Real.pi * c ^ 2 / |Y|) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth
            (Real.pi * |((d : ℝ) / 2) * Y| / 2)) := by
  have hdreal : 0 < (d : ℝ) := Nat.cast_pos.mpr hd
  have hℓ : 0 < (d : ℝ) / 2 := half_pos hdreal
  have hR : 0 < c * Real.sqrt d :=
    mul_pos hc (Real.sqrt_pos.2 hdreal)
  have hy : ((d : ℝ) / 2) * Y ≠ 0 :=
    mul_ne_zero hℓ.ne' hY
  have htail := lowerGammaBoundaryLog_dimension_log_tail
    hd hR hy
  have hratio :
      2 * Real.pi * (c * Real.sqrt d) ^ 2 /
        |((d : ℝ) / 2) * Y| =
          4 * Real.pi * c ^ 2 / |Y| := by
    rw [abs_mul, abs_of_pos hℓ, mul_pow,
      Real.sq_sqrt hdreal.le]
    field_simp [hℓ.ne', abs_ne_zero.mpr hY, hdreal.ne']
    ring
  rw [hratio] at htail
  exact htail

private theorem lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
    {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hY : Y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤
      ((d : ℝ) / 2) *
        Real.log (4 * Real.pi * c ^ 2 / |Y|) +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2)) := by
  have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
  have hℓ : 1 ≤ (d : ℝ) / 2 := by
    exact (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      (by exact_mod_cast hd)
  have ht : 0 < Real.pi * |Y| / 2 := by positivity
  have ht' : 0 < Real.pi * |((d : ℝ) / 2) * Y| / 2 := by
    positivity
  have hcompare :
      Real.pi * |Y| / 2 ≤
        Real.pi * |((d : ℝ) / 2) * Y| / 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ (d : ℝ) / 2)]
    linarith [mul_nonneg Real.pi_pos.le (abs_nonneg Y),
      mul_nonneg (sub_nonneg.mpr hℓ)
        (mul_nonneg Real.pi_pos.le (abs_nonneg Y))]
  have hcoth := lowerCoth_log_antitoneOn ht ht' hcompare
  have htail := lowerGammaBoundaryLog_dimension_scaled_log_tail
    hdpos hc hY
  linarith

private theorem lower_positiveLogRatio_integrable
    {A : ℝ} (hA : 0 < A) :
    Integrable (fun y : ℝ =>
      max (Real.log (A / |y|)) 0) := by
  let B : ℝ := max 1 A
  have hB : 0 ≤ B := le_trans (by norm_num) (le_max_left 1 A)
  have hbase := strip_exp_abs_integrable
    (by norm_num : 0 < (1 : ℝ))
  have hlog := strip_exp_abs_log_abs_integrable
    (by norm_num : 0 < (1 : ℝ))
  have hnear : Integrable (fun y : ℝ =>
      |Real.log A| * Real.exp ((-1 : ℝ) * |y|) +
        Real.exp ((-1 : ℝ) * |y|) *
          |Real.log (|y|)|) :=
    (hbase.const_mul |Real.log A|).add hlog
  have hmajor : Integrable (fun y : ℝ =>
      Real.exp B *
        (|Real.log A| * Real.exp ((-1 : ℝ) * |y|) +
          Real.exp ((-1 : ℝ) * |y|) *
            |Real.log (|y|)|)) :=
    hnear.const_mul (Real.exp B)
  apply hmajor.mono'
  · have harg : Measurable (fun y : ℝ => A / |y|) := by
      fun_prop
    exact (harg.log.max measurable_const).aestronglyMeasurable
  · filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_max_right _ _)]
    by_cases hy : y = 0
    · subst y
      simp only [abs_zero, div_zero, Real.log_zero, max_self, mul_zero, Real.exp_zero, mul_one,
        add_zero]
      positivity
    · by_cases hsmall : |y| ≤ B
      · have habslog :
            Real.log (A / |y|) ≤
              |Real.log A| + |Real.log (|y|)| := by
          rw [Real.log_div hA.ne' (abs_ne_zero.mpr hy)]
          linarith [le_abs_self (Real.log A),
            neg_le_abs (Real.log (|y|))]
        have hpoly : 0 ≤
            |Real.log A| + |Real.log (|y|)| := by positivity
        have hmax :
            max (Real.log (A / |y|)) 0 ≤
              |Real.log A| + |Real.log (|y|)| :=
          max_le habslog hpoly
        have hfactor :
            1 ≤ Real.exp B * Real.exp ((-1 : ℝ) * |y|) := by
          rw [← Real.exp_add]
          exact (Real.one_le_exp_iff).2 (by linarith)
        have hproduct :
            |Real.log A| + |Real.log (|y|)| ≤
              (Real.exp B * Real.exp ((-1 : ℝ) * |y|)) *
                (|Real.log A| + |Real.log (|y|)|) := by
          linarith [mul_nonneg (sub_nonneg.mpr hfactor) hpoly]
        calc
          max (Real.log (A / |y|)) 0 ≤
              |Real.log A| + |Real.log (|y|)| := hmax
          _ ≤ (Real.exp B * Real.exp ((-1 : ℝ) * |y|)) *
                (|Real.log A| + |Real.log (|y|)|) := hproduct
          _ = Real.exp B *
              (|Real.log A| * Real.exp ((-1 : ℝ) * |y|) +
                Real.exp ((-1 : ℝ) * |y|) *
                  |Real.log (|y|)|) := by ring
      · have hylarge : B < |y| := lt_of_not_ge hsmall
        have hyle : A ≤ |y| :=
          le_trans (le_max_right 1 A) hylarge.le
        have hratio : A / |y| ≤ 1 :=
          (div_le_one (abs_pos.mpr hy)).2 hyle
        have hlognonpos : Real.log (A / |y|) ≤ 0 :=
          Real.log_nonpos
            (div_nonneg hA.le (abs_nonneg y)) hratio
        rw [max_eq_right hlognonpos]
        positivity

private noncomputable def lowerGammaScaledPositivePart
    (d : ℕ) (c Y : ℝ) : ℝ :=
  max
    (lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) 0

private theorem lowerGammaScaledPositivePart_le
    {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c) (hY : Y ≠ 0) :
    lowerGammaScaledPositivePart d c Y ≤
      ((d : ℝ) / 2) *
        max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2)) := by
  have hℓ : 0 ≤ (d : ℝ) / 2 := by positivity
  have hcoth : 0 ≤ Real.log
      (lowerCoth (Real.pi * |Y| / 2)) :=
    lowerCoth_log_nonneg (by positivity)
  have hlog :
      ((d : ℝ) / 2) *
          Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
        ((d : ℝ) / 2) *
          max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) hℓ
  have htail := lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
    hd hc hY
  unfold lowerGammaScaledPositivePart
  apply max_le
  · linarith
  · positivity

private theorem lowerGammaScaledPositivePart_integrable
    {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    Integrable (lowerGammaScaledPositivePart d c) := by
  have hA : 0 < 4 * Real.pi * c ^ 2 := by positivity
  have hpositive := lower_positiveLogRatio_integrable hA
  have hmajor : Integrable (fun Y : ℝ =>
      ((d : ℝ) / 2) *
        max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2))) :=
    (hpositive.const_mul ((d : ℝ) / 2)).add
      (lowerCoth_log_abs_integrable.const_mul (1 / 2 : ℝ))
  apply hmajor.mono'
  · have hdpos : 0 < d := lt_of_lt_of_le (by norm_num) hd
    have hℓ : 0 < (d : ℝ) / 2 :=
      half_pos (Nat.cast_pos.mpr hdpos)
    have harg : Measurable (fun Y : ℝ => ((d : ℝ) / 2) * Y) := by
      fun_prop
    have hgamma : Measurable (fun Y : ℝ =>
        lowerGammaBoundaryLog ((d : ℝ) / 2)
          (c * Real.sqrt d) (((d : ℝ) / 2) * Y)) :=
      (lowerGammaBoundaryLog_measurable hℓ
        (c * Real.sqrt d)).comp harg
    exact (hgamma.max measurable_const).aestronglyMeasurable
  · filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
      with Y hY
    rw [Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ lowerGammaScaledPositivePart d c Y by
        exact le_max_right _ _)]
    exact lowerGammaScaledPositivePart_le hd hc hY

private theorem lowerGammaScaledPositivePart_integral_le
    {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
      ((d : ℝ) / 2) *
        (∫ Y : ℝ, max (Real.log
          (4 * Real.pi * c ^ 2 / |Y|)) 0) +
        (1 / 2 : ℝ) *
          (∫ Y : ℝ,
            Real.log (lowerCoth (Real.pi * |Y| / 2))) := by
  have hA : 0 < 4 * Real.pi * c ^ 2 := by positivity
  have hpositive := lower_positiveLogRatio_integrable hA
  have hcoth := lowerCoth_log_abs_integrable
  have hmajor : Integrable (fun Y : ℝ =>
      ((d : ℝ) / 2) *
        max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 +
        (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2))) :=
    (hpositive.const_mul ((d : ℝ) / 2)).add
      (hcoth.const_mul (1 / 2 : ℝ))
  calc
    (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
        ∫ Y : ℝ,
          (((d : ℝ) / 2) *
            max (Real.log (4 * Real.pi * c ^ 2 / |Y|)) 0 +
            (1 / 2 : ℝ) *
              Real.log (lowerCoth (Real.pi * |Y| / 2))) := by
      apply integral_mono_ae
        (lowerGammaScaledPositivePart_integrable hd hc) hmajor
      filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0]
        with Y hY
      exact lowerGammaScaledPositivePart_le hd hc hY
    _ = ((d : ℝ) / 2) *
        (∫ Y : ℝ, max (Real.log
          (4 * Real.pi * c ^ 2 / |Y|)) 0) +
        (1 / 2 : ℝ) *
          (∫ Y : ℝ,
            Real.log (lowerCoth (Real.pi * |Y| / 2))) := by
      rw [integral_add
        (hpositive.const_mul ((d : ℝ) / 2))
        (hcoth.const_mul (1 / 2 : ℝ)),
        integral_const_mul, integral_const_mul]

private theorem lowerGammaBoundaryLog_dimension_scaled_nonpos_of_large
    {d : ℕ} (hd : 2 ≤ d) {c Y : ℝ}
    (hc : 0 < c)
    (hlarge : max 1 (8 * Real.pi * c ^ 2) ≤ |Y|) :
    lowerGammaBoundaryLog ((d : ℝ) / 2)
      (c * Real.sqrt d) (((d : ℝ) / 2) * Y) ≤ 0 := by
  have hyone : 1 ≤ |Y| :=
    le_trans (le_max_left 1 _) hlarge
  have hY : Y ≠ 0 := by
    intro h
    norm_num [h] at hyone
  have hA : 0 < 4 * Real.pi * c ^ 2 := by positivity
  have hden : 0 < |Y| := abs_pos.mpr hY
  have hradius : 8 * Real.pi * c ^ 2 ≤ |Y| :=
    le_trans (le_max_right 1 _) hlarge
  have hratio :
      4 * Real.pi * c ^ 2 / |Y| ≤ (1 / 2 : ℝ) := by
    apply (div_le_iff₀ hden).2
    linarith
  have hratio_pos : 0 < 4 * Real.pi * c ^ 2 / |Y| :=
    div_pos hA hden
  have hlogratio :
      Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
        -(Real.log (2 : ℝ)) := by
    calc
      Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
          Real.log (1 / 2 : ℝ) :=
        Real.log_le_log hratio_pos hratio
      _ = -(Real.log (2 : ℝ)) := by
        rw [one_div, Real.log_inv]
  have hlogtwo : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
    have h := Real.one_sub_inv_le_log_of_pos
      (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hpiabs : 3 ≤ Real.pi * |Y| := by
    linarith [Real.pi_gt_three,
      mul_nonneg (by linarith [Real.pi_gt_three] : 0 ≤ Real.pi - 3)
        (sub_nonneg.mpr hyone)]
  have harg : 1 ≤ Real.pi * |Y| / 2 := by
    linarith
  have hexpthree : 4 ≤ Real.exp (3 : ℝ) := by
    linarith [Real.add_one_le_exp (3 : ℝ)]
  have hexpsmall :
      Real.exp ((-Real.pi) * |Y|) ≤ (1 / 4 : ℝ) := by
    calc
      Real.exp ((-Real.pi) * |Y|) ≤ Real.exp (-3 : ℝ) := by
        apply Real.exp_le_exp.mpr
        linarith
      _ = (Real.exp (3 : ℝ))⁻¹ := Real.exp_neg 3
      _ ≤ (1 / 4 : ℝ) := by
        simpa only [one_div] using!
          (one_div_le_one_div_of_le
            (by norm_num : (0 : ℝ) < 4) hexpthree)
  have hcoth := lowerCoth_log_le_four_exp_neg_two harg
  have hexp :
      Real.exp (-2 * (Real.pi * |Y| / 2)) =
        Real.exp ((-Real.pi) * |Y|) := by
    congr 1
    ring
  rw [hexp] at hcoth
  have hcorrection :
      (1 / 2 : ℝ) *
          Real.log (lowerCoth (Real.pi * |Y| / 2)) ≤
        (1 / 2 : ℝ) := by
    linarith
  have hℓ : 1 ≤ (d : ℝ) / 2 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    exact_mod_cast hd
  have hmain :
      ((d : ℝ) / 2) *
        Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
          -(Real.log (2 : ℝ)) := by
    calc
      ((d : ℝ) / 2) *
          Real.log (4 * Real.pi * c ^ 2 / |Y|) ≤
        ((d : ℝ) / 2) * (-(Real.log (2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hlogratio (by positivity)
      _ ≤ -(Real.log (2 : ℝ)) := by
        linarith [mul_nonneg
          (sub_nonneg.mpr hℓ)
          (show 0 ≤ Real.log (2 : ℝ) by linarith)]
  have htail := lowerGammaBoundaryLog_dimension_scaled_log_tail_uniform
    hd hc hY
  linarith

private theorem lowerGammaScaledPositivePart_support
    {d : ℕ} (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) :
    Function.support (lowerGammaScaledPositivePart d c) ⊆
      Icc (-(max 1 (8 * Real.pi * c ^ 2)))
        (max 1 (8 * Real.pi * c ^ 2)) := by
  intro Y hY
  change lowerGammaScaledPositivePart d c Y ≠ 0 at hY
  have hsmall : |Y| < max 1 (8 * Real.pi * c ^ 2) := by
    by_contra hnot
    have hlarge : max 1 (8 * Real.pi * c ^ 2) ≤ |Y| :=
      le_of_not_gt hnot
    have hnonpos :=
      lowerGammaBoundaryLog_dimension_scaled_nonpos_of_large
        hd hc hlarge
    apply hY
    unfold lowerGammaScaledPositivePart
    exact max_eq_right hnonpos
  exact ⟨(neg_lt_of_abs_lt hsmall).le,
    (lt_of_abs_lt hsmall).le⟩

private theorem exists_lowerGammaScaledPositivePart_uniform_bound
    {c : ℝ} (hc : 0 < c) :
    ∃ C : ℝ, 0 < C ∧
      ∀ d : ℕ, 2 ≤ d →
        Function.support (lowerGammaScaledPositivePart d c) ⊆
            Icc (-C) C ∧
          (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
            C * ((d : ℝ) / 2) := by
  let J : ℝ :=
    ∫ Y : ℝ, max (Real.log
      (4 * Real.pi * c ^ 2 / |Y|)) 0
  let K : ℝ :=
    ∫ Y : ℝ, Real.log (lowerCoth (Real.pi * |Y| / 2))
  let B : ℝ := max 1 (8 * Real.pi * c ^ 2)
  let C : ℝ := max B (J + (1 / 2 : ℝ) * K)
  have hB : 1 ≤ B := le_max_left 1 _
  have hC : B ≤ C := le_max_left _ _
  have hK : 0 ≤ K := by
    try dsimp [K]
    apply integral_nonneg
    intro Y
    by_cases hY : Y = 0
    · simp only [Pi.zero_apply, lowerCoth, hY, abs_zero, mul_zero, zero_div, Real.cosh_zero,
      Real.sinh_zero,
        div_zero, Real.log_zero, Std.le_refl]
    · exact lowerCoth_log_nonneg (by positivity)
  refine ⟨C, by linarith, ?_⟩
  intro d hd
  constructor
  · intro Y hY
    have hsupport :=
      lowerGammaScaledPositivePart_support hd hc hY
    exact ⟨le_trans (neg_le_neg hC) hsupport.1,
      le_trans hsupport.2 hC⟩
  · have hℓ : 1 ≤ (d : ℝ) / 2 := by
      apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
      exact_mod_cast hd
    have hmain := lowerGammaScaledPositivePart_integral_le hd hc
    change
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
        ((d : ℝ) / 2) * J + (1 / 2 : ℝ) * K at hmain
    have hphase :
        ((d : ℝ) / 2) * J + (1 / 2 : ℝ) * K ≤
          ((d : ℝ) / 2) *
            (J + (1 / 2 : ℝ) * K) := by
      linarith [mul_nonneg (sub_nonneg.mpr hℓ) hK]
    have hconstant : J + (1 / 2 : ℝ) * K ≤ C :=
      le_max_right B _
    calc
      (∫ Y : ℝ, lowerGammaScaledPositivePart d c Y) ≤
        ((d : ℝ) / 2) * J + (1 / 2 : ℝ) * K := hmain
      _ ≤ ((d : ℝ) / 2) *
            (J + (1 / 2 : ℝ) * K) := hphase
      _ ≤ ((d : ℝ) / 2) * C :=
        mul_le_mul_of_nonneg_left hconstant (by positivity)
      _ = C * ((d : ℝ) / 2) := by ring

private theorem lowerGammaBoundaryLog_integer_neg
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog (k : ℝ) R (-y) =
      lowerGammaBoundaryLog (k : ℝ) R y := by
  rw [lowerGammaBoundaryLog_integer k R (neg_ne_zero.mpr hy),
    lowerGammaBoundaryLog_integer k R hy]
  simp only [div_pow, even_two, Even.neg_pow]

private theorem lowerGammaBoundaryLog_halfInteger_neg
    (k : ℕ) (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R (-y) =
      lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y := by
  rw [lowerGammaBoundaryLog_halfInteger k R (neg_ne_zero.mpr hy),
    lowerGammaBoundaryLog_halfInteger k R hy]
  simp only [one_div, div_pow, even_two, Even.neg_pow, abs_neg]

private theorem lowerGammaBoundaryLog_dimension_neg
    {d : ℕ} (R : ℝ) {y : ℝ} (hy : y ≠ 0) :
    lowerGammaBoundaryLog ((d : ℝ) / 2) R (-y) =
      lowerGammaBoundaryLog ((d : ℝ) / 2) R y := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_integer_neg k R hy
  · have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_halfInteger_neg k R hy

private theorem lowerGammaBoundaryLog_integer_antitoneOn
    (k : ℕ) (R : ℝ) :
    AntitoneOn (lowerGammaBoundaryLog (k : ℝ) R)
      (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  rw [lowerGammaBoundaryLog_integer k R hy.ne',
    lowerGammaBoundaryLog_integer k R hx.ne']
  have hsum :
      (∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt ((j : ℝ) ^ 2 + (x / 2) ^ 2))) ≤
      ∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt ((j : ℝ) ^ 2 + (y / 2) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hradx : 0 < (j : ℝ) ^ 2 + (x / 2) ^ 2 := by
      linarith [sq_nonneg (j : ℝ), sq_pos_of_pos (half_pos hx)]
    apply Real.log_le_log (Real.sqrt_pos.mpr hradx)
    apply Real.sqrt_le_sqrt
    linarith [sq_nonneg (y / 2 - x / 2),
      mul_nonneg (half_pos hx).le
        (show 0 ≤ y / 2 - x / 2 by linarith)]
  linarith

private theorem lowerGammaBoundaryLog_halfInteger_antitoneOn
    (k : ℕ) (R : ℝ) :
    AntitoneOn (lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R)
      (Ioi (0 : ℝ)) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  rw [lowerGammaBoundaryLog_halfInteger k R hy.ne',
    lowerGammaBoundaryLog_halfInteger k R hx.ne']
  simp only [abs_of_pos hx, abs_of_pos hy]
  have hsum :
      (∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (x / 2) ^ 2))) ≤
      ∑ j ∈ Finset.range k,
        Real.log
          (Real.sqrt
            (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2)) := by
    apply Finset.sum_le_sum
    intro j hj
    have hradx :
        0 < ((j : ℝ) + 1 / 2) ^ 2 + (x / 2) ^ 2 := by
      linarith [sq_nonneg ((j : ℝ) + 1 / 2),
        sq_pos_of_pos (half_pos hx)]
    apply Real.log_le_log (Real.sqrt_pos.mpr hradx)
    apply Real.sqrt_le_sqrt
    linarith [sq_nonneg (y / 2 - x / 2),
      mul_nonneg (half_pos hx).le
        (show 0 ≤ y / 2 - x / 2 by linarith)]
  have hxarg : 0 < Real.pi * x / 2 := by positivity
  have hyarg : 0 < Real.pi * y / 2 := by positivity
  have harg : Real.pi * x / 2 ≤ Real.pi * y / 2 := by
    gcongr
  have hcoth :
      lowerCoth (Real.pi * y / 2) ≤
        lowerCoth (Real.pi * x / 2) :=
    lowerCoth_antitoneOn hxarg hyarg harg
  have hratio :
      lowerCoth (Real.pi * y / 2) / (y / 2) ≤
        lowerCoth (Real.pi * x / 2) / (x / 2) := by
    calc
      lowerCoth (Real.pi * y / 2) / (y / 2) ≤
        lowerCoth (Real.pi * x / 2) / (y / 2) :=
        div_le_div_of_nonneg_right hcoth (half_pos hy).le
      _ ≤ lowerCoth (Real.pi * x / 2) / (x / 2) :=
        div_le_div_of_nonneg_left
          (lowerCoth_pos hxarg).le (half_pos hx)
          (by linarith)
  have hcorr :
      Real.log (lowerCoth (Real.pi * y / 2) / (y / 2)) ≤
        Real.log (lowerCoth (Real.pi * x / 2) / (x / 2)) :=
    Real.log_le_log
      (div_pos (lowerCoth_pos hyarg) (half_pos hy)) hratio
  linarith

private theorem lowerGammaBoundaryLog_dimension_antitoneOn
    {d : ℕ} (R : ℝ) :
    AntitoneOn (lowerGammaBoundaryLog ((d : ℝ) / 2) R)
      (Ioi (0 : ℝ)) := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_integer_antitoneOn k R
  · have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_halfInteger_antitoneOn k R

private theorem even_antitone_superlevel_interval
    {f : ℝ → ℝ} {B t : ℝ}
    (heven : ∀ x : ℝ, f (-x) = f x)
    (hanti : AntitoneOn f (Ici (0 : ℝ)))
    (hsupport : Function.support f ⊆ Icc (-B) B)
    (ht : 0 < t) :
    ∃ r : ℝ, 0 ≤ r ∧
      Ioo (-r) r ⊆ {x : ℝ | t < f x} ∧
        {x : ℝ | t < f x} ⊆ Icc (-r) r := by
  have habs (x : ℝ) : f |x| = f x := by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, heven]
  let S : Set ℝ := {u : ℝ | 0 ≤ u ∧ t < f u}
  by_cases hS : S.Nonempty
  · have hbdd : BddAbove S := by
      refine ⟨B, ?_⟩
      intro u hu
      change 0 ≤ u ∧ t < f u at hu
      have hunonzero : f u ≠ 0 := by
        intro hzero
        rw [hzero] at hu
        linarith [hu.2]
      exact (hsupport hunonzero).2
    let r : ℝ := sSup S
    have hr : 0 ≤ r := by
      obtain ⟨u, hu⟩ := hS
      have hu' : 0 ≤ u ∧ t < f u := hu
      exact le_trans hu'.1 (le_csSup hbdd hu)
    refine ⟨r, hr, ?_, ?_⟩
    · intro x hx
      have hxabs : |x| < r := abs_lt.mpr hx
      obtain ⟨u, hu, hxu⟩ :=
        exists_lt_of_lt_csSup hS hxabs
      have hu' : 0 ≤ u ∧ t < f u := hu
      have horder : f u ≤ f |x| :=
        hanti (show |x| ∈ Ici 0 from abs_nonneg x)
          (show u ∈ Ici 0 from hu'.1) hxu.le
      change t < f x
      rw [← habs]
      exact lt_of_lt_of_le hu'.2 horder
    · intro x hx
      have hxS : |x| ∈ S := by
        change 0 ≤ |x| ∧ t < f |x|
        refine ⟨abs_nonneg x, ?_⟩
        rw [habs]
        exact hx
      have hxle : |x| ≤ r := le_csSup hbdd hxS
      exact (abs_le.mp hxle)
  · refine ⟨0, le_rfl, ?_, ?_⟩
    · simp only [neg_zero, lt_self_iff_false, not_false_eq_true, Ioo_eq_empty, empty_subset]
    · intro x hx
      exfalso
      apply hS
      refine ⟨|x|, ?_⟩
      change 0 ≤ |x| ∧ t < f |x|
      refine ⟨abs_nonneg x, ?_⟩
      rw [habs]
      exact hx

private theorem lowerGammaBoundaryLog_halfInteger_exp_integrable
    {a : ℝ} (ha : 0 < a) (k : ℕ) (R : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y) := by
  have hconstant :
      Integrable
        (fun y : ℝ =>
          (((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2)) *
            Real.exp ((-a) * |y|)) :=
    (strip_exp_abs_integrable ha).const_mul
      (((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2))
  have hsum :
      Integrable
        (fun y : ℝ =>
          ∑ j ∈ Finset.range k,
            Real.exp ((-a) * |y|) *
              Real.log
                (Real.sqrt
                  (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2))) := by
    exact integrable_finsetSum (Finset.range k)
      (fun j _ => lower_exp_log_sqrtFactor_integrable ha
        (by have hj : 0 ≤ (j : ℝ) := Nat.cast_nonneg j; linarith))
  have hcorrection :
      Integrable
        (fun y : ℝ =>
          (1 / 2 : ℝ) *
            (Real.exp ((-a) * |y|) *
              Real.log
                (lowerCoth (Real.pi * |y| / 2) / (|y| / 2)))) :=
    (lower_exp_log_coth_div_integrable ha).const_mul (1 / 2)
  have hbase := (hconstant.sub hsum).add hcorrection
  refine hbase.congr ?_
  filter_upwards [Measure.ae_ne (volume : Measure ℝ) 0] with y hy
  change
    ((((k : ℝ) + 1 / 2) * Real.log (Real.pi * R ^ 2)) *
      Real.exp ((-a) * |y|) -
        ∑ j ∈ Finset.range k,
          Real.exp ((-a) * |y|) *
            Real.log
              (Real.sqrt
                (((j : ℝ) + 1 / 2) ^ 2 + (y / 2) ^ 2))) +
      (1 / 2 : ℝ) *
        (Real.exp ((-a) * |y|) *
          Real.log
            (lowerCoth (Real.pi * |y| / 2) / (|y| / 2))) =
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryLog ((k : ℝ) + 1 / 2) R y
  rw [lowerGammaBoundaryLog_halfInteger k R hy]
  simp only [mul_add, mul_sub, Finset.mul_sum]
  ring

private theorem lowerGammaBoundaryLog_dimension_exp_integrable
    {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) (R : ℝ) :
    Integrable (fun y : ℝ =>
      Real.exp ((-a) * |y|) *
        lowerGammaBoundaryLog ((d : ℝ) / 2) R y) := by
  rcases d.even_or_odd with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · have hq : ((↑(k + k) : ℝ) / 2) = (k : ℝ) := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_integer_exp_integrable ha k R
  · have hq : ((↑(2 * k + 1) : ℝ) / 2) =
        (k : ℝ) + 1 / 2 := by
      push_cast
      ring
    rw [hq]
    exact lowerGammaBoundaryLog_halfInteger_exp_integrable ha k R

private theorem lowerStripGammaOuter_integrable_dimension
    {d : ℕ} (hd : 0 < d) {R : ℝ} {z : ℂ}
    (hz : z ∈ Complex.im ⁻¹'
      Ioo (-((d : ℝ) / 2)) ((d : ℝ) / 2)) :
    Integrable
      (fun y : ℝ =>
        stripRegularizedHolomorphicPoissonKernel
          ((d : ℝ) / 2) z y *
          (lowerGammaBoundaryLog ((d : ℝ) / 2) R y : ℂ)) := by
  have hℓ : 0 < (d : ℝ) / 2 :=
    half_pos (Nat.cast_pos.mpr hd)
  apply lowerStripGammaOuter_integrable_of_exp_integrable hℓ hz
  exact lowerGammaBoundaryLog_dimension_exp_integrable hd
    (div_pos Real.pi_pos (mul_pos (by norm_num) hℓ)) R

private noncomputable def lowerRiemannLog (T x : ℝ) : ℝ :=
  Real.log (Real.sqrt (x ^ 2 + T ^ 2 / 4))

private theorem lowerRiemannLog_monotoneOn {T : ℝ} (hT : T ≠ 0) :
    MonotoneOn (lowerRiemannLog T) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hrad : 0 < x ^ 2 + T ^ 2 / 4 := by
    linarith [sq_nonneg x, sq_pos_of_ne_zero hT]
  have hsquares : x ^ 2 ≤ y ^ 2 :=
    (sq_le_sq₀ hx hy).2 hxy
  unfold lowerRiemannLog
  exact Real.log_le_log (Real.sqrt_pos.2 hrad)
    (Real.sqrt_le_sqrt (by linarith))

private theorem monotone_leftRiemann_error
    (f : ℝ → ℝ) {k : ℕ} (hk : 0 < k)
    (hf : MonotoneOn f (Icc (0 : ℝ) 1)) :
    0 ≤
        (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) -
          ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, f x) -
          ∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ)) ≤
        f 1 - f 0 := by
  have hkpos : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := hkpos.ne'
  have hscaled :
      MonotoneOn (fun x : ℝ => f (x / (k : ℝ)))
        (Icc (0 : ℝ) (k : ℝ)) := by
    intro x hx y hy hxy
    apply hf
    · exact ⟨div_nonneg hx.1 hkpos.le,
        (div_le_one hkpos).2 hx.2⟩
    · exact ⟨div_nonneg hy.1 hkpos.le,
        (div_le_one hkpos).2 hy.2⟩
    · exact div_le_div_of_nonneg_right hxy hkpos.le
  have hscaled' :
      MonotoneOn (fun x : ℝ => f (x / (k : ℝ)))
        (Icc (0 : ℝ) (0 + (k : ℝ))) := by
    simpa only [zero_add] using! hscaled
  have hleft :
      (∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ))) ≤
        ∫ x in (0 : ℝ)..(k : ℝ), f (x / (k : ℝ)) := by
    simpa only [zero_add] using! (MonotoneOn.sum_le_integral
      (x₀ := (0 : ℝ)) (a := k) hscaled')
  have hright :
      (∫ x in (0 : ℝ)..(k : ℝ), f (x / (k : ℝ))) ≤
        ∑ j ∈ Finset.range k,
          f (((j : ℝ) + 1) / (k : ℝ)) := by
    simpa only [zero_add, Nat.cast_add, Nat.cast_one] using!
      (MonotoneOn.integral_le_sum
        (x₀ := (0 : ℝ)) (a := k) hscaled')
  have hintegral :
      (∫ x in (0 : ℝ)..(k : ℝ), f (x / (k : ℝ))) =
        (k : ℝ) * ∫ x in (0 : ℝ)..1, f x := by
    simp only [ne_eq, hkne, not_false_eq_true, intervalIntegral.integral_comp_div, zero_div,
      div_self,
      smul_eq_mul]
  have hshift :
      (∑ j ∈ Finset.range k,
        f (((j : ℝ) + 1) / (k : ℝ))) -
        (∑ j ∈ Finset.range k, f ((j : ℝ) / (k : ℝ))) =
          f 1 - f 0 := by
    rw [← Finset.sum_sub_distrib]
    convert! Finset.sum_range_sub
      (fun j : ℕ => f ((j : ℝ) / (k : ℝ))) k using 1
    · apply Finset.sum_congr rfl
      intro j _
      simp only [Nat.cast_add, Nat.cast_one]
    · simp only [ne_eq, hkne, not_false_eq_true, div_self, CharP.cast_eq_zero, zero_div]
  constructor
  · rw [← hintegral]
    linarith
  · rw [← hintegral]
    linarith

private theorem lower_integer_leftRiemann_error
    {T : ℝ} (hT : T ≠ 0) {k : ℕ} (hk : 0 < k) :
    0 ≤
        (k : ℝ) * (∫ x in (0 : ℝ)..1, lowerRiemannLog T x) -
          ∑ j ∈ Finset.range k,
            lowerRiemannLog T ((j : ℝ) / (k : ℝ)) ∧
      (k : ℝ) * (∫ x in (0 : ℝ)..1, lowerRiemannLog T x) -
          ∑ j ∈ Finset.range k,
            lowerRiemannLog T ((j : ℝ) / (k : ℝ)) ≤
        lowerRiemannLog T 1 - lowerRiemannLog T 0 := by
  exact monotone_leftRiemann_error (lowerRiemannLog T) hk
    ((lowerRiemannLog_monotoneOn hT).mono (by intro x hx; exact hx.1))

private theorem monotone_midpointIntegral_error
    (f : ℝ → ℝ) (k : ℕ)
    (hf : MonotoneOn f (Icc (0 : ℝ) (k : ℝ))) :
    |(∫ x in (0 : ℝ)..(k : ℝ), f x) -
        ∑ j ∈ Finset.range k, f ((j : ℝ) + 1 / 2)| ≤
      f (k : ℝ) - f 0 := by
  have hf' : MonotoneOn f (Icc (0 : ℝ) (0 + (k : ℝ))) := by
    simpa only [zero_add] using! hf
  have hleft :
      (∑ j ∈ Finset.range k, f (j : ℝ)) ≤
        ∫ x in (0 : ℝ)..(k : ℝ), f x := by
    simpa only [zero_add] using!
      (MonotoneOn.sum_le_integral (x₀ := (0 : ℝ)) (a := k) hf')
  have hright :
      (∫ x in (0 : ℝ)..(k : ℝ), f x) ≤
        ∑ j ∈ Finset.range k, f ((j : ℝ) + 1) := by
    simpa only [zero_add, Nat.cast_add, Nat.cast_one] using!
      (MonotoneOn.integral_le_sum (x₀ := (0 : ℝ)) (a := k) hf')
  have hmidleft :
      (∑ j ∈ Finset.range k, f (j : ℝ)) ≤
        ∑ j ∈ Finset.range k, f ((j : ℝ) + 1 / 2) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hjlast : (j : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hjk)
    exact hf ⟨hjnonneg, by linarith⟩
      ⟨by linarith, by linarith⟩ (by linarith)
  have hmidright :
      (∑ j ∈ Finset.range k, f ((j : ℝ) + 1 / 2)) ≤
        ∑ j ∈ Finset.range k, f ((j : ℝ) + 1) := by
    apply Finset.sum_le_sum
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    have hjnonneg : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
    have hjlast : (j : ℝ) + 1 ≤ (k : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt hjk)
    exact hf ⟨by linarith, by linarith⟩
      ⟨by linarith, hjlast⟩ (by linarith)
  have hshift :
      (∑ j ∈ Finset.range k, f ((j : ℝ) + 1)) -
        (∑ j ∈ Finset.range k, f (j : ℝ)) =
          f (k : ℝ) - f 0 := by
    rw [← Finset.sum_sub_distrib]
    convert! Finset.sum_range_sub (fun j : ℕ => f (j : ℝ)) k using 1
    · apply Finset.sum_congr rfl
      intro j _
      simp only [Nat.cast_add, Nat.cast_one]
    · simp only [CharP.cast_eq_zero]
  apply (abs_le).2
  constructor <;> linarith

private theorem lower_halfInteger_midpointRiemann_error
    {T : ℝ} (hT : T ≠ 0)
    {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℕ) :
    |ℓ * (∫ x in (0 : ℝ)..((k : ℝ) / ℓ), lowerRiemannLog T x) -
        ∑ j ∈ Finset.range k,
          lowerRiemannLog T (((j : ℝ) + 1 / 2) / ℓ)| ≤
      lowerRiemannLog T ((k : ℝ) / ℓ) - lowerRiemannLog T 0 := by
  have hscaled :
      MonotoneOn (fun x : ℝ => lowerRiemannLog T (x / ℓ))
        (Icc (0 : ℝ) (k : ℝ)) := by
    intro x hx y hy hxy
    apply lowerRiemannLog_monotoneOn hT
    · exact div_nonneg hx.1 hℓ.le
    · exact div_nonneg hy.1 hℓ.le
    · exact div_le_div_of_nonneg_right hxy hℓ.le
  have hmid := monotone_midpointIntegral_error
    (fun x : ℝ => lowerRiemannLog T (x / ℓ)) k hscaled
  have hscale :
      (∫ x in (0 : ℝ)..(k : ℝ), lowerRiemannLog T (x / ℓ)) =
        ℓ * ∫ x in (0 : ℝ)..((k : ℝ) / ℓ),
          lowerRiemannLog T x := by
    simpa only [zero_div, smul_eq_mul] using!
      (intervalIntegral.integral_comp_div
        (a := (0 : ℝ)) (b := (k : ℝ))
        (lowerRiemannLog T) hℓ.ne')
  rw [hscale] at hmid
  simpa only [one_div, ge_iff_le, zero_div] using! hmid

private noncomputable def lowerEndpointPhase (T : ℝ) : ℝ :=
  -Real.pi * |T| / 4 - (1 / 2 : ℝ) * Real.log (1 + T ^ 2 / 4) +
    |T| / 2 * Real.arctan (|T| / 2)

private noncomputable def lowerRiemannLogPrimitive (T x : ℝ) : ℝ :=
  x / 2 * Real.log (x ^ 2 + T ^ 2 / 4) - x +
    (|T| / 2) * Real.arctan (x / (|T| / 2))

private theorem lowerRiemannLogPrimitive_hasDerivAt
    {T : ℝ} (hT : T ≠ 0) (x : ℝ) :
    HasDerivAt (lowerRiemannLogPrimitive T)
      (lowerRiemannLog T x) x := by
  have hrad : 0 < x ^ 2 + T ^ 2 / 4 := by
    linarith [sq_nonneg x, sq_pos_of_ne_zero hT]
  have ha : 0 < |T| / 2 := half_pos (abs_pos.mpr hT)
  have hquad :
      HasDerivAt (fun u : ℝ => u ^ 2 + T ^ 2 / 4) (2 * x) x := by
    convert! ((hasDerivAt_id x).pow 2).add_const (T ^ 2 / 4)
      using 1; simp only [Nat.cast_ofNat, id_eq, Nat.add_one_sub_one, pow_one, mul_one]
  have hlog := hquad.log hrad.ne'
  have hfirst := ((hasDerivAt_id x).div_const 2).mul hlog
  have hatan := (Real.hasDerivAt_arctan (x / (|T| / 2))).comp x
    ((hasDerivAt_id x).div_const (|T| / 2))
  convert!
    (hfirst.sub (hasDerivAt_id x)).add
      (hatan.const_mul (|T| / 2)) using 1
  unfold lowerRiemannLog
  simp only [id_eq]
  rw [Real.log_sqrt hrad.le]
  have habs : |T| ^ 2 = T ^ 2 := sq_abs T
  field_simp [hrad.ne', ha.ne']
  nlinarith

private theorem integral_lowerRiemannLog
    {T : ℝ} (hT : T ≠ 0) :
    -(∫ x in (0 : ℝ)..1, lowerRiemannLog T x) =
      1 + lowerEndpointPhase T := by
  have hmono : MonotoneOn (lowerRiemannLog T)
      (Icc (0 : ℝ) 1) :=
    (lowerRiemannLog_monotoneOn hT).mono
      (by intro x hx; exact hx.1)
  have hmono' : MonotoneOn (lowerRiemannLog T)
      ([[0, 1]] : Set ℝ) := by
    simpa only [zero_le_one, uIcc_of_le] using! hmono
  have hint :
      IntervalIntegrable (lowerRiemannLog T) volume (0 : ℝ) 1 :=
    hmono'.intervalIntegrable
  have hFTC :
      (∫ x in (0 : ℝ)..1, lowerRiemannLog T x) =
        lowerRiemannLogPrimitive T 1 -
          lowerRiemannLogPrimitive T 0 := by
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun x _ => lowerRiemannLogPrimitive_hasDerivAt hT x) hint
  have ha : 0 < |T| / 2 := half_pos (abs_pos.mpr hT)
  have hatan :
      Real.arctan (1 / (|T| / 2)) =
        Real.pi / 2 - Real.arctan (|T| / 2) := by
    simpa only [one_div, inv_div] using! Real.arctan_inv_of_pos ha
  rw [hFTC]
  unfold lowerRiemannLogPrimitive lowerEndpointPhase
  simp only [one_pow, zero_pow (by norm_num : 2 ≠ 0), zero_add,
    zero_div, zero_mul, sub_zero, Real.arctan_zero]
  rw [hatan]
  ring

end
end CohnElkies
