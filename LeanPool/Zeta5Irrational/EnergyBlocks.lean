/-
Copyright (c) 2026 Moritz Firsching. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Moritz Firsching
-/

module

public import LeanPool.Zeta5Irrational.EnergyAtoms
public import LeanPool.Zeta5Irrational.Potential
import LeanPool.Zeta5Irrational.ArcsinePotential
import LeanPool.Zeta5Irrational.CircleAtoms
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Tactic.Ring.RingNF

/-! # The four blocks of the configuration energy

With `P k l = pairInt (atomγ t ε) (log ‖· - ·‖) k l`:

* (A) `P (inl i) (inl i) = (2π)² log ε`;
* (B) `(2π)² log |tᵢ - tᵢ'| ≤ P (inl i) (inl i')` for `tᵢ ≠ tᵢ'`;
* (C) `P (inl i) (inr j) ≤ (2π)² (Uω aⱼ bⱼ tᵢ + errⱼ(tᵢ))` (circle regularisation error);
* (D) `(2π)² log ((bⱼ' - aⱼ')/4) ≤ P (inr j) (inr j')`.
-/

public section

open MeasureTheory Set Real intervalIntegral Filter Topology

namespace Zeta5Irrational

/-- The pair integrals of the logarithmic kernel for the configuration atoms. -/
@[expose] noncomputable def Plog {h : ℕ} (t : Fin h → ℝ) (ε : ℝ) (k l : Idx h) : ℝ :=
  pairInt (atomγ t ε) (fun z w => Real.log ‖z - w‖) k l

lemma log_le_log_add_posLog {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    Real.log x ≤ Real.log ε + log⁺ (ε⁻¹ * x) := by
  have h1 : Real.log (ε⁻¹ * x) ≤ log⁺ (ε⁻¹ * x) := le_max_right _ _
  rw [Real.log_mul (inv_ne_zero hε.ne') hx.ne', Real.log_inv] at h1
  linarith

/-- The inner integrals are interval integrable in the outer variable. -/
lemma inner_intervalIntegrable {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (k l : Idx h) :
    IntervalIntegrable (fun θ => ∫ φ in (0 : ℝ)..2 * π, Real.log ‖atomγ t ε k θ - atomγ t ε l φ‖)
      volume 0 (2 * π) := by
  have := (atom_pair_integrable t hε k l).integral_prod_left
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)]
  simp_rw [intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * π)]
  exact this

lemma norm_circleMap_sub_center' (c : ℝ) {ε : ℝ} (hε : 0 < ε) (θ : ℝ) :
    ‖(c : ℂ) - circleMap c ε θ‖ = ε := by
  rw [norm_sub_rev, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]

lemma circle_log_integral' (c a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    ∫ θ in (0 : ℝ)..2 * π, Real.log ‖a - circleMap c R θ‖ =
      2 * π * (Real.log R + log⁺ (R⁻¹ * ‖c - a‖)) := by
  rw [← circle_log_integral c a hR]
  apply integral_congr
  intro θ _
  simp only
  rw [norm_sub_rev]

/-- (A): the self-energy of a circle. -/
lemma block_A {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin h) :
    Plog t ε (Sum.inl i) (Sum.inl i) = (2 * π) ^ 2 * Real.log ε := by
  unfold Plog pairInt
  have hin :
    ∀ θ,
      (∫ φ in (0 : ℝ)..2 * π, Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inl i) φ‖) =
        2 * π * Real.log ε := by
    intro θ
    simp only [atomγ]
    rw [circle_log_integral' _ _ hε.ne', norm_circleMap_sub_center' _ hε, inv_mul_cancel₀ hε.ne',
      (posLog_eq_zero_iff _).mpr (by simp), add_zero]
  simp_rw [hin]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

/-- (B): the mutual energy of two circles dominates `log |tᵢ - tᵢ'|`. -/
lemma block_B {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i i' : Fin h) (hne : t i ≠ t i') :
    (2 * π) ^ 2 * Real.log |t i - t i'| ≤ Plog t ε (Sum.inl i) (Sum.inl i') := by
  unfold Plog pairInt
  have hin :
    ∀ θ,
      circleMap (t i) ε θ ≠ (t i' : ℂ) →
        2 * π * Real.log ‖circleMap (t i) ε θ - t i'‖ ≤
          ∫ φ in (0 : ℝ)..2 * π, Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inl i') φ‖ := by
    intro θ hθ
    simp only [atomγ]
    rw [circle_log_integral' _ _ hε.ne', norm_sub_rev (t i' : ℂ)]
    have := log_le_log_add_posLog hε (norm_pos_iff.mpr (sub_ne_zero.mpr hθ))
    nlinarith [Real.pi_pos]
  have h1 :
    (∫ θ in (0 : ℝ)..2 * π, 2 * π * Real.log ‖circleMap (t i) ε θ - t i'‖) ≤
      ∫ θ in (0 : ℝ)..2 * π,
        ∫ φ in (0 : ℝ)..2 * π, Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inl i') φ‖ := by
    refine
      intervalIntegral.integral_mono_ae (by positivity)
        ((circle_log_integrable _ _ _).const_mul _) (inner_intervalIntegrable t hε _ _) ?_
    have hc :=
      (circleMap_preimage_countable (t i) hε.ne' (t i')).measure_zero (volume : Measure ℝ)
    filter_upwards [compl_mem_ae_iff.mpr hc] with θ hθ
    exact hin θ hθ
  have h2 :
    (∫ θ in (0 : ℝ)..2 * π, 2 * π * Real.log ‖circleMap (t i) ε θ - t i'‖) =
      2 * π * (2 * π * (Real.log ε + log⁺ (ε⁻¹ * ‖(t i : ℂ) - t i'‖))) :=
    by rw [intervalIntegral.integral_const_mul, circle_log_integral _ _ hε.ne']
  have h3 : Real.log |t i - t i'| ≤ Real.log ε + log⁺ (ε⁻¹ * ‖(t i : ℂ) - t i'‖) := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact log_le_log_add_posLog hε (abs_pos.mpr (sub_ne_zero.mpr hne))
  nlinarith [Real.pi_pos]

/-- The regularisation error of the arcsine potential at a real point `t`. -/
@[expose] noncomputable def errj (ε t m r : ℝ) : ℝ :=
  ε / r + Real.sqrt (ε / r * ((ε + 2 * |t - m|) / r))

lemma errj_nonneg {ε t m r : ℝ} (hε : 0 < ε) (hr : 0 < r) : 0 ≤ errj ε t m r := by
  unfold errj;
  positivity

/-- (C): circle–arcsine energy. -/
lemma block_C {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (i : Fin h) (j : Fin 16) :
    Plog t ε (Sum.inl i) (Sum.inr j) ≤
      (2 * π) ^ 2 *
        (Uω (aρ (j + 1)) (bρ (j + 1)) (t i) + errj ε (t i) (mρ (j + 1)) (rρ (j + 1))) := by
  unfold Plog pairInt
  have hr := rρ_pos j
  have hab : aρ (j + 1) < bρ (j + 1) := aρ_lt_bρ (j + 1) (by simp only [Finset.mem_Icc]; omega)
  have hm' : mρ (j + 1) = (aρ (j + 1) + bρ (j + 1)) / 2 := rfl
  have hr' : rρ (j + 1) = (bρ (j + 1) - aρ (j + 1)) / 2 := rfl
  set sq' : ℂ := ((((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq'_def
  have hsq' : sq' ^ 2 = (((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)) ^ 2 - 1 :=
    Complex.cpow_nat_inv_pow _ two_ne_zero
  have hU :
    2 * π *
        (Real.log (rρ (j + 1) / 2) + log⁺ ‖((t i : ℂ) - mρ (j + 1)) / rρ (j + 1) + sq'‖ +
          log⁺ ‖((t i : ℂ) - mρ (j + 1)) / rρ (j + 1) - sq'‖) =
      2 * π * Uω (aρ (j + 1)) (bρ (j + 1)) (t i) :=
    by rw [← arc_log_integral hr hsq', hm', hr', arc_potential_real hab (t i)]
  have hin :
    ∀ θ,
      (∫ φ in (0 : ℝ)..2 * π, Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inr j) φ‖) ≤
        2 * π * (Uω (aρ (j + 1)) (bρ (j + 1)) (t i) + errj ε (t i) (mρ (j + 1)) (rρ (j + 1))) := by
    intro θ
    simp only [atomγ]
    set z := circleMap (t i) ε θ with hz
    set sq : ℂ := (((z - mρ (j + 1)) / rρ (j + 1)) ^ 2 - 1) ^ ((2 : ℕ) : ℂ)⁻¹ with hsq_def
    have hsq : sq ^ 2 = ((z - mρ (j + 1)) / rρ (j + 1)) ^ 2 - 1 :=
      Complex.cpow_nat_inv_pow _ two_ne_zero
    rw [arc_log_integral hr hsq]
    have hG := Gpot_sub_le hsq hsq'
    have hzc : ‖z - (t i)‖ = ε := by
      rw [hz, circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]
    have hd :
      ‖(z - mρ (j + 1)) / rρ (j + 1) - ((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)‖ = ε / rρ (j + 1) := by
      rw [← sub_div, show z - mρ (j + 1) - ((t i : ℂ) - mρ (j + 1)) = z - (t i) by ring, norm_div,
        hzc, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have hs :
      ‖(z - mρ (j + 1)) / rρ (j + 1) + ((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)‖ ≤
        (ε + 2 * |(t i) - mρ (j + 1)|) / rρ (j + 1) := by
      rw [← add_div, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
      apply div_le_div_of_nonneg_right _ hr.le
      calc
        ‖z - mρ (j + 1) + ((t i : ℂ) - mρ (j + 1))‖ =
            ‖(z - t i) + 2 * ((t i : ℂ) - mρ (j + 1))‖ :=
          by ring_nf
        _ ≤ ‖z - (t i)‖ + ‖(2 : ℂ) * ((t i : ℂ) - mρ (j + 1))‖ := (norm_add_le _ _)
        _ = ε + 2 * |(t i) - mρ (j + 1)| := by
          rw [hzc, norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          simp
    have hsqrt :
      Real.sqrt
          (‖(z - mρ (j + 1)) / rρ (j + 1) - ((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)‖ *
            ‖(z - mρ (j + 1)) / rρ (j + 1) + ((t i : ℂ) - mρ (j + 1)) / rρ (j + 1)‖) ≤
        Real.sqrt (ε / rρ (j + 1) * ((ε + 2 * |(t i) - mρ (j + 1)|) / rρ (j + 1))) := by
      apply Real.sqrt_le_sqrt
      rw [hd]
      exact mul_le_mul_of_nonneg_left hs (by positivity)
    rw [hd] at hG hsqrt
    unfold errj
    nlinarith [Real.pi_pos]
  calc
    (∫ θ in (0 : ℝ)..2 * π,
          ∫ φ in (0 : ℝ)..2 * π, Real.log ‖atomγ t ε (Sum.inl i) θ - atomγ t ε (Sum.inr j) φ‖) ≤
        ∫ θ in (0 : ℝ)..2 * π,
          2 * π * (Uω (aρ (j + 1)) (bρ (j + 1)) (t i) + errj ε (t i) (mρ (j + 1)) (rρ (j + 1))) :=
      integral_mono_on (by positivity) (inner_intervalIntegrable t hε _ _)
        intervalIntegrable_const (fun θ _ => hin θ)
    _ = _ := by rw [intervalIntegral.integral_const]; simp only [sub_zero, smul_eq_mul]; ring

/-- `Uω a b t ≥ log ((b - a)/4)` for all `t`. -/
lemma log_le_Uω {a b : ℝ} (hab : a < b) (t : ℝ) : Real.log ((b - a) / 4) ≤ Uω a b t := by
  by_cases h : a ≤ t ∧ t ≤ b
  · rw [Uω_of_mem h.1 h.2]
  · unfold Uω
    rw [ite_eq_right h]
    have hs := Real.sqrt_nonneg ((t - a) * (t - b))
    have h1 : (b - a) / 2 ≤ |t - (a + b) / 2| := by
      rw [le_abs]
      rcases not_and_or.mp h with h | h
      · right; linarith [not_le.mp h]
      · left; linarith [not_le.mp h]
    apply Real.log_le_log (by linarith)
    linarith

/-- (D): arcsine–arcsine energy is at least `log ((bⱼ' - aⱼ')/4)`. -/
lemma block_D {h : ℕ} (t : Fin h → ℝ) {ε : ℝ} (hε : 0 < ε) (j j' : Fin 16) :
    (2 * π) ^ 2 * Real.log ((bρ (j' + 1) - aρ (j' + 1)) / 4) ≤
      Plog t ε (Sum.inr j) (Sum.inr j') := by
  unfold Plog pairInt
  have hab : aρ (j' + 1) < bρ (j' + 1) := aρ_lt_bρ (j' + 1) (by simp only [Finset.mem_Icc]; omega)
  have hin :
    ∀ θ,
      2 * π * Real.log ((bρ (j' + 1) - aρ (j' + 1)) / 4) ≤
        ∫ φ in (0 : ℝ)..2 * π, Real.log ‖atomγ t ε (Sum.inr j) θ - atomγ t ε (Sum.inr j') φ‖ := by
    intro θ
    change
      2 * π * Real.log ((bρ (j' + 1) - aρ (j' + 1)) / 4) ≤
        ∫ φ in (0 : ℝ)..2 * π,
          Real.log
            ‖((mρ (j + 1) + rρ (j + 1) * Real.cos θ : ℝ) : ℂ) -
                arcCurve ((aρ (j' + 1) + bρ (j' + 1)) / 2) ((bρ (j' + 1) - aρ (j' + 1)) / 2) φ‖
    rw [arc_potential_real hab]
    exact mul_le_mul_of_nonneg_left (log_le_Uω hab _) (by positivity)
  calc
    (2 * π) ^ 2 * Real.log ((bρ (j' + 1) - aρ (j' + 1)) / 4) =
        ∫ θ in (0 : ℝ)..2 * π, 2 * π * Real.log ((bρ (j' + 1) - aρ (j' + 1)) / 4) :=
      by rw [intervalIntegral.integral_const]; simp only [sub_zero, smul_eq_mul]; ring
    _ ≤ _ :=
      integral_mono_on (by positivity) intervalIntegrable_const
        (inner_intervalIntegrable t hε _ _) (fun θ _ => hin θ)

end Zeta5Irrational
