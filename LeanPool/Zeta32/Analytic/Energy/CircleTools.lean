/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang, Moritz Firsching
-/
module
public import Mathlib.Analysis.SpecialFunctions.Integrals.PosLog
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring

/-! Circle logarithmic integrals and the finite signed-energy algebra.
Everything in this file is copied from the Li₂(1/2) formalization (same toolchain), with
namespace changed:
-- adapted from Li2Unified/Modular/Base/CircleLogTools.lean, Base/CirclePairLog.lean
-- (themselves adapted from
--   mo271/Zeta5 Apery/CircleAtoms.lean, Apache-2.0),
-- adapted from Li2Unified/Modular/Positive/Packed/P194.lean (circle_fiber_null,
-- pair_collision_null),
-- adapted from Li2Unified/Modular/Base/FiniteSignedEnergyAlgebra.lean,
-- Base/FiniteSignedEnergyBound.lean,
--   Positive/Packed/P197.lean (complex_signed_energy_log_bound). -/

public section

open MeasureTheory Set Real intervalIntegral
open scoped BigOperators

namespace Zeta32.Analytic.EnergyI
noncomputable section

lemma circle_log_integrable (c a : ℂ) (R : ℝ) :
    IntervalIntegrable (fun θ => Real.log ‖circleMap c R θ - a‖) volume 0 (2 * π) :=
  circleIntegrable_log_norm_sub_const R

lemma circle_log_integral (c a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∫ θ in (0 : ℝ)..2 * π, Real.log ‖circleMap c R θ - a‖) =
      2 * π * (Real.log R + log⁺ (R⁻¹ * ‖c - a‖)) := by
  have h := circleAverage_log_norm_sub_const_eq_log_radius_add_posLog (a := a) (c := c) hR
  rw [circleAverage_def, smul_eq_mul] at h
  have hpi : (2 * π : ℝ) ≠ 0 := by positivity
  rw [← h, ← mul_assoc, mul_inv_cancel₀ hpi, one_mul]

lemma circle_log_integral_rev (c a : ℂ) {R : ℝ} (hR : R ≠ 0) :
    (∫ θ in (0 : ℝ)..2 * π, Real.log ‖a - circleMap c R θ‖) =
      2 * π * (Real.log R + log⁺ (R⁻¹ * ‖c - a‖)) := by
  rw [← circle_log_integral c a hR]
  apply intervalIntegral.integral_congr
  intro θ _
  dsimp only
  rw [norm_sub_rev]

private lemma continuous_posLog_of_nonneg {X : Type*} [TopologicalSpace X] {f : X → ℝ}
    (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) : Continuous (fun x => log⁺ (f x)) := by
  have he : (fun x => log⁺ (f x)) = (fun x => Real.log (max 1 (f x))) :=
    funext (fun x => Real.posLog_eq_log_max_one (hf0 x))
  rw [he]
  exact (continuous_const.max hf).log
    (fun x => (lt_of_lt_of_le zero_lt_one (le_max_left _ _)).ne')

lemma circle_abs_log_eq (x : ℝ) : |Real.log x| = 2 * log⁺ x - Real.log x := by
  rw [Real.posLog_def]
  change |Real.log x| = 2 * max 0 (Real.log x) - Real.log x
  rcases le_total 0 (Real.log x) with h | h
  · rw [max_eq_right h, abs_of_nonneg h]; ring
  · rw [max_eq_left h, abs_of_nonpos h]; ring

lemma continuous_circle_log_row (c d : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π,
      Real.log ‖circleMap c ε θ - circleMap d ε φ‖) := by
  have he : (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π,
        Real.log ‖circleMap c ε θ - circleMap d ε φ‖) =
      (fun θ : ℝ => 2 * π * (Real.log ε + log⁺ (ε⁻¹ * ‖d - circleMap c ε θ‖))) :=
    funext (fun θ => circle_log_integral_rev d (circleMap c ε θ) hε.ne')
  rw [he]
  apply continuous_const.mul
  apply continuous_const.add
  apply continuous_posLog_of_nonneg
  · exact continuous_const.mul (continuous_const.sub (continuous_circleMap c ε)).norm
  · intro θ; positivity

/-- Joint absolute integrability is established before any Fubini use. -/
theorem integrable_circle_pair_log (c d : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℝ × ℝ => Real.log ‖circleMap c ε p.1 - circleMap d ε p.2‖)
      ((volume.restrict (Ioc 0 (2 * π))).prod (volume.restrict (Ioc 0 (2 * π)))) := by
  let K : ℝ → ℝ → ℝ := fun θ φ => Real.log ‖circleMap c ε θ - circleMap d ε φ‖
  let P : ℝ → ℝ → ℝ := fun θ φ => log⁺ ‖circleMap c ε θ - circleMap d ε φ‖
  have hT : (0 : ℝ) ≤ 2 * π := by positivity
  have hK (θ : ℝ) : IntervalIntegrable (K θ) volume 0 (2 * π) := by
    simpa only [K, norm_sub_rev] using circle_log_integrable d (circleMap c ε θ) ε
  have hP : Continuous (Function.uncurry P) := by
    change Continuous (fun p : ℝ × ℝ => log⁺ ‖circleMap c ε p.1 - circleMap d ε p.2‖)
    apply continuous_posLog_of_nonneg
    · exact (((continuous_circleMap c ε).comp continuous_fst).sub
        ((continuous_circleMap d ε).comp continuous_snd)).norm
    · intro p; exact norm_nonneg _
  have hPi (θ : ℝ) : IntervalIntegrable (P θ) volume 0 (2 * π) :=
    (hP.comp (continuous_const.prodMk continuous_id)).intervalIntegrable 0 (2 * π)
  have hN : Continuous (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π, ‖K θ φ‖) := by
    have he : (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π, ‖K θ φ‖) =
        (fun θ : ℝ => 2 * (∫ φ in (0 : ℝ)..2 * π, P θ φ) -
          (∫ φ in (0 : ℝ)..2 * π, K θ φ)) := by
      funext θ
      calc
        _ = ∫ φ in (0 : ℝ)..2 * π, 2 * P θ φ - K θ φ := by
          apply intervalIntegral.integral_congr
          intro φ _
          dsimp only [K, P]
          rw [Real.norm_eq_abs]
          exact circle_abs_log_eq _
        _ = _ := by
          rw [intervalIntegral.integral_sub ((hPi θ).const_mul 2) (hK θ),
            intervalIntegral.integral_const_mul]
    rw [he]
    exact (continuous_const.mul
      (intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hP 0 (2 * π))).sub
        (continuous_circle_log_row c d hε)
  have hm : Measurable (fun p : ℝ × ℝ => K p.1 p.2) := by
    apply Real.measurable_log.comp
    exact (((continuous_circleMap c ε).comp continuous_fst).sub
      ((continuous_circleMap d ε).comp continuous_snd)).norm.measurable
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun θ =>
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp (hK θ))
  · have hi : IntegrableOn (fun θ : ℝ => ∫ φ in (0 : ℝ)..2 * π, ‖K θ φ‖)
        (Ioc (0 : ℝ) (2 * π)) volume :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
        (hN.intervalIntegrable 0 (2 * π))
    simpa only [IntegrableOn, intervalIntegral.integral_of_le hT] using hi

theorem circle_pair_log_self (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    (∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
      Real.log ‖circleMap c ε θ - circleMap c ε φ‖) = (2 * π) ^ 2 * Real.log ε := by
  have hin (θ : ℝ) : (∫ φ in (0 : ℝ)..2 * π,
        Real.log ‖circleMap c ε θ - circleMap c ε φ‖) = 2 * π * Real.log ε := by
    rw [circle_log_integral_rev _ _ hε.ne', norm_sub_rev c, circleMap_sub_center,
      norm_circleMap_zero, abs_of_pos hε, inv_mul_cancel₀ hε.ne', Real.posLog_one, add_zero]
  simp_rw [hin]
  rw [intervalIntegral.integral_const]
  simp only [sub_zero, smul_eq_mul]
  ring

private lemma log_le_log_add_posLog {ε x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    Real.log x ≤ Real.log ε + log⁺ (ε⁻¹ * x) := by
  have h1 : Real.log (ε⁻¹ * x) ≤ log⁺ (ε⁻¹ * x) := le_max_right _ _
  rw [Real.log_mul (inv_ne_zero hε.ne') hx.ne', Real.log_inv] at h1
  linarith

theorem circle_pair_log_lower (c d : ℂ) {ε : ℝ} (hε : 0 < ε) (hne : c ≠ d) :
    (2 * π) ^ 2 * Real.log ‖c - d‖ ≤ ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
      Real.log ‖circleMap c ε θ - circleMap d ε φ‖ := by
  have hin (θ : ℝ) (hθ : circleMap c ε θ ≠ d) :
      2 * π * Real.log ‖circleMap c ε θ - d‖ ≤ ∫ φ in (0 : ℝ)..2 * π,
        Real.log ‖circleMap c ε θ - circleMap d ε φ‖ := by
    rw [circle_log_integral_rev _ _ hε.ne', norm_sub_rev d]
    exact mul_le_mul_of_nonneg_left
      (log_le_log_add_posLog hε (norm_pos_iff.mpr (sub_ne_zero.mpr hθ))) (by positivity)
  have h1 : (∫ θ in (0 : ℝ)..2 * π, 2 * π * Real.log ‖circleMap c ε θ - d‖) ≤
      ∫ θ in (0 : ℝ)..2 * π, ∫ φ in (0 : ℝ)..2 * π,
        Real.log ‖circleMap c ε θ - circleMap d ε φ‖ := by
    apply intervalIntegral.integral_mono_ae (by positivity)
      ((circle_log_integrable c d ε).const_mul _)
      ((continuous_circle_log_row c d hε).intervalIntegrable _ _)
    have hc := ((countable_singleton d).preimage_circleMap c hε.ne').measure_zero (volume :
      Measure ℝ)
    filter_upwards [compl_mem_ae_iff.mpr hc] with θ hθ
    exact hin θ hθ
  have h2 : (∫ θ in (0 : ℝ)..2 * π, 2 * π * Real.log ‖circleMap c ε θ - d‖) =
      2 * π * (2 * π * (Real.log ε + log⁺ (ε⁻¹ * ‖c - d‖))) := by
    rw [intervalIntegral.integral_const_mul, circle_log_integral c d hε.ne']
  have h3 := log_le_log_add_posLog hε (norm_pos_iff.mpr (sub_ne_zero.mpr hne))
  calc
    _ ≤ (2 * π) ^ 2 * (Real.log ε + log⁺ (ε⁻¹ * ‖c - d‖)) :=
      mul_le_mul_of_nonneg_left h3 (sq_nonneg _)
    _ = ∫ θ in (0 : ℝ)..2 * π, 2 * π * Real.log ‖circleMap c ε θ - d‖ := by rw [h2]; ring
    _ ≤ _ := h1
lemma circle_fiber_null (c w : ℂ) (r a b : ℝ) (hr : r ≠ 0) :
    (volume.restrict (Ioc a b)) {t : ℝ | circleMap c r t = w} = 0 := by
  have h := (Set.countable_singleton w).preimage_circleMap c hr
  simpa using! h.measure_zero (volume.restrict (Ioc a b))

lemma pair_collision_null (f g : ℝ → ℂ) (μ ν : Measure ℝ) [SFinite ν]
    (hf : Continuous f) (hg : Continuous g)
    (hnull : ∀ w : ℂ, ν {t : ℝ | g t = w} = 0) :
    (μ.prod ν) {p : ℝ × ℝ | f p.1 = g p.2} = 0 := by
  have hm : MeasurableSet {p : ℝ × ℝ | f p.1 = g p.2} :=
    (isClosed_eq (hf.comp continuous_fst) (hg.comp continuous_snd)).measurableSet
  apply Measure.measure_prod_null_of_ae_null hm
  exact Filter.Eventually.of_forall (fun x => by simpa [eq_comm] using! hnull (f x))

theorem option_signed_weight_double_sum {h : ℕ} (c : ℝ)
    (E : Option (Fin h) → Option (Fin h) → ℝ) :
    let w : Option (Fin h) → ℝ := fun k => match k with | none => -1 | some _ => c
    (∑ k : Option (Fin h), ∑ l : Option (Fin h), w k * w l * E k l) =
      c ^ 2 * (∑ i : Fin h, ∑ j : Fin h, E (some i) (some j)) -
        c * (∑ i : Fin h, E (some i) none) -
        c * (∑ j : Fin h, E none (some j)) + E none none := by
  classical
  dsimp only
  simp only [Fintype.sum_option, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring
theorem symmetric_double_sum_eq_diag_add_two_Ioi {h : ℕ} (F : Fin h → Fin h → ℝ)
    (hF : ∀ i j, F i j = F j i) :
    (∑ i : Fin h, ∑ j : Fin h, F i j) =
      (∑ i : Fin h, F i i) + 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, F i j) := by
  classical
  have hoff : (∑ i : Fin h, ∑ j ∈ ({i} : Finset (Fin h))ᶜ, F j i) =
      2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, F i j) := by
    calc
      _ = ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, (F j i + F i j) :=
        (Finset.sum_sum_Ioi_add_eq_sum_sum_off_diag F).symm
      _ = ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, (2 * F i j) := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hF j i]
        ring
      _ = _ := by simp only [← Finset.mul_sum]
  calc
    (∑ i : Fin h, ∑ j : Fin h, F i j) = ∑ i : Fin h, ∑ j : Fin h, F j i := Finset.sum_comm
    _ = ∑ i : Fin h, (F i i + ∑ j ∈ ({i} : Finset (Fin h))ᶜ, F j i) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Finset.sum_singleton] using
        (Finset.sum_add_sum_compl ({i} : Finset (Fin h)) (fun j => F j i)).symm
    _ = (∑ i : Fin h, F i i) + (∑ i : Fin h, ∑ j ∈ ({i} : Finset (Fin h))ᶜ, F j i) :=
      Finset.sum_add_distrib
    _ = _ := by rw [hoff]
theorem finite_signed_energy_cross_sum_upper {h : ℕ} (T M ε : ℝ) (L : Fin h → ℝ)
    (E : Option (Fin h) → Option (Fin h) → ℝ)
    (hcross : ∀ i : Fin h, E (some i) none ≤ T * (L i + 2 * M * ε)) :
    (∑ i : Fin h, E (some i) none) ≤ T * ((∑ i : Fin h, L i) + 2 * M * ε * (h : ℝ)) := by
  classical
  calc
    _ ≤ ∑ i : Fin h, T * (L i + 2 * M * ε) := by
      apply Finset.sum_le_sum; intro i _; exact hcross i
    _ = T * (∑ i : Fin h, (L i + 2 * M * ε)) := by rw [Finset.mul_sum]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring
theorem complex_signed_energy_circle_sum_lower {h : ℕ} (x : Fin h → ℂ)
    (T ε : ℝ) (E : Option (Fin h) → Option (Fin h) → ℝ)
    (hEsym : ∀ k l, E k l = E l k)
    (hdiag : ∀ i : Fin h, E (some i) (some i) = T ^ 2 * Real.log ε)
    (hoff : ∀ i j : Fin h, i ≠ j →
      T ^ 2 * Real.log ‖x j - x i‖ ≤ E (some i) (some j)) :
    (h : ℝ) * T ^ 2 * Real.log ε +
      2 * T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
        Real.log ‖x j - x i‖) ≤
      ∑ i : Fin h, ∑ j : Fin h, E (some i) (some j) := by
  classical
  have hdiag_sum : (∑ i : Fin h, E (some i) (some i)) =
      (h : ℝ) * T ^ 2 * Real.log ε := by
    simp only [hdiag, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_assoc]
  have htri : T ^ 2 *
      (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log ‖x j - x i‖) ≤
      ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, E (some i) (some j) := by
    calc
      _ = ∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
          T ^ 2 * Real.log ‖x j - x i‖ := by
        simp only [Finset.mul_sum]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j hj
        exact hoff i j (ne_of_lt (Finset.mem_Ioi.mp hj))
  calc
    _ = (∑ i : Fin h, E (some i) (some i)) +
      2 * (T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
        Real.log ‖x j - x i‖)) := by
        rw [hdiag_sum]
        ring
    _ ≤ (∑ i : Fin h, E (some i) (some i)) +
      2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i, E (some i) (some j)) := by
        have hm := mul_le_mul_of_nonneg_left htri
          (by norm_num : (0 : ℝ) ≤ 2)
        linarith only [hm]
    _ = _ := (symmetric_double_sum_eq_diag_add_two_Ioi
      (fun i j : Fin h => E (some i) (some j))
      (fun i j => hEsym (some i) (some j))).symm

private theorem complex_signed_energy_clear_denominator
    {d S B I : ℝ} (hd : 0 < d)
    (he : (1 / d) ^ 2 * S - (1 / d) * B - (1 / d) * B + I ≤ 0) :
    S - 2 * d * B + d ^ 2 * I ≤ 0 := by
  calc
    _ = d ^ 2 * ((1 / d) ^ 2 * S - (1 / d) * B -
        (1 / d) * B + I) := by
      field_simp [ne_of_gt hd]
      ring
    _ ≤ 0 := by
      simpa only [mul_zero] using
        (mul_le_mul_of_nonneg_left he (sq_nonneg d))

theorem complex_signed_energy_log_bound {h : ℕ} (hh : 0 < h)
    (T ε M : ℝ) (hT : 0 < T)
    (x : Fin h → ℂ) (L : Fin h → ℝ) (I : ℝ)
    (E : Option (Fin h) → Option (Fin h) → ℝ)
    (hEsym : ∀ k l, E k l = E l k)
    (henergy : let w : Option (Fin h) → ℝ := fun k => match k with
      | none => -1 | some _ => 1 / ((h : ℝ) * T)
      (∑ k : Option (Fin h), ∑ l : Option (Fin h),
        w k * w l * E k l) ≤ 0)
    (h00 : E none none = I)
    (hcross : ∀ i : Fin h, E (some i) none ≤
      T * (L i + 2 * M * ε))
    (hdiag : ∀ i : Fin h, E (some i) (some i) =
      T ^ 2 * Real.log ε)
    (hoff : ∀ i j : Fin h, i ≠ j →
      T ^ 2 * Real.log ‖x j - x i‖ ≤ E (some i) (some j)) :
    2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
      Real.log ‖x j - x i‖) ≤
      2 * (h : ℝ) * (∑ i : Fin h, L i) -
        (h : ℝ) ^ 2 * I - (h : ℝ) * Real.log ε +
        4 * M * (h : ℝ) ^ 2 * ε := by
  classical
  have hhR : 0 < (h : ℝ) := Nat.cast_pos.mpr hh
  have hd : 0 < (h : ℝ) * T := mul_pos hhR hT
  have hcross_sym : (∑ i : Fin h, E none (some i)) =
      ∑ i : Fin h, E (some i) none := by
    apply Finset.sum_congr rfl
    intro i _
    exact hEsym none (some i)
  have he := henergy
  have hoption := option_signed_weight_double_sum
    (1 / ((h : ℝ) * T)) E
  dsimp only at he hoption
  have he' := hoption.symm.le.trans he
  rw [h00, hcross_sym] at he'
  have hscaled : (∑ i : Fin h, ∑ j : Fin h,
      E (some i) (some j)) -
      2 * ((h : ℝ) * T) * (∑ i : Fin h, E (some i) none) +
      ((h : ℝ) * T) ^ 2 * I ≤ 0 :=
    complex_signed_energy_clear_denominator hd he'
  have hcircle := complex_signed_energy_circle_sum_lower
    x T ε E hEsym hdiag hoff
  have hcross_sum := finite_signed_energy_cross_sum_upper
    T M ε L E hcross
  have hblock : (∑ i : Fin h, ∑ j : Fin h,
      E (some i) (some j)) ≤
      2 * ((h : ℝ) * T) *
        (T * ((∑ i : Fin h, L i) + 2 * M * ε * (h : ℝ))) -
      ((h : ℝ) * T) ^ 2 * I := by
    calc
      _ ≤ 2 * ((h : ℝ) * T) *
          (∑ i : Fin h, E (some i) none) -
          ((h : ℝ) * T) ^ 2 * I := by
        linarith only [hscaled]
      _ ≤ _ := sub_le_sub_right
        (mul_le_mul_of_nonneg_left hcross_sum
          (show 0 ≤ 2 * ((h : ℝ) * T) by positivity)) _
  refine le_of_mul_le_mul_left (a := T ^ 2) ?_
    (sq_pos_of_pos hT)
  calc
    T ^ 2 * (2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
      Real.log ‖x j - x i‖)) =
      ((h : ℝ) * T ^ 2 * Real.log ε +
        2 * T ^ 2 * (∑ i : Fin h, ∑ j ∈ Finset.Ioi i,
          Real.log ‖x j - x i‖)) -
        (h : ℝ) * T ^ 2 * Real.log ε := by ring
    _ ≤ (∑ i : Fin h, ∑ j : Fin h, E (some i) (some j)) -
      (h : ℝ) * T ^ 2 * Real.log ε :=
      sub_le_sub_right hcircle _
    _ ≤ (2 * ((h : ℝ) * T) *
      (T * ((∑ i : Fin h, L i) + 2 * M * ε * (h : ℝ))) -
      ((h : ℝ) * T) ^ 2 * I) -
      (h : ℝ) * T ^ 2 * Real.log ε :=
      sub_le_sub_right hblock _
    _ = T ^ 2 * (2 * (h : ℝ) * (∑ i : Fin h, L i) -
      (h : ℝ) ^ 2 * I - (h : ℝ) * Real.log ε +
      4 * M * (h : ℝ) ^ 2 * ε) := by ring

end
end Zeta32.Analytic.EnergyI

end
