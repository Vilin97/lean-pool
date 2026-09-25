/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsSourceTime
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Summation of the exterior source scales

The gap between the pressure Morrey exponent and the spatial critical
exponent is uniform. It makes the exterior source scales summable after
their spatial masses have been integrated in time.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- Minkowski's inequality for a finite family of nonnegative temporal
majorants at the pressure-gradient integrability exponent. -/
theorem pressure_time_finite_sum_bound
    {ι : Type*} (S : Finset ι) {μ : Measure ℝ} {M : ι → ℝ → ℝ≥0∞}
    (hM : ∀ n ∈ S, AEMeasurable (M n) μ) :
    (∫⁻ s, (∑ n ∈ S, M n s) ^ (6 / 5 : ℝ) ∂μ) ^ (5 / 6 : ℝ) ≤
      ∑ n ∈ S, (∫⁻ s, M n s ^ (6 / 5 : ℝ) ∂μ) ^ (5 / 6 : ℝ) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert n S hn ih =>
    simp only [Finset.sum_insert hn]
    have hs : AEMeasurable (fun s => ∑ k ∈ S, M k s) μ :=
      by simpa only [Finset.sum_fn] using
        Finset.aemeasurable_sum S (fun k hk => hM k (Finset.mem_insert_of_mem hk))
    have h := ENNReal.lintegral_Lp_add_le (hM n (Finset.mem_insert_self _ _)) hs
      (by norm_num : (1 : ℝ) ≤ 6 / 5)
    norm_num only [one_div_div] at h
    exact h.trans (add_le_add_right (ih (fun k hk => hM k (Finset.mem_insert_of_mem hk))) _)

/-- The dyadic exterior ratio is bounded by one fixed ratio strictly below
one throughout the pressure-gradient exponent range. -/
theorem pressure_source_dyadic_ratio_bound
    {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9) :
    (2 : ℝ≥0∞) ^ (5 / 3 - 5 / κ) ≤ (2 : ℝ≥0∞) ^ (-2 / 15 : ℝ) ∧
      (2 : ℝ≥0∞) ^ (-2 / 15 : ℝ) < 1 := by
  constructor
  · apply ENNReal.rpow_le_rpow_of_exponent_le (by norm_num)
    have hdiv : (9 / 5 : ℝ) ≤ 5 / κ := (le_div_iff₀ hκ).mpr (by
      nlinarith only [hκhi])
    linarith only [hdiv]
  · exact ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

/-- Every finite sum of exterior dyadic ratios has one universal bound. -/
theorem pressure_source_dyadic_sum_bound
    {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9) (N : ℕ) :
    (∑ n ∈ Finset.range N, ((2 : ℝ≥0∞) ^ (5 / 3 - 5 / κ)) ^ n) ≤
      (1 - (2 : ℝ≥0∞) ^ (-2 / 15 : ℝ))⁻¹ := by
  have hr := (pressure_source_dyadic_ratio_bound hκ hκhi).1
  calc
    _ ≤ ∑ n ∈ Finset.range N, ((2 : ℝ≥0∞) ^ (-2 / 15 : ℝ)) ^ n := by
      exact Finset.sum_le_sum (fun n _ => pow_le_pow_left₀ (by positivity) hr n)
    _ ≤ ∑' n : ℕ, ((2 : ℝ≥0∞) ^ (-2 / 15 : ℝ)) ^ n :=
      ENNReal.sum_le_tsum _
    _ = _ := ENNReal.tsum_geometric _

/-- The universal dyadic constant is finite. -/
theorem pressure_source_dyadic_constant_lt_top :
    (1 - (2 : ℝ≥0∞) ^ (-2 / 15 : ℝ))⁻¹ < ⊤ := by
  apply ENNReal.inv_lt_top.mpr
  exact (tsub_pos_iff_lt.mpr
    (ENNReal.rpow_lt_one_of_one_lt_of_neg (by norm_num : (1 : ℝ≥0∞) < 2)
      (by norm_num : (-2 / 15 : ℝ) < 0)))

/-- The spatial source mass is a measurable function of time. -/
theorem pressure_source_spatial_mass_aemeasurable
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume) (x : Vec3) (ρ : ℝ) :
    AEMeasurable (fun s : ℝ => ∫⁻ y in vec3Ball x ρ, ‖F (y, s)‖ₑ) volume := by
  have hprod : AEMeasurable F
      ((volume : Measure Vec3).prod (volume : Measure ℝ)) := by
    change AEMeasurable F (volume : Measure (Vec3 × ℝ))
    exact hF
  have hrestrict : AEMeasurable (fun z : Vec3 × ℝ => ‖F z‖ₑ)
      ((volume.restrict (vec3Ball x ρ)).prod (volume : Measure ℝ)) :=
    hprod.enorm.mono_measure (Measure.prod_mono Measure.restrict_le_self le_rfl)
  exact hrestrict.lintegral_prod_left'

/-- Pulling a nonnegative constant out of the temporal `L^{6/5}` norm. -/
theorem pressure_time_power_norm_const_mul
    {μ : Measure ℝ} {M : ℝ → ℝ≥0∞} (hM : AEMeasurable M μ) (c : ℝ≥0∞) :
    (∫⁻ s, (c * M s) ^ (6 / 5 : ℝ) ∂μ) ^ (5 / 6 : ℝ) =
      c * (∫⁻ s, M s ^ (6 / 5 : ℝ) ∂μ) ^ (5 / 6 : ℝ) := by
  simp_rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6 / 5)]
  rw [lintegral_const_mul'' _ (hM.pow_const _),
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 5 / 6),
    ← ENNReal.rpow_mul]
  norm_num

/-- Time integration and summation of finitely many exterior scales has a
constant independent of both the number of scales and the exponent. -/
theorem pressure_source_exterior_scale_sum_time_bound
    {κ : ℝ} (hκ : 0 < κ) (hκhi : κ ≤ 25 / 9)
    {F : ParabolicPoint → ℝ} (hF : AEMeasurable F volume)
    (x : Vec3) (t : ℝ) {r : ℝ} (hr : 0 < r) (N : ℕ) :
    (∫⁻ s in Ioc (t - r ^ 2) t,
      (∑ n ∈ Finset.range N,
        ENNReal.ofReal ((2 : ℝ) ^ n * r) ^ (-3 : ℝ) *
          ∫⁻ y in vec3Ball x ((2 : ℝ) ^ n * r), ‖F (y, s)‖ₑ) ^ (6 / 5 : ℝ)) ^
            (5 / 6 : ℝ) ≤
      ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 6 : ℝ) *
        ENNReal.ofReal r ^ (5 / 3 - 5 / κ) * morreyNorm (6 / 5 : ℝ) κ F *
          (1 - (2 : ℝ≥0∞) ^ (-2 / 15 : ℝ))⁻¹ := by
  let β : ℝ := 5 / 3 - 5 / κ
  let c : ℝ≥0∞ := ENNReal.ofReal (Real.pi * 4 / 3) ^ (1 / 6 : ℝ) *
    ENNReal.ofReal r ^ β * morreyNorm (6 / 5 : ℝ) κ F
  let M : ℕ → ℝ → ℝ≥0∞ := fun n s =>
    ENNReal.ofReal ((2 : ℝ) ^ n * r) ^ (-3 : ℝ) *
      ∫⁻ y in vec3Ball x ((2 : ℝ) ^ n * r), ‖F (y, s)‖ₑ
  have hm : ∀ n, AEMeasurable (M n) (volume.restrict (Ioc (t - r ^ 2) t)) := by
    intro n
    exact ((pressure_source_spatial_mass_aemeasurable hF x ((2 : ℝ) ^ n * r)).const_mul _).restrict
  have hterm : ∀ n : ℕ,
      (∫⁻ s in Ioc (t - r ^ 2) t, M n s ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤
        c * ((2 : ℝ≥0∞) ^ β) ^ n := by
    intro n
    have hrρ : r ≤ (2 : ℝ) ^ n * r := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right
        (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2 ^ n) hr.le
    dsimp only [M]
    rw [pressure_time_power_norm_const_mul (pressure_source_spatial_mass_aemeasurable hF x
      _).restrict]
    have h := pressure_source_exterior_mass_time_bound (κ := κ) hF (x := x) (t := t) hr hrρ
    refine h.trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2 ^ n),
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num only [ENNReal.ofReal_ofNat]
    rw [ENNReal.mul_rpow_of_ne_top (ENNReal.pow_ne_top (by norm_num)) ENNReal.ofReal_ne_top]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul,
      mul_comm (n : ℝ), ENNReal.rpow_mul_natCast]
    dsimp only [c, β]
    ac_rfl
  change (∫⁻ s in Ioc (t - r ^ 2) t,
    (∑ n ∈ Finset.range N, M n s) ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) ≤ _
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        (∫⁻ s in Ioc (t - r ^ 2) t, M n s ^ (6 / 5 : ℝ)) ^ (5 / 6 : ℝ) :=
      pressure_time_finite_sum_bound _ (fun n _ => hm n)
    _ ≤ ∑ n ∈ Finset.range N, c * ((2 : ℝ≥0∞) ^ β) ^ n :=
      Finset.sum_le_sum (fun n _ => hterm n)
    _ = c * ∑ n ∈ Finset.range N, ((2 : ℝ≥0∞) ^ β) ^ n := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_right (pressure_source_dyadic_sum_bound hκ hκhi N) c

end CKN.Core.Step4
