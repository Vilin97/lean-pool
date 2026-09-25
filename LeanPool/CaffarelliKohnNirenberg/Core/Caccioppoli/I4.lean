/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.I3
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Covering
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# I4

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

theorem caccioppoli_I4_qprime_lt
    {q : ℝ} (hq : 5 / 2 < q) :
    q / (q - 1) < 5 / 3 ∧ q / (q - 1) < 3 := by
  have hq1 : 0 < q - 1 := by linarith only [hq]
  constructor
  · apply (div_lt_iff₀ hq1).2
    linarith only [hq]
  · apply (div_lt_iff₀ hq1).2
    linarith only [hq]

theorem caccioppoli_I4_holder
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {F U : α → ℝ≥0∞}
    {q C : ℝ} (hq : 5 / 2 < q) (hF : AEMeasurable F μ)
    (hU : AEMeasurable U μ) (hC : ENNReal.ofReal C ≠ ∞) :
    (∫⁻ x, ENNReal.ofReal C * F x * U x ∂μ) ≤
      ENNReal.ofReal C *
        (∫⁻ x, F x ^ q ∂μ) ^ (1 / q : ℝ) *
        (∫⁻ x, U x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q : ℝ) := by
  have hqpos : 0 < q := by linarith only [hq]
  have hq1 : 0 < q - 1 := by linarith only [hq]
  have hconj : q.HolderConjugate (q / (q - 1)) := by
    rw [Real.holderConjugate_iff]
    constructor
    · linarith only [hq]
    · field_simp [hqpos.ne', hq1.ne']
      ring
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hF hU
  calc
    (∫⁻ x, ENNReal.ofReal C * F x * U x ∂μ) =
        ∫⁻ x, ENNReal.ofReal C * (F x * U x) ∂μ := by
      apply lintegral_congr
      intro x
      ring
    _ = ENNReal.ofReal C * ∫⁻ x, F x * U x ∂μ := by
      rw [lintegral_const_mul' (ENNReal.ofReal C) (fun x => F x * U x)
        hC]
    _ ≤ ENNReal.ofReal C *
        ((∫⁻ x, F x ^ q ∂μ) ^ (1 / q : ℝ) *
          (∫⁻ x, U x ^ (q / (q - 1)) ∂μ) ^
            (1 / (q / (q - 1)) : ℝ)) := by
      gcongr
      simpa only [Pi.mul_apply] using hholder
    _ = ENNReal.ofReal C *
        (∫⁻ x, F x ^ q ∂μ) ^ (1 / q : ℝ) *
        (∫⁻ x, U x ^ (q / (q - 1)) ∂μ) ^ ((q - 1) / q : ℝ) := by
      rw [show (1 / (q / (q - 1)) : ℝ) = (q - 1) / q by
        field_simp [hqpos.ne', hq1.ne']]
      ring

theorem caccioppoli_I4_force_integral_identity
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (z : ParabolicPoint)
    {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) =
      ENNReal.ofReal ((ρ ^ (5 / q - 3) * lambda q f z ρ) ^ q) := by
  exact sws_lintegral_vec3EuclideanNorm_pow_eq_ofReal_lambda_pow hsol z hρ hsub

private theorem caccioppoli_I4_root
    {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) :
    (ENNReal.ofReal (a ^ q)) ^ (1 / q : ℝ) = ENNReal.ofReal a := by
  rw [← ENNReal.ofReal_rpow_of_nonneg ha hq.le]
  rw [← ENNReal.rpow_mul]
  rw [show q * (1 / q) = 1 by field_simp [hq.ne']]
  simp

private theorem caccioppoli_I4_volume
    {x : Vec3} {t ρ : ℝ} (hρ : 0 < ρ) :
    volume (parabolicCylinder x t ρ) =
      ENNReal.ofReal (4 * Real.pi / 3 * ρ ^ 5) := by
  rw [volume_parabolicCylinder, volume_vec3Ball_eq]
  rw [← ENNReal.ofReal_pow hρ.le 3]
  rw [← ENNReal.ofReal_mul (by positivity)]
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

private theorem caccioppoli_I4_scale_identity
    {q ρ r γ ell : ℝ} {x₀ : Vec3} {t₀ : ℝ}
    (hq : 5 / 2 < q) (hρ : 0 < ρ) (hr : 0 < r)
    (hγ : 0 ≤ γ) (hell : 0 ≤ ell) :
    (ENNReal.ofReal (2000 / r) *
        ENNReal.ofReal ((ρ ^ (5 / q - 3) * ell) ^ q) ^ (1 / q : ℝ) *
        ENNReal.ofReal (ρ ^ 2 * γ ^ 3) ^ (1 / 3 : ℝ) *
        volume (parabolicCylinder x₀ t₀ ρ) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ)).toReal =
      2000 * (4 * Real.pi / 3) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ) *
        (r / ρ)⁻¹ * γ * ell := by
  have hqpos : 0 < q := by linarith only [hq]
  have hq1 : 0 < q - 1 := by linarith only [hq]
  have he : 0 ≤ 1 / (q / (q - 1)) - 1 / 3 := by
    have hlt := (caccioppoli_I4_qprime_lt hq).2
    have hqp : 0 < q / (q - 1) := div_pos hqpos hq1
    rw [sub_nonneg]
    apply (le_div_iff₀ hqp).2
    nlinarith only [hlt]
  have hA : 0 ≤ ρ ^ (5 / q - 3) * ell :=
    mul_nonneg (Real.rpow_nonneg hρ.le _) hell
  have hB : 0 ≤ ρ ^ 2 * γ ^ 3 := by positivity
  have hvol := caccioppoli_I4_volume (x := x₀) (t := t₀) hρ
  rw [caccioppoli_I4_root hA hqpos]
  have hrootB : (ENNReal.ofReal (ρ ^ 2 * γ ^ 3)) ^ (1 / 3 : ℝ) =
      ENNReal.ofReal ((ρ ^ 2 * γ ^ 3) ^ (1 / 3 : ℝ)) :=
    ENNReal.ofReal_rpow_of_nonneg hB (by norm_num : (0 : ℝ) ≤ 1 / 3)
  rw [hrootB, hvol]
  rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) he]
  have hprod :
      ENNReal.ofReal (2000 / r) * ENNReal.ofReal (ρ ^ (5 / q - 3) * ell) *
          ENNReal.ofReal ((ρ ^ 2 * γ ^ 3) ^ (1 / 3 : ℝ)) *
          ENNReal.ofReal ((4 * Real.pi / 3 * ρ ^ 5) ^
            (1 / (q / (q - 1)) - 1 / 3 : ℝ)) =
        ENNReal.ofReal ((2000 / r) * (ρ ^ (5 / q - 3) * ell) *
          ((ρ ^ 2 * γ ^ 3) ^ (1 / 3 : ℝ)) *
          ((4 * Real.pi / 3 * ρ ^ 5) ^
            (1 / (q / (q - 1)) - 1 / 3 : ℝ))) := by
    rw [← ENNReal.ofReal_mul (by positivity),
      ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity)]
  rw [hprod, ENNReal.toReal_ofReal]
  · have hK : 0 ≤ 4 * Real.pi / 3 := by positivity
    have hBroot : (ρ ^ 2 * γ ^ 3) ^ (1 / 3 : ℝ) =
        ρ ^ (2 / 3 : ℝ) * γ := by
      rw [Real.mul_rpow (by positivity) (by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      rw [← Real.rpow_natCast γ, ← Real.rpow_mul (by positivity)]
      norm_num
    have hVroot : (4 * Real.pi / 3 * ρ ^ 5) ^
        (1 / (q / (q - 1)) - 1 / 3 : ℝ) =
        (4 * Real.pi / 3) ^ (1 / (q / (q - 1)) - 1 / 3 : ℝ) *
          ρ ^ (5 * (1 / (q / (q - 1)) - 1 / 3 : ℝ)) := by
      rw [Real.mul_rpow hK (by positivity)]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [hBroot, hVroot]
    have hexp : 5 / q - 3 + 2 / 3 + 5 *
        (1 / (q / (q - 1)) - 1 / 3) = 1 := by
      field_simp [hqpos.ne', hq1.ne']
      ring
    have hrpow : ρ ^ (5 / q - 3) * ρ ^ (2 / 3 : ℝ) *
        ρ ^ (5 * (1 / (q / (q - 1)) - 1 / 3 : ℝ)) =
        ρ ^ (5 / q - 3 + 2 / 3 +
          5 * (1 / (q / (q - 1)) - 1 / 3 : ℝ)) := by
      rw [← Real.rpow_add hρ, ← Real.rpow_add hρ]
    calc
      _ = 2000 / r * (4 * Real.pi / 3) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ) *
          (ρ ^ (5 / q - 3) * ρ ^ (2 / 3 : ℝ) *
            ρ ^ (5 * (1 / (q / (q - 1)) - 1 / 3 : ℝ))) * γ * ell := by
          ring
      _ = _ := by
        rw [hrpow, hexp, Real.rpow_one]
        field_simp [hr.ne', hρ.ne']
  · positivity

theorem caccioppoli_I4_space_time_bound
    {q ρ r : ℝ} {x₀ : Vec3} {t₀ : ℝ}
    (hq : 5 / 2 < q) (hr : 0 < r)
    {u f : ParabolicPoint → Vec3} {φ : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hf : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (f w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hφ : ∀ w ∈ parabolicCylinder x₀ t₀ ρ, φ w ≤ 1000 / r) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) * ENNReal.ofReal (φ w)) ≤
      ENNReal.ofReal (2000 / r) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ^ (1 / q : ℝ) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
          (1 / 3 : ℝ) *
        (volume (parabolicCylinder x₀ t₀ ρ)) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ) := by
  have hC : ENNReal.ofReal (2000 / r) ≠ ∞ := ENNReal.ofReal_ne_top
  have hφ' : ∀ᵐ w ∂(volume.restrict (parabolicCylinder x₀ t₀ ρ)),
      ENNReal.ofReal (φ w) ≤ ENNReal.ofReal (1000 / r) := by
    filter_upwards [ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
      with w hw
    exact ENNReal.ofReal_le_ofReal (hφ w hw)
  have hmono :
      (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) * ENNReal.ofReal (φ w)) ≤
      ∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (2000 / r) *
          ENNReal.ofReal (vec3EuclideanNorm (f w)) *
            ENNReal.ofReal (vec3EuclideanNorm (u w)) := by
    apply lintegral_mono_ae
    filter_upwards [hφ', ae_restrict_mem (measurableSet_parabolicCylinder _ _ _)]
      with w hw hmem
    have h2 : (2 : ℝ≥0∞) * ENNReal.ofReal (φ w) ≤
        ENNReal.ofReal (2000 / r) := by
      calc
        (2 : ℝ≥0∞) * ENNReal.ofReal (φ w) = ENNReal.ofReal (2 * φ w) := by
          rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ 2)]
          norm_num
        _ ≤ ENNReal.ofReal (2 * (1000 / r)) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
            (hφ w hmem) (by positivity))
        _ = ENNReal.ofReal (2000 / r) := by congr 1; ring
    calc
      (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) * ENNReal.ofReal (φ w) =
        (2 * ENNReal.ofReal (φ w)) *
          (ENNReal.ofReal (vec3EuclideanNorm (f w)) *
            ENNReal.ofReal (vec3EuclideanNorm (u w))) := by ring
      _ ≤ ENNReal.ofReal (2000 / r) *
          (ENNReal.ofReal (vec3EuclideanNorm (f w)) *
            ENNReal.ofReal (vec3EuclideanNorm (u w))) := by
        exact mul_le_mul_of_nonneg_right h2 (by positivity)
      _ = _ := by ring
  calc
    _ ≤ ∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (2000 / r) *
          ENNReal.ofReal (vec3EuclideanNorm (f w)) *
            ENNReal.ofReal (vec3EuclideanNorm (u w)) := hmono
    _ ≤ _ := by
      have h := caccioppoli_I4_holder hq hf.aemeasurable hu.aemeasurable hC
      have hqpos : 0 < q := by linarith only [hq]
      have hq1 : 0 < q - 1 := by linarith only [hq]
      have hqexp : (q - 1) / q = 1 / (q / (q - 1)) := by
        field_simp [hqpos.ne', hq1.ne']
      rw [hqexp] at h
      have hqprimepos : 0 < q / (q - 1) := div_pos hqpos hq1
      have hqprime_le : q / (q - 1) ≤ 3 :=
        (caccioppoli_I4_qprime_lt hq).2.le
      let μ : Measure ParabolicPoint :=
        volume.restrict (parabolicCylinder x₀ t₀ ρ)
      have hcompare := eLpNorm'_le_eLpNorm'_mul_rpow_measure_univ
        hqprimepos hqprime_le hu
      have hmeasure : μ Set.univ = volume (parabolicCylinder x₀ t₀ ρ) := by
        simp [μ]
      have hc :
          (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
            ENNReal.ofReal (vec3EuclideanNorm (u w)) ^
              (q / (q - 1))) ^ (1 / (q / (q - 1)) : ℝ) ≤
            (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
              (1 / 3 : ℝ) *
            (volume (parabolicCylinder x₀ t₀ ρ)) ^
              (1 / (q / (q - 1)) - 1 / 3 : ℝ) := by
        rw [← hmeasure]
        simpa only [eLpNorm'_eq_lintegral_enorm, enorm_eq_self] using hcompare
      calc
        _ ≤ ENNReal.ofReal (2000 / r) *
            (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
              ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ^ (1 / q : ℝ) *
            (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
              ENNReal.ofReal (vec3EuclideanNorm (u w)) ^
                (q / (q - 1))) ^ (1 / (q / (q - 1)) : ℝ) := h
        _ ≤ _ := by
          calc
            _ ≤ ENNReal.ofReal (2000 / r) *
                (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
                  ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ^ (1 / q : ℝ) *
                ((∫⁻ w in parabolicCylinder x₀ t₀ ρ,
                  ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
                  (1 / 3 : ℝ) *
                (volume (parabolicCylinder x₀ t₀ ρ)) ^
                  (1 / (q / (q - 1)) - 1 / 3 : ℝ)) := by
                    exact mul_le_mul_of_nonneg_left hc (by positivity)
            _ = _ := by ring

theorem caccioppoli_I4_normalization
    {q ρ r γ ell : ℝ} {x₀ : Vec3} {t₀ : ℝ}
    (hq : 5 / 2 < q) (hρ : 0 < ρ) (hr : 0 < r)
    (hγ : 0 ≤ γ) (hell : 0 ≤ ell)
    {u f : ParabolicPoint → Vec3} {φ : ParabolicPoint → ℝ}
    (hu : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (u w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hf : AEStronglyMeasurable
      (fun w => ENNReal.ofReal (vec3EuclideanNorm (f w)))
      (volume.restrict (parabolicCylinder x₀ t₀ ρ)))
    (hφ : ∀ w ∈ parabolicCylinder x₀ t₀ ρ, φ w ≤ 1000 / r)
    (hforce : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) =
      ENNReal.ofReal ((ρ ^ (5 / q - 3) * ell) ^ q))
    (hvelocity : (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) =
      ENNReal.ofReal (ρ ^ 2 * γ ^ 3)) :
    (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
        (2 : ℝ≥0∞) * ENNReal.ofReal (vec3EuclideanNorm (f w)) *
          ENNReal.ofReal (vec3EuclideanNorm (u w)) * ENNReal.ofReal (φ w)).toReal ≤
      2000 * (4 * Real.pi / 3) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ) *
        (r / ρ)⁻¹ * γ * ell := by
  have hbound := caccioppoli_I4_space_time_bound hq hr hu hf hφ
  have hqpos : 0 < q := by linarith only [hq]
  have hq1 : 0 < q - 1 := by linarith only [hq]
  have he : 0 ≤ 1 / (q / (q - 1)) - 1 / 3 := by
    have hlt := (caccioppoli_I4_qprime_lt hq).2
    have hqp : 0 < q / (q - 1) := div_pos hqpos hq1
    rw [sub_nonneg]
    apply (le_div_iff₀ hqp).2
    nlinarith only [hlt]
  have hfinite :
      (ENNReal.ofReal (2000 / r) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (f w)) ^ q) ^ (1 / q : ℝ) *
        (∫⁻ w in parabolicCylinder x₀ t₀ ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) ^
          (1 / 3 : ℝ) *
        (volume (parabolicCylinder x₀ t₀ ρ)) ^
          (1 / (q / (q - 1)) - 1 / 3 : ℝ)) ≠ ∞ := by
    rw [hforce, hvelocity]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · apply ENNReal.mul_ne_top
        · exact ENNReal.ofReal_ne_top
        · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
      · exact ENNReal.rpow_ne_top_of_nonneg (by positivity) ENNReal.ofReal_ne_top
    · exact ENNReal.rpow_ne_top_of_nonneg he
        (ne_of_lt (volume_parabolicCylinder_lt_top (x := x₀)
          (t := t₀) (r := ρ)))
  have hbound' := ENNReal.toReal_mono hfinite hbound
  rw [hforce, hvelocity] at hbound'
  rw [caccioppoli_I4_scale_identity (x₀ := x₀) (t₀ := t₀)
    hq hρ hr hγ hell] at hbound'
  exact hbound'

theorem caccioppoli_I4_square_normalization
    {κ γ ell K C₂₆ I₄ : ℝ} (hκ : 0 < κ)
    (hγ : 0 ≤ γ) (hell : 0 ≤ ell)
    (hKbound : K ≤ C₂₆ ^ 2)
    (hraw : I₄ ≤ K * κ⁻¹ * γ * ell) :
    I₄ ≤ (C₂₆ * κ ^ (-1 / 2 : ℝ) * γ ^ (1 / 2 : ℝ) *
      ell ^ (1 / 2 : ℝ)) ^ 2 := by
  have hsqrt (x : ℝ) (hx : 0 ≤ x) :
      (x ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = x := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx]
    norm_num
  have hscale :
      (κ ^ (-1 / 2 : ℝ) * γ ^ (1 / 2 : ℝ) *
        ell ^ (1 / 2 : ℝ)) ^ 2 = κ⁻¹ * γ * ell := by
    rw [mul_pow, mul_pow, hsqrt γ hγ, hsqrt ell hell]
    have hk : (κ ^ (-1 / 2 : ℝ)) ^ (2 : ℕ) = κ⁻¹ := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hκ.le]
      norm_num
      simp [Real.rpow_neg hκ.le]
    rw [hk]
  calc
    I₄ ≤ K * (κ⁻¹ * γ * ell) := by simpa [mul_assoc] using hraw
    _ ≤ C₂₆ ^ 2 * (κ⁻¹ * γ * ell) := by
      gcongr
    _ = (C₂₆ * κ ^ (-1 / 2 : ℝ) * γ ^ (1 / 2 : ℝ) *
        ell ^ (1 / 2 : ℝ)) ^ 2 := by
      rw [← hscale]
      ring

end CKN
