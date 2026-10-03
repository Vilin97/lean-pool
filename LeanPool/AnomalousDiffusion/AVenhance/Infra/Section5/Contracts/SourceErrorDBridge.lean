/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section5.Integration.OpenInputs

/-! # `SourceErrorDContract`: the contract norm versus the space-time `L²` norm

The contract states `d_m` as the time-`L²` of the spatial `L²` norm (`gradNormSq`).  For a field
measurable on the time cube this is at most `2 ‖d_m‖_{L²((0,1)×𝕋²)}` (sup norm on `Vec 2`,
    Tonelli). -/

@[expose] public section

open MeasureTheory Homogenization
noncomputable section
namespace AVenhance.Infra.Section5.Contracts
open AVenhance

theorem sed_vecNormSq_le (v : Vec 2) : vecNormSq v ≤ 2 * ‖v‖ ^ 2 := by
  have h0 : |v 0| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 0
  have h1 : |v 1| ≤ ‖v‖ := by simpa using norm_le_pi_norm v 1
  simp only [vecNormSq, vecDot, Fin.sum_univ_two]
  have a0 : v 0 * v 0 ≤ ‖v‖ ^ 2 := by
    calc v 0 * v 0 = |v 0| ^ 2 := by rw [sq_abs]; ring
      _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h0 2
  have a1 : v 1 * v 1 ≤ ‖v‖ ^ 2 := by
    calc v 1 * v 1 = |v 1| ^ 2 := by rw [sq_abs]; ring
      _ ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h1 2
  linarith

theorem sed_ofReal_gradNormSq_le (u : Vec 2 → Vec 2) :
    ENNReal.ofReal (Real.sqrt (gradNormSq u)) ^ 2 ≤
      2 * ∫⁻ x in unitCube, ‖u x‖ₑ ^ (2 : ℝ) := by
  have hG : 0 ≤ gradNormSq u := integral_nonneg (fun x => vecNormSq_nonneg _)
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), Real.sq_sqrt hG]
  unfold gradNormSq
  have h1 : ENNReal.ofReal (∫ x in unitCube, vecNormSq (u x)) ≤
      ∫⁻ x in unitCube, ENNReal.ofReal (vecNormSq (u x)) := by
    by_cases hint : Integrable (fun x => vecNormSq (u x)) (volume.restrict unitCube)
    · rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun x => vecNormSq_nonneg _))]
    · rw [integral_undef hint]; simp
  refine h1.trans ?_
  rw [← lintegral_const_mul' _ _ (by norm_num)]
  refine lintegral_mono (fun x => ?_)
  have := sed_vecNormSq_le (u x)
  calc ENNReal.ofReal (vecNormSq (u x)) ≤ ENNReal.ofReal (2 * ‖u x‖ ^ 2) :=
      ENNReal.ofReal_le_ofReal this
    _ = 2 * ‖u x‖ₑ ^ (2 : ℝ) := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      simp

theorem sed_lhs_le_eLpNorm (d : ℝ → Vec 2 → Vec 2)
    (hd : AEStronglyMeasurable (fun z : ℝ × Vec 2 => d z.1 z.2)
      (volume.restrict timeCube)) :
    (∫⁻ t in Set.Ioo (0 : ℝ) 1,
      ENNReal.ofReal (Real.sqrt (gradNormSq (d t))) ^ 2) ^ (1 / 2 : ℝ) ≤
      2 * eLpNorm (fun z : ℝ × Vec 2 => d z.1 z.2) 2 (volume.restrict timeCube) := by
  have hvol : (volume : Measure (ℝ × Vec 2)) =
      (volume : Measure ℝ).prod (volume : Measure (Vec 2)) := Measure.volume_eq_prod ℝ (Vec 2)
  have hmeas : AEMeasurable (fun z : ℝ × Vec 2 => ‖d z.1 z.2‖ₑ ^ (2 : ℝ))
      (((volume : Measure ℝ).prod (volume : Measure (Vec 2))).restrict
        (Set.Ioo (0 : ℝ) 1 ×ˢ unitCube)) := by
    have h : AEMeasurable (fun z : ℝ × Vec 2 => ‖d z.1 z.2‖ₑ)
        (volume.restrict timeCube) := hd.enorm
    rw [hvol] at h
    exact (ENNReal.continuous_rpow_const (y := (2 : ℝ))).measurable.comp_aemeasurable h
  have hprod := setLIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure (Vec 2)))
    (s := Set.Ioo (0 : ℝ) 1) (t := unitCube) (fun z : ℝ × Vec 2 => ‖d z.1 z.2‖ₑ ^ (2 : ℝ)) hmeas
  have hnorm : eLpNorm (fun z : ℝ × Vec 2 => d z.1 z.2) 2 (volume.restrict timeCube) =
      (∫⁻ z in Set.Ioo (0 : ℝ) 1 ×ˢ unitCube, ‖d z.1 z.2‖ₑ ^ (2 : ℝ)
        ∂((volume : Measure ℝ).prod (volume : Measure (Vec 2)))) ^ (1 / 2 : ℝ) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hd]
    simp only [ENNReal.toReal_ofNat]
    rw [hvol]
    rfl
  rw [hnorm, hprod]
  calc (∫⁻ t in Set.Ioo (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt (gradNormSq (d t))) ^ 2) ^ (1 / 2 : ℝ)
      ≤ (∫⁻ t in Set.Ioo (0 : ℝ) 1, 2 * ∫⁻ x in unitCube, ‖d t x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        apply ENNReal.rpow_le_rpow _ (by norm_num)
        exact lintegral_mono (fun t => sed_ofReal_gradNormSq_le (d t))
    _ = (2 * ∫⁻ t in Set.Ioo (0 : ℝ) 1, ∫⁻ x in unitCube, ‖d t x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        rw [lintegral_const_mul' _ _ (by norm_num)]
    _ = 2 ^ (1 / 2 : ℝ) * (∫⁻ t in Set.Ioo (0 : ℝ) 1, ∫⁻ x in unitCube, ‖d t x‖ₑ ^ (2 : ℝ)) ^ (1 /
        2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ ≤ 2 * (∫⁻ t in Set.Ioo (0 : ℝ) 1, ∫⁻ x in unitCube, ‖d t x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        gcongr
        calc (2 : ENNReal) ^ (1 / 2 : ℝ) ≤ 2 ^ (1 : ℝ) :=
              ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 2 := by simp

end AVenhance.Infra.Section5.Contracts

end
