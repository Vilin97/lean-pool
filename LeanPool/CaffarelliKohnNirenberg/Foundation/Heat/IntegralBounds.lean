/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Heat.Integrability
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Integral Bounds

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set


noncomputable section

namespace CKN.Foundation.Heat

open CKN.Foundation.Parabolic

private lemma rhoTwo_measurable :
    Measurable (fun p : ParabolicPoint => rhoTwo p.1 p.2) := by
  unfold rhoTwo
  have hnorm : Measurable (fun p : ParabolicPoint => vec3EuclideanNorm p.1) := by
    rw [show (fun p : ParabolicPoint => vec3EuclideanNorm p.1) =
        fun p => ‖WithLp.toLp 2 p.1‖ by
      funext p
      exact vec3EuclideanNorm_eq_l2 _]
    exact continuous_norm.measurable.comp
      ((PiLp.continuous_toLp 2 _).measurable.comp measurable_fst)
  exact hnorm.add (Real.continuous_sqrt.measurable.comp measurable_snd)

private lemma heatKernelPlus_integral_time_strip {T : ℝ} (hT : 0 < T) :
    ∫ p in (Set.univ ×ˢ Ioc 0 T), heatKernelPlus p = T := by
  change ∫ p in ((Set.univ : Set Vec3) ×ˢ Ioc 0 T),
      heatKernelPlus (show ParabolicPoint from p) ∂(volume : Measure Vec3).prod volume = T
  rw [← Measure.prod_restrict]
  simp only [Measure.restrict_univ]
  have hprod := heatKernelPlus_integrable_prod (T := T)
  rw [← integral_prod_swap (fun p : Vec3 × ℝ =>
    heatKernelPlus (show ParabolicPoint from p))]
  rw [integral_prod (fun p : ℝ × Vec3 =>
    heatKernelPlus (show ParabolicPoint from p.swap)) hprod.swap]
  have hinner : (fun t : ℝ => ∫ x : Vec3,
      heatKernelPlus (show ParabolicPoint from (t, x).swap)) =ᵐ[volume.restrict (Ioc 0 T)]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [show (fun x : Vec3 =>
        heatKernelPlus (show ParabolicPoint from (t, x).swap)) =
        (fun x : Vec3 => heatKernel x t) by
      funext x
      exact heatKernelPlus_eq_heatKernel (show ParabolicPoint from (t, x).swap)]
    exact heatKernel_integral t ht.1
  rw [integral_congr_ae hinner, integral_const]
  rw [Measure.real_def, Measure.restrict_apply_univ, Real.volume_Ioc]
  simp
  exact hT.le

private lemma heatKernelPlus_setIntegral_pos {R : ℝ} :
    (∫ p in {p : ParabolicPoint | rhoTwo p.1 p.2 < R}, heatKernelPlus p) =
      ∫ p in ({p : ParabolicPoint | rhoTwo p.1 p.2 < R} ∩
        {p : ParabolicPoint | 0 < p.2}), heatKernelPlus p := by
  let S : Set ParabolicPoint := {p | rhoTwo p.1 p.2 < R}
  let P : Set ParabolicPoint := {p | 0 < p.2}
  have hS : MeasurableSet S := rhoTwo_measurable measurableSet_Iio
  have hP : MeasurableSet P := measurableSet_Ioi.preimage measurable_snd
  calc
    (∫ p in {p : ParabolicPoint | rhoTwo p.1 p.2 < R}, heatKernelPlus p) =
        ∫ p in S, P.indicator (fun q => heatKernelPlus q) p := by
      apply setIntegral_congr_fun hS
      intro p _hp
      rcases p with ⟨x, t⟩
      by_cases htp : 0 < t
      · have _hmem : (x, t) ∈ P := by exact htp
        change heatKernelPlus (show ParabolicPoint from (x, t)) =
          if 0 < t then heatKernelPlus (show ParabolicPoint from (x, t)) else 0
        simp [htp]
      · have _hmem : (x, t) ∉ P := by exact htp
        change heatKernelPlus (show ParabolicPoint from (x, t)) =
          if 0 < t then heatKernelPlus (show ParabolicPoint from (x, t)) else 0
        simpa [htp] using
          (heatKernelPlus_eq_zero_of_nonpos (x := x) (t := t) (le_of_not_gt htp))
    _ = ∫ p in S ∩ P, heatKernelPlus p := setIntegral_indicator hP
    _ = ∫ p in ({p : ParabolicPoint | rhoTwo p.1 p.2 < R} ∩
        {p : ParabolicPoint | 0 < p.2}), heatKernelPlus p := by rfl

private lemma time_sqrt_inv_integral_le {T : ℝ} (hT : 0 < T) :
    ∫ t in Ioc 0 T, (Real.sqrt t)⁻¹ ≤ 2 * Real.sqrt T := by
  have hpow : ∫ t in Ioc 0 T, t ^ (-(1 : ℝ) / 2) = 2 * T ^ ((1 : ℝ) / 2) := by
    rw [← intervalIntegral.integral_of_le hT.le,
      integral_rpow (Or.inl (by norm_num))]
    ring_nf
  have heq : (fun t : ℝ => (Real.sqrt t)⁻¹) =ᵐ[volume.restrict (Ioc 0 T)]
      (fun t => t ^ (-(1 : ℝ) / 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.sqrt_eq_rpow, show -(1 : ℝ) / 2 = -((1 : ℝ) / 2) by ring,
      Real.rpow_neg ht.1.le]
  rw [integral_congr_ae heq, hpow, Real.sqrt_eq_rpow]

private lemma heatKernelGradientNorm_slice_integrable {t : ℝ} (ht : 0 < t) :
    Integrable (fun x : Vec3 => heatKernelGradientNorm x t) volume := by
  have hM := (heatKernelGradientMajorant_slice_integrable ht).const_mul (100 : ℝ)
  have hgrad₀ := heatKernelGradientNorm_measurable.comp
    (measurable_prodMk_right (y := t))
  change Measurable (fun x : Vec3 => heatKernelGradientNorm x t) at hgrad₀
  apply hM.mono' hgrad₀.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    have hnonneg : 0 ≤ heatKernelGradientNorm x t := by
      unfold heatKernelGradientNorm
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact heatKernelGradientNorm_le_majorant ht

private lemma heatKernelGradientNorm_slice_integral_le {t : ℝ} (ht : 0 < t) :
    ∫ x : Vec3, heatKernelGradientNorm x t ≤ 400 * (Real.sqrt t)⁻¹ := by
  have hgrad := heatKernelGradientNorm_slice_integrable ht
  have hM := (heatKernelGradientMajorant_slice_integrable ht).const_mul (100 : ℝ)
  have hle : (fun x : Vec3 => heatKernelGradientNorm x t) ≤
      (fun x => 100 * heatKernelGradientMajorant x t) := by
    intro x
    exact heatKernelGradientNorm_le_majorant ht
  calc
    ∫ x : Vec3, heatKernelGradientNorm x t ≤
        ∫ x : Vec3, 100 * heatKernelGradientMajorant x t :=
      integral_mono hgrad hM hle
    _ = 100 * ∫ x : Vec3, heatKernelGradientMajorant x t := by
      rw [integral_const_mul]
    _ ≤ 100 * (4 * (Real.sqrt t)⁻¹) := by
      have hMnorm : (fun x : Vec3 => ‖heatKernelGradientMajorant x t‖) =
          (fun x : Vec3 => heatKernelGradientMajorant x t) := by
        funext x
        rw [Real.norm_eq_abs,
          abs_of_nonneg (heatKernelGradientMajorant_nonneg x t)]
      rw [← hMnorm]
      gcongr
      exact heatKernelGradientMajorant_slice_le ht
    _ = 400 * (Real.sqrt t)⁻¹ := by ring

private lemma heatKernelGradientNorm_integral_time_strip_le {T : ℝ} (hT : 0 < T) :
    ∫ p in (Set.univ ×ˢ Ioc 0 T),
      heatKernelGradientNorm p.1 p.2 ≤ 800 * Real.sqrt T := by
  change ∫ p in ((Set.univ : Set Vec3) ×ˢ Ioc 0 T),
      heatKernelGradientNorm p.1 p.2 ∂(volume : Measure Vec3).prod volume ≤
    800 * Real.sqrt T
  rw [← Measure.prod_restrict]
  simp only [Measure.restrict_univ]
  have hprod := heatKernelGradientNorm_integrable_prod (T := T) hT
  rw [← integral_prod_swap (fun p : Vec3 × ℝ =>
    heatKernelGradientNorm p.1 p.2)]
  change (∫ z : ℝ × Vec3, heatKernelGradientNorm z.2 z.1 ∂
      (volume.restrict (Ioc 0 T)).prod volume) ≤ 800 * Real.sqrt T
  rw [integral_prod (fun p : ℝ × Vec3 =>
    heatKernelGradientNorm p.2 p.1) hprod.swap]
  have hinner := hprod.swap.integral_prod_left
  have hinner' : Integrable (fun t : ℝ => ∫ x : Vec3,
      heatKernelGradientNorm x t) (volume.restrict (Ioc 0 T)) := by
    simpa using hinner
  have hdom := (time_sqrt_inv_integrable hT).const_mul (100 : ℝ)
  have hle : (∫ t : ℝ, (∫ x : Vec3,
      heatKernelGradientNorm x t) ∂(volume.restrict (Ioc 0 T))) ≤
      ∫ t : ℝ, 100 * (4 * (Real.sqrt t)⁻¹) ∂(volume.restrict (Ioc 0 T)) := by
    apply integral_mono_ae hinner' hdom
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    calc
      ∫ x : Vec3, heatKernelGradientNorm x t ≤ 400 * (Real.sqrt t)⁻¹ :=
        heatKernelGradientNorm_slice_integral_le ht.1
      _ = 100 * (4 * (Real.sqrt t)⁻¹) := by ring
  have htime := time_sqrt_inv_integral_le hT
  calc
    ∫ t in Ioc 0 T, ∫ x : Vec3, heatKernelGradientNorm x t ≤
        ∫ t in Ioc 0 T, 100 * (4 * (Real.sqrt t)⁻¹) := hle
    _ = 100 * (4 * ∫ t in Ioc 0 T, (Real.sqrt t)⁻¹) := by
      rw [integral_const_mul, integral_const_mul]
    _ ≤
        100 * (4 * (2 * Real.sqrt T)) := by gcongr
    _ = 800 * Real.sqrt T := by ring

private lemma heatKernelGradientNorm_setIntegral_pos {R : ℝ} :
    (∫ p in {p : ParabolicPoint | rhoTwo p.1 p.2 < R},
      heatKernelGradientNorm p.1 p.2) =
      ∫ p in ({p : ParabolicPoint | rhoTwo p.1 p.2 < R} ∩
        {p : ParabolicPoint | 0 < p.2}),
        heatKernelGradientNorm p.1 p.2 := by
  let S : Set ParabolicPoint := {p | rhoTwo p.1 p.2 < R}
  let P : Set ParabolicPoint := {p | 0 < p.2}
  have hS : MeasurableSet S := rhoTwo_measurable measurableSet_Iio
  have hP : MeasurableSet P := measurableSet_Ioi.preimage measurable_snd
  calc
    (∫ p in {p : ParabolicPoint | rhoTwo p.1 p.2 < R},
        heatKernelGradientNorm p.1 p.2) =
        ∫ p in S, P.indicator
          (fun q => heatKernelGradientNorm q.1 q.2) p := by
      apply setIntegral_congr_fun hS
      intro p _hp
      rcases p with ⟨x, t⟩
      by_cases htp : 0 < t
      · change heatKernelGradientNorm x t =
          if 0 < t then heatKernelGradientNorm x t else 0
        simp [htp]
      · change heatKernelGradientNorm x t =
          if 0 < t then heatKernelGradientNorm x t else 0
        simpa [htp] using
          (heatKernelGradientNorm_eq_zero_of_nonpos (x := x) (t := t)
            (le_of_not_gt htp))
    _ = ∫ p in S ∩ P, heatKernelGradientNorm p.1 p.2 :=
      setIntegral_indicator hP
    _ = ∫ p in ({p : ParabolicPoint | rhoTwo p.1 p.2 < R} ∩
        {p : ParabolicPoint | 0 < p.2}), heatKernelGradientNorm p.1 p.2 := by rfl

lemma heatKernelPlus_integral_rho_lt_le {R : ℝ} (hR : 0 < R) :
    ∫ p in {p : ParabolicPoint | rhoTwo p.1 p.2 < R}, heatKernelPlus p ≤
      1000 * R ^ 2 := by
  rw [heatKernelPlus_setIntegral_pos]
  have hstrip := heatKernelPlus_integral_time_strip (T := R ^ 2) (by positivity)
  have hU := heatKernelPlus_integrableOn_time (T := R ^ 2)
  have hsubset :
      {p : ParabolicPoint | rhoTwo p.1 p.2 < R} ∩
          {p : ParabolicPoint | 0 < p.2} ⊆
        (Set.univ : Set Vec3) ×ˢ Ioc 0 (R ^ 2) := by
    intro p hp
    rcases hp with ⟨hρ, ht⟩
    change rhoTwo p.1 p.2 < R at hρ
    have hsqrt : Real.sqrt p.2 < R := by
      exact (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg p.1)).trans_lt hρ
    have htime : p.2 < R ^ 2 := (Real.sqrt_lt' hR).mp hsqrt
    change p.1 ∈ (Set.univ : Set Vec3) ∧ p.2 ∈ Ioc 0 (R ^ 2)
    exact ⟨Set.mem_univ _, ht, htime.le⟩
  calc
    ∫ p in ({p : ParabolicPoint | rhoTwo p.1 p.2 < R} ∩
        {p : ParabolicPoint | 0 < p.2}), heatKernelPlus p ≤
        ∫ p in ((Set.univ : Set Vec3) ×ˢ Ioc 0 (R ^ 2)), heatKernelPlus p :=
      setIntegral_mono_set hU (ae_of_all _ fun p => heatKernelPlus_nonneg p)
        (ae_of_all _ hsubset)
    _ = R ^ 2 := hstrip
    _ ≤ 1000 * R ^ 2 := by nlinarith only [sq_nonneg R]

lemma heatKernelGradientNorm_integral_rho_lt_le {R : ℝ} (hR : 0 < R) :
    ∫ p in {p : ParabolicPoint | rhoTwo p.1 p.2 < R},
      heatKernelGradientNorm p.1 p.2 ≤ 100000 * R := by
  rw [heatKernelGradientNorm_setIntegral_pos]
  have hstrip := heatKernelGradientNorm_integral_time_strip_le
    (T := R ^ 2) (by positivity)
  have hsubset :
      {p : ParabolicPoint | rhoTwo p.1 p.2 < R} ∩
          {p : ParabolicPoint | 0 < p.2} ⊆
        (Set.univ : Set Vec3) ×ˢ Ioc 0 (R ^ 2) := by
    intro p hp
    rcases hp with ⟨hρ, ht⟩
    change rhoTwo p.1 p.2 < R at hρ
    have hsqrt : Real.sqrt p.2 < R := by
      exact (le_add_of_nonneg_left (vec3EuclideanNorm_nonneg p.1)).trans_lt hρ
    have htime : p.2 < R ^ 2 := (Real.sqrt_lt' hR).mp hsqrt
    change p.1 ∈ (Set.univ : Set Vec3) ∧ p.2 ∈ Ioc 0 (R ^ 2)
    exact ⟨Set.mem_univ _, ht, htime.le⟩
  calc
    ∫ p in ({p : ParabolicPoint | rhoTwo p.1 p.2 < R} ∩
        {p : ParabolicPoint | 0 < p.2}), heatKernelGradientNorm p.1 p.2 ≤
        ∫ p in ((Set.univ : Set Vec3) ×ˢ Ioc 0 (R ^ 2)),
          heatKernelGradientNorm p.1 p.2 :=
      setIntegral_mono_set
        (heatKernelGradientNorm_integrableOn_time (T := R ^ 2) (by positivity))
        (ae_of_all _ fun p => by
          unfold heatKernelGradientNorm
          positivity) (ae_of_all _ hsubset)
    _ ≤ 800 * Real.sqrt (R ^ 2) := hstrip
    _ = 800 * R := by rw [Real.sqrt_sq_eq_abs, abs_of_pos hR]
    _ ≤ 100000 * R := by
      gcongr
      norm_num


end CKN.Foundation.Heat
