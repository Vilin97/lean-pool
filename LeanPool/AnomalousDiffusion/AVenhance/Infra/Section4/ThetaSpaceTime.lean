/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.ThetaIntegratedEnergy
public import LeanPool.AnomalousDiffusion.AVenhance.Statements.Roots.TimeCube
public import Mathlib.MeasureTheory.Integral.MeanInequalities

/-! L² estimates on the closed time-space cell used by the differentiated
energy recursion. -/

@[expose] public section

noncomputable section

open MeasureTheory Homogenization

namespace AVenhance.Infra.Section4

/-- Closed time-space unit cell for the temperature space-time estimates. -/
def ThetaSpaceTime.thetaTimeClosedCell : Set (ℝ × Homogenization.Vec 2) :=
  Set.Icc (0 : ℝ) 1 ×ˢ
    Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)

theorem ThetaSpaceTime.thetaTimeClosedCell_compact : IsCompact ThetaSpaceTime.thetaTimeClosedCell
    := by
  apply IsCompact.prod isCompact_Icc
  simpa using isCompact_univ_pi (fun _ : Fin 2 => isCompact_Icc)

theorem ThetaSpaceTime.thetaTimeCube_subset_closedCell :
    AVenhance.timeCube ⊆ ThetaSpaceTime.thetaTimeClosedCell := by
  intro p hp
  rcases hp with ⟨ht, hx⟩
  refine ⟨⟨le_of_lt ht.1, le_of_lt ht.2⟩, ?_⟩
  change ∀ i ∈ Set.univ, p.2 i ∈ Set.Ioo (0 : ℝ) 1 at hx
  change ∀ i ∈ Set.univ, p.2 i ∈ Set.Icc (0 : ℝ) 1
  intro i hi
  have hxi := hx i hi
  exact ⟨le_of_lt hxi.1, le_of_lt hxi.2⟩

/-- Every continuous function is square-integrable on the space-time cell.
The compact closed cell gives both finite measure and a uniform bound. -/
theorem theta_continuous_timeCube_memLp_two
    {f : ℝ × Homogenization.Vec 2 → ℝ} (hf : Continuous f) :
    MemLp f (ENNReal.ofReal (2 : ℝ))
      ((volume : Measure (ℝ × Homogenization.Vec 2)).restrict AVenhance.timeCube) := by
  have hfinite : IsFiniteMeasure
      ((volume : Measure (ℝ × Homogenization.Vec 2)).restrict AVenhance.timeCube) := by
    rw [MeasureTheory.isFiniteMeasure_iff, Measure.restrict_apply_univ]
    exact (measure_mono ThetaSpaceTime.thetaTimeCube_subset_closedCell).trans_lt
      ThetaSpaceTime.thetaTimeClosedCell_compact.measure_lt_top
  obtain ⟨C, hCpos, hC⟩ := ThetaSpaceTime.thetaTimeClosedCell_compact.image hf
      |>.isBounded.subset_ball_lt 0 0
  have hmeas : AEStronglyMeasurable f
      ((volume : Measure (ℝ × Homogenization.Vec 2)).restrict AVenhance.timeCube) :=
    hf.measurable.aestronglyMeasurable.restrict
  apply MemLp.of_bound hmeas C
  filter_upwards [ae_restrict_mem (by
    exact (measurableSet_Ioo.prod AVenhance.Infra.Section4.thetaTime_measurableSet_unitCube))]
    with p hp
  have hp' : p ∈ ThetaSpaceTime.thetaTimeClosedCell :=
      ThetaSpaceTime.thetaTimeCube_subset_closedCell hp
  have hfp : f p ∈ f '' ThetaSpaceTime.thetaTimeClosedCell := ⟨p, hp', rfl⟩
  have hball := hC hfp
  have hnorm : ‖f p‖ < C := by
    simpa [Metric.mem_ball, Real.dist_eq] using hball
  exact le_of_lt hnorm

/-- Cauchy–Schwarz for products integrated over the full space-time cell. -/
theorem theta_timeCube_integral_mul_abs_le
    {f g : ℝ × Homogenization.Vec 2 → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    |∫ p in AVenhance.timeCube, f p * g p| ≤
      Real.sqrt (∫ p in AVenhance.timeCube, f p ^ 2) *
        Real.sqrt (∫ p in AVenhance.timeCube, g p ^ 2) := by
  have hfLp := theta_continuous_timeCube_memLp_two (f := fun p => |f p|)
    (continuous_abs.comp hf)
  have hgLp := theta_continuous_timeCube_memLp_two (f := fun p => |g p|)
    (continuous_abs.comp hg)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (f := fun p => |f p|) (g := fun p => |g p|)
    (μ := (volume : Measure (ℝ × Homogenization.Vec 2)).restrict AVenhance.timeCube)
    Real.HolderConjugate.two_two
    (ae_of_all _ (fun _ => abs_nonneg _))
    (ae_of_all _ (fun _ => abs_nonneg _)) hfLp hgLp
  have hholder' :
      (∫ p in AVenhance.timeCube, |f p| * |g p|) ≤
        (∫ p in AVenhance.timeCube, |f p| ^ 2) ^ (1 / 2 : ℝ) *
          (∫ p in AVenhance.timeCube, |g p| ^ 2) ^ (1 / 2 : ℝ) := by
    simpa [Real.rpow_natCast] using hholder
  calc
    |∫ p in AVenhance.timeCube, f p * g p| ≤
        ∫ p in AVenhance.timeCube, |f p * g p| := by
      have h := norm_integral_le_integral_norm
        (μ := (volume : Measure (ℝ × Homogenization.Vec 2)).restrict AVenhance.timeCube)
        (fun p => f p * g p)
      simpa [Real.norm_eq_abs] using h
    _ = ∫ p in AVenhance.timeCube, |f p| * |g p| := by
      apply integral_congr_ae
      filter_upwards with p
      simp [abs_mul]
    _ ≤ _ := by
      simpa [Real.sqrt_eq_rpow, sq_abs] using hholder'

/-- Fubini on the open time-space cell, with the time integral written in the
paper's interval convention. The omitted right endpoint is null. -/
theorem theta_timeCube_integral_eq_interval_integral
    {f : ℝ × Homogenization.Vec 2 → ℝ} (hf : Continuous f) :
    (∫ p in AVenhance.timeCube, f p) =
      ∫ t in (0 : ℝ)..1, ∫ x in AVenhance.unitCube, f (t, x) := by
  let μ : Measure ℝ := volume
  let ν : Measure (Homogenization.Vec 2) := volume
  have htime : Set.Ioo (0 : ℝ) 1 =ᵐ[μ] Set.Ioc 0 1 := by
    rw [MeasureTheory.ae_eq_set]
    constructor
    · rw [show Set.Ioo (0 : ℝ) 1 \ Set.Ioc 0 1 = ∅ by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact ht.2 ⟨ht.1.1, ht.1.2.le⟩]
      simp
    · rw [show Set.Ioc (0 : ℝ) 1 \ Set.Ioo 0 1 = {1} by
        ext t
        constructor
        · intro ht
          have htIoc : t ∈ Set.Ioc (0 : ℝ) 1 := ht.1
          have htNot : t ∉ Set.Ioo (0 : ℝ) 1 := ht.2
          simp only [Set.mem_Ioc] at htIoc
          simp only [Set.mem_Ioo] at htNot
          simp only [Set.mem_singleton_iff]
          rcases lt_or_eq_of_le htIoc.2 with hlt | heq
          · exact (htNot ⟨htIoc.1, hlt⟩).elim
          · exact heq
        · intro ht
          simp only [Set.mem_singleton_iff] at ht
          subst t
          simp]
      simp
  have htimeMeasure : μ.restrict (Set.Ioo (0 : ℝ) 1) =
      μ.restrict (Set.Ioc 0 1) := MeasureTheory.Measure.restrict_congr_set htime
  have hproductMeasure :
      (μ.restrict (Set.Ioo (0 : ℝ) 1)).prod
          (ν.restrict AVenhance.unitCube) =
        (volume : Measure (ℝ × Homogenization.Vec 2)).restrict AVenhance.timeCube := by
    rw [MeasureTheory.Measure.prod_restrict]
    rw [← MeasureTheory.Measure.volume_eq_prod ℝ (Homogenization.Vec 2)]
    rfl
  have hfInt : IntegrableOn f AVenhance.timeCube :=
    (hf.continuousOn.integrableOn_compact ThetaSpaceTime.thetaTimeClosedCell_compact).mono_set
      ThetaSpaceTime.thetaTimeCube_subset_closedCell
  have hfProd : Integrable f
      ((μ.restrict (Set.Ioo (0 : ℝ) 1)).prod (ν.restrict AVenhance.unitCube)) := by
    rw [hproductMeasure]
    exact hfInt
  have hprod := MeasureTheory.integral_prod f hfProd
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  calc
    (∫ p in AVenhance.timeCube, f p) =
        ∫ t in Set.Ioo (0 : ℝ) 1, ∫ x in AVenhance.unitCube, f (t, x) := by
          rw [← hproductMeasure]
          exact hprod
    _ = ∫ t in Set.Ioc (0 : ℝ) 1, ∫ x in AVenhance.unitCube, f (t, x) := by
          change (∫ t, (∫ x in AVenhance.unitCube, f (t, x)) ∂
              (μ.restrict (Set.Ioo (0 : ℝ) 1))) = _
          rw [htimeMeasure]

/-- Cauchy--Schwarz with a bounded coefficient on the space-time cell. -/
theorem theta_timeCube_integral_mul_bounded_le
    {f g a : ℝ × Homogenization.Vec 2 → ℝ} {M : ℝ}
    (hf : Continuous f) (hg : Continuous g) (ha : Continuous a)
    (hM : 0 ≤ M) (haM : ∀ p ∈ AVenhance.timeCube, |a p| ≤ M) :
    |∫ p in AVenhance.timeCube, f p * (a p * g p)| ≤
      M * Real.sqrt (∫ p in AVenhance.timeCube, f p ^ 2) *
        Real.sqrt (∫ p in AVenhance.timeCube, g p ^ 2) := by
  let μ : Measure (ℝ × Homogenization.Vec 2) := volume
  have hfg : Continuous (fun p => a p * g p) := ha.mul hg
  have hcs := theta_timeCube_integral_mul_abs_le hf hfg
  have hleftInt : IntegrableOn (fun p => (a p * g p) ^ 2) AVenhance.timeCube μ :=
    ((ha.mul hg).pow 2).continuousOn.integrableOn_compact
        ThetaSpaceTime.thetaTimeClosedCell_compact |>.mono_set
      ThetaSpaceTime.thetaTimeCube_subset_closedCell
  have hrightInt : IntegrableOn (fun p => M ^ 2 * g p ^ 2) AVenhance.timeCube μ :=
    (continuous_const.mul (hg.pow 2)).continuousOn.integrableOn_compact
      ThetaSpaceTime.thetaTimeClosedCell_compact |>.mono_set
          ThetaSpaceTime.thetaTimeCube_subset_closedCell
  have hmeas : MeasurableSet AVenhance.timeCube :=
    MeasurableSet.prod measurableSet_Ioo thetaTime_measurableSet_unitCube
  have hsq :
      (∫ p in AVenhance.timeCube, (a p * g p) ^ 2 ∂μ) ≤
        ∫ p in AVenhance.timeCube, M ^ 2 * g p ^ 2 ∂μ := by
    apply MeasureTheory.setIntegral_mono_on hleftInt hrightInt hmeas
    intro p hp
    have ha' : a p ^ 2 ≤ M ^ 2 := by
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg (a p)) hM).2 (haM p hp)
    calc
      (a p * g p) ^ 2 = a p ^ 2 * g p ^ 2 := by ring
      _ ≤ M ^ 2 * g p ^ 2 := mul_le_mul_of_nonneg_right ha' (sq_nonneg _)
  have hscale :
      (∫ p in AVenhance.timeCube, M ^ 2 * g p ^ 2 ∂μ) =
        M ^ 2 * (∫ p in AVenhance.timeCube, g p ^ 2 ∂μ) := by
    rw [MeasureTheory.integral_const_mul]
  have hsq' := hsq.trans_eq hscale
  have hradicand : 0 ≤ ∫ p in AVenhance.timeCube, g p ^ 2 := by
    exact MeasureTheory.setIntegral_nonneg hmeas (fun p hp => sq_nonneg (g p))
  have hroot := Real.sqrt_le_sqrt hsq'
  have hroot' : Real.sqrt (∫ p in AVenhance.timeCube, (a p * g p) ^ 2) ≤
      M * Real.sqrt (∫ p in AVenhance.timeCube, g p ^ 2) := by
    calc
      _ ≤ Real.sqrt (M ^ 2 * (∫ p in AVenhance.timeCube, g p ^ 2)) := hroot
      _ = M * Real.sqrt (∫ p in AVenhance.timeCube, g p ^ 2) := by
        rw [Real.sqrt_mul (sq_nonneg M), Real.sqrt_sq_eq_abs, abs_of_nonneg hM]
  calc
    |∫ p in AVenhance.timeCube, f p * (a p * g p)| ≤
        Real.sqrt (∫ p in AVenhance.timeCube, f p ^ 2) *
          Real.sqrt (∫ p in AVenhance.timeCube, (a p * g p) ^ 2) := hcs
    _ ≤ Real.sqrt (∫ p in AVenhance.timeCube, f p ^ 2) *
          (M * Real.sqrt (∫ p in AVenhance.timeCube, g p ^ 2)) :=
      mul_le_mul_of_nonneg_left hroot' (Real.sqrt_nonneg _)
    _ = M * Real.sqrt (∫ p in AVenhance.timeCube, f p ^ 2) *
          Real.sqrt (∫ p in AVenhance.timeCube, g p ^ 2) := by ring

end AVenhance.Infra.Section4

end
