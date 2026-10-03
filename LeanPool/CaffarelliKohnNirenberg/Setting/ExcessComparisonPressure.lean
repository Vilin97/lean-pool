/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.ExcessComparisonCore

/-! Pressure-side comparisons for the Tsai excess quantities. -/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration


noncomputable section

namespace CKN

private theorem sws_integrable_pressure_power_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ))
      (parabolicCylinder z.1 z.2 r) volume := by
  have hfin := sws_pressure_integral_lt_top hsol hr hsub
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hr hsub
  obtain ⟨-, -, hpmeas, -, -, -, -, -, -⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  have hmeas : AEStronglyMeasurable
      (fun w => |p w| ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
    have hcont : Continuous (fun a : ℝ => |a| ^ (3 / 2 : ℝ)) := by
      exact (Real.continuous_rpow_const (by norm_num)).comp continuous_abs
    exact hcont.comp_aestronglyMeasurable
      (hpmeas.mono_measure (Measure.restrict_mono hcyl le_rfl))
  have hfin' : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))) ≠ ⊤ := by
    have hfin'' := ne_of_lt hfin
    convert hfin'' using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  exact (lintegral_ofReal_ne_top_iff_integrable hmeas
    (Filter.Eventually.of_forall fun w => Real.rpow_nonneg
      (abs_nonneg _) _)).mp hfin'
private theorem sws_integrable_pressure_on_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    IntegrableOn p (parabolicCylinder z.1 z.2 r) volume := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hr hsub
  obtain ⟨-, -, hpmeas, -, -, -, -, -, -⟩ :=
    hsol.2.2.2.2.2.1 Ω' J hbox
  have hpS : AEStronglyMeasurable p
      (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    hpmeas.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hp3 := sws_integrable_pressure_power_on_cylinder hsol hr hsub
  have hp3' : Integrable (fun w => ‖p w‖ ^ (3 / 2 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
    have hp3'' : Integrable (fun w => |p w| ^ (3 / 2 : ℝ))
        (volume.restrict (parabolicCylinder z.1 z.2 r)) := hp3
    simpa only [Real.norm_eq_abs] using hp3''
  let _ : IsFiniteMeasure (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
    refine ⟨?_⟩
    simpa only [Measure.restrict_apply_univ] using
      (volume_parabolicCylinder_lt_top (x := z.1) (t := z.2) (r := r))
  have hp1 : Integrable (fun w => ‖p w‖ ^ (1 : ℝ))
      (volume.restrict (parabolicCylinder z.1 z.2 r)) :=
    integrable_norm_rpow_of_le hpS (p := (1 : ℝ)) (q := (3 / 2 : ℝ))
      (by norm_num) (by norm_num) (by norm_num) hp3'
  change Integrable p (volume.restrict (parabolicCylinder z.1 z.2 r))
  refine ⟨hpS, ?_⟩
  have hp1' : Integrable (fun w => ‖p w‖)
      (volume.restrict (parabolicCylinder z.1 z.2 r)) := by
    convert hp1 using 1
    funext w
    rw [Real.rpow_one]
  change (∫⁻ w in parabolicCylinder z.1 z.2 r, ‖p w‖ₑ) < ⊤
  have h := hp1'.hasFiniteIntegral
  change (∫⁻ w in parabolicCylinder z.1 z.2 r, ‖‖p w‖‖ₑ) < ⊤ at h
  simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs, abs_abs,
    abs_of_nonneg (norm_nonneg _)] using h

private lemma scalar_spatial_excess_lintegral_bound
    {p : ParabolicPoint → ℝ} {x : Vec3} {t r : ℝ}
    (hr : 0 < r)
    (hp : IntegrableOn p (parabolicCylinder x t r) volume)
    (hpp : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ))
      (parabolicCylinder x t r) volume) :
    (∫⁻ w in parabolicCylinder x t r, ENNReal.ofReal
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ)) ≤
      2 ^ (3 / 2 : ℝ) * (∫⁻ w in parabolicCylinder x t r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ∧
    IntegrableOn (fun w => |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ))
      (parabolicCylinder x t r) volume := by
  let B : Set Vec3 := vec3Ball x r
  let T : Set ℝ := Ioc (t - r ^ 2) t
  have hp' : Integrable p ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    change IntegrableOn p (vec3Ball x r ×ˢ Ioc (t-r^2) t)
      ((volume : Measure Vec3).prod (volume : Measure ℝ))
    exact hp
  have hpp' : Integrable (fun w => |p w| ^ (3 / 2 : ℝ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    rw [Measure.prod_restrict]
    change IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ))
      (vec3Ball x r ×ˢ Ioc (t-r^2) t)
      ((volume : Measure Vec3).prod (volume : Measure ℝ))
    exact hpp
  have hpmeas := hp'.aestronglyMeasurable
  have hppmeas := hpp'.aestronglyMeasurable
  have havg : AEStronglyMeasurable
      (fun s : ℝ => average (volume.restrict B)
        (fun y : Vec3 => p (y,s))) (volume.restrict T) := by
    have hi := hpmeas.prod_swap.integral_prod_right'
    convert hi.const_smul ((volume B).toReal⁻¹) using 1
    · funext s
      rw [MeasureTheory.average_eq (μ := volume.restrict B)]
      simp only [MeasureTheory.measureReal_restrict_apply_univ]
      rfl
  have hcoord : AEStronglyMeasurable
      (fun w : Vec3 × ℝ => p w - average (volume.restrict B)
        (fun y : Vec3 => p (y,w.2)))
      ((volume.restrict B).prod (volume.restrict T)) := by
    have hsnd := Measure.quasiMeasurePreserving_snd
      (μ := volume.restrict B) (ν := volume.restrict T)
    have hm := havg.comp_quasiMeasurePreserving hsnd
    change AEStronglyMeasurable ((fun w : Vec3 × ℝ => p w) -
      (fun w : Vec3 × ℝ => average (volume.restrict B)
        (fun y : Vec3 => p (y,w.2))))
      ((volume.restrict B).prod (volume.restrict T))
    have hpmeas' : AEStronglyMeasurable (fun w : Vec3 × ℝ => p w)
        ((volume.restrict B).prod (volume.restrict T)) := hpmeas
    have hdiff := hpmeas'.sub hm
    change AEStronglyMeasurable (fun w : Vec3 × ℝ => p w -
      average (volume.restrict B) (fun y : Vec3 => p (y,w.2)))
      ((volume.restrict B).prod (volume.restrict T)) at hdiff
    exact hdiff
  have hmeas : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    have hc : Continuous (fun a : ℝ => |a| ^ (3 / 2 : ℝ)) := by
      exact (Real.continuous_rpow_const (by norm_num)).comp continuous_abs
    have hh := (hc.comp_aestronglyMeasurable hcoord).aemeasurable
    have hbase := hh.ennreal_ofReal
    have hbase' := hbase.congr (Filter.Eventually.of_forall fun w =>
      (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)).symm)
    simpa [spatialAverage, B] using hbase'
  have hslice := hp'.prod_left_ae
  have hpslice := hpp'.prod_left_ae
  have hgood : ∀ᵐ s ∂volume.restrict T, (∫⁻ y in B,
      ENNReal.ofReal |p (y,s) - spatialAverage x r s p| ^ (3 / 2 : ℝ)) ≤
      2 ^ (3 / 2 : ℝ) * (∫⁻ y in B,
        ENNReal.ofReal |p (y,s)| ^ (3 / 2 : ℝ)) := by
    filter_upwards [hslice, hpslice] with s hs hps
    have hps' : IntegrableOn (fun y => |p (y,s) - 0| ^ (3 / 2 : ℝ)) B volume := by
      change Integrable (fun y => |p (y,s) - 0| ^ (3 / 2 : ℝ)) (volume.restrict B)
      simpa [abs_sub_comm] using hps
    have hh := ball_setLaverage_abs_sub_spatialAverage_rpow_le
      (p := (3 / 2 : ℝ)) (c := (0 : ℝ)) (by norm_num) hr hs hps'
    rw [MeasureTheory.setLAverage_eq, MeasureTheory.setLAverage_eq] at hh
    have hh' : (∫⁻ y in B, ENNReal.ofReal
        |p (y,s) - spatialAverage x r s p| ^ (3 / 2 : ℝ)) / volume B ≤
        2 ^ (3 / 2 : ℝ) * ((∫⁻ y in B, ENNReal.ofReal
          |p (y,s)| ^ (3 / 2 : ℝ)) / volume B) := by
      convert hh using 1
      · rw [show B = vec3Ball x r by rfl]
        apply congrArg (fun h => h / volume (vec3Ball x r))
        apply lintegral_congr
        intro y
        rw [← ofReal_norm]
        simp only [Real.norm_eq_abs]
      · congr 2
        rw [show B = vec3Ball x r by rfl]
        apply lintegral_congr
        intro y
        rw [← ofReal_norm]
        norm_num [Real.norm_eq_abs]
    have hvpos : 0 < volume B := volume_vec3Ball_pos hr
    have hvtop : volume B < ∞ := volume_vec3Ball_lt_top (x := x) (r := r)
    calc
      _ = (∫⁻ y in B, ENNReal.ofReal
          |p (y,s) - spatialAverage x r s p| ^ (3 / 2 : ℝ)) /
          volume B * volume B := by rw [ENNReal.div_mul_cancel hvpos.ne' hvtop.ne]
      _ ≤ (2 ^ (3 / 2 : ℝ) * ((∫⁻ y in B, ENNReal.ofReal
          |p (y,s)| ^ (3 / 2 : ℝ)) / volume B)) * volume B :=
        mul_le_mul_of_nonneg_right hh' (by positivity)
      _ = 2 ^ (3 / 2 : ℝ) * (∫⁻ y in B, ENNReal.ofReal
          |p (y,s)| ^ (3 / 2 : ℝ)) := by
        rw [mul_assoc, ENNReal.div_mul_cancel hvpos.ne' hvtop.ne]
  have hprod : (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ)) ≤
      2 ^ (3 / 2 : ℝ) * (∫⁻ w in B ×ˢ T,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) := by
    change (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≤ _
    have hF := setLIntegral_prod_symm
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ)) (s := B) (t := T)
      (fun w : Vec3 × ℝ => ENNReal.ofReal
        |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ)) (by
          rw [← Measure.prod_restrict]
          exact hmeas)
    have hppmeas' : AEMeasurable (fun w : Vec3 × ℝ => ENNReal.ofReal
        |p w| ^ (3 / 2 : ℝ)) ((volume.restrict B).prod (volume.restrict T)) := by
      have h := hppmeas.aemeasurable.ennreal_ofReal
      exact h.congr (Filter.Eventually.of_forall fun w =>
        (ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)).symm)
    have hG := setLIntegral_prod_symm
      (μ := (volume : Measure Vec3)) (ν := (volume : Measure ℝ)) (s := B) (t := T)
      (fun w : Vec3 × ℝ => ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) (by
          rw [← Measure.prod_restrict]
          exact hppmeas')
    calc
      _ = ∫⁻ s in T, ∫⁻ y in B, ENNReal.ofReal
          |p (y,s) - spatialAverage x r s p| ^ (3 / 2 : ℝ) := by
            simpa only [Prod.fst, Prod.snd] using hF
      _ ≤ ∫⁻ s in T, 2 ^ (3 / 2 : ℝ) * (∫⁻ y in B,
          ENNReal.ofReal |p (y,s)| ^ (3 / 2 : ℝ)) := lintegral_mono_ae hgood
      _ = 2 ^ (3 / 2 : ℝ) * (∫⁻ s in T, ∫⁻ y in B,
          ENNReal.ofReal |p (y,s)| ^ (3 / 2 : ℝ)) := by
            rw [lintegral_const_mul' _ _ (by norm_num)]
      _ = 2 ^ (3 / 2 : ℝ) * (∫⁻ w in B ×ˢ T,
          ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) := by
            congr 1
            exact hG.symm
  have hbound : (∫⁻ w in parabolicCylinder x t r, ENNReal.ofReal
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ)) ≤
      2 ^ (3 / 2 : ℝ) * (∫⁻ w in parabolicCylinder x t r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) := by
    rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
    change (∫⁻ w in B ×ˢ T, ENNReal.ofReal
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≤ _
    exact hprod
  have hrealmeas : AEStronglyMeasurable (fun w : Vec3 × ℝ =>
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ))
      ((volume.restrict B).prod (volume.restrict T)) := by
    have hc : Continuous (fun a : ℝ => |a| ^ (3 / 2 : ℝ)) := by
      exact (Real.continuous_rpow_const (by norm_num)).comp continuous_abs
    exact hc.comp_aestronglyMeasurable hcoord
  have hbaseTop0 : (∫⁻ w in B ×ˢ T,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ)) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≠ ⊤ := by
    rw [← Measure.prod_restrict]
    exact (lintegral_ofReal_ne_top_iff_integrable
      hppmeas
      (Filter.Eventually.of_forall fun w =>
        Real.rpow_nonneg (abs_nonneg _) _)).2 hpp'
  have hbaseTop : (∫⁻ w in B ×ˢ T,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≠ ⊤ := by
    convert hbaseTop0 using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (p w)) (by norm_num)]
  have hboundTop : (∫⁻ w in B ×ˢ T,
      ENNReal.ofReal |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≠ ⊤ := by
    exact ne_of_lt (lt_of_le_of_lt hprod
      (ENNReal.mul_lt_top
        (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofNat_ne_top)
        hbaseTop.lt_top))
  have hrealmeas' : AEStronglyMeasurable (fun w : Vec3 × ℝ =>
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (B ×ˢ T)) := by
    rw [← Measure.prod_restrict]
    exact hrealmeas
  have hboundTop' : (∫⁻ w in B ×ˢ T,
      ENNReal.ofReal (|p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ)) ∂
        ((volume : Measure Vec3).prod (volume : Measure ℝ))) ≠ ⊤ := by
    convert hboundTop using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  have hIntProd : Integrable (fun w : Vec3 × ℝ =>
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (B ×ˢ T)) := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      hrealmeas' (Filter.Eventually.of_forall fun w =>
        Real.rpow_nonneg (abs_nonneg _) _)).mp
    exact hboundTop'
  have hIntCyl : IntegrableOn (fun w =>
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ))
      (parabolicCylinder x t r) volume := by
    rw [parabolicCylinder, volume_parabolicPoint_eq_prod]
    change Integrable (fun w : Vec3 × ℝ =>
      |p w - spatialAverage x r w.2 p| ^ (3 / 2 : ℝ))
      (((volume : Measure Vec3).prod (volume : Measure ℝ)).restrict (B ×ˢ T))
    exact hIntProd
  exact ⟨hbound, hIntCyl⟩
private theorem scalar_pressure_excess_le
    {p : ParabolicPoint → ℝ} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r)
    (hp : IntegrableOn p (parabolicCylinder z.1 z.2 r) volume)
    (hpp : IntegrableOn (fun w => |p w| ^ (3 / 2 : ℝ))
      (parabolicCylinder z.1 z.2 r) volume) :
    tsaiPressureExcess p z r ≤ 2 ^ (3 / 2 : ℝ) * delta p z r ^ (3 : ℕ) := by
  obtain ⟨hbound, hInt⟩ := scalar_spatial_excess_lintegral_bound hr hp hpp
  have hleftTop : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (|p w - spatialAverage z.1 r w.2 p| ^ (3 / 2 : ℝ))) ≠ ⊤ := by
    exact (lintegral_ofReal_ne_top_iff_integrable
      hInt.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w =>
        Real.rpow_nonneg (abs_nonneg _) _)).2 hInt
  have hleftTop' : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal |p w - spatialAverage z.1 r w.2 p| ^ (3 / 2 : ℝ)) ≠ ⊤ := by
    convert hleftTop using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  have hbaseTop : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ⊤ := by
    have h := (lintegral_ofReal_ne_top_iff_integrable
      hpp.aestronglyMeasurable
      (Filter.Eventually.of_forall fun w =>
        Real.rpow_nonneg (abs_nonneg _) _)).2 hpp
    convert h using 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  have hrightTop : (2 : ℝ≥0∞) ^ (3 / 2 : ℝ) *
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)) ≠ ⊤ :=
    ENNReal.mul_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofNat_ne_top)
      hbaseTop
  have hbound' := (ENNReal.toReal_le_toReal hleftTop' hrightTop).2 hbound
  rw [ENNReal.toReal_mul] at hbound'
  have hc : ((2 : ℝ≥0∞) ^ (3 / 2 : ℝ)).toReal =
      (2 : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofNat]
  rw [hc] at hbound'
  have hbound'' : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (|p w - spatialAverage z.1 r w.2 p| ^ (3 / 2 : ℝ))).toReal ≤
      2 ^ (3 / 2 : ℝ) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))).toReal := by
    convert hbound' using 1
    · apply congrArg ENNReal.toReal
      apply lintegral_congr
      intro w
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
    · apply congrArg (fun x => (2 : ℝ) ^ (3 / 2 : ℝ) * x)
      apply congrArg ENNReal.toReal
      apply lintegral_congr
      intro w
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  unfold tsaiPressureExcess
  rw [setIntegral_eq_toReal_setLIntegral_of_nonneg hInt
    (Filter.Eventually.of_forall fun w =>
      Real.rpow_nonneg (abs_nonneg _) _)]
  have hbaseEq : (∫⁻ w in parabolicCylinder z.1 z.2 r,
      ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))).toReal =
      (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal := by
    congr 1
    apply lintegral_congr
    intro w
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
  have hscale : r⁻¹ ^ (2 : ℕ) = r ^ (-2 : ℝ) := by
    rw [Real.rpow_neg hr.le]
    norm_num [inv_pow]
  calc
    r⁻¹ ^ (2 : ℕ) *
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (|p w - spatialAverage z.1 r w.2 p| ^ (3 / 2 : ℝ))).toReal ≤
      r⁻¹ ^ (2 : ℕ) *
        (2 ^ (3 / 2 : ℝ) *
          (∫⁻ w in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal (|p w| ^ (3 / 2 : ℝ))).toReal) :=
      mul_le_mul_of_nonneg_left hbound'' (by positivity)
    _ = 2 ^ (3 / 2 : ℝ) * delta p z r ^ (3 : ℕ) := by
      rw [hscale]
      rw [hbaseEq]
      have hdelta : r ^ (-2 : ℝ) *
          (∫⁻ w in parabolicCylinder z.1 z.2 r,
            ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal =
          delta p z r ^ (3 : ℕ) := (delta_cube_eq p z r hr).symm
      calc
        r ^ (-2 : ℝ) * (2 ^ (3 / 2 : ℝ) *
            (∫⁻ w in parabolicCylinder z.1 z.2 r,
              ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) =
            2 ^ (3 / 2 : ℝ) * (r ^ (-2 : ℝ) *
              (∫⁻ w in parabolicCylinder z.1 z.2 r,
                ENNReal.ofReal |p w| ^ (3 / 2 : ℝ)).toReal) := by ring
        _ = _ := by rw [hdelta]

theorem tsaiPressureExcess_le_two_three_halves_delta_cube
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    tsaiPressureExcess p z r ≤
      2 ^ (3 / 2 : ℝ) * delta p z r ^ (3 : ℕ) := by
  exact scalar_pressure_excess_le hr
    (sws_integrable_pressure_on_cylinder hsol hr hsub)
    (sws_integrable_pressure_power_on_cylinder hsol hr hsub)

theorem tsaiPhi_le_two_gamma_add_two_delta_sq
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    tsaiPhi u p z r ≤ 2 * gamma u z r + 2 * delta p z r ^ (2 : ℕ) := by
  have hC := tsaiVelocityExcess_le_eight_gamma_cube hsol hr hsub
  have hD := tsaiPressureExcess_le_two_three_halves_delta_cube hsol hr hsub
  have hC0 : 0 ≤ tsaiVelocityExcess u z r := by
    unfold tsaiVelocityExcess
    exact mul_nonneg (sq_nonneg (r⁻¹))
      (integral_nonneg fun w =>
        pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
  have hD0 : 0 ≤ tsaiPressureExcess p z r := by
    unfold tsaiPressureExcess
    exact mul_nonneg (sq_nonneg (r⁻¹))
      (integral_nonneg fun w => Real.rpow_nonneg (abs_nonneg _) _)
  have hg0 : 0 ≤ gamma u z r := by
    unfold gamma
    positivity
  have hd0 : 0 ≤ delta p z r := by
    unfold delta
    positivity
  have h1 : tsaiVelocityExcess u z r ^ (1 / 3 : ℝ) ≤
      (8 * gamma u z r ^ (3 : ℕ)) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow hC0 hC (by norm_num)
  have h2 : tsaiPressureExcess p z r ^ (2 / 3 : ℝ) ≤
      (2 ^ (3 / 2 : ℝ) * delta p z r ^ (3 : ℕ)) ^ (2 / 3 : ℝ) :=
    Real.rpow_le_rpow hD0 hD (by norm_num)
  have h1' : (8 * gamma u z r ^ (3 : ℕ)) ^ (1 / 3 : ℝ) =
      2 * gamma u z r := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
    rw [show (8 : ℝ) ^ (1 / 3 : ℝ) = 2 by norm_num [Real.rpow_def_of_pos]]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hg0]
    norm_num
  have h2' : (2 ^ (3 / 2 : ℝ) * delta p z r ^ (3 : ℕ)) ^ (2 / 3 : ℝ) =
      2 * delta p z r ^ (2 : ℕ) := by
    rw [Real.mul_rpow (by positivity) (by positivity)]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul hd0]
    norm_num
  unfold tsaiPhi
  linarith only [h1, h2, h1', h2']
private theorem tsaiPsi_le_C3_gamma_of_integrability
    {u : ParabolicPoint → Vec3} {z : ParabolicPoint} {r : ℝ}
    (hr : 0 < r)
    (hu : IntegrableOn u (parabolicCylinder z.1 z.2 r) volume)
    (hu3 : IntegrableOn (fun w => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume) :
    r * vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w) ≤
      (4 * Real.pi / 3) ^ (-1 / 3 : ℝ) * gamma u z r := by
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ
    (fun _ : Fin 3 => ℝ)).symm
  have hL : (L : Vec3 → L2Vec3) = WithLp.toLp 2 := by
    funext v
    exact rfl
  have hLint : IntegrableOn (fun w => L (u w))
      (parabolicCylinder z.1 z.2 r) volume :=
    L.toContinuousLinearMap.integrable_comp hu.integrable
  have hL3 : IntegrableOn (fun w => ‖L (u w)‖ ^ (3 : ℕ))
      (parabolicCylinder z.1 z.2 r) volume := by
    simpa only [vec3EuclideanNorm_eq_l2, hL] using hu3
  have hJ0 := setAverage_norm_rpow_le (μ := (volume : Measure ParabolicPoint))
    (s := parabolicCylinder z.1 z.2 r) (f := fun w => L (u w)) (p := (3 : ℝ))
    (by norm_num) (volume_parabolicCylinder_pos hr)
    (volume_parabolicCylinder_lt_top (x := z.1) (t := z.2) (r := r)) hLint
    (by simpa [Real.rpow_natCast] using hL3)
  have hmap : L (⨍ w in parabolicCylinder z.1 z.2 r, u w) =
      ⨍ w in parabolicCylinder z.1 z.2 r, L (u w) := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
    change L ((volume (parabolicCylinder z.1 z.2 r)).toReal⁻¹ •
        ∫ w in parabolicCylinder z.1 z.2 r, u w) =
      (volume (parabolicCylinder z.1 z.2 r)).toReal⁻¹ •
        ∫ w in parabolicCylinder z.1 z.2 r, L (u w)
    rw [map_smul, L.integral_comp_comm]
  rw [← hmap] at hJ0
  have hJ1 : ‖L (⨍ w in parabolicCylinder z.1 z.2 r, u w)‖ ^ (3 : ℝ) ≤
      (volume (parabolicCylinder z.1 z.2 r)).toReal⁻¹ *
        (∫ w in parabolicCylinder z.1 z.2 r, ‖L (u w)‖ ^ (3 : ℝ)) := by
    rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq] at hJ0
    rw [MeasureTheory.setAverage_eq]
    simpa [MeasureTheory.measureReal_def, MeasureTheory.measureReal_restrict_apply_univ,
      smul_eq_mul, div_eq_mul_inv] using hJ0
  have hJ : vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w) ^ (3 : ℕ) ≤
      (∫ w in parabolicCylinder z.1 z.2 r,
        vec3EuclideanNorm (u w) ^ (3 : ℕ)) /
        (volume (parabolicCylinder z.1 z.2 r)).toReal := by
    convert hJ1 using 1 <;> simp [vec3EuclideanNorm_eq_l2, hL,
      div_eq_mul_inv]
    all_goals ring
  have hvol : (volume (parabolicCylinder z.1 z.2 r)).toReal =
      (4 * Real.pi / 3) * r ^ 5 := by
    rw [volume_parabolicCylinder, volume_vec3Ball_eq, ENNReal.toReal_mul,
      ENNReal.toReal_mul, ENNReal.toReal_pow]
    rw [ENNReal.toReal_ofReal hr.le,
      ENNReal.toReal_ofReal (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    ring
  have hI : 0 ≤ ∫ w in parabolicCylinder z.1 z.2 r,
      vec3EuclideanNorm (u w) ^ (3 : ℕ) :=
    integral_nonneg (fun w => pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
  have hgamma : gamma u z r ^ (3 : ℕ) =
      r ^ (-2 : ℝ) * (∫ w in parabolicCylinder z.1 z.2 r,
        vec3EuclideanNorm (u w) ^ (3 : ℕ)) := by
    rw [gamma_cube_eq u z r hr]
    have h := setIntegral_eq_toReal_setLIntegral_of_nonneg hu3
      (Filter.Eventually.of_forall fun w =>
        pow_nonneg (vec3EuclideanNorm_nonneg _) 3)
    have h' : (∫⁻ w in parabolicCylinder z.1 z.2 r,
        ENNReal.ofReal (vec3EuclideanNorm (u w) ^ (3 : ℕ))).toReal =
        (∫⁻ w in parabolicCylinder z.1 z.2 r,
          ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)).toReal := by
      congr 1
      apply lintegral_congr
      intro w
      rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3]
      norm_num [ENNReal.rpow_natCast]
    have hEq := h.trans h'
    rw [hEq]
  have hcube : (r * vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w)) ^ (3 : ℕ) ≤
      ((4 * Real.pi / 3) ^ (-1 / 3 : ℝ) * gamma u z r) ^ (3 : ℕ) := by
    rw [mul_pow]
    have hc : ((4 * Real.pi / 3) ^ (-1 / 3 : ℝ)) ^ (3 : ℕ) =
        (4 * Real.pi / 3) ^ (-1 : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    rw [mul_pow, hc, hgamma]
    have h := mul_le_mul_of_nonneg_left hJ (by positivity : 0 ≤ r ^ 3)
    rw [hvol] at h
    calc
      r ^ 3 * vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w) ^ 3 ≤
          r ^ 3 * ((∫ w in parabolicCylinder z.1 z.2 r,
            vec3EuclideanNorm (u w) ^ 3) /
            ((4 * Real.pi / 3) * r ^ 5)) := h
      _ = (4 * Real.pi / 3) ^ (-1 : ℝ) *
          (r ^ (-2 : ℝ) * (∫ w in parabolicCylinder z.1 z.2 r,
            vec3EuclideanNorm (u w) ^ 3)) := by
            rw [Real.rpow_neg (by positivity : 0 ≤ (4 * Real.pi / 3 : ℝ)),
              Real.rpow_neg hr.le]
            norm_num [inv_pow]
            field_simp [ne_of_gt hr, Real.pi_ne_zero]
  have hleft : 0 ≤ r * vec3EuclideanNorm (⨍ w in parabolicCylinder z.1 z.2 r, u w) :=
    mul_nonneg hr.le (vec3EuclideanNorm_nonneg _)
  have hgamma0 : 0 ≤ gamma u z r := by unfold gamma; positivity
  have hright : 0 ≤ (4 * Real.pi / 3) ^ (-1 / 3 : ℝ) * gamma u z r :=
    mul_nonneg (by positivity) hgamma0
  exact (pow_le_pow_iff_left₀ hleft hright (by norm_num : (3 : ℕ) ≠ 0)).mp hcube

theorem tsaiPsi_le_C3_gamma
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder z.1 z.2 r) ⊆ spaceTimeSet Ω I) :
    tsaiPsi u z r ≤ (4 * Real.pi / 3) ^ (-1 / 3 : ℝ) * gamma u z r := by
  exact tsaiPsi_le_C3_gamma_of_integrability hr
    (tsai_integrable_velocity_on_cylinder hsol hr hsub)
    (tsai_integrable_velocity_cube_on_cylinder hsol hr hsub)

end CKN
