/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.AdamsBridge
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Morrey.Indicator
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedOriginTransfer
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsShellTime

/-!
# Time integrals on clipped origin cells

The time integrals in `prop:bootstrap` use the spatial intersection of a cell
with the origin carrier and the corresponding intersection of backward time
windows. Tonelli identifies these integrals with the carrier-restricted
space-time mass without extending any data outside the carrier.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey

noncomputable section
namespace CKN.Core.Step4

/-- The time integral of the powers of spatial slice norms equals the
space-time power integral on an arbitrary product box. -/
theorem origin_time_slice_norm_power_eq
    {P : ℝ} (hP : 0 < P) {g : Vec3 × ℝ → ℝ}
    {E : Set Vec3} {J : Set ℝ}
    (hg : AEMeasurable g (volume.restrict (E ×ˢ J))) :
    (∫⁻ s in J, eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P)
      (volume.restrict E) ^ P) =
      ∫⁻ w in E ×ˢ J, ENNReal.ofReal |g w| ^ P := by
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (E ×ˢ J) =
      (volume.restrict E).prod (volume.restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  rw [hprod] at hg ⊢
  rw [lintegral_prod_symm _ (by simpa only [Real.enorm_eq_ofReal_abs] using hg.enorm.pow_const P)]
  apply lintegral_congr_ae
  filter_upwards [hg.aestronglyMeasurable.prodMk_right] with s hs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hP).ne' ENNReal.ofReal_ne_top hs,
    ENNReal.toReal_ofReal hP.le, ← ENNReal.rpow_mul,
    one_div_mul_cancel hP.ne', ENNReal.rpow_one]
  simp only [Real.enorm_eq_ofReal_abs]

/-- Spatial slice norms are measurable on the chosen time window whenever
the scalar field is measurable on the product box. -/
theorem origin_time_slice_norm_aemeasurable
    {P : ℝ} (hP : 0 < P) {g : Vec3 × ℝ → ℝ}
    {E : Set Vec3} {J : Set ℝ}
    (hg : AEMeasurable g (volume.restrict (E ×ˢ J))) :
    AEMeasurable (fun s => eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P)
      (volume.restrict E)) (volume.restrict J) := by
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (E ×ˢ J) =
      (volume.restrict E).prod (volume.restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  rw [hprod] at hg
  have hm := ((hg.enorm.pow_const P).lintegral_prod_left').pow_const (1 / P)
  apply hm.congr
  filter_upwards [hg.aestronglyMeasurable.prodMk_right] with s hs
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ENNReal.ofReal_pos.mpr hP).ne' ENNReal.ofReal_ne_top hs,
    ENNReal.toReal_ofReal hP.le]

/-- Clipped time and spatial slice norms have exactly the power integral
of the origin-carrier indicator, for every cell centre and radius. -/
theorem origin_clipped_slice_norm_power_eq
    {P : ℝ} (hP : 0 < P) {g : Vec3 × ℝ → ℝ}
    (R : ℝ) (hg : AEMeasurable g
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 R))) (x : Vec3) (t r : ℝ) :
    (∫⁻ s in Ioc (t - r ^ 2) t ∩ Ioc (-(R ^ 2)) 0,
      eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P)
        (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R)) ^ P) =
      cylinderPowerIntegral P
        ((parabolicCylinder (0 : Vec3) 0 R).indicator g) (x, t) r := by
  have hS : MeasurableSet (parabolicCylinder (0 : Vec3) 0 R) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have hgeom : parabolicCylinder x t r ∩ parabolicCylinder (0 : Vec3) 0 R =
      (vec3Ball x r ∩ vec3Ball (0 : Vec3) R) ×ˢ
        (Ioc (t - r ^ 2) t ∩ Ioc (-(R ^ 2)) 0) := by
    ext w
    change ((w.1 ∈ vec3Ball x r ∧ w.2 ∈ Ioc (t - r ^ 2) t) ∧
      (w.1 ∈ vec3Ball 0 R ∧ w.2 ∈ Ioc (0 - R ^ 2) 0)) ↔ _
    simp only [zero_sub]
    change ((_ ∧ _) ∧ (_ ∧ _)) ↔ ((_ ∧ _) ∧ (_ ∧ _))
    tauto
  have hgbox : AEMeasurable g (volume.restrict
      ((vec3Ball x r ∩ vec3Ball (0 : Vec3) R) ×ˢ
        (Ioc (t - r ^ 2) t ∩ Ioc (-(R ^ 2)) 0))) := by
    apply hg.mono_measure
    apply Measure.restrict_mono_set
    rw [← hgeom]
    exact inter_subset_right
  refine (origin_time_slice_norm_power_eq hP hgbox).trans ?_
  have h := Morrey.cylinderPowerIntegral_indicator hP hS
    (fun w => g (w.1, w.2)) (x, t) r
  have h' : cylinderPowerIntegral P
      ((parabolicCylinder (0 : Vec3) 0 R).indicator g) (x, t) r =
      ∫⁻ w in (vec3Ball x r ∩ vec3Ball (0 : Vec3) R) ×ˢ
        (Ioc (t - r ^ 2) t ∩ Ioc (-(R ^ 2)) 0), ENNReal.ofReal |g w| ^ P := by
    rw [hgeom] at h
    exact h
  exact h'.symm

/-- A source Morrey bound gives the exact clipped time-power growth used
by the origin data clause. The constant is independent of the cell. -/
theorem origin_clipped_slice_norm_time_bound
    {P κ R : ℝ} {K : ℝ≥0∞} {g : Vec3 × ℝ → ℝ}
    (hP : 0 < P) (hg : AEMeasurable g
      (volume.restrict (parabolicCylinder (0 : Vec3) 0 R)))
    (hK : morreyNorm P κ ((parabolicCylinder (0 : Vec3) 0 R).indicator g) ≤ K)
    (x : Vec3) (t : ℝ) {r : ℝ} (hr : 0 < r) :
    (∫⁻ s in Ioc (t - r ^ 2) t ∩ Ioc (-(R ^ 2)) 0,
      eLpNorm (fun y => g (y, s)) (ENNReal.ofReal P)
        (volume.restrict (vec3Ball x r ∩ vec3Ball (0 : Vec3) R)) ^ P) ≤
      K ^ P * ENNReal.ofReal (r ^ (5 * (1 - P / κ))) := by
  rw [origin_clipped_slice_norm_power_eq hP R hg x t r]
  have hS : MeasurableSet (parabolicCylinder (0 : Vec3) 0 R) :=
    (vec3Ball_measurable _ _).prod measurableSet_Ioc
  have h := cylinderPowerIntegral_le_morreyNorm_pow (q := κ) hP
    ((aemeasurable_indicator_iff hS).mpr hg) (z := (x, t)) hr
  refine h.trans ?_
  rw [ENNReal.ofReal_rpow_of_pos hr]
  exact (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hK hP.le)).trans_eq (mul_comm _ _)

end CKN.Core.Step4
