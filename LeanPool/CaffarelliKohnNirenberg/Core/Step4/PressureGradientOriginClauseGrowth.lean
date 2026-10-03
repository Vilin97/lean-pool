/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseGauge
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGluedTimeBounds
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGaugeMajorantHolder
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientLargeCells

/-!
# Pressure oscillation on clipped origin windows

The pressure contribution to the slice bound is controlled by its spatial
`3/2` power mass and Hölder in time. The required mass exponent is
`13/2 - 15/(2κ)`, which yields the gradient mass exponent `5 - 6/κ`.
The separate large-radius estimate is supplied by
`pressure_gradient_origin_cylinder_large_cell_le` in `PressureGradientLargeCells`.
No estimate for the complete slice majorant is asserted here.
-/

public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- Hölder in a clipped time window for the pressure part of the doubled
slice estimate, retaining its spatial power mass on that same window. -/
theorem originClause_pressure_clipped_holder
    {P : ParabolicPoint → ℝ} {x : Vec3} {t r R : ℝ} (hr : 0 < r)
    (hm : AEStronglyMeasurable P
      ((volume.restrict (vec3Ball x (2 * r))).prod
        (volume.restrict (Ioc (t - r ^ 2) t ∩ Ioc (-R ^ 2) 0)))) :
    (∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-R^2) 0,
      (ENNReal.ofReal ((2*r) ^ (-1/2 : ℝ)) *
        eLpNorm (fun y => P (y,s)) (ENNReal.ofReal (3/2 : ℝ))
          (volume.restrict (vec3Ball x (2*r)))) ^ (6/5 : ℝ)) ≤
    ENNReal.ofReal ((2*r) ^ (-3/5 : ℝ)) *
      ((∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-R^2) 0,
        ∫⁻ y in vec3Ball x (2*r), ‖P (y,s)‖ₑ ^ (3/2 : ℝ)) ^ (4/5 : ℝ) *
        ENNReal.ofReal (r^2) ^ (1/5 : ℝ)) := by
  let W := Ioc (t-r^2) t ∩ Ioc (-R^2) 0
  let J := fun s => ∫⁻ y in vec3Ball x (2*r), ‖P (y,s)‖ₑ ^ (3/2 : ℝ)
  have hJ : AEMeasurable J (volume.restrict W) :=
    (hm.aemeasurable.enorm.pow_const (3/2 : ℝ)).lintegral_prod_left'
  have h2r : 0 < 2*r := by positivity
  have heq : ∀ᵐ s ∂volume.restrict W,
      (ENNReal.ofReal ((2*r) ^ (-1/2 : ℝ)) *
        eLpNorm (fun y => P (y,s)) (ENNReal.ofReal (3/2 : ℝ))
          (volume.restrict (vec3Ball x (2*r)))) ^ (6/5 : ℝ) =
      ENNReal.ofReal ((2*r) ^ (-3/5 : ℝ)) * J s ^ (4/5 : ℝ) := by
    filter_upwards [hm.prodMk_right] with s hs
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) ENNReal.ofReal_ne_top hs]
    norm_num only [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 3/2),
      show (1 / (3/2) : ℝ) = 2/3 by norm_num]
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 6/5),
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos h2r _),
      ← Real.rpow_mul h2r.le, ← ENNReal.rpow_mul]
    norm_num only [show (-1/2 : ℝ)*(6/5) = -3/5 by norm_num,
      show (2/3 : ℝ)*(6/5) = 4/5 by norm_num]
    rfl
  have hv : volume W ≤ ENNReal.ofReal (r^2) := by
    calc volume W ≤ volume (Ioc (t-r^2) t) := measure_mono inter_subset_left
         _ = _ := by rw [Real.volume_Ioc]; congr 1; ring_nf
  rw [lintegral_congr_ae heq, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply mul_le_mul' le_rfl
  have hh := lintegral_rpow_le_rpow_lintegral_mul_measure hJ
    (by norm_num : (0 : ℝ) < 4/5) (by norm_num : (4/5 : ℝ) < 1)
  simp only [Measure.restrict_apply_univ, show (1-4/5 : ℝ) = 1/5 by norm_num] at hh
  exact hh.trans (mul_le_mul' le_rfl (ENNReal.rpow_le_rpow hv (by norm_num)))

/-- The precise pressure mass exponent gives the growth exponent used for
`L^{6/5}` gradients, without a loss from time clipping. -/
theorem originClause_pressure_clipped_growth
    {P : ParabolicPoint → ℝ} {x : Vec3} {t r R κ : ℝ} {K : ℝ≥0∞}
    (hr : 0 < r)
    (hm : AEStronglyMeasurable P
      ((volume.restrict (vec3Ball x (2 * r))).prod
        (volume.restrict (Ioc (t - r ^ 2) t ∩ Ioc (-R ^ 2) 0))))
    (hpressure : (∫⁻ s in Ioc (t - r ^ 2) t ∩ Ioc (-R ^ 2) 0,
      ∫⁻ y in vec3Ball x (2 * r), ‖P (y, s)‖ₑ ^ (3 / 2 : ℝ)) ≤
        K * ENNReal.ofReal (r ^ (13 / 2 - 15 / (2 * κ)))) :
    (∫⁻ s in Ioc (t-r^2) t ∩ Ioc (-R^2) 0,
      (ENNReal.ofReal ((2*r) ^ (-1/2 : ℝ)) *
        eLpNorm (fun y => P (y,s)) (ENNReal.ofReal (3/2 : ℝ))
          (volume.restrict (vec3Ball x (2*r)))) ^ (6/5 : ℝ)) ≤
    (ENNReal.ofReal ((2 : ℝ)^(-3/5 : ℝ)) * K ^ (4/5 : ℝ)) *
      ENNReal.ofReal (r ^ (5 * (1 - (6/5 : ℝ)/κ))) := by
  have hb := originClause_pressure_clipped_holder hr hm
  have hmono := ENNReal.rpow_le_rpow hpressure (by norm_num : (0 : ℝ) ≤ 4/5)
  apply hb.trans
  calc
    _ ≤ ENNReal.ofReal ((2*r)^(-3/5 : ℝ)) *
        ((K * ENNReal.ofReal (r ^ (13/2 - 15/(2*κ)))) ^ (4/5 : ℝ) *
          ENNReal.ofReal (r^2) ^ (1/5 : ℝ)) :=
      mul_le_mul' le_rfl (mul_le_mul' hmono le_rfl)
    _ = _ := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 4/5),
        ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hr _),
        ENNReal.ofReal_rpow_of_pos (sq_pos_of_pos hr),
        ← Real.rpow_mul hr.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hr.le,
        ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (2 : ℝ)^(-3/5 : ℝ)),
        ← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
      have he : (-3/5 : ℝ) + (13/2 - 15/(2*κ))*(4/5) + 2*(1/5) =
          5*(1-(6/5 : ℝ)/κ) := by
        rw [div_mul_eq_div_div]
        ring_nf
      calc
        _ = (ENNReal.ofReal ((2 : ℝ)^(-3/5 : ℝ)) * K ^ (4/5 : ℝ)) *
            (ENNReal.ofReal (r ^ (-3/5 : ℝ)) *
              ENNReal.ofReal (r ^ ((13/2 - 15/(2*κ))*(4/5))) *
                ENNReal.ofReal (r ^ ((2 : ℝ)*(1/5)))) := by ring_nf
        _ = _ := by
          rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _),
            ← Real.rpow_add hr, ← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _),
            ← Real.rpow_add hr, he]

private theorem growth_pressure_measurable_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    AEStronglyMeasurable p (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
  obtain ⟨B, J, hbox, hcyl⟩ := exists_localBox_of_closure_subset hsol.1 hsol.2.1 hρ hsub
  exact (hsol.2.2.2.2.2.1 B J hbox).2.2.2.2.2.2.1.aestronglyMeasurable.mono_measure
    (Measure.restrict_mono_set volume hcyl)

/-- A single explicit pressure oscillation hypothesis gives the pressure
contribution's growth on every margin-small cell centred in the closed carrier.
The spatial mean is the same fixed carrier mean as in `originClauseGaugeMajorant`.
Measurability of that mean and of the local pressure slices follows from suitability. -/
theorem originClauseGauge_pressure_growth_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ κ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (Kp : ℝ≥0∞) (hKp : Kp < ⊤)
    (hpressure : ∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁),
      ∀ r : ℝ, 0 < r → r ≤ (1-R₁)/4 →
        (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-R₁^2) 0,
          ∫⁻ y in vec3Ball z.1 (2*r),
            ‖p (y,s) - average (volume.restrict (vec3Ball (0 : Vec3) R₁))
              (fun v => p (v,s))‖ₑ ^ (3/2 : ℝ)) ≤
          Kp * ENNReal.ofReal (r ^ (13/2 - 15/(2*κ))))
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁one : R₁ < 1) :
    let A := ENNReal.ofReal ((2 : ℝ)^(-3/5 : ℝ)) * Kp ^ (4/5 : ℝ)
    A < ⊤ ∧ ∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁),
      ∀ r : ℝ, 0 < r → r ≤ (1-R₁)/4 →
        (∫⁻ s in Ioc (z.2-r^2) z.2 ∩ Ioc (-R₁^2) 0,
          (ENNReal.ofReal ((2*r) ^ (-1/2 : ℝ)) *
            eLpNorm (fun y => p (y,s) -
              average (volume.restrict (vec3Ball (0 : Vec3) R₁)) (fun v => p (v,s)))
              (ENNReal.ofReal (3/2 : ℝ))
              (volume.restrict (vec3Ball z.1 (2*r)))) ^ (6/5 : ℝ)) ≤
          A * ENNReal.ofReal (r ^ (5 * (1 - (6/5 : ℝ)/κ))) := by
  refine ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hKp.ne), ?_⟩
  intro z hz r hr hmargin
  let W := Ioc (z.2-r^2) z.2 ∩ Ioc (-R₁^2) 0
  have hsmall : r ≤ (1-R₁)/2 := by linarith only [hmargin, hR₁one]
  have houter := growth_pressure_measurable_of_sws (z := z) hsol (by positivity : 0 < 2*r)
    ((originClauseGauge_doubleRadius_subset_unit hR₁ hR₁one hr hsmall hz).trans hdom)
  have hcarrier := growth_pressure_measurable_of_sws (z := ((0 : Vec3), 0)) hsol hR₁
    ((closure_parabolicCylinder_mono hR₁.le hR₁one.le).trans hdom)
  have hWouter : W ⊆ Ioc (z.2-(2*r)^2) z.2 := by
    intro s hs
    exact ⟨by nlinarith only [hs.1.1, sq_nonneg r], hs.1.2⟩
  have hpm : AEStronglyMeasurable p
      ((volume.restrict (vec3Ball z.1 (2*r))).prod (volume.restrict W)) := by
    rw [← originClauseRestrict_prod_eq]
    exact houter.mono_measure (Measure.restrict_mono_set volume (Set.prod_mono Subset.rfl hWouter))
  have hpc : AEStronglyMeasurable p
      ((volume.restrict (vec3Ball (0 : Vec3) R₁)).prod (volume.restrict W)) := by
    rw [← originClauseRestrict_prod_eq]
    apply hcarrier.mono_measure
    apply Measure.restrict_mono_set volume
    simpa only [parabolicCylinder, zero_sub] using
      (Set.prod_mono (Subset.rfl : vec3Ball (0 : Vec3) R₁ ⊆ vec3Ball (0 : Vec3) R₁)
        (inter_subset_right : W ⊆ Ioc (-R₁^2) 0))
  have hmean : AEStronglyMeasurable
      (fun s => average (volume.restrict (vec3Ball (0 : Vec3) R₁)) (fun v => p (v,s)))
      (volume.restrict W) := by
    simp_rw [average_eq]
    exact hpc.prod_swap.integral_prod_right'.const_smul
      (((volume : Measure Vec3).restrict (vec3Ball (0 : Vec3) R₁)).real Set.univ)⁻¹
  exact originClause_pressure_clipped_growth
    (P := fun w => p w - average (volume.restrict (vec3Ball (0 : Vec3) R₁))
      (fun v => p (v,w.2))) (x := z.1) (t := z.2) (R := R₁) (κ := κ) (K := Kp)
    hr (hpm.sub hmean.comp_snd)
    (hpressure z hz r hr hmargin)

end CKN.Core.Step4
