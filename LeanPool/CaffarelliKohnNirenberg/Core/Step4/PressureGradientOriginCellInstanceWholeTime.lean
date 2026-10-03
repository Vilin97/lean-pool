/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceHarmonicForceTime
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTermTime

/-!
# Compact-time integrability of the complete centered slice majorant

Every term of the explicit majorant in `eq:pressure-gradient-morrey` is
integrable in time at a fixed interior origin radius, on every local box of
the solution interval.
-/

public section

section

/-!
# Time integrability of the direct force-gradient contribution

Both cutoff source norms and the spatial force mass in
`eq:pressure-gradient-morrey` are time integrable on any interior local box.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The direct force-gradient slot is time integrable from suitability,
for arbitrary fixed real coefficients. -/
theorem origin_force_gradient_integrable_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q ρ : ℝ} {x : Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hρ : 0 < ρ)
    (hbox : localBox Ω I (vec3Ball x ρ) J) (C D : ℝ) :
    Integrable (fun s => sliceForceGradientBound C D x hρ f s) (volume.restrict J) := by
  have hf (j : Fin 3) : AEStronglyMeasurable (fun w : Vec3 × ℝ => f w j)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact (hsol.2.2.2.2.1 (vec3Ball x ρ) J hbox j).aestronglyMeasurable
  have hη : AEStronglyMeasurable (mollifiedBallCutoff x hρ) volume := (mollifiedBallCutoff_smooth
    x hρ).continuous.aestronglyMeasurable
  have hs := (subset_tsupport _).trans (pressure_cutoff_support_subset_ball x hρ)
  have hcut (j : Fin 3) := origin_cutoff_product_aestronglyMeasurable
    (vec3Ball_measurable x ρ) (hf j) hη hs
  have hnorm (j : Fin 3) : AEMeasurable (fun s => eLpNorm
      (fun y => mollifiedBallCutoff x hρ y * f (y, s) j)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) (volume.restrict J) := by
    have hg := (hcut j).aemeasurable
    have hprod : (volume : Measure (Vec3 × ℝ)).restrict (univ ×ˢ J) =
        (volume : Measure Vec3).prod (volume.restrict J) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [← hprod] at hg
    simpa only [Measure.restrict_univ] using
      origin_time_slice_norm_aemeasurable (by norm_num : (0 : ℝ) < 6 / 5) hg
  have hnormInt (j : Fin 3) : Integrable (fun s => lpNorm
      (fun y => mollifiedBallCutoff x hρ y * f (y, s) j)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) (volume.restrict J) := by
    have hfin := lintegral_cutoff_force_slice_eLpNorm_lt_top_of_sws hsol hbox hη
      (fun y => by rw [abs_of_nonneg (mollifiedBallCutoff_nonneg x hρ y)]; exact
        mollifiedBallCutoff_le_one x hρ y)
      hs j
    exact integrable_toReal_of_lintegral_ne_top (hnorm j) hfin.ne
  have hdata := hsol.2.2.2.2.2.1 (vec3Ball x ρ) J hbox
  let : IsFiniteMeasure ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact CKN.Core.Step3.local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  have hfLp : MemLp (fun w : Vec3 × ℝ => f w) (ENNReal.ofReal q)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact hdata.2.2.2.2.2.2.2.1
  have hfi := hfLp.integrable (ENNReal.one_le_ofReal.mpr
    (by linarith only [hsol.2.2.2.1] : (1 : ℝ) ≤ q))
  let L := (PiLp.continuousLinearEquiv (2 : ℝ≥0∞) ℝ (fun _ : Fin 3 => ℝ)).symm
  have hfE : Integrable (fun w : Vec3 × ℝ => vec3EuclideanNorm (f w))
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    have hh : Integrable (fun w : Vec3 × ℝ => ‖L (f w)‖)
        ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) :=
      (L.toContinuousLinearMap.integrable_comp hfi).norm
    simpa only [vec3EuclideanNorm_eq_l2, show (L : Vec3 → L2Vec3) = WithLp.toLp 2 by rfl] using hh
  have hsum : Integrable (fun s => ∑ j : Fin 3, lpNorm
      (fun y => mollifiedBallCutoff x hρ y * f (y, s) j)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) (volume.restrict J) :=
    integrable_finsetSum Finset.univ (fun j _ => hnormInt j)
  exact (hsum.const_mul C).add ((hfE.integral_prod_right.const_mul D).mul_const _)

end CKN.Core.Step4
end

end

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

private theorem integrable_ofReal_toReal {J : Set ℝ} {F : ℝ → ℝ}
    (hF : Integrable F (volume.restrict J)) :
    Integrable (fun s => (ENNReal.ofReal (F s)).toReal) (volume.restrict J) := by
  apply (hF.sup (integrable_zero ℝ ℝ (volume.restrict J))).congr
  exact Eventually.of_forall fun s => by
    change max (F s) 0 = (ENNReal.ofReal (F s)).toReal
    by_cases hs : 0 ≤ F s
    · rw [max_eq_left hs, ENNReal.toReal_ofReal hs]
    · have hn := (lt_of_not_ge hs).le
      rw [max_eq_right hn, ENNReal.ofReal_eq_zero.mpr hn, ENNReal.toReal_zero]

/-- Suitability gives time integrability of the complete fixed-origin slice
majorant on every local box with its source ball. -/
theorem origin_slice_majorant_integrable_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q ρ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hρ : 0 < ρ)
    (hbox : localBox Ω I (vec3Ball 0 ρ) J) :
    Integrable (fun s => (originSliceGradientMajorant u Du p f ((0 : Vec3), 0) hρ s).toReal)
      (volume.restrict J) := by
  have hsource := origin_centered_source_norm_time_obligations hsol hρ hbox
  have hd := hsol.2.2.2.2.2.1 (vec3Ball 0 ρ) J hbox
  have hpm := origin_time_slice_norm_aemeasurable (by norm_num : (0 : ℝ) < 3 / 2)
    hd.2.2.1.aemeasurable
  have hp : Integrable (fun s => lpNorm (fun y => p (y, s)) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (vec3Ball 0 ρ))) (volume.restrict J) :=
    integrable_toReal_of_lintegral_ne_top hpm
      (lintegral_pressure_slice_eLpNorm_lt_top_of_sws hsol hbox).ne
  have hE := origin_tensor_energy_integrable_on_local_box hsol hρ hbox
  have hF := origin_harmonic_force_integrable_on_local_box hsol hρ hbox
  have hH := (((hp.add (hE.const_mul (9 * max czP1OperatorConstant 0))).add hF).const_mul
    (1000 * harmonicInteriorDisplayConstant)).mul_const (ρ ^ (-1 / 2 : ℝ))
  have hdirect := origin_force_gradient_integrable_on_local_box hsol hρ hbox
    czGradientOperatorConstant sliceForceGradientConstant
  have htotal := ((hsource.2.2.const_mul (ENNReal.ofReal czGradientOperatorConstant).toReal).add
    (integrable_ofReal_toReal hH)).add (integrable_ofReal_toReal hdirect)
  apply htotal.congr
  filter_upwards [hsource.2.1] with s hs
  have hsrc : ENNReal.ofReal czGradientOperatorConstant * originCenteredSourceNorm 0 hρ u Du s ≠ ⊤
    :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs
  unfold originCenteredSourceNorm at hsrc
  unfold originSliceGradientMajorant
  dsimp only
  rw [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨hsrc, ENNReal.ofReal_ne_top⟩)
    ENNReal.ofReal_ne_top,
    ENNReal.toReal_add hsrc ENNReal.ofReal_ne_top, ENNReal.toReal_mul]
  rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball hρ]
  rfl

end CKN.Core.Step4
