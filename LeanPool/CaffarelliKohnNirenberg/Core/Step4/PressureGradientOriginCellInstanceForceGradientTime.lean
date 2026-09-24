/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceHarmonicForceTime

/-!
# Time integrability of the direct force-gradient contribution

Both cutoff source norms and the spatial force mass in
`eq:pressure-gradient-morrey` are time integrable on any interior local box.
-/

@[expose] public section

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
  have hη : AEStronglyMeasurable (mollifiedBallCutoff x hρ) volume := (mollifiedBallCutoff_smooth x hρ).continuous.aestronglyMeasurable
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
      (fun y => by rw [abs_of_nonneg (mollifiedBallCutoff_nonneg x hρ y)]; exact mollifiedBallCutoff_le_one x hρ y)
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
