/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedSelection
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientHGCloserCellsMeanMorrey
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientGaugeMajorantExponents
public import LeanPool.CaffarelliKohnNirenberg.Core.Endgame.CarrierRestriction

/-! # Morrey membership of the fixed near-force source

Local force integrability on a finite fixed carrier gives the target source
Morrey class. The cutoff is bounded by one, and no spatial supremum bound
on the force is used.
-/

public section

section

/-! # Morrey membership of the fixed force-free pressure source

The localization cylinder is inside the prescribed velocity and gradient
carrier. Suitability controls its fixed spatial mean through the local energy
bound, and the force-free tensor estimate then gives the target source class.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey CKN.Foundation.Heat
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-- The fixed pressure localization lies in the original radius ball. -/
theorem fixed_pressure_cylinder_subset_ball
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R) :
    parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R ⊆ Metric.ball z₀ R := by
  rw [metricBall_eq_parabolicBall]
  intro z hz
  have hs : 0 < R ^ 2 := sq_pos_of_pos hR
  exact ⟨hz.1, by nlinarith only [hz.2.1, hs], by nlinarith only [hz.2.2, hs]⟩

/-- The fixed force-free centred source has finite target Morrey seminorm
under the velocity and gradient hypotheses of the pressure transfer. -/
theorem fixed_centred_source_morrey_lt_top_of_sws
    {τ q : ℝ} (hq : 5 / 2 < q) (hτ : 25 / 3 ≤ τ) (hτhi : τ ≤ 25)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I)
    (hu : morreyVecMem 3 τ (Metric.ball z₀ R) u)
    (hDu : ∀ i : Fin 3, morreyVecMem 2 (25 / 8 : ℝ)
      (Metric.ball z₀ R) (fun z => Du z i)) (i : Fin 3) :
    let η := mollifiedBallCutoff z₀.1 hR
    let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η)
      u Du (sourceSliceCentredMean z₀.1 R u)
    morreyNorm (6 / 5 : ℝ) (min ((1 / τ + 8 / 25)⁻¹) q)
      ((parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R).indicator (fun w => V w i)) < ⊤ := by
  dsimp only
  let Q := parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R
  let B := vec3Ball z₀.1 R
  let J := Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)
  let η := mollifiedBallCutoff z₀.1 hR
  have hbox : localBox Ω I B J := localBox_of_parabolic_ball hR hdom
  have hQ : MeasurableSet Q := measurableSet_parabolicCylinder _ _ _
  have hQB : Q ⊆ Metric.ball z₀ R := fixed_pressure_cylinder_subset_ball z₀ hR
  have hQbox : Q ⊆ B ×ˢ J := by
    intro z hz
    have ht := hQB hz
    rw [metricBall_eq_parabolicBall] at ht
    exact ht
  have hτ3 : 3 ≤ τ := by linarith only [hτ]
  have hU (j : Fin 3) : morreyNorm 3 τ (Q.indicator (fun w => u w j)) < ⊤ :=
    (morreyNorm_le_morreyBallNorm (by norm_num) hτ3 _).trans_lt
      ((morreyVecMem_mono_carrier (by norm_num) hQB hu) j)
  have hD (j k : Fin 3) : morreyNorm 2 (25 / 8 : ℝ)
      (Q.indicator (fun w => Du w j k)) < ⊤ :=
    (morreyNorm_le_morreyBallNorm (by norm_num) (by norm_num) _).trans_lt
      ((morreyVecMem_mono_carrier (by norm_num) hQB (hDu j)) k)
  have hW := pressure_centred_velocity_morrey_data_of_sws hτ3 hsol hbox hQ hQbox hU
  have hdata := hsol.2.2.2.2.2.1 B J hbox
  have hUa (j : Fin 3) : AEMeasurable (Q.indicator (fun w => u w j)) volume :=
    (aemeasurable_indicator_iff hQ).mpr
      (((measurable_pi_apply j).comp_aemeasurable hdata.1.aemeasurable).mono_measure
        (Measure.restrict_mono_set volume hQbox))
  have hDa (j k : Fin 3) : AEMeasurable (Q.indicator (fun w => Du w j k)) volume :=
    (aemeasurable_indicator_iff hQ).mpr
      (((measurable_pi_apply k).comp_aemeasurable
        ((measurable_pi_apply j).comp_aemeasurable hdata.2.1.aemeasurable)).mono_measure
        (Measure.restrict_mono_set volume hQbox))
  have hη : AEMeasurable (fun w : ParabolicPoint => η w.1) volume :=
    ((mollifiedBallCutoff_smooth z₀.1 hR).continuous.measurable.comp measurable_fst).aemeasurable
  have hdη (j : Fin 3) : AEMeasurable (fun w : ParabolicPoint => spatialDeriv η j w.1) volume :=
    ((contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth z₀.1 hR)
      j).continuous.measurable.comp
      measurable_fst).aemeasurable
  have he (x : Vec3) : |η x| ≤ |(1 : ℝ)| := by
    rw [abs_of_nonneg (mollifiedBallCutoff_nonneg z₀.1 hR x), abs_one]
    exact mollifiedBallCutoff_le_one z₀.1 hR x
  have hd (j : Fin 3) (x : Vec3) : |spatialDeriv η j x| ≤ |cutoffGradientConstant / R| :=
    ((abs_apply_le_vecEuclideanNorm (classicalGradient η x) j).trans
      (mollifiedBallCutoff_gradient_bound z₀.1 hR x)).trans (le_abs_self _)
  apply pressure_centred_tensor_source_morrey_lt_top
    (S := Q) (η := η) (dη := spatialDeriv η) (u := u) (Du := Du)
    (c := sourceSliceCentredMean z₀.1 R u)
    (z₀ := (z₀.1, z₀.2 + R ^ 2 / 4)) hτ
    (le_trans (by norm_num) (endgame_kappa_ge hτ hq))
    (endgame_kappa_le (by linarith only [hτ]) hτhi) (min_le_left _ _) hR
    (Subset.rfl : Q ⊆ Q) hη hdη he hd hUa
    (fun j => (hW j).1) hDa hU (fun j => (hW j).2) hD i

end CKN.Core.Step4
end

end

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-- The fixed near-force source has finite target Morrey seminorm directly
from the suitable solution's local force integrability. -/
theorem fixed_near_force_source_morrey_lt_top_of_sws
    {κ q : ℝ} (hκ : 6 / 5 ≤ κ) (hκq : κ ≤ q)
    {Ω : Set Vec3} {I : Set ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I) (j : Fin 3) :
    morreyNorm (6 / 5 : ℝ) κ
      ((parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R).indicator
        (fun w => mollifiedBallCutoff z₀.1 hR w.1 * f w j)) < ⊤ := by
  let Q := parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R
  let B := vec3Ball z₀.1 R
  let J := Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2)
  let η := mollifiedBallCutoff z₀.1 hR
  have hbox : localBox Ω I B J := localBox_of_parabolic_ball hR hdom
  have hQ : MeasurableSet Q := measurableSet_parabolicCylinder _ _ _
  have hQbox : Q ⊆ B ×ˢ J := by
    intro z hz
    have ht := fixed_pressure_cylinder_subset_ball z₀ hR hz
    rw [metricBall_eq_parabolicBall] at ht
    exact ht
  have hdata := hsol.2.2.2.2.2.1 B J hbox
  have hfq : MemLp (fun w => f w j) (ENNReal.ofReal q) (volume.restrict Q) :=
    (hdata.2.2.2.2.2.2.2.1.eval j).mono_measure (Measure.restrict_mono_set volume hQbox)
  have hQfinite : volume Q < ⊤ := by
    rw [volume_parabolicCylinder]
    exact ENNReal.mul_lt_top (Integration.volume_vec3Ball_lt_top) ENNReal.ofReal_lt_top
  let : IsFiniteMeasure (volume.restrict Q) := isFiniteMeasure_restrict.mpr hQfinite.ne
  have hfk : MemLp (fun w => f w j) (ENNReal.ofReal κ) (volume.restrict Q) :=
    hfq.mono_exponent (ENNReal.ofReal_le_ofReal hκq)
  have hη : Measurable (fun w : ParabolicPoint => η w.1) :=
    (mollifiedBallCutoff_smooth z₀.1 hR).continuous.measurable.comp measurable_fst
  have hprod : MemLp (fun w => η w.1 * f w j) (ENNReal.ofReal κ) (volume.restrict Q) := by
    apply hfk.of_le (hη.aestronglyMeasurable.mul hfk.aestronglyMeasurable)
    exact Eventually.of_forall fun w => by
      have he : ‖η w.1‖ ≤ 1 :=
        (abs_of_nonneg (mollifiedBallCutoff_nonneg z₀.1 hR w.1)).le.trans
          (mollifiedBallCutoff_le_one z₀.1 hR w.1)
      exact (norm_mul (η w.1) (f w j)).le.trans
        (mul_le_of_le_one_left (norm_nonneg _) he)
  exact pressure_source_morrey_lt_top_of_memLp (by norm_num) hκ
    ((memLp_indicator_iff_restrict hQ).mpr hprod)

end CKN.Core.Step4
