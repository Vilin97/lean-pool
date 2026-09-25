/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSFinal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszSelection

/-! # Measurability of the fixed localized pressure sources

The spatial mean is taken on the fixed localization ball. Both sources are
restricted to the fixed time window and spatial ball before the completed
operators are selected.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal BigOperators Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- Suitability gives joint measurability of the localized force-free source
and near-force source, including their time restriction. -/
theorem fixed_pressure_sources_aemeasurable_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    let η := mollifiedBallCutoff z.1 hρ
    let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η)
      u Du (sourceSliceCentredMean z.1 ρ u)
    ∀ i : Fin 3,
      AEMeasurable ((parabolicCylinder z.1 z.2 ρ).indicator (fun w => V w i)) volume ∧
      AEMeasurable ((parabolicCylinder z.1 z.2 ρ).indicator (fun w => η w.1 * f w i)) volume := by
  dsimp only
  let B := vec3Ball z.1 ρ
  let J := Ioc (z.2 - ρ ^ 2) z.2
  let S : Set ParabolicPoint := parabolicCylinder z.1 z.2 ρ
  let η := mollifiedBallCutoff z.1 hρ
  obtain ⟨Ω', J', hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hdata := hsol.2.2.2.2.2.1 Ω' J' hbox
  have hSsub : S ⊆ spaceTimeSet Ω' J' := prod_mono hball htime
  have hu := hdata.1.aemeasurable.mono_measure (Measure.restrict_mono_set volume hSsub)
  have hd := hdata.2.1.aemeasurable.mono_measure (Measure.restrict_mono_set volume hSsub)
  have hf := hdata.2.2.2.1.aemeasurable.mono_measure (Measure.restrict_mono_set volume hSsub)
  have hU (i : Fin 3) : AEMeasurable (fun w => u w i) (volume.restrict S) :=
    (measurable_pi_apply i).comp_aemeasurable hu
  have hD (i j : Fin 3) : AEMeasurable (fun w => Du w i j) (volume.restrict S) :=
    (measurable_pi_apply j).comp_aemeasurable ((measurable_pi_apply i).comp_aemeasurable hd)
  have hF (i : Fin 3) : AEMeasurable (fun w => f w i) (volume.restrict S) :=
    (measurable_pi_apply i).comp_aemeasurable hf
  have hprod : (volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J) =
      (volume.restrict B).prod (volume.restrict J) := by
    rw [volume_eq_prod, ← Measure.prod_restrict]
  have hc (i : Fin 3) : AEMeasurable
      (fun w : ParabolicPoint => sourceSliceCentredMean z.1 ρ u w.2 i) (volume.restrict S) := by
    have hUi : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w i)
        ((volume.restrict B).prod (volume.restrict J)) := by
      rw [← hprod]
      exact (hU i).aestronglyMeasurable
    have hm := hUi.prod_swap.integral_prod_right'.aemeasurable
    have ha : AEMeasurable (fun s => sourceSliceCentredMean z.1 ρ u s i)
        (volume.restrict J) := by
      simp only [sourceSliceCentredMean, average_eq, smul_eq_mul]
      exact hm.const_mul _
    have hl := ha.comp_quasiMeasurePreserving
      (Measure.quasiMeasurePreserving_snd (μ := volume.restrict B))
    change AEMeasurable (fun w : Vec3 × ℝ => sourceSliceCentredMean z.1 ρ u w.2 i)
      ((volume : Measure (Vec3 × ℝ)).restrict (B ×ˢ J))
    rw [hprod]
    exact hl
  have hη : AEMeasurable (fun w : ParabolicPoint => η w.1) (volume.restrict S) :=
    ((mollifiedBallCutoff_smooth z.1 hρ).continuous.measurable.comp measurable_fst).aemeasurable
  have hdη (j : Fin 3) : AEMeasurable (fun w : ParabolicPoint => spatialDeriv η j w.1)
      (volume.restrict S) :=
    ((contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth z.1 hρ) j).continuous.measurable.comp
      measurable_fst).aemeasurable
  intro i
  constructor
  · apply (aemeasurable_indicator_iff (measurableSet_parabolicCylinder _ _ _)).mpr
    change AEMeasurable (fun w : ParabolicPoint => ∑ j,
      (η w.1 * Du w i j * (u w j - sourceSliceCentredMean z.1 ρ u w.2 j) +
        spatialDeriv η j w.1 * u w i * (u w j - sourceSliceCentredMean z.1 ρ u w.2 j)))
      (volume.restrict S)
    convert Finset.aemeasurable_sum Finset.univ (fun j _ =>
      ((hη.mul (hD i j)).mul ((hU j).sub (hc j))).add
        (((hdη j).mul (hU i)).mul ((hU j).sub (hc j)))) using 1
    ext w
    simp only [Finset.sum_apply, Pi.add_apply, Pi.mul_apply, Pi.sub_apply]
  · exact (aemeasurable_indicator_iff (measurableSet_parabolicCylinder _ _ _)).mpr (hη.mul (hF i))

end CKN.Core.Step4
