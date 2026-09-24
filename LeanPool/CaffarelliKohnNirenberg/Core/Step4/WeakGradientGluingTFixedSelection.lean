/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTFixedField

/-! # Fixed jointly measurable pressure decomposition on an inner ball

One pressure field and two matrices of completed Riesz representatives are
chosen from suitability. Their measurable remainder represents the classical
harmonic and far-force gradient on almost every slice of the target carrier.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

/-- The fixed radius localization with shifted top time lies in the doubled
parabolic ball containing the suitable solution. -/
theorem closure_fixed_pressure_cylinder_subset_doubled_ball
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R) :
    closure (parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R) ⊆
      Metric.ball z₀ (2 * R) := by
  rw [closure_parabolicCylinder hR, metricBall_eq_parabolicBall]
  intro z hz
  have hx : vec3EuclideanNorm (z.1 - z₀.1) ≤ R := hz.1
  have ht₁ := hz.2.1
  have ht₂ := hz.2.2
  have hs : 0 < R ^ 2 := sq_pos_of_pos hR
  refine ⟨?_, ?_, ?_⟩
  · change vec3EuclideanNorm (z.1 - z₀.1) < 2 * R
    linarith only [hx, hR]
  · nlinarith only [ht₁, hs]
  · nlinarith only [ht₂, hs]

/-- Suitability yields a single measurable weak pressure gradient and its
fixed signed completed-Riesz decomposition, with a measurable remainder
identified with the classical harmonic and far-force gradient on slices. -/
theorem exists_measurable_fixed_pressure_decomposition_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I) :
    let η := mollifiedBallCutoff z₀.1 hR
    let c := sourceSliceCentredMean z₀.1 R u
    let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η) u Du c
    let Q := parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) R
    let J := Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)
    ∃ (Dp : ParabolicPoint → Vec3) (T Tforce : Fin 3 → Fin 3 → ParabolicPoint → ℝ)
      (H : Fin 3 → ParabolicPoint → ℝ),
      Measurable Dp ∧ (∀ j i, Measurable (T j i)) ∧
      (∀ j i, Measurable (Tforce j i)) ∧ (∀ i, Measurable (H i)) ∧
      (∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball z₀.1 (R / 2)) volume ∧
        HasWeakPartialDerivOn (vec3Ball z₀.1 (R / 2)) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) ∧
      (∀ j i, ∀ᵐ s ∂volume, (fun y => T j i (y, s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
          (fun y => Q.indicator (fun w => V w j) (y, s))) ∧
      (∀ j i, ∀ᵐ s ∂volume, (fun y => Tforce j i (y, s)) =ᵐ[volume]
        rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i)
          (fun y => Q.indicator (fun w => η w.1 * f w j) (y, s))) ∧
      (∀ i w, Dp w i = -(∑ j, T j i w) + H i w + ∑ j, Tforce j i w) ∧
      (∀ᵐ s ∂volume.restrict J, ∀ i : Fin 3,
        (fun y => H i (y, s)) =ᵐ[volume.restrict (vec3Ball z₀.1 (R / 2))]
        fun y => classicalGradient (harmonicPressurePart η u c p s + pressureP8 η f s) y i) := by
  dsimp only
  let z : ParabolicPoint := (z₀.1, z₀.2 + R ^ 2 / 4)
  let J := Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)
  have hsub : closure (parabolicCylinder z.1 z.2 R) ⊆ spaceTimeSet Ω I :=
    (closure_fixed_pressure_cylinder_subset_doubled_ball z₀ hR).trans hdom
  obtain ⟨Dp, hm, hd⟩ := exists_measurable_inner_pressure_gradient_of_sws hsol z₀ hR hdom
  obtain ⟨T, F, ht, hf, hti, hfi⟩ := exists_measurable_fixed_riesz_fields_of_sws hsol hR hsub
  let H : Fin 3 → ParabolicPoint → ℝ := fun i w => Dp w i + (∑ j, T j i w) - ∑ j, F j i w
  have hH (i : Fin 3) : Measurable (H i) :=
    ((measurable_pi_apply i |>.comp hm).add
      (Finset.measurable_sum _ (fun j _ => ht j i))).sub
      (Finset.measurable_sum _ (fun j _ => hf j i))
  have hJsub : J ⊆ Ioc (z.2 - R ^ 2) z.2 := by
    intro s hs
    have hsq : 0 ≤ R ^ 2 := sq_nonneg R
    exact ⟨by dsimp [J, z] at *; linarith only [hs.1, hsq], hs.2.le⟩
  have heq := ae_fixed_remainder_eq_classical_gradient hsol hR hsub
    measurableSet_Ioo hJsub hd hti hfi
  refine ⟨Dp, T, F, H, hm, ht, hf, hH, hd, hti, hfi, ?_, heq⟩
  intro i w
  dsimp only [H]
  ring

end CKN.Core.Step4
