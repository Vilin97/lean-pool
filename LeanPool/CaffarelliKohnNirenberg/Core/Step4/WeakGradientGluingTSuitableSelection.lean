/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.WeakGradientGluingTMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSFinal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSymmetricGeometry
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientSymmetricCell
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSWS

/-! # One measurable pressure gradient on the inner symmetric carrier

Suitability on the doubled parabolic ball supplies spatial slice derivatives
on a larger ball. Measurable selection fixes one field on the inner ball
before any smaller cells or quantitative estimates are considered.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Heat CKN.Foundation.Euclidean

noncomputable section
namespace CKN.Core.Step4

/-- The larger auxiliary cylinder lies in the doubled parabolic ball. -/
theorem closure_gradient_selection_cylinder_subset_doubled_ball
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R) :
    closure (parabolicCylinder z₀.1 (z₀.2 + R ^ 2 / 4) (3 * R / 2)) ⊆
      Metric.ball z₀ (2 * R) := by
  rw [closure_parabolicCylinder (by positivity : 0 < 3 * R / 2),
    metricBall_eq_parabolicBall]
  intro z hz
  have hx : vec3EuclideanNorm (z.1 - z₀.1) ≤ 3 * R / 2 := hz.1
  have ht₁ := hz.2.1
  have ht₂ := hz.2.2
  have hs : 0 < R ^ 2 := sq_pos_of_pos hR
  refine ⟨?_, ?_, ?_⟩
  · change vec3EuclideanNorm (z.1 - z₀.1) < 2 * R
    linarith only [hx, hR]
  · nlinarith only [ht₁, hs]
  · nlinarith only [ht₂, hs]

/-- Suitability fixes a single jointly measurable spatial weak pressure
gradient over the entire time interval of the inner symmetric ball. -/
theorem exists_measurable_inner_pressure_gradient_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (z₀ : ParabolicPoint) {R : ℝ} (hR : 0 < R)
    (hdom : Metric.ball z₀ (2 * R) ⊆ spaceTimeSet Ω I) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      ∀ᵐ s ∂volume.restrict (Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)),
        ∀ i : Fin 3,
          LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball z₀.1 (R / 2)) volume ∧
          HasWeakPartialDerivOn (vec3Ball z₀.1 (R / 2)) i
            (fun y => p (y, s)) (fun y => Dp (y, s) i) := by
  let J : Set ℝ := Ioo (z₀.2 - R ^ 2 / 4) (z₀.2 + R ^ 2 / 4)
  have hJsub : J ⊆ Ioo (z₀.2 - R ^ 2) (z₀.2 + R ^ 2) := by
    intro s hs
    have hsq : 0 ≤ R ^ 2 := sq_nonneg R
    exact ⟨by dsimp [J] at hs; linarith only [hs.1, hsq],
      by dsimp [J] at hs; linarith only [hs.2, hsq]⟩
  have hBsub : vec3Ball z₀.1 (3 * R / 4) ⊆ vec3Ball z₀.1 R := by
    intro x hx
    change vec3EuclideanNorm (x - z₀.1) < R
    change vec3EuclideanNorm (x - z₀.1) < 3 * R / 4 at hx
    exact hx.trans_le (by linarith only [hR])
  have hpBig := pressure_integrable_on_of_suitable_local_box hsol
    (Core.Endgame.localBox_of_parabolic_ball hR hdom) hBsub
  have hp : IntegrableOn p (vec3Ball z₀.1 (3 * R / 4) ×ˢ J) volume :=
    hpBig.mono_set (prod_mono Subset.rfl hJsub)
  have hρ : 0 < 3 * R / 2 := by positivity
  have hsub := (closure_gradient_selection_cylinder_subset_doubled_ball z₀ hR).trans hdom
  have hslices := centredSWS_selected_gradient_ae
    (1000 * harmonicInteriorDisplayConstant) (max czP1OperatorConstant 0)
    sliceForceGradientConstant le_rfl (le_max_right _ _) (le_max_left _ _) le_rfl
    hsol (z := (z₀.1, z₀.2 + R ^ 2 / 4)) hρ hsub
  have htime : J ⊆ Ioc (z₀.2 + R ^ 2 / 4 - (3 * R / 2) ^ 2)
      (z₀.2 + R ^ 2 / 4) := by
    intro s hs
    have hsq : 0 ≤ R ^ 2 := sq_nonneg R
    exact ⟨by dsimp [J] at hs; nlinarith only [hs.1, hsq], hs.2.le⟩
  have heq : euclideanBall z₀.1 (3 * R / 2 / 2) = vec3Ball z₀.1 (3 * R / 4) := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by positivity : 0 < 3 * R / 2 / 2)]
    congr 1
    ring
  have hslice (k : Fin 3) : ∀ᵐ s ∂volume.restrict J, ∃ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball z₀.1 (3 * R / 4)) volume ∧
      HasWeakPartialDerivOn (vec3Ball z₀.1 (3 * R / 4)) k (fun x => p (x, s)) g := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset htime hslices] with s hs
    obtain ⟨D, hloc, _hmem, hweak, _hbound⟩ := hs
    exact ⟨fun x => D x k, by simpa only [heq] using hloc k,
      by simpa only [heq] using hweak k⟩
  have hUB : closure (vec3Ball z₀.1 (R / 2)) ⊆ vec3Ball z₀.1 (3 * R / 4) := by
    rw [closure_vec3Ball (by positivity : 0 < R / 2)]
    intro x hx
    change vec3EuclideanNorm (x - z₀.1) ≤ R / 2 at hx
    change vec3EuclideanNorm (x - z₀.1) < 3 * R / 4
    exact lt_of_le_of_lt hx (by linarith only [hR])
  obtain ⟨Dp, hDp, hweak⟩ := exists_measurable_weakGradient_on_time_union
    (isOpen_vec3Ball _ _) (isOpen_vec3Ball _ _)
    (CKN.Foundation.Parabolic.isCompact_closure_vec3Ball (by positivity : 0 < R / 2)) hUB
    (J := fun _ : ℕ => J) (fun _ => measurableSet_Ioo) (by simp only [iUnion_const])
    (fun _ => hp) hslice
  exact ⟨Dp, hDp, hweak.mono (fun _ hs i => ⟨(hs i).1, (hs i).2.1⟩)⟩

end CKN.Core.Step4
