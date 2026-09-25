/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.WeakGradientGluingTRieszIdentification
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSFinal
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientSymmetricGeometry

/-! # Concrete pressure-gradient identification from suitability

One fixed spatial localization gives the force-free centred source, a near
force source, and the smooth sum of the harmonic and far force potentials.
Every locally integrable weak pressure derivative agrees with their signed
completed-operator decomposition on almost every slice.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal BigOperators Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

private theorem fixed_pressure_representation
    {u : ParabolicPoint → Vec3} {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {c : ℝ → Vec3} {V : ParabolicPoint → Vec3} {x₀ : Vec3} {ρ s : ℝ} (hρ : 0 < ρ)
    (hi : pressureP1 (mollifiedBallCutoff x₀ hρ) u c p f s
      =ᵐ[volume.restrict (vec3Ball x₀ (ρ / 2))]
      fun x => ∑ j, pressureNewtonianDerivativePotential j (fun y => V (y, s) j) x) :
    (fun y => p (y, s)) =ᵐ[volume.restrict (vec3Ball x₀ (ρ / 2))] fun x =>
      (∑ j, pressureNewtonianDerivativePotential j (fun y => V (y, s) j) x) +
        ((harmonicPressurePart (mollifiedBallCutoff x₀ hρ) u c p s +
          pressureP8 (mollifiedBallCutoff x₀ hρ) f s) x -
          ∑ j, pressureNewtonianDerivativePotential j
            (fun y => mollifiedBallCutoff x₀ hρ y * f (y, s) j) x) := by
  have hinner : vec3Ball x₀ (ρ / 2) ⊆ euclideanBall x₀ (13 * ρ / 20) := by
    rw [CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by positivity : 0 < 13 * ρ / 20)]
    intro x hx
    change vec3EuclideanNorm (x - x₀) < ρ / 2 at hx
    change vec3EuclideanNorm (x - x₀) < 13 * ρ / 20
    exact hx.trans_le (by linarith only [hρ])
  have hr := ae_restrict_of_ae_restrict_of_subset hinner
    (pressure_remainder_eq_on_inner (u := u) (c := c)
      (p := p) (f := f) (x₀ := x₀) (ρ := ρ) (s := s) hρ)
  filter_upwards [hr, hi] with x hx hix
  change harmonicPressurePart (mollifiedBallCutoff x₀ hρ) u c p s x =
    p (x, s) - pressureP1 (mollifiedBallCutoff x₀ hρ) u c p f s x -
      (pressureP7 (mollifiedBallCutoff x₀ hρ) f s x +
        pressureP8 (mollifiedBallCutoff x₀ hρ) f s x) at hx
  simp only [Pi.add_apply]
  rw [← hix]
  rw [pressureP7] at hx
  linarith only [hx]

private theorem fixed_pressure_source_identification
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    let η := mollifiedBallCutoff z.1 hρ
    let c := sourceSliceCentredMean z.1 ρ u
    let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η) u Du c
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP1 η u c p f s =ᵐ[volume.restrict (euclideanBall z.1 (ρ / 2))]
        fun x => ∑ j, pressureNewtonianDerivativePotential j (fun y => V (y, s) j) x := by
  dsimp only
  let c := sourceSliceCentredMean z.1 ρ u
  have hV := centredSWS_source_data_ae hsol hρ hsub c
  have hCZ := pressureP1_thetaDecay_hCZ_of_sws (max czP1OperatorConstant 0)
    (le_max_right _ _) (le_max_left _ _) hsol hρ hsub
    (pressureSecondExtension_residual_growth_ae_of_sws hsol hρ hsub)
  have hpair := centredSWS_pairing_ae hsol hρ hsub c
  exact slice_selected_gradient_hident_ae_of_sws
    hsol hρ hsub (hCZ.mono (fun _ hs => hs.1)) hV
      (hpair.mono (fun _ hs ψ hψ _hψc => hs ψ hψ))

private theorem fixed_pressure_remainder_smooth
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ContDiffOn ℝ (1 : ℕ∞)
        (harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u
          (sourceSliceCentredMean z.1 ρ u) p s +
          pressureP8 (mollifiedBallCutoff z.1 hρ) f s) (vec3Ball z.1 (ρ / 2)) := by
  have hh := slice_harmonic_part_contDiffOn_ae_of_sws hsol hρ hsub
  have hf := slice_force_source_data_ae_of_sws hsol hρ hsub
  have hhalf : euclideanBall z.1 (ρ / 2) = vec3Ball z.1 (ρ / 2) :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by positivity)
  filter_upwards [hh, hf] with s hhs hfs
  rw [hhalf] at hhs
  exact hhs.add (contDiffOn_pressureP8_halfBall hρ hfs.2.2.1)

/-- Suitability identifies every weak pressure derivative on the half ball
with the fixed-localization completed Riesz terms and smooth remainder. -/
theorem ae_weak_pressure_derivative_eq_fixed_riesz_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    let η := mollifiedBallCutoff z.1 hρ
    let c := sourceSliceCentredMean z.1 ρ u
    let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η) u Du c
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ i : Fin 3, ∀ g : Vec3 → ℝ,
      LocallyIntegrableOn g (vec3Ball z.1 (ρ / 2)) volume →
      HasWeakPartialDerivOn (vec3Ball z.1 (ρ / 2)) i (fun y => p (y, s)) g →
      g =ᵐ[volume.restrict (vec3Ball z.1 (ρ / 2))] fun x =>
        -(∑ j, rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => V (y, s) j) x) +
        classicalGradient (harmonicPressurePart η u c p s + pressureP8 η f s) x i +
        ∑ j, rieszSecondGradientExtensionOperator
          (rieszSecondL2Input j i) (rieszSecondL2_weak_type j i) (fun y => η y * f (y, s) j) x := by
  dsimp only
  let η := mollifiedBallCutoff z.1 hρ
  let c := sourceSliceCentredMean z.1 ρ u
  let V := sourceMorreyCutoffVCentredTensorSpacetime η (spatialDeriv η) u Du c
  have hV := centredSWS_source_data_ae hsol hρ hsub c
  have hid := fixed_pressure_source_identification hsol hρ hsub
  have hh := fixed_pressure_remainder_smooth hsol hρ hsub
  have hf := slice_force_source_data_ae_of_sws hsol hρ hsub
  have hhalf : euclideanBall z.1 (ρ / 2) = vec3Ball z.1 (ρ / 2) :=
    CKN.Foundation.Parabolic.euclideanBall_eq_vec3Ball (by positivity)
  filter_upwards [hV, hid, hh, hf] with s hVs hids hhs hfs
  intro i g hg hpg
  have hcs (j : Fin 3) : HasCompactSupport (fun y => η y * f (y, s) j) :=
    (mollifiedBallCutoff_hasCompactSupport z.1 hρ).mul_right
  have hi : pressureP1 η u c p f s =ᵐ[volume.restrict (vec3Ball z.1 (ρ / 2))]
      fun x => ∑ j, pressureNewtonianDerivativePotential j (fun y => V (y, s) j) x := by
    rw [hhalf] at hids
    exact hids
  have hrep := fixed_pressure_representation hρ hi
  exact weak_pressure_derivative_eq_riesz_sum_remainder (isOpen_vec3Ball _ _) i
    hVs.1 hVs.2 hfs.2.1 hcs hhs hrep hg hpg

end CKN.Core.Step4
