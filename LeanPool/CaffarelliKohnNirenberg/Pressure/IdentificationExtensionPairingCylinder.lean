/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationExtensionPairing
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalCore
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Integration.Average

/-!
# The identification data on a parabolic cylinder

The identification data for the leading local pressure, specialized to the
cut-off `mollifiedBallCutoff z.1 hρ` of the parabolic cylinder of radius `ρ`
about `z` and to the ball average of the velocity used as the subtracted
constant.  The conclusion is stated on the cylinder's time interval, which is
the form the slice pressure estimates consume.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

/-- The Calderón--Zygmund identification data for the leading local pressure on
the parabolic cylinder of radius `ρ` about `z`: for almost every time of the
cylinder, the whole-space pairing identity and the pairing integrability hold
simultaneously for every compactly supported smooth spatial test function, with
tensor source the cut-off velocity tensor. -/
theorem pressureP1_cz_identification_data_ae_of_sws_cylinder
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          Integrable (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y : Vec3 => u (y, t) j))
            p f s x * spatialLaplacian ψ x) volume →
          ∫ x, pressureP1 (mollifiedBallCutoff z.1 hρ) u
              (fun t j => MeasureTheory.average
                (volume.restrict (vec3Ball z.1 ρ)) (fun y : Vec3 => u (y, t) j))
              p f s x * spatialLaplacian ψ x =
            pressureSecondPairing
              (fun i j x => mollifiedBallCutoff z.1 hρ x *
                pressureUTensor u (fun t j => MeasureTheory.average
                  (volume.restrict (vec3Ball z.1 ρ))
                  (fun y : Vec3 => u (y, t) j)) (x, s) i j) ψ) ∧
        ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          Integrable (fun x => pressureP1 (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y : Vec3 => u (y, t) j))
            p f s x * spatialLaplacian ψ x) volume := by
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hBΩ : vec3Ball z.1 ρ ⊆ Ω := by
    intro x hx
    exact hbox.2.2.1 (subset_closure (hball hx))
  have hηΩ : tsupport (mollifiedBallCutoff z.1 hρ) ⊆ Ω :=
    (pressure_cutoff_support_subset_ball z.1 hρ).trans hBΩ
  have hTI : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I :=
    htime.trans (subset_closure.trans hbox.2.2.2.2.2)
  exact ae_restrict_of_ae_restrict_of_subset hTI
    (pressureP1_cz_identification_data_ae_of_sws hsol
      (mollifiedBallCutoff_smooth z.1 hρ)
      (mollifiedBallCutoff_hasCompactSupport z.1 hρ) hηΩ
      (fun t j => MeasureTheory.average
        (volume.restrict (vec3Ball z.1 ρ)) (fun y : Vec3 => u (y, t) j)))

end CKN

end
