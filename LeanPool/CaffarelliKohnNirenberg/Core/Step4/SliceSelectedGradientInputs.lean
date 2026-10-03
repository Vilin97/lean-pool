/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SourceMorreySlice
public import LeanPool.CaffarelliKohnNirenberg.Pressure.HarmonicRemainderSliceSWS

/-!
# Slice Selected Gradient Inputs

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-! The two solution-level inputs which are independent of the selection and
identity producers.  This file only changes the carrier of the already established
slice estimates; it does not select a gradient or prove a pressure identity. -/

/-- The force-potential input of `slice_selected_gradient_ae_of_sws`, supplied
by the solution-level force producer on the exact inner ball used there. -/
theorem slice_selected_gradient_hP78_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      0 ≤ harmonicRemainderForceBound z hρ f s ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤
        harmonicRemainderForceBound z hρ f s := by
  exact pressure_force_inner_memLp_and_lpNorm_ae_of_sws hsol hρ hsub

/-- The exact two-conjunct force-potential input used by the selected-gradient
construction. -/
theorem slice_selected_gradient_hP78_input_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (ENNReal.ofReal (3 / 2 : ℝ))
          (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤
        harmonicRemainderForceBound z hρ f s := by
  filter_upwards [slice_selected_gradient_hP78_of_sws hsol hρ hsub] with s hs
  exact ⟨hs.1, hs.2.2⟩

end CKN.Core.Step4
