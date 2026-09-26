/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.SliceVelocityCube

/-! # Velocity slices and compact tensor sources

The slice Sobolev estimate and the nine-component tensor estimate supply
`ext:CZ` in the proof of `thm:B`. These names retain the endgame interface for
the estimates proved in `CKN.Pressure.SliceVelocityCube`.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Endgame

/-- Spatial Sobolev slices supply the local L³ input of `ext:CZ`. -/
theorem velocity_norm_memLp_three_on_ball_of_slices
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {x₀ : Vec3} {ρ t : ℝ} {Ω' : Set Vec3}
    (hρ : 0 < ρ) (hball : vec3Ball x₀ ρ ⊆ Ω')
    (hts : MemLp (fun x : Vec3 => u (x, t)) 2 (volume.restrict Ω'))
    (hDu : MemLp (fun x : Vec3 => Du (x, t)) 2 (volume.restrict Ω'))
    (hgrad : ∀ i : Fin 3,
      HasWeakGradientOn Ω' (fun x : Vec3 => u (x, t) i)
        (fun x => Du (x, t) i)) :
    MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, t)))
      (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x₀ ρ)) := by
  exact CKN.velocity_norm_memLp_three_on_ball_of_slices hρ hball hts hDu hgrad

/-- Almost every velocity slice has the L³ membership used in `ext:CZ`. -/
theorem velocity_norm_memLp_three_ae_on_ball_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (fun x : Vec3 => vec3EuclideanNorm (u (x, s)))
        (ENNReal.ofReal (3 : ℝ))
        (volume.restrict (vec3Ball z.1 ρ)) := by
  exact CKN.velocity_norm_memLp_three_ae_on_ball_of_sws hsol hρ hsub

/-- The compact tensor source of `ext:CZ` has L³/² components and the
nine-component norm bound expressed as `(27 * E)^(2/3)`. -/
theorem pressureUTensor_source_data_of_memLp_three
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {η : Vec3 → ℝ} {x₀ : Vec3} {ρ s : ℝ} (_ : 0 < ρ)
    (hηmeas : AEStronglyMeasurable η volume)
    (hηc : HasCompactSupport η)
    (hηsupport : tsupport η ⊆ vec3Ball x₀ ρ)
    (hηbound : ∀ y, |η y| ≤ 1)
    (humeas : AEStronglyMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hu : MemLp (fun y : Vec3 => vec3EuclideanNorm (u (y, s)))
      (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x₀ ρ))) :
    (∀ i j : Fin 3, MemLp
      (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) ∧
    (∀ i j : Fin 3, HasCompactSupport
      (fun y => η y * pressureUTensor u c (y, s) i j)) ∧
    (∑ i, ∑ j, lpNorm
      (fun y => η y * pressureUTensor u c (y, s) i j)
      (ENNReal.ofReal (3 / 2 : ℝ)) volume) ≤
      (27 * (∫ y in vec3Ball x₀ ρ,
        pressureUTensorNorm u c s y ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ) := by
  exact CKN.pressureUTensor_source_data_of_memLp_three
    ‹0 < ρ› hηmeas hηc hηsupport hηbound humeas hu

end CKN.Core.Endgame
