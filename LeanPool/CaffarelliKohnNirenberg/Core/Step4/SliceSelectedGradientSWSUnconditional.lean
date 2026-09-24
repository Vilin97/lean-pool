/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientIdentification
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientRegularity
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForceUnconditional

/-! # Display (3.5) on a slice, with no condition on the divergence of the force

Display (3.5) of the pressure-gradient section selects, for almost every time
of the one-sided interval `J_ρ`, a weak spatial gradient of the pressure slice
on the half ball `B_{ρ/2}(x₀)` together with its `L^{6/5}` bound.  The general
form of that selection carries three analytic hypotheses: the interior
regularity of the harmonic part of the local pressure decomposition, the
first-order identification of the first pressure potential, and the weak
gradient of the two force potentials.

The class `def:sws` imposes no condition on the spatial divergence of the
force, so the two force potentials of `eq:pk` do not cancel and the display
must carry them.  This file discharges the first hypothesis outright, reduces
the second to the divergence-form characterization of the slice source `V`, and
discharges the third from the force data of the solution alone: the bound
gains the `ρ^{-1/2}`-weighted force term `sliceForceGradientBound`.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-- Conditional display (3.5) on a slice of a suitable weak solution.  The
weak-gradient construction `hP1` remains an explicit input; the interior
regularity of the harmonic part, first-order identification, and force slot
are discharged from the solution data, with **no** condition on the divergence
of the force.

Almost every slice of the pressure has a `Vec3`-valued weak spatial gradient on
`B_{ρ/2}(x₀)`, in `L^{6/5}` there, bounded by the Calderón–Zygmund norm of the
divergence-form source, the `ρ^{-1/2}`-weighted `L^{3/2}` norm of the pressure,
and the force term of the display. -/
theorem slice_selected_gradient_ae_of_sws_of_source_data_unconditional_with_hP1
    (C_CZ C₁₇ C₁₁ C₈ : ℝ)
    (hC_CZ : 0 ≤ C_CZ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
    (hC₈ : sliceForceGradientConstant ≤ C₈)
    {E F : ℝ → ℝ}
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    {V : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hC₁₁ : 0 ≤ C₁₁) (hE : ∀ s, 0 ≤ E s) (hF : ∀ s, 0 ≤ F s)
    (hP1 : ∀ (i : Fin 3) (G : Vec3 → ℝ),
      MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume → HasCompactSupport G →
      ∃ D : Vec3 → Vec3,
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ)) volume ∧
        (∀ (j : Fin 3) (ψ : Vec3 → ℝ),
          ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
          (∫ x, pressureNewtonianDerivativePotential i G x * spatialDeriv ψ j x) =
            -(∫ x, D x j * ψ x)) ∧
        eLpNorm D (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
          ENNReal.ofReal C_CZ * eLpNorm G (ENNReal.ofReal (6 / 5 : ℝ)) volume)
    (hCZ_p1 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
      lpNorm (pressureP1 (mollifiedBallCutoff z.1 hρ) u
        (fun t j => average (volume.restrict (vec3Ball z.1 ρ))
          (fun y : Vec3 => u (y, t) j)) p f s)
        (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤ C₁₁ * (E s) ^ (2 / 3 : ℝ))
    (hP78 : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      MemLp (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ∧
      lpNorm (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
        (ENNReal.ofReal (3 / 2 : ℝ))
        (volume.restrict (euclideanBall z.1 (13 * ρ / 20))) ≤ F s)
    (hV : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, MemLp (fun x => V (x, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x => V (x, s) i)))
    (hVpair : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
        (∑ i : Fin 3, ∫ x, V (x, s) i * spatialDeriv ψ i x) =
          pressureSecondPairing
            (fun i j x => mollifiedBallCutoff z.1 hρ x *
              pressureUTensor u (fun t j => average
                (volume.restrict (vec3Ball z.1 ρ))
                (fun y : Vec3 => u (y, t) j)) (x, s) i j) ψ) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k)
          (euclideanBall z.1 (ρ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (fun x => p (x, s)) (fun x => D x k)) ∧
        (∀ k : Fin 3, eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
            (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
          ENNReal.ofReal C_CZ *
              (∑ i : Fin 3, eLpNorm (fun x => V (x, s) i)
                (ENNReal.ofReal (6 / 5 : ℝ)) volume) +
            ENNReal.ofReal (C₁₇ *
              (lpNorm (fun x : Vec3 => p (x, s)) (ENNReal.ofReal (3 / 2 : ℝ))
                  (volume.restrict (euclideanBall z.1 ρ)) +
                C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s) * ρ ^ (-1 / 2 : ℝ)) +
            ENNReal.ofReal (sliceForceGradientBound C_CZ C₈ z.1 hρ f s)) := by
  have hregular := slice_harmonic_part_contDiffOn_ae_of_sws hsol hρ hsub
  obtain ⟨gw, hforce⟩ :=
    exists_slice_force_weak_gradient_ae_of_sws C_CZ C₈ hC_CZ hC₈ hsol hρ hsub hP1
  have hident := slice_selected_gradient_hident_ae_of_sws hsol hρ hsub
    (hCZ_p1.mono fun s hs => hs.1) hV hVpair
  exact slice_selected_gradient_ae_of_sws C_CZ C₁₇ C₁₁ hC₁₇
    (Sw := fun s => sliceForceGradientBound C_CZ C₈ z.1 hρ f s) (gw := gw)
    hsol hρ hsub hC₁₁ hE hF hP1 hCZ_p1 hP78 hregular hV hident hforce

end CKN.Core.Step4
