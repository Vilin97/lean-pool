/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradient
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientIdentification
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientRegularity
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientForce

/-! # Display (3.5) on a slice, with the analytic slots discharged

Display (3.5) of the pressure-gradient section selects, for almost every time
of the one-sided interval `J_ρ`, a weak spatial gradient of the pressure slice
on the half ball `B_{ρ/2}(x₀)` together with its `L^{6/5}` bound.  The general
form of that selection carries three analytic hypotheses: the interior
regularity of the harmonic part of the local pressure decomposition, the
first-order identification of the first pressure potential, and the weak
gradient of the two force potentials.

This file removes the first of the three outright, and reduces the other two to
named inputs which are visibly about the data and not about the pressure: the
divergence-form characterization of the slice source `V` and the
distributional divergence-freedom of the force in space-time.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-- Display (3.5) on a slice of a suitable weak solution, with the interior
regularity of the harmonic part discharged from the solution, the force slot
discharged from the distributional divergence-freedom of the force, and the
first-order identification discharged from the divergence-form characterization
of the slice source.

Almost every slice of the pressure has a `Vec3`-valued weak spatial gradient on
`B_{ρ/2}(x₀)`, in `L^{6/5}` there, bounded by the Calderón–Zygmund norm of the
divergence-form source and the `ρ^{-1/2}`-weighted `L^{3/2}` norm of the
pressure. -/
theorem slice_selected_gradient_ae_of_sws_of_source_data
    (C_CZ C₁₇ C₁₁ : ℝ)
    (hC₁₇ : 1000 * harmonicInteriorDisplayConstant ≤ C₁₇)
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
                (fun y : Vec3 => u (y, t) j)) (x, s) i j) ψ)
    (hloc : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ i : Fin 3,
      LocallyIntegrable (fun x : Vec3 => f (x, s) i) volume)
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        ∫ x, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i)
          ∂volume = 0) :
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
                C₁₁ * (E s) ^ (2 / 3 : ℝ) + F s) * ρ ^ (-1 / 2 : ℝ))) := by
  have hregular := slice_harmonic_part_contDiffOn_ae_of_sws hsol hρ hsub
  have hforce := slice_force_weak_gradient_ae_of_sws_divergence_free
    hsol hρ hsub hloc hdiv
  have hident := slice_selected_gradient_hident_ae_of_sws hsol hρ hsub
    (hCZ_p1.mono fun s hs => hs.1) hV hVpair
  have hmain := slice_selected_gradient_ae_of_sws C_CZ C₁₇ C₁₁ hC₁₇
    (Sw := fun _ => (0 : ℝ)) (gw := fun _ _ => fun _ : Vec3 => (0 : ℝ))
    hsol hρ hsub hC₁₁ hE hF hP1 hCZ_p1 hP78 hregular hV hident hforce
  filter_upwards [hmain] with s hs
  obtain ⟨D, hloc', hmem, hweak, hbound⟩ := hs
  refine ⟨D, hloc', hmem, hweak, fun k => ?_⟩
  simpa using hbound k

end CKN.Core.Step4
