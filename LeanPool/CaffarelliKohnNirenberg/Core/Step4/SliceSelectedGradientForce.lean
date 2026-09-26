/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.ForceCancellationUnconditional
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientRemainder

/-! # The force potentials of a slice carry a vanishing weak gradient

The last two summands `p₇ + p₈` of the local pressure decomposition `eq:pk`
are the force potentials.  When the force is distributionally divergence free
in space-time the two cancel on almost every slice, and the slice field of
display (3.5) needs no contribution from them: the zero function is their weak
gradient on the inner ball, with vanishing `L^{6/5}` norm.

The cancellation itself is the whole-space harmonic uniqueness statement of
the force section; this file only converts it into the weak-gradient shape
that display (3.5) consumes.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Core.Step4

/-- A function vanishing almost everywhere has the zero function as each of
its weak partial derivatives on every set. -/
theorem hasWeakPartialDerivOn_zero_of_ae_eq_zero
    {B : Set Vec3} {w : Vec3 → ℝ} (k : Fin 3) (hw : w =ᵐ[volume] 0) :
    HasWeakPartialDerivOn B k w (fun _ => 0) := by
  intro φ _hφ _hφc _hφB
  have hleft : ∫ x in B, w x * (fderiv ℝ φ x) (basisVec k) ∂volume = 0 := by
    refine integral_eq_zero_of_ae ?_
    filter_upwards [ae_restrict_of_ae hw] with x hx
    simp only [Pi.zero_apply] at hx
    simp [hx]
  rw [hleft]
  simp

/-- The zero function is locally integrable on every set. -/
theorem locallyIntegrableOn_zero (B : Set Vec3) :
    LocallyIntegrableOn (fun _ : Vec3 => (0 : ℝ)) B volume :=
  (locallyIntegrable_const (0 : ℝ)).locallyIntegrableOn B

/-- Display (3.5) for the force potentials of a slice, in the case where they
cancel: the zero field is their weak gradient on the inner ball and its
`L^{6/5}` norm is zero. -/
theorem slice_force_weak_gradient_ae_of_ae_zero
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ) {f : ParabolicPoint → Vec3}
    (hzero : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
        pressureP8 (mollifiedBallCutoff z.1 hρ) f s =ᵐ[volume] 0) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ k : Fin 3,
      HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
            pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (fun _ => (0 : ℝ)) ∧
        LocallyIntegrableOn (fun _ : Vec3 => (0 : ℝ))
          (euclideanBall z.1 (ρ / 2)) volume ∧
        eLpNorm (fun _ : Vec3 => (0 : ℝ)) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
          ENNReal.ofReal (0 : ℝ) := by
  filter_upwards [hzero] with s hs
  intro k
  refine ⟨hasWeakPartialDerivOn_zero_of_ae_eq_zero k hs,
    locallyIntegrableOn_zero _, ?_⟩
  simp

/-- The force slot of display (3.5) for a suitable weak solution whose force is
distributionally divergence free in space-time: the slice force potentials
cancel and their weak gradient on the inner ball is zero. -/
theorem slice_force_weak_gradient_ae_of_sws_divergence_free
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (hloc : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ i : Fin 3,
      LocallyIntegrable (fun x : Vec3 => f (x, s) i) volume)
    (hdiv : ∀ ψ : Vec3 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ →
      ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
        ∫ x, ∑ i : Fin 3, f (x, s) i * (fderiv ℝ ψ x) (basisVec i)
          ∂volume = 0) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ k : Fin 3,
      HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
            pressureP8 (mollifiedBallCutoff z.1 hρ) f s)
          (fun _ => (0 : ℝ)) ∧
        LocallyIntegrableOn (fun _ : Vec3 => (0 : ℝ))
          (euclideanBall z.1 (ρ / 2)) volume ∧
        eLpNorm (fun _ : Vec3 => (0 : ℝ)) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
          ENNReal.ofReal (0 : ℝ) :=
  slice_force_weak_gradient_ae_of_ae_zero hρ
    (pressure_force_eq_zero_of_sws_unconditional hsol hρ hsub hloc hdiv)

end CKN.Core.Step4
