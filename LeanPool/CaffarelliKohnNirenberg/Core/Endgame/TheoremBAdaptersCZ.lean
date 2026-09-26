/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.IdentificationCZP1Unconditional

/-! # The `ext:CZ` pressure interface of `thm:B`

The Calderón--Zygmund display `ext:CZ` for the centred first pressure
potential enters the theta-decay display of `thm:B` as an almost-every-time
time-slice certificate: membership of `pressureP1` in `L^{3/2}` on the space
slice together with a ball-local `lpNorm` bound in terms of `utensorNorm`.
The slice transfer `pressureP1_thetaDecay_hCZ_of_global_slice` converts one
such certificate into the `r`-scaled extended-real estimate on the
concentric parabolic sub-cylinder.

This module re-quantifies that transfer over all suitable weak solutions at
a fixed integrability exponent, so a single named hypothesis supplies the
exact pressure binder consumed by the gradient criterion of `thm:B`.  The
constant relation is the one exposed by the transfer: the cylinder constant
`C₁₂_p1` dominates `C_CZ * (9 * sobolevPoincareL6Constant)`. -/

public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean
open CKN.Core.Step3


noncomputable section

namespace CKN

namespace Core.Endgame

/-- **`ext:CZ` for the centred first pressure potential, at fixed exponent.**
Given the Calderón--Zygmund slice certificate for `pressureP1`, uniform over
all suitable weak solutions at a fixed `q` and with a single constant
`C_CZ`, the theta-decay pressure binder of the gradient criterion holds for
every solution.  The slice hypothesis is the almost-every-time `MemLp`
membership at exponent `3/2` together with the ball-local `lpNorm` bound in
terms of `utensorNorm`; the conclusion is exactly the `pressureP1` display
consumed by the gradient criterion. -/
theorem theoremB_hCZ_p1_of_slice_bounds
    (q C₁₂_p1 C_CZ : ℝ) (hC_CZ : 0 ≤ C_CZ)
    (hconst : C_CZ * (9 * sobolevPoincareL6Constant.toReal) ≤ C₁₂_p1)
    (hSlice :
      ∀ (Ω : Set Vec3) (I : Set ℝ)
        (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
        (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
        IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
        ∀ {z : ParabolicPoint} {ρ : ℝ}, (hρ : 0 < ρ) →
        closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
        ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
          MemLp (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ∧
          lpNorm (fun x : Vec3 => pressureP1
            (mollifiedBallCutoff z.1 hρ) u
            (fun t j => MeasureTheory.average
              (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
            p f s x) (ENNReal.ofReal (3 / 2 : ℝ)) volume ≤
            C_CZ *
              (∫ y in vec3Ball z.1 ρ,
                (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) :
    (∀ (Ω : Set Vec3) (I : Set ℝ)
      (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
      (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3),
      IsSuitableWeakSolutionIntegrable Ω I q u Du p f →
      ∀ {z : ParabolicPoint} {ρ r : ℝ}, (hρ : 0 < ρ) → 0 < r → r ≤ ρ / 2 →
      closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I →
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun w : ParabolicPoint => pressureP1
          (mollifiedBallCutoff z.1 hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball z.1 ρ)) (fun y => u (y, t) j))
          p f w.2 w.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder z.1 z.2 r)) ≤
        ENNReal.ofReal (C₁₂_p1 * (r / ρ)⁻¹ *
          alpha u z ρ * beta u Du z ρ)) := by
  intro Ω I u Du p f hsol z ρ r hρ hr hhalf hsub
  exact pressureP1_thetaDecay_hCZ_of_global_slice
    C₁₂_p1 C_CZ hC_CZ hconst hsol hρ hr hhalf hsub
    (hSlice Ω I u Du p f hsol hρ hsub)

end Core.Endgame

end CKN
