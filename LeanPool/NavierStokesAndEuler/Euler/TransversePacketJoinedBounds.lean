/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedPaths
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketAmplitude
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHomogeneity
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedUnitBounds

/-!
The actual complete transverse inverse has one source-only radius budget.
Its bounds are linear in the forcing amplitude and independent of grade.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketJoin.Budget

open Set ContinuousLinearMap EulerSmoothLimit EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : Budget D τ hτ hτT B ι q) {raw : VectorField} (G : Forcing P D raw)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))) n 0 ≤ A * majorant L.R
        d
        n)

include hdir hA hforce

/-- The genuine joined velocity divided by its actual piecewise profile. -/
theorem velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B G))) n 0 ≤
        (L.velocityCost*A)*majorant L.R (d+3) n :=
  amplitude_bound (fun {r} H => velocityPath τ hτ hτT B (H : Forcing P D r))
    (fun H => velocityPath_orbit τ hτ hτT B H)
    (fun H J a he => velocityPath_eq_smul τ hτ hτT B H J a he)
    L.fullProfile L.fullProfile_pos directions q L.R L.velocityCost d (d+3)
    (fun H he => L.velocity_unit_bound H directions hdir d he) G A hA hforce n

/-- The genuine time derivative divided by the same profile, with no g derivative. -/
theorem derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B G))) n 0 ≤
        (L.derivativeCost*A)*majorant L.R (d+3) n :=
  amplitude_bound (fun {r} H => derivativePath τ hτ hτT B (H : Forcing P D r))
    (fun H => derivativePath_orbit τ hτ hτT B H)
    (fun H J a he => derivativePath_eq_smul τ hτ hτT B H J a he)
    L.fullProfile L.fullProfile_pos directions q L.R L.derivativeCost d (d+3)
    (fun H he => L.derivative_unit_bound H directions hdir d he) G A hA hforce n

end EulerTransversePacketJoin.Budget
