/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPairAmplitude

@[expose] public section

/-! The genuine direct-forward solution has amplitude-linear estimates at
one source-dependent radius, for arbitrary admissible initial data and forcing. -/

noncomputable section

namespace EulerTransversePacketForward.Budget

open Set ContinuousLinearMap EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerTransversePacketProvider EulerPacketProfileRecursion
  EulerParameterWordGevrey EulerGevrey EulerContinuousTimeWeight
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {ι : Type*} [Fintype ι] {q : ℕ} (L : Budget D ι q)
  {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (A : ℝ) (hA : 0 ≤ A) (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a
    (normalize L.g L.positive (HistoryData.forcingPath G))) n 0 ≤ A*majorant L.R d n)
  (hinitial : ∀ n, block directions q (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤
    A*majorant L.R d n)

include hdir hA hforce hinitial

theorem velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullVelocityPath I))) n 0 ≤
        (L.velocityCost*A)*majorant L.R (d+1) n :=
  pair_amplitude_bound (fun {r} H Y => (H : Forcing P D r).fullVelocityPath Y)
    (fun H Y => H.velocityPath_orbit Y)
    (fun H J Y Z a he hi => by
      change includePath P D.support D.support_measurable (J.velocityPath Z) =
        a • includePath P D.support D.support_measurable (H.velocityPath Y)
      rw [H.velocityPath_eq_smul J Y Z a he hi,map_smul])
    L.g L.positive directions q L.R L.velocityCost d (d+1)
    (fun H Y hf hi => L.velocity_unit_bound H Y directions hdir d hf hi)
    G I A hA hforce hinitial n

theorem derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullDerivativePath I))) n 0 ≤
        (L.derivativeCost*A)*majorant L.R (d+1) n :=
  pair_amplitude_bound (fun {r} H Y => (H : Forcing P D r).fullDerivativePath Y)
    (fun H Y => H.derivativePath_orbit Y)
    (fun H J Y Z a he hi => by
      change includePath P D.support D.support_measurable (J.derivativePath Z) =
        a • includePath P D.support D.support_measurable (H.derivativePath Y)
      rw [H.derivativePath_eq_smul J Y Z a he hi,map_smul])
    L.g L.positive directions q L.R L.derivativeCost d (d+1)
    (fun H Y hf hi => L.derivative_unit_bound H Y directions hdir d hf hi)
    G I A hA hforce hinitial n

theorem velocity_common_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullVelocityPath I))) n 0 ≤
        (L.commonCost*A)*majorant L.R (d+1) n :=
  (L.velocity_bound G I directions hdir A hA d hforce hinitial n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right L.velocityCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_one) (d+1) n))

theorem derivative_common_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullDerivativePath I))) n 0 ≤
        (L.commonCost*A)*majorant L.R (d+1) n :=
  (L.derivative_bound G I directions hdir A hA d hforce hinitial n).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right L.derivativeCost_le_common hA)
      (majorant_nonneg L.R (zero_le_one.trans L.radius_one) (d+1) n))

end EulerTransversePacketForward.Budget
