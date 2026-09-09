/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketPrimaryPaths

@[expose] public section

/-!
Unit-terminal-data estimates for the actual joined primary. The same
external radius controls its history, actual trace, and weighted future.
-/

noncomputable section

namespace EulerTransversePacketPrimary.Budget

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerGevrey EulerParameterWordGevrey EulerLpCylinderTranslation
  EulerLpCylinderPaths EulerContinuousTimeWeight EulerTimeIntervalRestriction
  EulerElapsedTimePathGluing EulerFixedEvolutionSobolev
open scoped ContDiff

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  {L : EulerTransversePacketJoin.Budget D τ hτ hτT B ι q}
  (H : Budget L) (Y : InitialData P D)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (d : ℕ)
  (hYb : ∀ n, block directions q (fun a => translate P a (Y.value : CylinderL2 P U)) n 0 ≤
    majorant L.R d n)

include H hdir hYb

theorem terminal_bound (n : ℕ) :
    block directions q (fun a => translate P a
      ((forwardInitial τ hτ hτT B Y).value : CylinderL2 P U)) n 0 ≤
        H.endpointBudget.coordinateCost*majorant L.R (d+2) n :=
  (trace_block_le P directions q
    (B.coefficients.endpointCoordinate P (Y.value : CylinderL2 P U))
    (EulerTransversePacketEndpoint.coordinatePath_orbit B (endpointData τ hτ hτT Y))
    ⟨τ,hτ.le,le_rfl⟩ n 0).trans
      (H.endpointBudget.coordinate_unit_bound P directions hdir Y.value Y.orbit d hYb n)

theorem past_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (pastVelocity τ hτ hτT B Y)) n 0 ≤
      H.endpointBudget.velocityCost*majorant L.R (d+2) n :=
  H.endpointBudget.velocity_unit_bound P directions hdir Y.value Y.orbit d hYb n

theorem past_derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (pastDerivative τ hτ hτT B Y)) n 0 ≤
      H.endpointBudget.derivativeCost*majorant L.R (d+3) n :=
  H.endpointBudget.derivative_unit_bound P directions hdir Y.value Y.orbit d hYb n

theorem future_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (futureVelocity τ hτ hτT B Y))) n 0 ≤
        (3*sobolevCoefficientAmplitude ι q L.Rc L.C₀)*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (zeroForcing (P := P) (D.tail τ hτ.le
        hτT)))))
        j 0 ≤ 0*majorant L.R (d+2) j := by
    simp only [HistoryData.forcingPath,zeroForcing,map_zero,zero_mul]
    erw [map_zero]
    simp only [map_zero,block_zero_function,le_refl]
  dsimp only [futureVelocity]
  rw [show d+3=d+2+1 by omega]
  exact
    (zeroForcing (D.tail τ hτ.le hτT)).source_velocity_normalized_bound (forwardInitial τ hτ hτT B
      Y)
      L.g L.positive directions hdir q L.neighborhood L.neighborhood_measurable L.neighborhood_open
      L.support_subset L.neighborhood_halfball L.initial_one
      L.C H.endpointBudget.coordinateCost 0 L.Rc L.C₀ L.C₁ L.Ri L.R
      L.C_nonneg H.endpointBudget.coordinateCost_nonneg le_rfl L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
      L.forward_inverse
      (fun j t x => L.frame_bound j (tailInclusion D.T τ hτ.le t) x)
      (fun j t x => L.frameDerivative_bound j (tailInclusion D.T τ hτ.le t) x)
      L.forcing_radius H.forward_radius L.propagator (d+2) hf
      (H.terminal_bound Y directions hdir d hYb) L.radius_bounds.2 n

theorem future_derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (futureDerivative τ hτ hτT B Y))) n 0 ≤
        EulerSourceCylinderTimeBounds.physicalCost ι q L.Ri L.C₀ L.C₁ 0 1*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (zeroForcing (P := P) (D.tail τ hτ.le
        hτT)))))
        j 0 ≤ 0*majorant L.R (d+2) j := by
    simp only [HistoryData.forcingPath,zeroForcing,map_zero,zero_mul]
    erw [map_zero]
    simp only [map_zero,block_zero_function,le_refl]
  dsimp only [futureDerivative]
  rw [show d+3=d+2+1 by omega]
  exact
    (zeroForcing (D.tail τ hτ.le hτT)).source_derivative_normalized_bound (forwardInitial τ hτ hτT
      B Y)
      L.g L.positive directions hdir q L.neighborhood L.neighborhood_measurable L.neighborhood_open
      L.support_subset L.neighborhood_halfball L.initial_one
      L.C H.endpointBudget.coordinateCost 0 L.Rc L.C₀ L.C₁ L.Ri L.R
      L.C_nonneg H.endpointBudget.coordinateCost_nonneg le_rfl L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
      L.forward_inverse
      (fun j t x => L.frame_bound j (tailInclusion D.T τ hτ.le t) x)
      (fun j t x => L.frameDerivative_bound j (tailInclusion D.T τ hτ.le t) x)
      L.forcing_radius H.forward_radius L.propagator (d+2) hf
      (H.terminal_bound Y directions hdir d hYb) L.radius_bounds.1 n

theorem velocity_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B Y))) n 0 ≤
        H.velocityCost*majorant L.R (d+3) n := by
  have hb := normalized_join_block P D.T τ hτ.le hτT.le L.g L.positive L.initial_one
    (pastVelocity τ hτ hτT B Y) (futureVelocity τ hτ hτT B Y) (velocity_match τ hτ hτT B Y)
    (pastVelocity_orbit τ hτ hτT B Y) (futureVelocity_orbit τ hτ hτT B Y) directions q n 0
  have hC : 0 ≤ H.endpointBudget.velocityCost :=
    mul_nonneg (mul_nonneg (by norm_num)
      (sobolevCoefficientAmplitude_nonneg q L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg))
      H.endpointBudget.coordinateCost_nonneg
  have hp := (H.past_velocity_bound Y directions hdir d hYb n).trans
    (mul_le_mul_of_nonneg_left (majorant_mono_shift L.R L.radius_bounds.1 (d+2) (d+3) n (by omega))
      hC)
  exact hb.trans (by
    simpa only [velocityCost,add_mul] using
      add_le_add hp (H.future_velocity_bound Y directions hdir d hYb n))

theorem derivative_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B Y))) n 0 ≤
        H.derivativeCost*majorant L.R (d+3) n := by
  have hb := normalized_join_block P D.T τ hτ.le hτT.le L.g L.positive L.initial_one
    (pastDerivative τ hτ hτT B Y) (futureDerivative τ hτ hτT B Y) (derivative_match τ hτ hτT B Y)
    (pastDerivative_orbit τ hτ hτT B Y) (futureDerivative_orbit τ hτ hτT B Y) directions q n 0
  exact hb.trans (by
    simpa only [derivativeCost,add_mul] using
      add_le_add (H.past_derivative_bound Y directions hdir d hYb n)
        (H.future_derivative_bound Y directions hdir d hYb n))

end EulerTransversePacketPrimary.Budget
