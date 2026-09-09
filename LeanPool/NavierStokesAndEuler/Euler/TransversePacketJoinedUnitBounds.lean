/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketBudget
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketJoinedPaths

@[expose] public section

/-!
# Unit-amplitude bounds for the complete actual transverse inverse

One source-only budget controls the history trace, forward solve and their
joined physical velocity and genuine time derivative. The input and output
use the same fixed mixed-word Sobolev order and the same external radius.
-/

noncomputable section

namespace EulerTransversePacketJoin.Budget

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerGevrey EulerParameterWordGevrey EulerFixedEvolutionSobolev
  EulerLpCylinderTranslation EulerLpCylinderPaths EulerContinuousTimeWeight
    EulerTimeIntervalRestriction
  EulerElapsedTimePathGluing EulerPacketProfileRecursion
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} {τ : ℝ} {hτ : 0 < τ} {hτT : τ < D.T}
  {B : HistoryData (D.initial τ hτ hτT.le)} {ι : Type*} [Fintype ι] {q : ℕ}
  (L : Budget D τ hτ hτT B ι q) {raw : VectorField} (G : Forcing P D raw)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1)
  (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))) n 0 ≤ majorant L.R d n)

include hforce

theorem history_forcing_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (HistoryData.forcingPath (G.initial τ hτ hτT.le))) n 0 ≤ majorant L.R d n := by
  have he : (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G)).comp
      (initialInclusion D.T τ hτT.le) = HistoryData.forcingPath (G.initial τ hτ hτT.le) :=
    normalize_initial D.T τ hτ.le hτT.le L.g L.initial_one L.positive (HistoryData.forcingPath G)
  have hb := timeComp_block_le P directions q
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))
    (normalize_orbit_contDiff P L.fullProfile L.fullProfile_pos _ G.path_orbit)
    (initialInclusion D.T τ hτT.le) n 0
  rw [he] at hb
  exact hb.trans (hforce n)

theorem forward_forcing_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (G.tail τ hτ.le hτT)))) n 0 ≤ majorant L.R
        d n := by
  have he : (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G)).comp
      (tailInclusion D.T τ hτ.le) =
        normalize L.g L.positive (HistoryData.forcingPath (G.tail τ hτ.le hτT)) :=
    normalize_tail D.T τ hτ.le hτT.le L.g L.initial_one L.positive (HistoryData.forcingPath G)
  have hb := timeComp_block_le P directions q
    (normalize L.fullProfile L.fullProfile_pos (HistoryData.forcingPath G))
    (normalize_orbit_contDiff P L.fullProfile L.fullProfile_pos _ G.path_orbit)
    (tailInclusion D.T τ hτ.le) n 0
  rw [he] at hb
  exact hb.trans (hforce n)

include hdir

/-- This is the actual datum passed to the forward solution, not a new hypothesis. -/
theorem terminal_bound (n : ℕ) :
    block directions q (fun a => translate P a
      ((forwardInitial τ hτ hτT B G).value : CylinderL2 P U)) n 0 ≤
        traceCost τ*majorant L.R (d+2) n := by
  exact B.source_terminal_bound (G.initial τ hτ hτT.le) directions hdir q
    L.Rc L.C₀ L.C₁ L.CH 1 L.R L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg L.CH_nonneg zero_le_one
    (fun j t x => L.frame_bound j (initialInclusion D.T τ hτT.le t) x)
    (fun j t x => L.frameDerivative_bound j (initialInclusion D.T τ hτT.le t) x)
    L.hessian_bound L.history_weak L.history_strong L.history_length d
    (fun j => by simpa only [one_mul] using L.history_forcing_bound G directions d hforce j) n

theorem past_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (pastVelocity τ hτ hτT B G)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q L.Rc L.C₀*traceCost τ)*majorant L.R (d+2) n := by
  exact B.source_velocity_bound (G.initial τ hτ hτT.le) directions hdir q
    L.Rc L.C₀ L.C₁ L.CH 1 L.R L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg L.CH_nonneg zero_le_one
    (fun j t x => L.frame_bound j (initialInclusion D.T τ hτT.le t) x)
    (fun j t x => L.frameDerivative_bound j (initialInclusion D.T τ hτT.le t) x)
    L.hessian_bound L.history_weak L.history_strong L.history_length d
    (fun j => by simpa only [one_mul] using L.history_forcing_bound G directions d hforce j) n

theorem past_derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a (pastDerivative τ hτ hτT B G)) n 0 ≤
      (3*sobolevCoefficientAmplitude ι q L.Rc L.C₁*traceCost τ+
        3*sobolevCoefficientAmplitude ι q L.Rc L.C₀)*majorant L.R (d+3) n := by
  exact B.source_derivative_bound (G.initial τ hτ hτT.le) directions hdir q
    L.Rc L.C₀ L.C₁ L.CH 1 L.R L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg L.CH_nonneg zero_le_one
    (fun j t x => L.frame_bound j (initialInclusion D.T τ hτT.le t) x)
    (fun j t x => L.frameDerivative_bound j (initialInclusion D.T τ hτT.le t) x)
    L.hessian_bound L.history_weak L.history_strong L.history_length d
    (fun j => by simpa only [one_mul] using L.history_forcing_bound G directions d hforce j)
    L.history_uniform n

theorem future_velocity_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (futureVelocity τ hτ hτT B G))) n 0 ≤
        (3*sobolevCoefficientAmplitude ι q L.Rc L.C₀)*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (G.tail τ hτ.le hτT)))) j 0 ≤
        1*majorant L.R (d+2) j := by
    simpa only [one_mul] using (L.forward_forcing_bound G directions d hforce j).trans
      (majorant_mono_shift L.R L.radius_bounds.1 d (d+2) j (by omega))
  dsimp only [futureVelocity]
  rw [show d+3=d+2+1 by omega]
  exact
    (G.tail τ hτ.le hτT).source_velocity_normalized_bound (forwardInitial τ hτ hτT B G)
      L.g L.positive directions hdir q L.neighborhood L.neighborhood_measurable L.neighborhood_open
      L.support_subset L.neighborhood_halfball L.initial_one
      L.C (traceCost τ) 1 L.Rc L.C₀ L.C₁ L.Ri L.R
      L.C_nonneg (traceCost_nonneg τ hτ.le) zero_le_one L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
      L.forward_inverse
      (fun j t x => L.frame_bound j (tailInclusion D.T τ hτ.le t) x)
      (fun j t x => L.frameDerivative_bound j (tailInclusion D.T τ hτ.le t) x)
      L.forcing_radius L.forward_radius L.propagator (d+2) hf
      (L.terminal_bound G directions hdir d hforce) L.radius_bounds.2 n

theorem future_derivative_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (futureDerivative τ hτ hτT B G))) n 0 ≤
        EulerSourceCylinderTimeBounds.physicalCost ι q L.Ri L.C₀ L.C₁ 1 1*majorant L.R (d+3) n := by
  have hf (j : ℕ) : block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (HistoryData.forcingPath (G.tail τ hτ.le hτT)))) j 0 ≤
        1*majorant L.R (d+2) j := by
    simpa only [one_mul] using (L.forward_forcing_bound G directions d hforce j).trans
      (majorant_mono_shift L.R L.radius_bounds.1 d (d+2) j (by omega))
  dsimp only [futureDerivative]
  rw [show d+3=d+2+1 by omega]
  exact
    (G.tail τ hτ.le hτT).source_derivative_normalized_bound (forwardInitial τ hτ hτT B G)
      L.g L.positive directions hdir q L.neighborhood L.neighborhood_measurable L.neighborhood_open
      L.support_subset L.neighborhood_halfball L.initial_one
      L.C (traceCost τ) 1 L.Rc L.C₀ L.C₁ L.Ri L.R
      L.C_nonneg (traceCost_nonneg τ hτ.le) zero_le_one L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg
      L.forward_inverse
      (fun j t x => L.frame_bound j (tailInclusion D.T τ hτ.le t) x)
      (fun j t x => L.frameDerivative_bound j (tailInclusion D.T τ hτ.le t) x)
      L.forcing_radius L.forward_radius L.propagator (d+2) hf
      (L.terminal_bound G directions hdir d hforce) L.radius_bounds.1 n

/-- The entire constructed A/g, with the input's original external radius. -/
theorem velocity_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (velocityPath τ hτ hτT B G))) n 0 ≤
        L.velocityCost*majorant L.R (d+3) n := by
  have hb := normalized_join_block P D.T τ hτ.le hτT.le L.g L.positive L.initial_one
    (pastVelocity τ hτ hτT B G) (futureVelocity τ hτ hτT B G) (velocity_match τ hτ hτT B G)
    (pastVelocity_orbit τ hτ hτT B G) (futureVelocity_orbit τ hτ hτT B G) directions q n 0
  have ha : 0 ≤ 3*sobolevCoefficientAmplitude ι q L.Rc L.C₀*traceCost τ :=
    mul_nonneg (mul_nonneg (by norm_num) (sobolevCoefficientAmplitude_nonneg q L.Rc L.C₀
      L.Rc_nonneg L.C₀_nonneg)) (traceCost_nonneg τ hτ.le)
  have hp := (L.past_velocity_bound G directions hdir d hforce n).trans
    (mul_le_mul_of_nonneg_left
      (majorant_mono_shift L.R L.radius_bounds.1 (d+2) (d+3) n (by omega)) ha)
  exact hb.trans (by
    simpa only [velocityCost,add_mul] using
      add_le_add hp (L.future_velocity_bound G directions hdir d hforce n))

/-- The entire actual A_t/g. The profile itself is never differentiated. -/
theorem derivative_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.fullProfile L.fullProfile_pos (derivativePath τ hτ hτT B G))) n 0 ≤
        L.derivativeCost*majorant L.R (d+3) n := by
  have hb := normalized_join_block P D.T τ hτ.le hτT.le L.g L.positive L.initial_one
    (pastDerivative τ hτ hτT B G) (futureDerivative τ hτ hτT B G) (derivative_match τ hτ hτT B G)
    (pastDerivative_orbit τ hτ hτT B G) (futureDerivative_orbit τ hτ hτT B G) directions q n 0
  exact hb.trans (by
    simpa only [derivativeCost,add_mul] using
      add_le_add (L.past_derivative_bound G directions hdir d hforce n)
        (L.future_derivative_bound G directions hdir d hforce n))

end EulerTransversePacketJoin.Budget
