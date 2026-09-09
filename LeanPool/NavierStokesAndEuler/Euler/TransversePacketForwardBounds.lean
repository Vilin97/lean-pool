/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForwardSobolev
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderTimeBounds
public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForcing
import LeanPool.NavierStokesAndEuler.Euler.ElapsedTimePathWeight
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderDerivativeBounds
import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderWeight
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketHistoryBounds

/-!
# The source forward estimates apply to the actual packet paths

The input bound below is on the literal forcing divided by g. The weighted
Duhamel identities identify the result with the actual unweighted solution,
and with its actual time derivative divided by g. No g derivative or profile
extremum is introduced.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketProvider.Forcing

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients
  EulerLiftedGradientSpace EulerLpCylinderTranslation EulerLpCylinderPaths
      EulerLpCylinderRectangular
  EulerPacketProfileRecursion EulerGevrey EulerParameterWordGevrey EulerContinuousTimeWeight
  EulerSourceCylinderForwardSobolev EulerSourceCylinderEquation EulerSourceCylinderTimeBounds
  EulerSourceCylinderForward EulerSourceForwardCoefficient EulerLinearFundamentalExistence
  EulerTimeLpGramGevrey EulerLinearDuhamel
open scoped ContDiff BoundedContinuousFunction

variable {P : ℝ} [Fact (0 < P)]
  {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketForwardBounds1 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketForwardBounds2 : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

variable
  {D : Data U} {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (g : C(Icc (0 : ℝ) D.T, ℝ)) (hg : ∀ t, 0 < g t)
  {ι : Type*} [Fintype ι] (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (q : ℕ)
  (Ω : Set Space) (hΩ : MeasurableSet Ω) (hΩo : IsOpen Ω) (hsub : D.support ⊆ Ω)
  (hΩball : ∀ x ∈ Ω, ‖x‖ ≤ (1 / 2 : ℝ))
  (hg0 : g ⟨0, le_rfl, D.T_pos.le⟩ = 1)
  (C A Cf Rc C₀ C₁ Ri R : ℝ)
  (hC : 0 ≤ C) (hA : 0 ≤ A) (hCf : 0 ≤ Cf) (hRc : 0 ≤ Rc) (hC₀ : 0 ≤ C₀) (hC₁ : 0 ≤ C₁)
  (hRi : 2 * gramCost D.frameLower C₀ 1 * (Rc + 1) ≤ Ri)
  (hbF : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₀ * majorant
      Rc
      0 n)
  (hbF₁ : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₁ * majorant
      Rc 0 n)
  (hRforcing : sobolevCoefficientRadius ι (4 * Ri) ≤ R)
  (hR : 2 * forwardSobolevCost ι q D.T C A (forcingCost ι q Ri C₀ * Cf) (18 * Ri * C₀ * C₁) (4 *
      Ri) *
    (sobolevCoefficientRadius ι (4 * Ri) + 1) ≤ R)
  (hH3 : ∀ t s : Icc (0 : ℝ) D.T, s ≤ t → ∀ x : Space, ‖x‖ ≤ (1 / 2 : ℝ) →
    ‖((fundamentalPath D.T D.T_pos.le
        (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos
            D.frame_lower)).forward t x).comp
      ((fundamentalPath D.T D.T_pos.le
        (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos
            D.frame_lower)).backward s x)‖ ≤ C * g t / g s)
  (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a
    (normalize g hg (includePath P D.support D.support_measurable G.path))) n 0 ≤ Cf * majorant R d
        n)
  (hinitial : ∀ n, block directions q
    (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤ A * majorant R d n)

include hdir hΩ hΩo hsub hΩball hg0 hC hA hCf hRc hC₀ hC₁ hRi hbF hbF₁ hRforcing hR hH3 hforce
    hinitial

/-- The literal forward packet velocity divided by g, at the input radius. -/
theorem source_velocity_normalized_bound
    (hRframe : sobolevCoefficientRadius ι Rc ≤ R) (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize g hg (includePath P D.support D.support_measurable (G.velocityPath I)))) n 0 ≤
        (3*sobolevCoefficientAmplitude ι q Rc C₀)*majorant R (d+1) n := by
  have he := normalized_full_velocity_eq P D.support D.support_measurable D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
    (normalize g hg G.path) I.value
  rw [weight_normalize] at he
  change block directions q (fun a => pathTranslate P a
    (normalize g hg (includePath P D.support D.support_measurable
      (velocity P D.support D.support_measurable D.T D.T_pos.le
        D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value)))) n
            0 ≤ _
  rw [he]
  exact physical_forward_block_bound P D.T D.T_pos.le D.support D.support_measurable
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
    (normalize g hg G.path) I.value directions hdir q Ω hΩ D.support_compact hΩo hsub hΩball hg0
    (normalize_orbit_contDiff P g hg _ G.path_orbit) I.orbit C A Cf Rc C₀ C₁ Ri R
    hC hA hCf hRc hC₀ hC₁ hRi
    (fun j => D.frame_spatial_bound j _ (hbF j))
    (fun j => D.frameDerivative_spatial_bound j _ (hbF₁ j))
    hRforcing hRframe hR hH3 d hforce hinitial n

/-- This is A_t/g for the actual raw solution, not a derivative of A/g. -/
theorem source_derivative_normalized_bound (hRone : 1 ≤ R) (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize g hg (includePath P D.support D.support_measurable (G.derivativePath I)))) n 0 ≤
        physicalCost ι q Ri C₀ C₁ Cf 1*majorant R (d+1) n := by
  have he := normalized_full_velocityDerivative_eq P D.support D.support_measurable D.T D.T_pos.le
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower
    (normalize g hg G.path) I.value g hg
  rw [weight_normalize] at he
  change block directions q (fun a => pathTranslate P a
    (normalize g hg (includePath P D.support D.support_measurable
      (velocityDerivative P D.support D.support_measurable D.T D.T_pos.le
        D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower G.path I.value)))) n
            0 ≤ _
  rw [he]
  exact derivative_forward_block_bound P D.T D.T_pos.le D.support D.support_measurable
    D.frame D.frameDerivative D.frameLower D.frameLower_pos D.frame_lower g hg
    (normalize g hg G.path) I.value directions hdir q Ω hΩ D.support_compact hΩo hsub hΩball hg0
    (normalize_orbit_contDiff P g hg _ G.path_orbit) I.orbit C A Cf Rc C₀ C₁ Ri R
    hC hA hCf hRc hC₀ hC₁ hRi
    (fun j => D.frame_spatial_bound j _ (hbF j))
    (fun j => D.frameDerivative_spatial_bound j _ (hbF₁ j))
    hRforcing hR hH3 d hforce hinitial hRone n

end EulerTransversePacketProvider.Forcing
