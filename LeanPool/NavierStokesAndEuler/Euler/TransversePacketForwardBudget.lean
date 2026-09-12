/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.TransversePacketCorrector
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderForwardSobolev
public import LeanPool.NavierStokesAndEuler.Euler.SourceCylinderTimeBounds
import LeanPool.NavierStokesAndEuler.Euler.TransverseForwardCoefficientGevrey
import LeanPool.NavierStokesAndEuler.Euler.TransversePacketForwardBounds

/-!
Source-only budgets for the genuine forward transverse problem starting at
time zero.  The same fixed radius controls unit forcing and unit initial
coordinates; there is no history interval or terminal variational problem.
-/

@[expose] public section


noncomputable section

namespace EulerTransversePacketForward

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerTransversePacketProvider
  EulerLiftedGradientSpace EulerGevrey EulerParameterWordGevrey
  EulerSourceCylinderForward EulerSourceCylinderForwardSobolev EulerSourceForwardCoefficient
  EulerLinearFundamentalExistence EulerSourceCylinderTimeBounds EulerLinearDuhamel
  EulerTimeLpGramGevrey EulerLpCylinderTranslation EulerLpCylinderPaths EulerContinuousTimeWeight
  EulerPacketProfileRecursion
open scoped ContDiff BoundedContinuousFunction

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]

/-- Cache the standard `NormedRing (U →L[ℝ] U)` instance to shorten typeclass synthesis. -/
local instance instTransversePacketForwardBudget1 : NormedRing (U →L[ℝ] U) := inferInstance
/-- Cache the standard `NormedRing (Space →ᵇ U →L[ℝ] U)` instance to shorten typeclass
synthesis. -/
local instance instTransversePacketForwardBudget2 : NormedRing (Space →ᵇ U →L[ℝ] U) := inferInstance

/-- Budget data, collecting `g`, `positive`, `initial_one`, `neighborhood`,
`neighborhood_measurable`, `neighborhood_open` and their compatibility conditions. -/
structure Budget (D : Data U) (ι : Type*) [Fintype ι] (q : ℕ) where
  /-- G of `Budget`, of type `C(Icc (0 : ℝ) D.T,ℝ)`. -/
  g : C(Icc (0 : ℝ) D.T,ℝ)
  positive : ∀ t, 0 < g t
  initial_one : g ⟨0,le_rfl,D.T_pos.le⟩ = 1
  /-- Neighborhood of `Budget`, of type `Set Space`. -/
  neighborhood : Set Space
  neighborhood_measurable : MeasurableSet neighborhood
  neighborhood_open : IsOpen neighborhood
  support_subset : D.support ⊆ neighborhood
  neighborhood_halfball : ∀ x ∈ neighborhood, ‖x‖ ≤ (1/2 : ℝ)
  /-- Rc of `Budget`, of type `ℝ`. -/
  Rc : ℝ
  /-- C₀ of `Budget`, of type `ℝ`. -/
  C₀ : ℝ
  /-- First-derivative bound coefficient of `Budget`, of type `ℝ`. -/
  C₁ : ℝ
  /-- Bound coefficient of `Budget`, of type `ℝ`. -/
  C : ℝ
  /-- Ri of `Budget`, of type `ℝ`. -/
  Ri : ℝ
  /-- Radius parameter of `Budget`, of type `ℝ`. -/
  R : ℝ
  Rc_nonneg : 0 ≤ Rc
  C₀_nonneg : 0 ≤ C₀
  C₁_nonneg : 0 ≤ C₁
  C_nonneg : 0 ≤ C
  frame_bound : ∀ n t x, ‖iteratedFDeriv ℝ n (D.F.field t : Space → Space →L[ℝ] Space) x‖ ≤
    C₀*majorant Rc 0 n
  frameDerivative_bound : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F₁.field t : Space → Space →L[ℝ] Space) x‖ ≤ C₁*majorant Rc 0 n
  forward_inverse : 2*gramCost D.frameLower C₀ 1*(Rc+1) ≤ Ri
  radius_one : 1 ≤ R
  frame_radius : sobolevCoefficientRadius ι Rc ≤ R
  forcing_radius : sobolevCoefficientRadius ι (4*Ri) ≤ R
  forward_radius :
    2*forwardSobolevCost ι q D.T C 1 (forcingCost ι q Ri C₀*1)
      (18*Ri*C₀*C₁) (4*Ri)*(sobolevCoefficientRadius ι (4*Ri)+1) ≤ R
  propagator : ∀ t s : Icc (0 : ℝ) D.T, s ≤ t → ∀ x : Space, ‖x‖ ≤ (1/2 : ℝ) →
    ‖((fundamentalPath D.T D.T_pos.le
        (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos
            D.frame_lower)).forward t x).comp
      ((fundamentalPath D.T D.T_pos.le
        (sourceGenerator D.frame D.frameDerivative D.frameLower D.frameLower_pos
            D.frame_lower)).backward s x)‖ ≤
      C*g t/g s

namespace Budget

variable {D : Data U} {ι : Type*} [Fintype ι] {q : ℕ} (L : Budget D ι q)

/-- Velocity cost, given by `3*sobolevCoefficientAmplitude ι q L.Rc L.C₀`. -/
def velocityCost : ℝ := 3*sobolevCoefficientAmplitude ι q L.Rc L.C₀
/-- Derivative cost, given by `physicalCost ι q L.Ri L.C₀ L.C₁ 1 1`. -/
def derivativeCost : ℝ := physicalCost ι q L.Ri L.C₀ L.C₁ 1 1
/-- Common cost, given by `L.velocityCost+L.derivativeCost`. -/
def commonCost : ℝ := L.velocityCost+L.derivativeCost

/-- Enlarge radius as an element of `Budget D ι q`. -/
def enlargeRadius (R' : ℝ) (hR : L.R ≤ R') : Budget D ι q :=
  { L with
    R := R'
    radius_one := L.radius_one.trans hR
    frame_radius := L.frame_radius.trans hR
    forcing_radius := L.forcing_radius.trans hR
    forward_radius := L.forward_radius.trans hR }

theorem velocityCost_nonneg : 0 ≤ L.velocityCost :=
  mul_nonneg (by norm_num)
    (sobolevCoefficientAmplitude_nonneg q L.Rc L.C₀ L.Rc_nonneg L.C₀_nonneg)

theorem derivativeCost_nonneg : 0 ≤ L.derivativeCost := by
  have hi := (EulerTransverseForwardCoefficientGevrey.inverseRadius_bounds
    D.frameLower L.C₀ L.Rc L.Ri D.frameLower_pos L.Rc_nonneg L.forward_inverse).1
  have h0 := L.C₀_nonneg
  have h1 := L.C₁_nonneg
  have hb0 := sobolevCoefficientAmplitude_nonneg (ι := ι) q (4*L.Ri) L.C₀ (by positivity) h0
  have hb1 := sobolevCoefficientAmplitude_nonneg (ι := ι) q (4*L.Ri) L.C₁ (by positivity) h1
  have hbb := sobolevCoefficientAmplitude_nonneg (ι := ι) q (4*L.Ri) (18*L.Ri*L.C₀*L.C₁)
    (by positivity) (by positivity)
  have hbf := sobolevCoefficientAmplitude_nonneg (ι := ι) q (4*L.Ri) (3*L.Ri*L.C₀)
    (by positivity) (by positivity)
  unfold derivativeCost physicalCost coordinateCost
  positivity

theorem commonCost_nonneg : 0 ≤ L.commonCost := add_nonneg L.velocityCost_nonneg
    L.derivativeCost_nonneg
theorem velocityCost_le_common : L.velocityCost ≤ L.commonCost := le_add_of_nonneg_right
    L.derivativeCost_nonneg
theorem derivativeCost_le_common : L.derivativeCost ≤ L.commonCost := le_add_of_nonneg_left
    L.velocityCost_nonneg

variable {P : ℝ} [Fact (0 < P)] {raw : VectorField} (G : Forcing P D raw) (I : InitialData P D)
  (directions : ι → LiftTangent) (hdir : ∀ i, ‖directions i‖ ≤ 1) (d : ℕ)
  (hforce : ∀ n, block directions q (fun a => pathTranslate P a
    (normalize L.g L.positive (includePath P D.support D.support_measurable G.path))) n 0 ≤
        majorant L.R d n)
  (hinitial : ∀ n, block directions q (fun a => translate P a (I.value : CylinderL2 P U)) n 0 ≤
      majorant L.R d n)

include hdir hforce hinitial

theorem velocity_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullVelocityPath I))) n 0 ≤ L.velocityCost*majorant L.R (d+1) n
          :=
  G.source_velocity_normalized_bound I L.g L.positive directions hdir q
    L.neighborhood L.neighborhood_measurable L.neighborhood_open L.support_subset
        L.neighborhood_halfball
    L.initial_one L.C 1 1 L.Rc L.C₀ L.C₁ L.Ri L.R L.C_nonneg zero_le_one zero_le_one
    L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg L.forward_inverse L.frame_bound L.frameDerivative_bound
    L.forcing_radius L.forward_radius L.propagator d
    (fun j => by simpa only [one_mul] using hforce j)
    (fun j => by simpa only [one_mul] using hinitial j) L.frame_radius n

theorem derivative_unit_bound (n : ℕ) :
    block directions q (fun a => pathTranslate P a
      (normalize L.g L.positive (G.fullDerivativePath I))) n 0 ≤ L.derivativeCost*majorant L.R
          (d+1) n :=
  G.source_derivative_normalized_bound I L.g L.positive directions hdir q
    L.neighborhood L.neighborhood_measurable L.neighborhood_open L.support_subset
        L.neighborhood_halfball
    L.initial_one L.C 1 1 L.Rc L.C₀ L.C₁ L.Ri L.R L.C_nonneg zero_le_one zero_le_one
    L.Rc_nonneg L.C₀_nonneg L.C₁_nonneg L.forward_inverse L.frame_bound L.frameDerivative_bound
    L.forcing_radius L.forward_radius L.propagator d
    (fun j => by simpa only [one_mul] using hforce j)
    (fun j => by simpa only [one_mul] using hinitial j) L.radius_one n

end Budget
end EulerTransversePacketForward
