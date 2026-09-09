/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.ParentShortForwardRadius
public import LeanPool.NavierStokesAndEuler.Euler.PacketSourceUniformEnvelope
public import LeanPool.NavierStokesAndEuler.Euler.BasePacketSetup

@[expose] public section

/-! The concrete compact base Euler solution supplies a uniform polynomial
source envelope for its first packet, independent of beta and the support scale. -/

noncomputable section

namespace EulerBaseDatum

open Set EulerSmoothLimit EulerPacketSupport EulerParentPacketFrames
  EulerPacketTerminalDatum EulerPacketCylinderField EulerPacketUniformSource
  EulerParentInitializedRadius

def firstParameterSize (T δ hchild : ℝ) : ℝ :=
  4+solutionLabelConstant+T⁻¹+δ⁻¹+hchild

theorem firstParameterSize_bounds (T δ hchild : ℝ) (hT : 0 < T) (hδ : 0 < δ)
    (hh : 0 ≤ hchild) :
    1 ≤ firstParameterSize T δ hchild ∧ solutionLabelConstant ≤ firstParameterSize T δ hchild ∧
    T⁻¹ ≤ firstParameterSize T δ hchild ∧ 2 ≤ firstParameterSize T δ hchild ∧
    δ⁻¹ ≤ firstParameterSize T δ hchild ∧ hchild ≤ firstParameterSize T δ hchild := by
  have hK := solutionLabelConstant_one
  have hTi := (inv_pos.mpr hT).le
  have hdi := (inv_pos.mpr hδ).le
  unfold firstParameterSize
  exact ⟨by linarith,by linarith,by linarith,by linarith,by linarith,by linarith⟩

variable (β : ℝ) (hβ : |β| ≤ 1) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
  (T : ℝ) (hT : 0 < T) (hTB : T ≤ initialTime)

local notation "A" => firstPacketInputs β hβ ell hell hell1 T hT hTB
local notation "G" => packetBaseParent β hβ ell hell hell1 T hT hTB
local notation "L" => SmoothState.labels (packetBaseState β hβ ell hell hell1 T hT hTB)
local notation "H" => packetBaseLowBounds β hβ ell hell hell1 T hT hTB
local notation "D" => Parent.transverseData G firstNormal firstNormal_unit firstFrame support compact
local notation "BC" => forwardCoefficientBudget period (Parent.meanData G H) D rfl (ForwardInputs.normal A)

theorem firstPacket_uniform_primitives (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hchild : ℝ) (hh : 0 ≤ hchild) :
    let X := firstParameterSize T δ hchild
    EulerPacketForwardRadius.RadiusPrimitives (A).linear (A).mean (A).normal BC δ firstCoordinate
      (profileEnvelope X) ∧
    (∀ t, (δ*hchild)*(A).linear.g t ≤ profileEnvelope X) ∧
    EulerPacketInitializedOutputCost.uniformConstant*
      (profileEnvelope X)^EulerPacketInitializedOutputCost.uniformPower ≤
      frequencyConstant*X^frequencyPower := by
  let X := firstParameterSize T δ hchild
  obtain ⟨hX,hK,hTi,h2,hd,hhX⟩ := firstParameterSize_bounds T δ hchild hT hδ hh
  have hr := (L).shortForward_radius_primitives H firstNormal firstNormal_unit firstFrame support
    compact
    initialCoefficientCost initialCoefficientCost_nonneg
    (fun t x _ => packetBase_strain_bound β hβ ell hell hell1 T hT hTB t x)
    (packetBase_short T hTB) (Metric.ball 0 (1/2 : ℝ)) Metric.isOpen_ball.measurableSet
    Metric.isOpen_ball subset_halfBall
    (fun x hx => le_of_lt (by simpa only [Metric.mem_ball,dist_zero_right] using hx))
    T⁻¹ (hTB.trans initialTime_le_one) le_rfl δ firstCoordinate X hK hTi h2
    (zero_le_one.trans hX) hd (by simpa only [firstCoordinate_norm] using hX)
  have hSX : X ≤ sourceEnvelope X :=
    (inputEnvelope_bounds X X hX le_rfl).2.1.trans
      (EulerPacketSourceRadius.le_sourceRadiusEnvelope _
        (zero_le_one.trans (inputEnvelope_bounds X X hX le_rfl).1))
  refine ⟨hr.mono (profileEnvelope_bounds X hX).2.1,?_,frequency_bound X hX⟩
  intro t
  change (δ*hchild)*1 ≤ _
  rw [mul_one]
  exact ((mul_le_mul_of_nonneg_right hδ1 hh).trans_eq (one_mul _)).trans
    (hhX.trans (hSX.trans (profileEnvelope_bounds X hX).2.1))

end EulerBaseDatum
