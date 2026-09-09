/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketParentCoefficientBounds
public import LeanPool.NavierStokesAndEuler.Euler.MeanPacketData
public import LeanPool.NavierStokesAndEuler.Euler.MeanStrongEstimates

@[expose] public section

/-! Explicit polynomial bounds for the actual mean Gram and time-form
inverse constants, derived from a determinant-one parent deformation. -/

noncomputable section

namespace EulerPacketParentMeanCoercivity

open Set ContinuousLinearMap EulerSmoothLimit EulerMeanCoefficients EulerPacketPiola
  EulerPacketCofactor EulerMeanSolenoidal EulerMeanVariationalInverse
  EulerMeanSourceFixedInverse EulerMeanFixedSpaceInverse EulerTimeH1FrameTransport

private local instance : NormedAddCommGroup solenoidalSpace := inferInstance
private local instance : InnerProductSpace ℝ solenoidalSpace := inferInstance
private local instance : NormedAddCommGroup (solenoidalSpace →L[ℝ] L2) := inferInstance
private local instance : NormedSpace ℝ (solenoidalSpace →L[ℝ] L2) := inferInstance

def gramInverseEnvelope (C : ℝ) : ℝ := (3*C^2+1)^2

def transportEnvelope (C C₁ : ℝ) : ℝ :=
  1+(2*(gramInverseEnvelope C)^2*C^2*C₁+gramInverseEnvelope C*C₁)+gramInverseEnvelope C*C

def inverseEnvelope (C C₁ : ℝ) : ℝ := 2*(transportEnvelope C C₁)^2

theorem transportEnvelope_nonneg (C C₁ : ℝ) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁) :
    0 ≤ transportEnvelope C C₁ := by unfold transportEnvelope gramInverseEnvelope; positivity

theorem inverseEnvelope_nonneg (C C₁ : ℝ) : 0 ≤ inverseEnvelope C C₁ := by
  unfold inverseEnvelope
  positivity

variable (D : EulerMeanPacketProvider.Data) (C C₁ : ℝ) (hC : 0 ≤ C) (hC₁ : 0 ≤ C₁)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)
  (hF : ∀ t x, ‖D.F.field t x‖ ≤ C)
  (hF₁ : ∀ t x, ‖D.F₁.field t x‖ ≤ C₁)

include hC hdet hF in
theorem inverseOperator_norm : ‖D.opInv‖ ≤ 3*C^2 :=
  (operatorPath_norm_le D.T D.FInv).trans
    (coefficientInverse_norm_le D.F D.FInv hdet D.inverse_left C hC hF)

include hC hdet hF in
theorem gramInverse_bound : D.frameLower⁻¹ ≤ gramInverseEnvelope C := by
  have hi := inverseOperator_norm D C hC hdet hF
  change (((‖D.opInv‖+1)^2)⁻¹)⁻¹ ≤ (3*C^2+1)^2
  rw [inv_inv]
  gcongr

include hC hC₁ hdet hF hF₁ in
theorem transport_bound (hT : D.T ≤ 1) :
    meanTransportCost D.T D.opInv D.opF D.opF₁ ≤ transportEnvelope C C₁ := by
  have hFop : ‖D.opF‖ ≤ C :=
    (operatorPath_norm_le D.T D.F.field).trans (coefficientPath_norm_le D.F C hC hF)
  have hF₁op : ‖D.opF₁‖ ≤ C₁ :=
    (operatorPath_norm_le D.T D.F₁.field).trans (coefficientPath_norm_le D.F₁ C₁ hC₁ hF₁)
  have hQ : ‖solenoidalFrame D.T D.opF‖ ≤ C :=
    (solenoidalFrame_norm_le D.T D.opF).trans hFop
  have hQ₁ : ‖solenoidalFrame D.T D.opF₁‖ ≤ C₁ :=
    (solenoidalFrame_norm_le D.T D.opF₁).trans hF₁op
  have hi := gramInverse_bound D C hC hdet hF
  have hc : 0 ≤ D.frameLower⁻¹ := inv_nonneg.mpr D.frameLower_pos.le
  have hT0 := D.T_pos.le
  have hi0 : 0 ≤ gramInverseEnvelope C := by unfold gramInverseEnvelope; positivity
  change 1+((2*(D.frameLower⁻¹)^2*‖solenoidalFrame D.T D.opF‖^2*‖solenoidalFrame D.T D.opF₁‖+
      D.frameLower⁻¹*‖solenoidalFrame D.T D.opF₁‖)*D.T+D.frameLower⁻¹*‖solenoidalFrame D.T D.opF‖)
        ≤ _
  unfold transportEnvelope
  calc
    _ ≤ 1+((2*(gramInverseEnvelope C)^2*C^2*C₁+gramInverseEnvelope C*C₁)*1+
        gramInverseEnvelope C*C) := by gcongr
    _ = _ := by ring

include hC hC₁ hdet hF hF₁ in
theorem sourceInverse_bound (hT : D.T ≤ 1) :
    (sourceFixedCoercivity D.T D.F D.F₁ D.opInv)⁻¹ ≤ inverseEnvelope C C₁ := by
  have ht := transport_bound D C C₁ hC hC₁ hdet hF hF₁ hT
  have hp := meanTransportCost_pos D.T D.T_pos.le D.opInv D.opF D.opF₁
  change ((meanTransportCost D.T D.opInv D.opF D.opF₁)⁻¹^2/2)⁻¹ ≤ _
  calc
    _ = 2*(meanTransportCost D.T D.opInv D.opF D.opF₁)^2 := by field_simp
    _ ≤ 2*(transportEnvelope C C₁)^2 :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hp.le ht 2) (by norm_num : (0 : ℝ) ≤ 2)

end EulerPacketParentMeanCoercivity
