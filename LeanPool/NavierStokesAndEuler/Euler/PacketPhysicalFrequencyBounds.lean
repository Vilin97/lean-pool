/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketPhysicalGevrey
public import LeanPool.NavierStokesAndEuler.Euler.FieldTowerPhysicalL2

@[expose] public section

/-! A fixed polynomial frequency loss for every actual physical spatial
derivative of a reconstructed lifted field. -/

noncomputable section

namespace EulerPacketPhysicalGevrey

open Set EulerSmoothLimit EulerLiftedGradientSpace EulerMetricTransport EulerCylinderSobolev
  EulerCylinderCoordinates EulerCylinderPhysicalTensor EulerPacketInverseFlowGevrey
  EulerPacketPiola EulerGevrey
open scoped ContDiff

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  (D : EulerTransversePacketProvider.Data U)

def physicalRadiusCost (R C S : ℝ) : ℝ :=
  sourceInverseRadius C R*(9*C^2*(R+
    (‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖D.m₀‖))*S)+2)

theorem physicalRadiusCost_nonneg (R C S : ℝ) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    0 ≤ physicalRadiusCost D R C S := by
  have hL := (sourceInverseRadius_pos C R hR).le
  unfold physicalRadiusCost
  positivity

theorem physicalRadius_le_linear (k R C S : ℝ) (hk : 1 ≤ k) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    physicalRadius D k R C S ≤ physicalRadiusCost D R C S*k := by
  let χ := ‖coordinateEquiv.symm.toContinuousLinearMap‖*(1+‖D.m₀‖)
  have hχ := frequencyFactor_le_linear k hk D.m₀
  change frequencyFactor k D.m₀ ≤ χ*k at hχ
  have hsum : R+frequencyFactor k D.m₀*S ≤ (R+χ*S)*k := by
    calc
      _ ≤ R*k+(χ*k)*S := add_le_add (le_mul_of_one_le_right hR hk)
        (mul_le_mul_of_nonneg_right hχ hS)
      _ = _ := by ring
  have hi : 9*C^2*(R+frequencyFactor k D.m₀*S)+2 ≤ (9*C^2*(R+χ*S)+2)*k := by
    calc
      _ ≤ 9*C^2*((R+χ*S)*k)+2*k := add_le_add
        (mul_le_mul_of_nonneg_left hsum (by positivity)) (by linarith)
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_left hi (sourceInverseRadius_pos C R hR).le).trans_eq (by
    unfold physicalRadiusCost
    dsimp only [χ]
    ring)

def physicalFixedCost (R C S : ℝ) (n : ℕ) : ℝ :=
  3*C*(physicalRadiusCost D R C S)^n*(n.factorial : ℝ)^2

theorem physicalFixedCost_nonneg (R C S : ℝ) (n : ℕ)
    (hR : 0 ≤ R) (hC : 0 ≤ C) (hS : 0 ≤ S) :
    0 ≤ physicalFixedCost D R C S n := by
  have hh := physicalRadiusCost_nonneg D R C S hR hS
  unfold physicalFixedCost
  positivity

variable (P κ k : ℝ) (e : Icc (0 : ℝ) D.T → LiftDomain P → Space)
  (he : ∀ t x, ContDiff ℝ ∞ (localFieldLift P (e t) x))
  (R C A S : ℝ) (hR : 0 ≤ R) (hC : 0 ≤ C) (hA : 0 ≤ A) (hS : 0 ≤ S)
  (hF : ∀ n t x,
    ‖iteratedFDeriv ℝ n (D.F.field t : Space → (Space →L[ℝ] Space)) x‖ ≤ C*majorant R 0 n)
  (hb : ∀ n t x, (∑ w : Fin n → Fin 4, ‖iteratedFieldDerivative P w (e t) x‖) ≤
    A*S^n*(n.factorial : ℝ)^2)
  (X Y : Icc (0 : ℝ) D.T → Space → Space)
  (hX : ∀ t x, HasFDerivAt (X t) (D.F.field t x) x)
  (hY : ∀ t, Differentiable ℝ (Y t))
  (hXY : ∀ t x, X t (Y t x) = x)
  (hdet : ∀ t x, (operatorMatrix (D.F.field t x)).det = 1)

include he hR hC hA hS hF hb hX hY hXY hdet in
theorem physicalReconstruction_power_bound (hk : 1 ≤ k) (hκ : |κ| ≤ 1)
    (n : ℕ) (t : Icc (0 : ℝ) D.T) (x : Space) :
    ‖iteratedFDeriv ℝ n (physicalReconstruction D P κ k e Y t) x‖ ≤
      physicalFixedCost D R C S n*A*k^n := by
  have h := physicalReconstruction_gevrey D P κ k e he R C A S hR hC hA hS hF hb
    X Y hX hY hXY hdet n t x
  have hL := (sourceInverseRadius_pos C R hR).le
  have hr : 0 ≤ physicalRadius D k R C S := by
    unfold physicalRadius
    have hf := frequencyFactor_nonneg k D.m₀
    positivity
  have ha : |κ| *3*C*A ≤ 3*C*A := by
    simpa only [one_mul,mul_assoc] using
      mul_le_mul_of_nonneg_right hκ (by positivity : 0 ≤ 3*C*A)
  have hbnd := mul_le_mul ha
    (pow_le_pow_left₀ hr (physicalRadius_le_linear D k R C S hk hR hS) n)
    (pow_nonneg hr n) (by positivity)
  exact h.trans ((mul_le_mul_of_nonneg_right hbnd (sq_nonneg (n.factorial : ℝ))).trans_eq
    (by unfold physicalFixedCost; rw [mul_pow]; ring))

end EulerPacketPhysicalGevrey
