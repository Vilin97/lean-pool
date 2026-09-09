/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PhysicalGraphFlowBounds
public import LeanPool.NavierStokesAndEuler.Euler.PacketLiftedTimeBounds
import Mathlib.Algebra.Order.Star.Real

/-! A fixed actual correction and the derived approximation bounds
construct physical graph-flow data. No new solution or inverse is an input. -/

@[expose] public section


noncomputable section


namespace EulerAllOrderDriftCorrection

open Set MeasureTheory EulerAllOrderCorrectionData EulerLiftedGradientSpace EulerSmoothLimit
  EulerPacketCylinderField EulerPacketProfileRecursion EulerSobolevGevreyOperators
  EulerPhysicalGraphFlowBounds EulerCylinderCoverDescent
open scoped ContDiff

/-- Physical input radius, given by `max (liftedInputRadius R ρ) (liftedInputRadius Rt ρ)`. -/
def physicalInputRadius (R Rt ρ : ℝ) : ℝ :=
  max (liftedInputRadius R ρ) (liftedInputRadius Rt ρ)

/-- Physical input size, given by `liftedInputConstant P*((C0+Cn)/k+2*Ev)`. -/
def physicalInputSize (P k C0 Cn Ev : ℝ) [Fact (0 < P)] : ℝ :=
  liftedInputConstant P*((C0+Cn)/k+2*Ev)

theorem envelope_radius_mono {C R S : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (hRS : R ≤ S) (n : ℕ) :
    C*R^n*(n.factorial : ℝ)^2 ≤ C*S^n*(n.factorial : ℝ)^2 :=
  mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR hRS n) hC) (sq_nonneg _)

variable (P : ℝ) [Fact (0 < P)] {T : ℝ} {hT : 0 < T} {A : EulerAllOrderCorrectionData.Data P T}
  (B : Budget P hT A) {raw raw_t : VectorField}

/-- Physical flow data as an element of `EulerPhysicalGraphFlowBounds.Data P T`. -/
def Budget.physicalFlowData (G : Field P T raw) (H : Field P T raw_t)
    (hGfield : A.approximation = G.toFieldTower) (htime : TimeDerivative hT.le G H)
    (k R Rt ρ C0 Cn Ch Ev Et : ℝ)
    (hk : 1 ≤ k) (hκ : A.κ = k⁻¹) (hm : ‖A.direction‖ ≤ 1)
    (hR : 0 ≤ R) (hRt : 0 ≤ Rt) (hρ : 0 < ρ)
    (hC0 : 0 ≤ C0) (hCn : 0 ≤ Cn) (hCh : 0 ≤ Ch) (hEv : 0 ≤ Ev) (hEt : 0 ≤ Et)
    (hG : G.WordBound 6 R C0 0)
    (hN : (G.map (normalComponentMap A.direction)).WordBound 6 R (Cn / k) 0)
    (hH : H.WordBound 6 Rt Ch 0)
    (hE : ∀ n (t : Icc (0 : ℝ) T), weightedNorm P 6 n ρ
      ((B.fieldTower P).realization (n + 6) t) ≤ Ev)
    (hEtower : ∀ n (t : Icc (0 : ℝ) T), weightedNorm P 6 n ρ
      ((B.timeDerivativeTower P).realization (n + 6) t) ≤ Et)
    (hsmall : physicalInputSize P k C0 Cn Ev * physicalInputRadius R Rt ρ * T ≤ 1 / 8) :
    EulerPhysicalGraphFlowBounds.Data P T := by
  have hrv := (liftedInputRadius_pos R ρ hR hρ)
  have hrt := (liftedInputRadius_pos Rt ρ hRt hρ)
  have hK : 0 ≤ liftedInputConstant P := zero_le_one.trans (liftedInputConstant_one_le P)
  have hamp : 0 ≤ physicalInputSize P k C0 Cn Ev := by
    dsimp [physicalInputSize]
    positivity
  have hamp1 : 0 ≤ 2*liftedInputConstant P*(Ch+Et) := by positivity
  have hκ1 : |A.κ| ≤ 1 := by
    rw [hκ,abs_of_pos (inv_pos.mpr (by linarith : 0 < k))]
    exact inv_le_one_of_one_le₀ hk
  refine {
    time_nonneg := hT.le
    A := B.liftedPacketCoefficient P G
    A₁ := B.liftedPacketDerivativeCoefficient P H
    time_derivative := B.liftedPacketCoefficient_timeDerivative P G H htime
    periodic := B.liftedPacketCoefficient_periodic P G
    periodic_time := B.liftedPacketDerivativeCoefficient_periodic P H
    divergence := B.liftedPacketCoefficient_trace P G hGfield
    B := physicalInputSize P k C0 Cn Ev
    R := physicalInputRadius R Rt ρ
    C := physicalInputSize P k C0 Cn Ev
    S := physicalInputRadius R Rt ρ
    C₁ := 2*liftedInputConstant P*(Ch+Et)
    S₁ := physicalInputRadius R Rt ρ
    B_nonneg := hamp
    R_pos := hrv.trans_le (le_max_left _ _)
    C_nonneg := hamp
    S_nonneg := hrv.le.trans (le_max_left _ _)
    C₁_nonneg := hamp1
    S₁_nonneg := hrv.le.trans (le_max_left _ _)
    small := hsmall
    sup_bound := ?_
    integrable := fun t n => B.liftedPacketCoefficient_memLp P G hGfield n t
    lp_bound := ?_
    integrable_time := fun t n => B.liftedPacketDerivativeCoefficient_memLp P H n t
    lp_bound_time := ?_ }
  · intro n
    exact (B.liftedPacketCoefficient_jet_bound P G k R ρ C0 Cn Ev hk hκ hm
      hR hρ hC0 hCn hEv hG hN hE n).trans
      (envelope_radius_mono hamp hrv.le (le_max_left _ _) n)
  · intro t n
    exact (B.liftedPacketCoefficient_L2_bound P G hGfield k R ρ C0 Cn Ev hk hκ hm
      hR hρ hC0 hCn hEv hG hN hE n t).trans
      (envelope_radius_mono hamp hrv.le (le_max_left _ _) n)
  · intro t n
    exact (B.liftedPacketDerivativeCoefficient_L2_bound P H Rt ρ Ch Et hκ1 hm
      hRt hρ hCh hEt hH hEtower n t).trans
      (envelope_radius_mono hamp1 hrt.le (le_max_right _ _) n)

end EulerAllOrderDriftCorrection
