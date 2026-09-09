/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.UnshiftedProducts
public import LeanPool.NavierStokesAndEuler.Euler.H6NonlinearPressure

@[expose] public section

/-! The lower Sobolev pressure estimate needed for the base energy commutator. -/

noncomputable section

namespace EulerH6Nonlinear

open MeasureTheory InnerProductSpace EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerVectorCylinder
  EulerJetProductBounds EulerSpatialSobolevInverse EulerPacketWeights EulerH6Pressure
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine pressure of transport has an unshifted H⁵ bound using only H⁶ velocity at the same external cutoff. -/
theorem nonlinear_pressure_lower_bound {s : ℕ} {A : SmoothCoefficient period} {F : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection s F)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 5 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 5 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 5 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Vector3)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
      period))
    (heL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w e) 2 (liftMeasure
      period))
    (hsource : (F : LiftDomain period → Vector3) =ᵐ[liftMeasure period] transportField period 3 b
      e) :
    (∑ n ∈ Finset.range (N+1), weight ρ n *
      blockNorm period (J.solvePressure K κ m c hc hpos) 5 n) ≤
      2 * M * (5460 * lowerProductConstant period 3) *
        (∑ l ∈ Finset.range (N+1), weight ρ l * wordSobolevNorm period 6 l b) *
        (∑ j ∈ Finset.range (N+1), weight ρ j * wordSobolevNorm period 6 j e) := by
  have hFs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (transportField period 3 b e) x) := by
    apply smooth_sum period Finset.univ
    intro i _ x
    exact (postcomp_smooth period (coordinate 4 i) b hb x).smul (fieldDerivative_smooth period _ e
      he x)
  have heq : (∑ n ∈ Finset.range (N+1), weight ρ n * blockNorm period J 5 n) =
      ∑ n ∈ Finset.range (N+1), weight ρ n *
        wordSobolevNorm period 5 n (transportField period 3 b e) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [blockNorm_eq_classical period J (by have := Finset.mem_range.mp hn; omega) _ hsource hFs]
  have hp := pressure_unshifted_Hq_bound period K J κ m c hc hpos N hN (by omega)
    ρ Rc M hρ hRc hM hbase hsmall hcoeff
  rw [heq] at hp
  have ht := mul_le_mul_of_nonneg_left
    (transport_lower_weighted_bound period N ρ hρ b e hb he hbL2 heL2)
    (show 0 ≤ 2*M by linarith)
  exact hp.trans (ht.trans_eq (by ring))


end EulerH6Nonlinear
