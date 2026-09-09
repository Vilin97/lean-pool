/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.H6TransportSource
public import LeanPool.NavierStokesAndEuler.Euler.H6Pressure
import LeanPool.NavierStokesAndEuler.Euler.Foundations.StrongSmoothJet
import LeanPool.NavierStokesAndEuler.Euler.Foundations.VectorCylinder
import LeanPool.NavierStokesAndEuler.Euler.H6PressureInverse

/-! Source18 for the actual coercively constructed pressure of the nonlinear transport source. -/

@[expose] public section


noncomputable section

namespace EulerH6Nonlinear

open MeasureTheory InnerProductSpace EulerSobolev EulerCylinderSobolev EulerCylinderAlgebra
  EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives EulerVectorCylinder
  EulerJetProductBounds EulerSpatialSobolevInverse EulerPacketWeights EulerH6Pressure
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual strong-jet Hq blocks equal the classical external-word Hq norms of any smooth
representative. -/
theorem blockNorm_eq_classical {s q n : ℕ} {U : LiftL2 period}
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection s U) (h : n + q ≤ s)
    (f : LiftDomain period → Vector3)
    (hrep : (U : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) :
    blockNorm period J q n = wordSobolevNorm period q n f := by
  rw [blockNorm_eq_word_sizes J h]
  apply Finset.sum_congr rfl
  intro w _
  rw [sobolevSize_eq period (EulerH6Pressure.SpatialJet.derivativeJet J w h)]
  exact EulerStrongSmoothJet.jet_sobolevNorm_eq period (J.word w)
    (EulerH6Pressure.SpatialJet.derivativeJet J w h) (iteratedFieldDerivative period w f)
    (EulerStrongSmoothJet.jet_word_ae period (by omega) U J w f hrep hf)
    (iteratedFieldDerivative_smooth period w f hf)

/-- Source18's shifted H⁶ estimate for the genuine pressure of b·∇e.
The largest velocity order is N+1 and the largest pressure order is N. -/
theorem nonlinear_pressure_shifted_bound {s : ℕ} {A : SmoothCoefficient period} {F : LiftL2 period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (J : EulerSpatialSobolevInverse.SpatialJet period standardDirection s F)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (b : LiftDomain period → Domain 4) (e : LiftDomain period → Vector3)
    (hb : ∀ x, ContDiff ℝ ∞ (localFieldLift period b x))
    (he : ∀ x, ContDiff ℝ ∞ (localFieldLift period e x))
    (hbL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
        period))
    (heL2 : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w e) 2 (liftMeasure
        period))
    (hsource : (F : LiftDomain period → Vector3) =ᵐ[liftMeasure period] transportField period 3 b
        e) :
    (∑ n ∈ Finset.range (N+1), ((n+1 : ℕ) : ℝ) * weight ρ (n+1) *
      blockNorm period (J.solvePressure K κ m c hc hpos) 6 n) ≤
      4 * M * productConstant period 3 *
        (∑ l ∈ Finset.range (N+2), weight ρ l * wordSobolevNorm period 6 l b) *
        (∑ j ∈ Finset.range (N+2), (j : ℝ) * weight ρ j * wordSobolevNorm period 6 j e) := by
  have hFs : ∀ x, ContDiff ℝ ∞ (localFieldLift period (transportField period 3 b e) x) := by
    apply smooth_sum period Finset.univ
    intro i _ x
    exact (postcomp_smooth period (coordinate 4 i) b hb x).smul (fieldDerivative_smooth period _ e
        he x)
  have heq : (∑ n ∈ Finset.range (N+1), ((n+1 : ℕ) : ℝ) * weight ρ (n+1) * blockNorm period J 6 n) =
      ∑ n ∈ Finset.range (N+1), ((n+1 : ℕ) : ℝ) * weight ρ (n+1) *
        wordSobolevNorm period 6 n (transportField period 3 b e) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [blockNorm_eq_classical period J (by have := Finset.mem_range.mp hn; omega) _ hsource hFs]
  have hp := pressure_shifted_Hq_bound K J κ m c hc hpos N hN (by omega)
    ρ Rc M hρ hRc hM hbase hsmall hcoeff
  rw [heq] at hp
  have ht := mul_le_mul_of_nonneg_left
    (transport_shifted_weighted_bound period 3 (N+1) ρ hρ b e hb he hbL2 heL2)
    (show 0 ≤ 2*M by linarith)
  exact hp.trans (ht.trans_eq (by ring))

end EulerH6Nonlinear
