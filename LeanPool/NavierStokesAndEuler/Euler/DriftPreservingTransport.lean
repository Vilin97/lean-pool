/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.GevreyTransportCommutator
public import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureShifted

@[expose] public section

/-! Actual transport and pressure bounds retaining the small four-component drift norm. -/

noncomputable section

namespace EulerDriftPreservingTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure EulerPacketWeights
  EulerSobolevGevreyOperators EulerSobolevWordLevel EulerSobolevTransport EulerSobolevL2Product
  EulerFunctionalVelocity EulerH6Nonlinear EulerVectorCylinder EulerExternalTransportCommutator
  EulerSobolevGevreyProduct EulerSobolevHeat EulerSobolevTransportCommutator
  EulerSobolevCoefficientPressure EulerGevreyPressureTransport
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual external commutator keeps the weighted norm of the four genuine drift components, including scale and tangency gains. -/
theorem weightedCommutator_drift_smooth {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N+6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period)) :
    weightedCommutatorNorm period hs N hN ρ L hL u v ≤
      (productConstant period 3)*ρ⁻¹*
        (∑ n ∈ Finset.range (N+1), weight ρ n*wordSobolevNorm period 6 n (velocityMap L ∘ f))*
        weightedLoss period 6 N ρ v := by
  let b := velocityMap L ∘ f
  have hb := postcomp_smooth period (velocityMap L) f hf
  have hbL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
    period) :=
    fun j w => postcomp_word_memLp period (le_refl j) (velocityMap L) f hf (fun r _ a => hfL r a) w
  have heq : weightedCommutatorNorm period hs N hN ρ L hL u v =
      ∑ n ∈ Finset.range (N+1), weight ρ n*transportCommutatorNorm period n b g := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    apply Finset.sum_congr rfl
    intro w _
    exact externalCommutator_sumNorm period hs n.val w (by have := n.isLt; omega) L hL u v f g hu
      hv hf hg
  rw [heq]
  conv_rhs => rw [weightedLoss_eq_classical period 6 N (by omega) ρ v g hv hg]
  exact transportCommutator_weighted_bound period N ρ hρ b g hb hg hbL hgL

/-- The actual shifted coercive pressure bound retains the weighted drift norm instead of replacing it by the full vector-field norm. -/
theorem transportPressure_shifted_drift_smooth {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c*‖v‖^2 ≤ ⟪A.coefficient x v,v⟫_ℝ)
    (N : ℕ) (hN : N+6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4*M*(ρ*Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s+1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
      period))
    (hgL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
      period)) :
    shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (4*M*productConstant period 3)*
        (∑ n ∈ Finset.range (N+2), weight ρ n*wordSobolevNorm period 6 n (velocityMap L ∘ f))*
        weightedLoss period 6 (N+1) ρ v := by
  let b := velocityMap L ∘ f
  have hb := postcomp_smooth period (velocityMap L) f hf
  have hbL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w b) 2 (liftMeasure
    period) :=
    fun j w => postcomp_word_memLp period (le_refl j) (velocityMap L) f hf (fun r _ a => hfL r a) w
  have hp := nonlinear_pressure_shifted_bound period K (toJet period (transportBilinear period hs L
    hL u v))
    κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase hsmall hcoeff b g hb hg hbL hgL
    (transport_ae_velocityMap period hs L hL u v f g hu hv hg)
  have heq : shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL u v) =
      ∑ n ∈ Finset.range (N+1), ((n+1 : ℕ) : ℝ) * weight ρ (n+1) * blockNorm period
        ((toJet period (transportBilinear period hs L hL u v)).solvePressure K κ m c hc hpos) 6 n
          := by
    apply Finset.sum_congr rfl
    intro n hn
    exact congrArg (fun a : ℝ => ((n+1 : ℕ) : ℝ)*weight ρ (n+1)*a)
      (pressure_block_eq period (q := 6) (n := n) K κ m c hc hpos (transportBilinear period hs L hL
        u v)
        (by have := Finset.mem_range.mp hn; omega : n+6 ≤ s))
  rw [heq]
  conv_rhs => rw [weightedLoss_eq_classical period 6 (N+1) (by omega) ρ v g hv hg]
  exact hp

end EulerDriftPreservingTransport
