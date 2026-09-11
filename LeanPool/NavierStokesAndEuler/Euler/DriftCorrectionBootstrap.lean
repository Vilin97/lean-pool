/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyBootstrap
import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyScalar
import LeanPool.NavierStokesAndEuler.Euler.IntegralEnergyBootstrap
import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyRestriction
import LeanPool.NavierStokesAndEuler.Euler.MildMajorantEnergy
import LeanPool.NavierStokesAndEuler.Euler.SobolevMaximalRegularity
public import LeanPool.NavierStokesAndEuler.Euler.DriftCorrectionBudget
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyMajorants
public import LeanPool.NavierStokesAndEuler.Euler.TimeLpSubintervalBound
public import LeanPool.NavierStokesAndEuler.Euler.SobolevDriftNorm
public import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionBound
public import LeanPool.NavierStokesAndEuler.Euler.GevreyOrderZero
import LeanPool.NavierStokesAndEuler.Euler.GevreyNonlinearEstimate
import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureComplete
import LeanPool.NavierStokesAndEuler.Euler.GevreyUniformConstants
import LeanPool.NavierStokesAndEuler.Euler.WeightedForcingAlgebra
import Mathlib.Algebra.Order.Star.Real
public import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureShifted
import LeanPool.NavierStokesAndEuler.Euler.HeatAllOrders
import LeanPool.NavierStokesAndEuler.Euler.H6NonlinearPressure
public import LeanPool.NavierStokesAndEuler.Euler.NonlinearEnergyConstants
import LeanPool.NavierStokesAndEuler.Euler.GevreyGrowthCoefficient

/-! The actual nonlinear viscous correction closes its shrinking-radius Gevrey bootstrap from the
constructed mild equation. -/

section

/-! Separate the full background norm from the drift norm in the radius-loss term. -/

@[expose] public section

noncomputable section

namespace EulerDriftEnergyConstants

open EulerGevreyCorrectionBound EulerGevreyMetricEstimate EulerGevreyGrowthCoefficient
  EulerNonlinearEnergyConstants

variable (period : ℝ) [Fact (0 < period)]

/-- The full velocity enters the zero-order coefficient; only the drift enters the loss term. -/
def forcingPolynomial (B M Z0 B0 B1 A0 A2 residual c Rc ρ X Y : ℝ) : ℝ :=
  sourceConstant B M * residual + linearCoefficient period B M Z0 B1 A0 A2 c * X +
    quadraticCoefficient period B M A2 c * X ^ 2 +
    lossCoefficient period M c * (ρ⁻¹ + Rc) * (B0 + X) * Y

/-- The existing polynomial growth constant absorbs the sharp drift forcing without
replacing its small drift envelope by the full background envelope. -/
theorem actual_scalar_bound (g0 g1 k B M Z0 B0 B1 A0 A2 c Rc ρ residual X Y b : ℝ)
    (hg0 : 0 ≤ g0) (hg1 : 0 ≤ g1) (hk : 0 ≤ k) (hB : 0 ≤ B) (hM : 0 ≤ M)
    (hZ0 : 0 ≤ Z0) (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (hA0 : 0 ≤ A0)
    (hA2 : 0 ≤ A2) (hc : 0 < c) (hRc : 0 ≤ Rc) (hρ : 0 < ρ)
    (hr : 0 ≤ residual) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    let C := energyConstant period g0 g1 k B M Z0 B1 A0 A2 c
    (g0 + g1 * X) * X + b * Y +
        k * forcingPolynomial period B M Z0 B0 B1 A0 A2 residual c Rc ρ X Y ≤
      C * (X + X ^ 2 + residual) + (b + C * (ρ⁻¹ + Rc) * (B0 + X)) * Y := by
  obtain ⟨hl, hq, hd⟩ := coefficients_nonneg period B M Z0 B1 A0 A2 c
    hB hM hZ0 hB1 hA0 hA2 hc
  have hs := sourceConstant_nonneg hB hM
  have h := absorb_scalar_coefficients g0 g1 (k * sourceConstant B M)
    (k * linearCoefficient period B M Z0 B1 A0 A2 c)
    (k * quadraticCoefficient period B M A2 c) (k * lossCoefficient period M c)
    residual X Y B0 (ρ⁻¹ + Rc) (energyConstant period g0 g1 k B M Z0 B1 A0 A2 c)
    hg0 hg1 (mul_nonneg hk hs) (mul_nonneg hk hl) (mul_nonneg hk hq)
    (mul_nonneg hk hd) hr hX hY hB0 (add_nonneg (inv_nonneg.mpr hρ.le) hRc)
    (le_refl _) b
  calc
    _ = (g0 + g1 * X) * X + b * Y +
        ((k * sourceConstant B M) * residual +
        (k * linearCoefficient period B M Z0 B1 A0 A2 c) * X +
        (k * quadraticCoefficient period B M A2 c) * X ^ 2 +
        (k * lossCoefficient period M c) * (ρ⁻¹ + Rc) * (B0 + X) * Y) := by
      unfold forcingPolynomial
      ring
    _ ≤ _ := h

end EulerDriftEnergyConstants

end
end

end

section

/-! The actual correction forcing in metric energy with distinct full-background and small-drift
budgets. -/

section

/-! Sharp drift-preserving transport and pressure estimates for actual finite Sobolev fields. -/

section

/-! Actual transport and pressure bounds retaining the small four-component drift norm. -/

@[expose] public section

noncomputable section

namespace EulerDriftPreservingTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure EulerPacketWeights
  EulerSobolevGevreyOperators EulerSobolevWordLevel EulerSobolevTransport EulerSobolevL2Product
  EulerFunctionalVelocity EulerH6Nonlinear EulerVectorCylinder EulerExternalTransportCommutator
   EulerSobolevHeat EulerSobolevTransportCommutator
  EulerSobolevCoefficientPressure EulerGevreyPressureTransport
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual external commutator keeps the weighted norm of the four genuine drift components,
including scale and tangency gains. -/
theorem weightedCommutator_drift_smooth {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
        period))
    (hgL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
        period)) :
    weightedCommutatorNorm period hs N hN ρ L hL u v ≤
      (productConstant period 3)*ρ⁻¹ *
        (∑ n ∈ Finset.range (N+1), weight ρ n*wordSobolevNorm period 6 n (velocityMap L ∘ f)) *
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
    exact externalCommutator_sumNorm period hs n.val w (by
        have := n.isLt; omega) L hL u v f g hu hv hf hg
  rw [heq]
  conv_rhs => rw [weightedLoss_eq_classical period 6 N (by omega) ρ v g hv hg]
  exact transportCommutator_weighted_bound period N ρ hρ b g hb hg hbL hgL

/-- The actual shifted coercive pressure bound retains the weighted drift norm instead of replacing
it by the full vector-field norm. -/
theorem transportPressure_shifted_drift_smooth {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f g : LiftDomain period → Vector3)
    (hu : (value period u : LiftDomain period → Vector3) =ᵐ[liftMeasure period] f)
    (hv : (value period v : LiftDomain period → Vector3) =ᵐ[liftMeasure period] g)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hg : ∀ x, ContDiff ℝ ∞ (localFieldLift period g x))
    (hfL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w f) 2 (liftMeasure
        period))
    (hgL : ∀ j, ∀ w : Fin j → Fin 4, MemLp (iteratedFieldDerivative period w g) 2 (liftMeasure
        period)) :
    shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (4*M*productConstant period 3) *
        (∑ n ∈ Finset.range (N+2), weight ρ n*wordSobolevNorm period 6 n (velocityMap L ∘ f)) *
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

end
end

end

@[expose] public section

noncomputable section

namespace EulerSobolevDriftTransport

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerMetricTransport EulerH6Pressure EulerPacketWeights
  EulerSobolevGevreyOperators EulerSobolevWordLevel EulerSobolevTransport EulerSobolevL2Product
  EulerFunctionalVelocity EulerH6Nonlinear EulerVectorCylinder EulerExternalTransportCommutator
   EulerSobolevHeat EulerSobolevTransportCommutator
  EulerSobolevCoefficientPressure EulerGevreyPressureTransport EulerSobolevDriftNorm
      EulerDriftPreservingTransport
open scoped ContDiff ENNReal Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine finite-Sobolev commutator retains the actual small drift norm in its radius-loss
factor. -/
theorem weightedCommutator_drift_bound {s : ℕ} (hs : 6 ≤ s) (N : ℕ) (hN : N + 6 ≤ s)
    (ρ : ℝ) (hρ : 0 < ρ) (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    weightedCommutatorNorm period hs N hN ρ L hL u v ≤
      (productConstant period 3)*ρ⁻¹*weightedDriftNorm period 6 N ρ (velocityMap L) u*weightedLoss
          period 6 N ρ v := by
  let U : ℕ → SobolevSpace period (s+1) := fun n => restrictOperator period (by
      omega : s+1 ≤ s+1+3) (smoothApprox period (s+1) n u)
  let V : ℕ → SobolevSpace period (s+1) := fun n => restrictOperator period (by
      omega : s+1 ≤ s+1+3) (smoothApprox period (s+1) n v)
  have hU : Filter.Tendsto U Filter.atTop (𝓝 u) := smoothApprox_tendsto period u
  have hV : Filter.Tendsto V Filter.atTop (𝓝 v) := smoothApprox_tendsto period v
  have hpairs : Filter.Tendsto (fun n => (U n,V n)) Filter.atTop (𝓝 (u,v)) := hU.prodMk_nhds hV
  have hC : Filter.Tendsto
      (fun p : SobolevSpace period (s+1) × SobolevSpace period (s+1) => weightedCommutatorNorm
          period hs N hN ρ L hL p.1 p.2)
      (𝓝 (u,v)) (𝓝 (weightedCommutatorNorm period hs N hN ρ L hL u v)) :=
    (continuous_weightedCommutatorNorm period hs N hN ρ L hL).tendsto (u,v)
  have hleft := hC.comp hpairs
  have hW : Continuous (weightedDriftNorm period (s := s+1) 6 N ρ (velocityMap L)) :=
      continuous_weightedDriftNorm period 6 N (by
      omega) ρ (velocityMap L)
  have hY : Continuous (weightedLoss period (s := s+1) 6 N ρ) := continuous_weightedLoss period 6 N
      (by
      omega) ρ
  have hright : Filter.Tendsto (fun n => (productConstant period 3)*ρ⁻¹*weightedDriftNorm period 6
      N ρ (velocityMap L) (U n)*weightedLoss period 6 N ρ (V n))
      Filter.atTop (𝓝 ((productConstant period 3)*ρ⁻¹*weightedDriftNorm period 6 N ρ (velocityMap
          L) u*weightedLoss period 6 N ρ v)) :=
    ((hW.tendsto u |>.comp hU).const_mul ((productConstant period 3)*ρ⁻¹)).mul (hY.tendsto v
        |>.comp hV)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨f,hf,hfs,hfL⟩ := smoothApprox_representative_all period n u
  obtain ⟨g,hg,hgs,hgL⟩ := smoothApprox_representative_all period n v
  change weightedCommutatorNorm period hs N hN ρ L hL (U n) (V n) ≤
    productConstant period 3 * ρ⁻¹ * weightedDriftNorm period 6 N ρ (velocityMap L) (U n) *
        weightedLoss period 6 N ρ (V n)
  rw [weightedDriftNorm_eq_classical period 6 N (by omega) ρ (velocityMap L) (U n) f hf hfs]
  exact weightedCommutator_drift_smooth period hs N hN ρ hρ L hL (U n) (V n) f g hf hg hfs hgs hfL
      hgL

/-- The actual rough finite-Sobolev pressure estimate retains the small drift norm. -/
theorem transportPressure_shifted_drift {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (4*M*productConstant period 3)*weightedDriftNorm period 6 (N+1) ρ (velocityMap L)
          u*weightedLoss period 6 (N+1) ρ v := by
  let U : ℕ → SobolevSpace period (s+1) := fun n => restrictOperator period (by
      omega : s+1 ≤ s+1+3) (smoothApprox period (s+1) n u)
  let V : ℕ → SobolevSpace period (s+1) := fun n => restrictOperator period (by
      omega : s+1 ≤ s+1+3) (smoothApprox period (s+1) n v)
  have hU : Filter.Tendsto U Filter.atTop (𝓝 u) := smoothApprox_tendsto period u
  have hV : Filter.Tendsto V Filter.atTop (𝓝 v) := smoothApprox_tendsto period v
  have hpairs : Filter.Tendsto (fun n => (U n,V n)) Filter.atTop (𝓝 (u,v)) := hU.prodMk_nhds hV
  have hP : Filter.Tendsto
      (fun p : SobolevSpace period (s+1) × SobolevSpace period (s+1) => transportPressure period hs
          K κ m c hc hpos L hL p.1 p.2)
      (𝓝 (u,v)) (𝓝 (transportPressure period hs K κ m c hc hpos L hL u v)) :=
    (transportPressure_continuous period hs K κ m c hc hpos L hL).tendsto (u,v)
  have hpress := hP.comp hpairs
  have hW5 : Continuous (shiftedPressureNorm period (s := s) N ρ) := continuous_shiftedPressureNorm
      period N hN ρ
  have hleft := (hW5.tendsto _).comp hpress
  have hW : Continuous (weightedDriftNorm period (s := s+1) 6 (N+1) ρ (velocityMap L)) :=
      continuous_weightedDriftNorm period 6 (N+1) (by
      omega) ρ (velocityMap L)
  have hY : Continuous (weightedLoss period (s := s+1) 6 (N+1) ρ) := continuous_weightedLoss period
      6 (N+1) (by
      omega) ρ
  have hright : Filter.Tendsto (fun n => (4*M*productConstant period 3)*weightedDriftNorm period 6
      (N+1) ρ (velocityMap L) (U n)*weightedLoss period 6 (N+1) ρ (V n))
      Filter.atTop (𝓝 ((4*M*productConstant period 3)*weightedDriftNorm period 6 (N+1) ρ
          (velocityMap L) u*weightedLoss period 6 (N+1) ρ v)) :=
    ((hW.tendsto u |>.comp hU).const_mul (4*M*productConstant period 3)).mul (hY.tendsto v |>.comp
        hV)
  apply le_of_tendsto_of_tendsto hleft hright
  apply Filter.Eventually.of_forall
  intro n
  obtain ⟨f,hf,hfs,hfL⟩ := smoothApprox_representative_all period n u
  obtain ⟨g,hg,hgs,hgL⟩ := smoothApprox_representative_all period n v
  change shiftedPressureNorm period N ρ (transportPressure period hs K κ m c hc hpos L hL (U n) (V
      n)) ≤
    (4*M*productConstant period 3) * weightedDriftNorm period 6 (N+1) ρ (velocityMap L) (U n) *
        weightedLoss period 6 (N+1) ρ (V n)
  rw [weightedDriftNorm_eq_classical period 6 (N+1) (by omega) ρ (velocityMap L) (U n) f hf hfs]
  exact transportPressure_shifted_drift_smooth period hs K κ m c hc hpos N hN ρ Rc M hρ hRc hM
      hbase hsmall hcoeff
    L hL (U n) (V n) f g hf hg hfs hgs hfL hgL

end EulerSobolevDriftTransport

end
end

end

section

/-! Actual nonlinear correction forcing with distinct full-velocity and drift factors. -/

@[expose] public section

noncomputable section

namespace EulerDriftCorrectionForcing

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerPacketWeights EulerSobolevGevreyOperators
  EulerBaseWordMetric EulerFiniteMetricEnergy EulerWeightedCylinderEnergy
      EulerGevreyMetricComparison
  EulerSobolevWordLevel EulerSobolevTransportCommutator EulerGevreyPressureEnergy
      EulerBasePressureCommutator
  EulerGevreyBaseTransport EulerGevreyForcingComponents EulerWeightedForcingAlgebra
  EulerGevreyPressureTransport EulerSobolevCoefficientPressure EulerH6Nonlinear EulerBaseTransportL2
  EulerGevreyCorrectionForcing EulerGevreyCorrectionBound EulerGevreyUniformConstants
  EulerSobolevDriftNorm EulerSobolevDriftTransport EulerFunctionalVelocity

variable (period : ℝ) [Fact (0 < period)]

/-- The nonlinear external pressure commutator keeps the actual drift norm at positive cutoff. -/
theorem nonlinear_externalPressure_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : (N + 1) + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N + 1 → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^
        2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    externalPressureNorm period K (N+1) ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (8*Rc*M*productConstant period 3)*weightedDriftNorm period 6 (N+1) ρ (velocityMap L)
          u*weightedLoss period 6 (N+1) ρ v := by
  have hhalf : ρ*Rc ≤ 1/2 := by nlinarith [mul_nonneg hρ.le hRc]
  have hcN : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc^l*(l.factorial : ℝ)^2 :=
    fun l hl hn => hcoeff l hl (by omega)
  have hp := transportPressure_shifted_drift period hs K κ m c hc hpos N (by
      omega) ρ Rc M hρ hRc hM hbase hsmall hcN L hL u v
  exact (externalPressureNorm_shifted period K N hN ρ Rc hρ hRc hhalf hcoeff _).trans
    ((mul_le_mul_of_nonneg_left hp (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hRc)).trans_eq (by ring))

/-- The sharp external pressure bound also includes zero cutoff. -/
theorem nonlinear_externalPressure_bound_all {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) :
    externalPressureNorm period K N ρ (transportPressure period hs K κ m c hc hpos L hL u v) ≤
      (8*Rc*M*productConstant period 3)*weightedDriftNorm period 6 N ρ (velocityMap L)
          u*weightedLoss period 6 N ρ v := by
  cases N with
  | zero => simp [externalPressureNorm, weightedLoss, commutatorBlock_zero]
  | succ N =>
      exact nonlinear_externalPressure_bound period hs K κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase
          hsmall hcoeff L hL u v

/-- Seven actual forcing arrays retain the sharp drift commutator factor. -/
theorem correctionForcing_raw_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ : ℝ) (hρ : 0 < ρ)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f p0 p1 : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val) (correctionForcing period hs K K0 N hN
        L hL u v f p0 p1) ≤
      weightedNorm period 6 N ρ f + (productConstant period 3)*ρ⁻¹*weightedDriftNorm period 6 N ρ
          (velocityMap L) u*weightedLoss period 6 N ρ v +
      (5461*baseTransportConstant period)*weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v +
      externalPressureNorm period K N ρ p0 + basePressureNorm period K0 N hN ρ p0 +
      externalPressureNorm period K N ρ p1 + basePressureNorm period K0 N hN ρ p1 := by
  have h := forcing_seven_le ρ hρ (fun I : ExternalWord N => I.1.val)
    (-energyValues period 6 N hN f) (-externalTransportForcing period hs N hN L hL u v)
    (-baseTransportForcing period N hN L hL u v) (externalPressureForcing period K N hN p0)
    (basePressureForcing period K0 N hN p0) (externalPressureForcing period K N hN p1)
    (basePressureForcing period K0 N hN p1)
  simp only [weightedForcingSum_neg] at h
  have hS := sourceForcing_weighted_bound period N hN ρ hρ f
  have hE := (externalTransportForcing_bound period hs N hN ρ hρ L hL u v).trans
    (weightedCommutator_drift_bound period hs N hN ρ hρ L hL u v)
  have hB := baseTransportForcing_weighted_bound period N hN ρ hρ L hL u v
  have hP0 := externalPressureForcing_bound period K N hN ρ hρ p0
  have hQ0 := basePressureForcing_bound period K0 N hN ρ hρ p0
  have hP1 := externalPressureForcing_bound period K N hN ρ hρ p1
  have hQ1 := basePressureForcing_bound period K0 N hN ρ hρ p1
  exact h.trans (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add (add_le_add hS hE) hB)
      hP0) hQ0) hP1) hQ1)

/-- The full actual forcing with both genuine projected pressure solves obeys the spatial part of
equation (19).
Every velocity derivative in the bound lies at or below the chosen cutoff. -/
theorem correctionForcing_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict K 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs K K0 N hN L hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f) (transportPressure period hs K κ m c hc
            hpos L hL u v)) ≤
      (1+2*M*(weightedCoefficient period K 6 N ρ + 448*baseCoefficientSum period K0))*weightedNorm
          period 6 N ρ f +
      (5461*baseTransportConstant period + (448*baseCoefficientSum period
          K0)*(8*M*(5460*lowerProductConstant period 3))) *
        weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v +
      ((productConstant period 3)*ρ⁻¹ + 8*Rc*M*productConstant period 3) *
        weightedDriftNorm period 6 N ρ (velocityMap L) u*weightedLoss period 6 N ρ v := by
  let p0 := pressureSobolevOperator period K κ m c hc hpos f
  let p1 := transportPressure period hs K κ m c hc hpos L hL u v
  have h := correctionForcing_raw_bound period hs K K0 N hN ρ hρ L hL u v f p0 p1
  have hp0 := source_pressure_commutators period K K0 κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase6
      hsmall hcoeff f
  have hp1e := nonlinear_externalPressure_bound_all period hs K κ m c hc hpos N hN ρ Rc M hρ hRc hM
      hbase6 hsmall hcoeff L hL u v
  have hp1b := nonlinear_basePressure_bound period hs K K0 κ m c hc hpos N hN ρ Rc M hρ hRc hM
      hbase5 hsmall hcoeff L hL u v
  change externalPressureNorm period K N ρ p0 + basePressureNorm period K0 N hN ρ p0 ≤ _ at hp0
  change externalPressureNorm period K N ρ p1 ≤ _ at hp1e
  change basePressureNorm period K0 N hN ρ p1 ≤ _ at hp1b
  nlinarith only [h, hp0, hp1e, hp1b]

/-- Uniform fixed-base constants preserve the separate drift norm. -/
theorem correctionForcing_uniform_bound {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (K : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (K0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M B : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict K 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict K 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period K 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (hB : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period K r ≤ B)
    (hB0 : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period K0 r ≤ B)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period (s + 1)) (f : SobolevSpace period s) :
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs K K0 N hN L hL u v f
        (pressureSobolevOperator period K κ m c hc hpos f) (transportPressure period hs K κ m c hc
            hpos L hL u v)) ≤
      sourceConstant B M*weightedNorm period 6 N ρ f +
        transportConstant period B M*weightedNorm period 6 N ρ u*weightedNorm period 6 N ρ v +
        (productConstant period 3*ρ⁻¹+8*Rc*M*productConstant period 3)*weightedDriftNorm period 6 N
            ρ (velocityMap L) u*weightedLoss period 6 N ρ v := by
  have hhalf : ρ*Rc ≤ 1/2 := by nlinarith [mul_nonneg hρ.le hRc]
  have hw := weightedCoefficient_uniform period K N ρ Rc B hρ hRc hhalf hB hcoeff
  have hb := baseCoefficientSum_le period K0 B hB0
  have hM0 : 0 ≤ M := by linarith
  have hsf : 1+2*M*(weightedCoefficient period K 6 N ρ+448*baseCoefficientSum period K0) ≤
      sourceConstant B M := by
    have h := add_le_add (le_refl (1 : ℝ)) (mul_le_mul_of_nonneg_left
      (add_le_add hw (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 448)))
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hM0))
    exact h.trans_eq (by unfold sourceConstant; ring)
  have htf : 5461*baseTransportConstant period+(448*baseCoefficientSum period
      K0)*(8*M*(5460*lowerProductConstant period 3)) ≤
      transportConstant period B M := by
    have hp : 0 ≤ 8*M*(5460*lowerProductConstant period 3) :=
      mul_nonneg (mul_nonneg (by
          norm_num) hM0) (mul_nonneg (by norm_num) (lowerProductConstant_nonneg period 3))
    have h := add_le_add (le_refl (5461*baseTransportConstant period)) (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 448)) hp)
    exact h.trans_eq (by unfold transportConstant; ring)
  have h := correctionForcing_bound period hs K K0 κ m c hc hpos N hN ρ Rc M hρ hRc hM hbase5
      hbase6 hsmall hcoeff L hL u v f
  exact h.trans (add_le_add (add_le_add
    (mul_le_mul_of_nonneg_right hsf (weightedNorm_nonneg period 6 N ρ hρ f))
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right htf (weightedNorm_nonneg period 6 N ρ
        hρ u))
      (weightedNorm_nonneg period 6 N ρ hρ v)))
    (le_refl _))

end EulerDriftCorrectionForcing

end
end

end

section

/-! Actual nonlinear forcing with separate full-background and drift envelopes. -/

@[expose] public section

noncomputable section

namespace EulerDriftNonlinearEstimate

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators
      EulerGevreyCorrectionForcing
  EulerH6Nonlinear EulerSobolevTransportCommutator EulerGevreyPressureTransport
      EulerSobolevCoefficientPressure
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy
      EulerGevreyOrderZero
  EulerGevreyCorrectionBound EulerGevreyNonlinearEstimate EulerSobolevDriftNorm
      EulerFunctionalVelocity

/-- The factor four is spent only on the correction drift, recovering the original uniform loss
constant. -/
theorem drift_loss_absorption (P M Rc ρ B E Y D : ℝ)
    (hP : 0 ≤ P) (hM : 0 ≤ M) (hRc : 0 ≤ Rc) (hρ : 0 < ρ)
    (hB : 0 ≤ B) (hE : 0 ≤ E) (hY : 0 ≤ Y) (hD : D ≤ 4 * (B + E)) :
    (P*ρ⁻¹+8*Rc*M*P)*D*Y ≤ ((4+32*M)*P)*(ρ⁻¹+Rc)*(B+E)*Y := by
  have ha : 0 ≤ P*ρ⁻¹+8*Rc*M*P := by positivity
  have hc : 4*(P*ρ⁻¹+8*Rc*M*P) ≤ ((4+32*M)*P)*(ρ⁻¹+Rc) := by
    have h1 := mul_nonneg hP hRc
    have h2 := mul_nonneg (mul_nonneg hM hP) (inv_nonneg.mpr hρ.le)
    nlinarith only [h1,h2]
  calc
    _ ≤ (P*ρ⁻¹+8*Rc*M*P)*(4*(B+E))*Y :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hD ha) hY
    _ = (4*(P*ρ⁻¹+8*Rc*M*P))*(B+E)*Y := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (add_nonneg hB hE)) hY

/-- Scalar assembly keeps the independent full-velocity and drift envelopes in their respective
terms. -/
theorem polynomial_assembly (S T D Z B P B1 A0 A2 R E Y V F H : ℝ)
    (hS : 0 ≤ S) (hT : 0 ≤ T) (hE : 0 ≤ E)
    (hV : V ≤ Z + E) (hF : F ≤ R + (P * B1 + A0 + 2 * A2 * P * Z) * E + A2 * P * E ^ 2)
    (hH : H ≤ S * F + T * V * E + D * (B + E) * Y) :
    H ≤ S*R+(S*(P*B1+A0+2*A2*P*Z)+T*Z)*E+(S*A2*P+T)*E^2+D*(B+E)*Y := by
  have h := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hF hS)
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hV hT) hE)) (le_refl (D*(B+E)*Y))
  exact hH.trans (h.trans_eq (by ring))

variable (period : ℝ) [Fact (0 < period)]

/-- The literal seven-term Euler forcing has a scalar bound preserving the actual small background
drift. -/
theorem correctionForcing_polynomial {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (KG : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (KG0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M B : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict KG 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict KG 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period KG 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (hG : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period KG r ≤ B)
    (hG0 : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period KG0 r ≤ B)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SmoothCoefficient period) (K0 : EulerSpatialSobolevInverse.CoefficientJet period
        standardDirection s C0)
    (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period standardDirection s (C i))
    (z e : SobolevSpace period (s + 1)) (r : SobolevSpace period s)
    (Z0 B0 B1 A0 A2 R : ℝ) (hA2 : 0 ≤ A2)
    (hz : weightedNorm period 6 N ρ z ≤ Z0)
    (hb : weightedDriftNorm period 6 N ρ (velocityMap L) z ≤ B0)
    (hdz : (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period s i z)) ≤ B1)
    (hC0 : weightedCoefficient period K0 6 N ρ ≤ A0)
    (hC : (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) ≤ A2)
    (hr : weightedNorm period 6 N ρ r ≤ R) :
    let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
      (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs KG KG0 N hN L hL (z+e) e f
        (pressureSobolevOperator period KG κ m c hc hpos f) (transportPressure period hs KG κ m c
            hc hpos L hL (z+e) e)) ≤
      sourceConstant B M*R +
      (sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
          3*Z0)+transportConstant period B M*Z0) *
        weightedNorm period 6 N ρ e +
      (sourceConstant B M*A2*productConstant period 3+transportConstant period B M)*(weightedNorm
          period 6 N ρ e)^2 +
      lossConstant period M*(ρ⁻¹+Rc)*(B0+weightedNorm period 6 N ρ e)*weightedLoss period 6 N ρ e
          := by
  let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
    (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
  have hf := orderZeroSource_uniform period hs N hN ρ hρ L hL C0 K0 C K z e r Z0 B1 A0 A2 R hA2 hz
      hdz hC0 hC hr
  have hv := (weightedNorm_add_le period 6 N (by omega : N+6 ≤ s+1) ρ hρ z e).trans
    (add_le_add hz (le_refl (weightedNorm period 6 N ρ e)))
  have hB0 : 0 ≤ B0 := (weightedDriftNorm_nonneg period 6 N ρ hρ (velocityMap L) z).trans hb
  have heD := weightedDriftNorm_velocityMap_le period 6 N ρ hρ L hL e
  have hD : weightedDriftNorm period 6 N ρ (velocityMap L) (z+e) ≤
      4*(B0+weightedNorm period 6 N ρ e) := by
    have h := (weightedDriftNorm_add_le period 6 N (by
        omega : N+6 ≤ s+1) ρ hρ (velocityMap L) z e).trans
      (add_le_add hb heD)
    nlinarith only [h,hB0]
  have hraw := EulerDriftCorrectionForcing.correctionForcing_uniform_bound period hs KG KG0 κ m c
      hc hpos
    N hN ρ Rc M B hρ hRc hM hbase5 hbase6 hsmall hcoeff hG hG0 L hL (z+e) e f
  have hloss : (productConstant period 3*ρ⁻¹+8*Rc*M*productConstant period 3) *
      weightedDriftNorm period 6 N ρ (velocityMap L) (z+e)*weightedLoss period 6 N ρ e ≤
      lossConstant period M*(ρ⁻¹+Rc)*(B0+weightedNorm period 6 N ρ e)*weightedLoss period 6 N ρ e
          := by
    simpa only [lossConstant] using drift_loss_absorption (productConstant period 3) M Rc ρ B0
      (weightedNorm period 6 N ρ e) (weightedLoss period 6 N ρ e)
      (weightedDriftNorm period 6 N ρ (velocityMap L) (z+e))
      (productConstant_nonneg period 3) (by linarith) hRc hρ hB0
      (weightedNorm_nonneg period 6 N ρ hρ e) (weightedLoss_nonneg period 6 N ρ hρ e) hD
  have h := hraw.trans (add_le_add (le_refl _) hloss)
  exact polynomial_assembly (sourceConstant B M) (transportConstant period B M)
    (lossConstant period M*(ρ⁻¹+Rc)) Z0 B0 (productConstant period 3) B1 A0 A2 R
    (weightedNorm period 6 N ρ e) (weightedLoss period 6 N ρ e) (weightedNorm period 6 N ρ (z+e))
    (weightedNorm period 6 N ρ f) _
    (sourceConstant_nonneg hB (by linarith)) (transportConstant_nonneg period hB (by linarith))
    (weightedNorm_nonneg period 6 N ρ hρ e) hv hf h

end EulerDriftNonlinearEstimate

end
end

end

@[expose] public section

noncomputable section

namespace EulerDriftMetricForcing

open MeasureTheory InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerH6Pressure EulerSobolevGevreyOperators
      EulerGevreyCorrectionForcing
  EulerH6Nonlinear EulerSobolevTransportCommutator EulerGevreyPressureTransport
      EulerSobolevCoefficientPressure
  EulerGevreyMetricComparison EulerWeightedCylinderEnergy
      EulerGevreyOrderZero
  EulerGevreyCorrectionBound EulerGevreyMetricEstimate EulerSobolevDriftNorm EulerFunctionalVelocity

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine seven-term correction forcing obeys the metric polynomial retaining the small drift
envelope. -/
theorem correctionForcing_metric {s : ℕ} (hs : 6 ≤ s) {A : SmoothCoefficient period}
    (KG : EulerSpatialSobolevInverse.CoefficientJet period standardDirection s A)
    (KG0 : EulerSpatialSobolevInverse.CoefficientJet period standardDirection 6 A)
    (κ : ℝ) (m : Vector3) (c : ℝ) (hc : 0 < c)
    (hpos : ∀ x v, c * ‖v‖ ^ 2 ≤ ⟪A.coefficient x v, v⟫_ℝ)
    (N : ℕ) (hN : N + 6 ≤ s) (ρ Rc M B : ℝ) (hρ : 0 < ρ) (hRc : 0 ≤ Rc) (hM : 1 ≤ M) (hB : 0 ≤ B)
    (hbase5 : (EulerH6Pressure.CoefficientJet.restrict KG 5 (by omega)).pressureConstant c ≤ M)
    (hbase6 : (EulerH6Pressure.CoefficientJet.restrict KG 6 (by omega)).pressureConstant c ≤ M)
    (hsmall : 4 * M * (ρ * Rc) ≤ 1)
    (hcoeff : ∀ l, 1 ≤ l → l ≤ N → coefficientBlock period KG 6 l ≤ Rc ^ l * (l.factorial : ℝ) ^ 2)
    (hG : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period KG r ≤ B)
    (hG0 : ∀ r ≤ 6, EulerJetProductBounds.boundLevel period KG0 r ≤ B)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (C0 : SmoothCoefficient period) (K0 : EulerSpatialSobolevInverse.CoefficientJet period
        standardDirection s C0)
    (C : Fin 3 → SmoothCoefficient period)
    (K : ∀ i, EulerSpatialSobolevInverse.CoefficientJet period standardDirection s (C i))
    (z e : SobolevSpace period (s + 1)) (r : SobolevSpace period s)
    (Z0 B0 B1 A0 A2 R : ℝ) (hA2 : 0 ≤ A2)
    (hz : weightedNorm period 6 N ρ z ≤ Z0)
    (hb : weightedDriftNorm period 6 N ρ (velocityMap L) z ≤ B0)
    (hdz : (∑ i : Fin 4, weightedNorm period 6 N ρ (derivativeOperator period s i z)) ≤ B1)
    (hC0 : weightedCoefficient period K0 6 N ρ ≤ A0)
    (hC : (∑ i : Fin 3, weightedCoefficient period (K i) 6 N ρ) ≤ A2)
    (hr : weightedNorm period 6 N ρ r ≤ R)
    (KM : LiftL2 period →L[ℝ] LiftL2 period) (cM : ℝ) (hcM : 0 < cM)
    (hKM : ∀ v, cM ^ 2 * ‖v‖ ^ 2 ≤ ⟪KM v, v⟫_ℝ) :
    let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
      (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
    weightedForcingSum ρ (fun I : ExternalWord N => I.1.val)
      (correctionForcing period hs KG KG0 N hN L hL (z+e) e f
        (pressureSobolevOperator period KG κ m c hc hpos f) (transportPressure period hs KG κ m c
            hc hpos L hL (z+e) e)) ≤
      EulerDriftEnergyConstants.forcingPolynomial period B M Z0 B0 B1 A0 A2 R cM Rc ρ
        (energyNorm period N (by omega : N+6 ≤ s+1) ρ KM e)
        (energyLoss period N (by omega : N+6 ≤ s+1) ρ KM e) := by
  let f := orderZeroSource period hs L hL (coefficientSobolevOperator period K0)
    (fun i => coefficientSobolevOperator period (K i)) z r (truncateOperator period s e)
  have h := EulerDriftNonlinearEstimate.correctionForcing_polynomial period hs KG KG0 κ m c hc hpos
      N hN ρ Rc M B hρ hRc hM hB
    hbase5 hbase6 hsmall hcoeff hG hG0 L hL C0 K0 C K z e r Z0 B0 B1 A0 A2 R hA2 hz hb hdz hC0 hC hr
  have hM0 : 0 ≤ M := by linarith
  have hP := productConstant_nonneg period 3
  have hz0 : 0 ≤ Z0 := (weightedNorm_nonneg period 6 N ρ hρ z).trans hz
  have hb0 : 0 ≤ B0 := (weightedDriftNorm_nonneg period 6 N ρ hρ (velocityMap L) z).trans hb
  have hb1 : 0 ≤ B1 := (Finset.sum_nonneg (fun i _ =>
    weightedNorm_nonneg period 6 N ρ hρ (derivativeOperator period s i z))).trans hdz
  have ha0 : 0 ≤ A0 := (weightedCoefficient_nonneg period K0 6 N ρ hρ).trans hC0
  have hsf := sourceConstant_nonneg hB hM0
  have htf := transportConstant_nonneg period hB hM0
  have hlf := lossConstant_nonneg period hM0
  have hlin : 0 ≤ sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
      3*Z0) +
      transportConstant period B M*Z0 := by positivity
  have hquad : 0 ≤ sourceConstant B M*A2*productConstant period 3+transportConstant period B M := by
      positivity
  have hconv := metric_polynomial_conversion (sourceConstant B M)
    (sourceConstant B M*(productConstant period 3*B1+A0+2*A2*productConstant period
        3*Z0)+transportConstant period B M*Z0)
    (sourceConstant B M*A2*productConstant period 3+transportConstant period B M)
    (lossConstant period M*(ρ⁻¹+Rc)) R B0 (metricAmplification cM)
    (weightedNorm period 6 N ρ e) (weightedLoss period 6 N ρ e)
    (energyNorm period N (by
        omega : N+6 ≤ s+1) ρ KM e) (energyLoss period N (by omega : N+6 ≤ s+1) ρ KM e) _
    hlin hquad (mul_nonneg hlf (add_nonneg (inv_nonneg.mpr hρ.le) hRc)) hb0
        (metricAmplification_one_le hcM)
    (weightedNorm_nonneg period 6 N ρ hρ e) (weightedLoss_nonneg period 6 N ρ hρ e)
    (energyNorm_nonneg period N (by omega : N+6 ≤ s+1) ρ hρ KM e)
    (weightedNorm_le_energy period N (by omega : N+6 ≤ s+1) ρ hρ KM e cM hcM hKM)
    (weightedLoss_le_energy period N (by omega : N+6 ≤ s+1) ρ hρ KM e cM hcM hKM) h
  simpa only [EulerDriftEnergyConstants.forcingPolynomial,
    EulerNonlinearEnergyConstants.linearCoefficient,
        EulerNonlinearEnergyConstants.quadraticCoefficient,
    EulerNonlinearEnergyConstants.lossCoefficient, mul_assoc, mul_left_comm, mul_comm] using hconv

end EulerDriftMetricForcing

end
end

end

section

/-! Continuous energy majorants that retain the actual small transport drift. -/

@[expose] public section

noncomputable section

namespace EulerDriftEnergyMajorants

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerCorrectionEnergyMajorants
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerTimeLpSubintervalBound
  EulerVolterraConvolution EulerDriftCorrectionBudget
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The sharp polynomial is evaluated on the actual continuous metric energy paths. -/
def forcingMajorant {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, ℝ) := by
  let X := energyPath period N hN T R (K.operatorPath period) e
  let Y := lossPath period N hN T R (K.operatorPath period) e
  refine ⟨fun t => EulerDriftEnergyConstants.forcingPolynomial period
    S.full.B S.full.M S.full.B0 S.drift S.full.B1 S.full.A0 S.full.A2
    S.full.residual K.c S.full.Rc (R t) (X t) (Y t), ?_⟩
  have hi : Continuous (fun t => (R t)⁻¹) :=
    R.continuous.inv₀ (fun t => (S.full.radius_pos t).ne')
  unfold EulerDriftEnergyConstants.forcingPolynomial
  fun_prop

/-- The genuine scalar majorant retains full velocity only in terms with no derivative loss. -/
def correctionRhs {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (Rdot : C(Icc (0 : ℝ) T, ℝ))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, ℝ) :=
  scalarEnergyRhs T (growthPath period S.full hN K e)
    (radiusLossPath R Rdot S.full.radius_pos) (ContinuousMap.const _ (K.multiplier period))
    (energyPath period N hN T R (K.operatorPath period) e)
    (lossPath period N hN T R (K.operatorPath period) e)
    (forcingMajorant period S hN K e)

/-- The source's radius-loss factor uses the drift envelope, with the unchanged full-data growth
constant. -/
theorem correctionRhs_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (Rdot : C(Icc (0 : ℝ) T, ℝ))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    let X := energyPath period N hN T R (K.operatorPath period) e t
    let Y := lossPath period N hN T R (K.operatorPath period) e t
    let C := combinedConstant period S.full K
    correctionRhs period S hN K Rdot e t ≤ C * (X + X ^ 2 + S.full.residual) +
      (Rdot t / R t + C * ((R t)⁻¹ + S.full.Rc) * (S.drift + X)) * Y := by
  obtain ⟨hg0, hg1, hk⟩ := K.constants_nonneg period S.full.B0 S.full.B0_nonneg
  exact EulerDriftEnergyConstants.actual_scalar_bound period
    (K.growth0 period S.full.B0) (K.growth1 period) (K.multiplier period)
    S.full.B S.full.M S.full.B0 S.drift S.full.B1 S.full.A0 S.full.A2 K.c
    S.full.Rc (R t) S.full.residual
    (energyPath period N hN T R (K.operatorPath period) e t)
    (lossPath period N hN T R (K.operatorPath period) e t) (Rdot t / R t)
    hg0 hg1 hk S.full.B_nonneg (zero_le_one.trans S.full.M_one_le)
    S.full.B0_nonneg S.drift_nonneg S.full.B1_nonneg S.full.A0_nonneg
    S.full.A2_nonneg K.c_pos S.full.Rc_nonneg (S.full.radius_pos t)
    S.full.residual_pos.le (energy_nonneg period S.full hN K e t)
    (loss_nonneg period S.full hN K e t)

end EulerDriftEnergyMajorants

end
end

end

section

/-! Actual nonlinear correction mild solutions obey the drift-sensitive integral energy estimate. -/

section

/-! The actual time-dependent correction forcing obeys the sharp drift majorant. -/

@[expose] public section

noncomputable section

namespace EulerDriftCorrectionEnergyBound

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCylinderSobolev EulerSpatialSobolevInverse EulerCorrectionOperators
  EulerCorrectionEnergyTime EulerEnergyMetricPaths EulerGevreyMetricEstimate
  EulerH6Pressure EulerSobolevGevreyOperators EulerSobolevTransportCommutator
  EulerSobolevTransport EulerH6Nonlinear EulerGevreyMetricComparison EulerTimeLp
  EulerVolterraConvolution EulerSobolevWordValueIdentity EulerRegularizedTopBlocks
  EulerGevreyOrderZero EulerTimeCorrectionSource EulerWeightedCylinderEnergy
  EulerCorrectionEnergyData EulerDriftCorrectionBudget EulerDriftEnergyMajorants
  EulerFunctionalVelocity EulerSobolevDriftNorm
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual correction array is controlled by the continuous drift majorant,
independently of its auxiliary higher-Sobolev representative. -/
theorem correctionArray_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (V : SobolevSpace period ((q + 1) + 1)) (τ : Icc (0 : ℝ) T)
    (hV : truncateOperator period (q + 1) V = e τ) :
    weightedForcingSum (R τ) (fun I : ExternalWord N => I.1.val)
      (correctionArray period hq D (baseMetricJet period hq D) N hN e V τ) ≤
        forcingMajorant period S hN K e τ := by
  have h := EulerDriftMetricForcing.correctionForcing_metric period hq
    (D.metric.jet τ) (baseMetricJet period hq D τ)
    D.κ D.direction D.coercivity D.coercivity_pos (D.metric_pos τ)
    N hN (R τ) S.full.Rc S.full.M S.full.B (S.full.radius_pos τ)
    S.full.Rc_nonneg S.full.M_one_le S.full.B_nonneg
    (S.full.inverse_five τ) (S.full.inverse_six τ) (S.full.radius_small τ)
    (S.full.metric_derivatives τ) (S.full.metric_base τ) (S.full.base_bound period τ)
    (velocityComponents D.κ D.direction)
    (velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound)
    (D.linear.coefficient τ) (D.linear.jet τ)
    (fun i => (D.quadratic i).coefficient τ) (fun i => (D.quadratic i).jet τ)
    (D.approximation τ) V (D.residual τ)
    S.full.B0 S.drift S.full.B1 S.full.A0 S.full.A2 S.full.residual S.full.A2_nonneg
    (S.full.background τ) (S.drift_bound τ) (S.full.background_derivative τ)
    (S.full.linear τ) (S.full.quadratic τ) (S.full.residual_bound τ)
    (K.operatorPath period τ) K.c K.c_pos (K.operator_coercive period τ)
  have hv : value period V = value period (e τ) := congrArg (value period) hV
  rw [energyNorm_of_value_eq period N (by omega) hN (R τ) (K.operatorPath period τ) V (e τ) hv,
    energyLoss_of_value_eq period N (by omega) hN (R τ) (K.operatorPath period τ) V (e τ) hv] at h
  simpa only [correctionArray, lowerOrderPath, orderZeroPath, ContinuousMap.coe_mk,
    CoefficientPath.operatorPath, EulerGevreyPressureTransport.transportPressure, hV,
    forcingMajorant, energyPath_apply, lossPath_apply] using h

/-- The full Bochner forcing inherits the drift bound from the actual spatial fields. -/
theorem weightedCorrectionForcing_bound {q : ℕ} {T : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) T)}
    {N : ℕ} {R : C(Icc (0 : ℝ) T, ℝ)}
    (S : Budget period hq D N R) (hN : N + 6 ≤ q + 1)
    {hT : 0 ≤ T} (K : MetricBudget period T hT D)
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e))
      Filter.atTop (𝓝 U)) :
    (weightedCorrectionForcing period hq T hT D hG N hN R e U : ℝ → ℝ) ≤ᵐ[timeMeasure T]
      extendPath T hT (forcingMajorant period S hN K e) := by
  filter_upwards [weightedCorrectionForcing_ae period hq T hT D hG
    (baseMetricJet period hq D) N hN R e U hU,
    reindexMaximalTime_restriction period T hT e U hU] with t hforce hv
  exact hforce.le.trans (correctionArray_bound period S hN K e
    (reindexMaximalTime period q T U t) (projIcc 0 T hT t) hv)

end EulerDriftCorrectionEnergyBound

end
end

end

@[expose] public section

noncomputable section

namespace EulerDriftCorrectionMildEnergy

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyRestriction EulerCorrectionEnergyTime EulerCorrectionEnergyData
      EulerCorrectionEnergyMajorants
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerMildMajorantEnergy
      EulerEnergyWordCoordinates
  EulerTimeLpSubintervalBound EulerTimeLp EulerVolterraConvolution EulerSobolevHeat
      EulerSobolevMaximalRegularity
  EulerDriftCorrectionBudget EulerDriftEnergyMajorants
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual nonlinear lower mild equation yields the full energy-order scalar integral bound on
every subinterval.
Maximal regularity, the higher nonlinear source, the pressure, and their constraints are all
constructed or proved inside the argument. -/
theorem correction_mild_integral {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R Rdot : C(Icc (0 : ℝ) T, ℝ))
    (S : Budget period (by omega : 6 ≤ q + 1) D N R) (K : MetricBudget period T hT D)
    (hRd : ∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT R) (extendPath T hT Rdot t) t)
    (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1) (e₀ : SobolevSpace period (q + 1))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      e t = heatOperator period (q+1) (2*ν*t.val).toNNReal e₀ +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (extendPath T hT (forcingPath period hq (lowerData period D KG KL KQ hGq hLq hQq) e)
              (t.val-r)))
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (he : ∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction)
    (s t : ℝ) (h0s : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T) :
    energyPath period N hN T R (K.operatorPath period) e ⟨t,h0s.trans hst,htT⟩ -
      energyPath period N hN T R (K.operatorPath period) e ⟨s,h0s,hst.trans htT⟩ ≤
      ∫ r in s..t, extendPath T hT (correctionRhs period S hN K Rdot e) r := by
  let Dlow := lowerData period D KG KL KQ hGq hLq hQq
  let f := forcingPath period hq Dlow e
  let p := pressurePath period hq Dlow e
  obtain ⟨U,hU⟩ := exists_maximal_mild_limit period ν hν T hT e₀ f e hsol
  let F := sourceTime period (by omega : 6 ≤ q+1) T hT D e U
  let P := signedPressureTime period (by omega : 6 ≤ q+1) T hT D e U
  let X := energyPath period N hN T R (K.operatorPath period) e
  let Y := lossPath period N hN T R (K.operatorPath period) e
  let k : C(Icc (0 : ℝ) T, ℝ) := ContinuousMap.const _ (K.multiplier period)
  have hF := sourceTime_restriction period hq T hT D KG KL KQ hGq hLq hQq e U hU
  have hP := signedPressureTime_restriction period hq T hT D KG KL KQ hGq hLq hQq e U hU
  have henergy := mild_majorized_energy_subinterval period (by omega : 3 ≤ q+1) T hT s t h0s hst htT
    energyLength energyWord (energyLength_le hN) (fun I : EulerGevreyMetricComparison.ExternalWord
        N => I.1.val)
    ν hν D.κ D.direction K.c K.c_pos R Rdot S.full.radius_pos hRd K.metric D.metric.coefficient
    K.continuous hG K.derivative K.hasDeriv K.symmetric K.coercive K.inverse
    (fun τ => metricVelocityBound period K.c S.full.B0 (X τ)) (velocityPath period D e) e e₀ f p
        hsol he
    (pressurePath_gradient period hq Dlow e)
    (velocity_divergenceFree period D e hz he) (velocity_bound period S.full hN K e)
    U F P hU hF hP (growthPath period S.full hN K e) (radiusLossPath R Rdot S.full.radius_pos) k
    (growthPath_bound period S.full hN K e ν hν1) (fun _ => rfl)
    (fun τ => div_le_div_of_nonneg_right (K.bound_le τ) K.c_pos.le)
  have hforce := EulerDriftCorrectionEnergyBound.weightedCorrectionForcing_bound period S hN K hG e
      U hU
  have hk : ∀ τ, 0 ≤ k τ := fun _ => (K.constants_nonneg period S.full.B0 S.full.B0_nonneg).2.2
  exact scalar_rhs_subinterval T hT s t h0s hst htT
    (growthPath period S.full hN K e) (radiusLossPath R Rdot S.full.radius_pos) k X Y
    (forcingMajorant period S hN K e) hk
    (weightedCorrectionForcing period (by omega : 6 ≤ q+1) T hT D hG N hN R e U) hforce henergy

end EulerDriftCorrectionMildEnergy

end
end

end

@[expose] public section

noncomputable section

namespace EulerDriftCorrectionBootstrap

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
    EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerSobolevCoefficientPressure
      EulerCorrectionLowerData
  EulerCorrectionEnergyData EulerCorrectionEnergyMajorants EulerCorrectionMildEnergy
      EulerCorrectionEnergyScalar
  EulerEnergyMetricPaths EulerGevreyMetricEstimate EulerTimeLp EulerVolterraConvolution
      EulerSobolevHeat
  EulerIntegralEnergyBootstrap
open EulerDriftCorrectionBudget EulerDriftEnergyMajorants EulerCorrectionEnergyBootstrap
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Every actual zero-initial nonlinear correction mild solution satisfies the closed Gevrey
estimate.
The proof derives its full-order all-subinterval energy inequality, source bound, pressure
cancellation, and maximal regularity rather than assuming them. -/
theorem correction_mild_bootstrap {q : ℕ} (hq : 6 ≤ q) (T : ℝ) (hT : 0 ≤ T)
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hGq : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hLq : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQq : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (hG : Continuous (fun t => (D.metric.coefficient t).operator))
    (N : ℕ) (hN : N + 6 ≤ q + 1) (R Rdot : C(Icc (0 : ℝ) T, ℝ))
    (S : Budget period (by omega : 6 ≤ q + 1) D N R) (K : MetricBudget period T hT D)
    (C Δ ρ0 : ℝ) (hC : combinedConstant period S.full K ≤ C) (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hρ0 : 0 <
        ρ0)
    (hdecay : 2 * C * (S.drift + Δ) * T ≤ ρ0 / 2) (hscale : ρ0 * S.full.Rc ≤ 1)
    (hsmall : 2 * S.full.residual * Real.exp (3 * C * T) ≤ Δ / 2)
    (hR : ∀ t, R t = ρ0 - 2 * C * (S.drift + Δ) * t.val)
    (hRdot : ∀ t, Rdot t = -2 * C * (S.drift + Δ))
    (ν : ℝ) (hν : 0 < ν) (hν1 : ν ≤ 1)
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (hsol : ∀ t : Icc (0 : ℝ) T,
      e t = heatOperator period (q+1) (2*ν*t.val).toNNReal 0 +
        ∫ r in (0 : ℝ)..t.val, heatKernel period q ν hν r
          (extendPath T hT (forcingPath period hq (lowerData period D KG KL KQ hGq hLq hQq) e)
              (t.val-r)))
    (hz : ∀ t, value period (D.approximation t) ∈ divergenceFreeSpace period D.κ D.direction)
    (he : ∀ t, value period (e t) ∈ divergenceFreeSpace period D.κ D.direction) :
    ∀ t : Icc (0 : ℝ) T,
      energyNorm period N hN (R t) (K.operatorPath period t) (e t) ≤ 2*S.full.residual*Real.exp
          (3*C*t.val) ∧
      energyNorm period N hN (R t) (K.operatorPath period t) (e t) ≤ Δ/2 := by
  let X := energyPath period N hN T R (K.operatorPath period) e
  let Y := lossPath period N hN T R (K.operatorPath period) e
  let A := EulerDriftEnergyMajorants.correctionRhs period S hN K Rdot e
  have hCp : 0 < C := (combinedConstant_pos period S.full K).trans_le hC
  have hRd : ∀ t ∈ Ioo 0 T, HasDerivAt (extendPath T hT R) (extendPath T hT Rdot t) t := by
    intro t ht
    exact affine_radius_derivative T hT R Rdot ρ0 (2*C*(S.drift+Δ)) hR
      (fun τ => (hRdot τ).trans (by ring)) t ht
  have hinit : extendPath T hT X 0 ≤ 2*S.full.residual := by
    have he0 := zero_mild_trace period ν hν T hT
      (forcingPath period hq (lowerData period D KG KL KQ hGq hLq hQq) e) e hsol
    change X (projIcc 0 T hT 0) ≤ _
    rw [projIcc_of_mem hT ⟨le_rfl,hT⟩]
    change energyPath period N hN T R (K.operatorPath period) e ⟨0,le_rfl,hT⟩ ≤ _
    rw [energyPath_apply,he0,energyNorm_zero]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) S.full.residual_pos.le
  have hint : ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T, s ≤ t →
      extendPath T hT X t-extendPath T hT X s ≤ ∫ r in s..t, extendPath T hT A r := by
    intro s hs t ht hst
    have h := EulerDriftCorrectionMildEnergy.correction_mild_integral period hq T hT D KG KL KQ hGq
        hLq hQq hG N hN R Rdot S K hRd
      ν hν hν1 0 e hsol hz he s t hs.1 hst ht.2
    change X (projIcc 0 T hT t)-X (projIcc 0 T hT s) ≤ _
    rw [projIcc_of_mem hT ht,projIcc_of_mem hT hs]
    exact h
  have hineq : ∀ t ∈ Ico (0 : ℝ) T,
      extendPath T hT A t ≤ C*(extendPath T hT X t+(extendPath T hT X t)^2+S.full.residual) +
        ((-2*C*(S.drift+Δ))/(ρ0-2*C*(S.drift+Δ)*t) +
          C*((ρ0-2*C*(S.drift+Δ)*t)⁻¹+S.full.Rc)*(S.drift+extendPath T hT X t))*extendPath T hT Y t
              := by
    intro t ht
    let τ : Icc (0 : ℝ) T := ⟨t,ht.1,ht.2.le⟩
    have h := EulerDriftEnergyMajorants.correctionRhs_bound period S hN K Rdot e τ
    have h' := raise_energy_constant (combinedConstant period S.full K) C (X τ) (Y τ)
        S.full.residual
      (Rdot τ/R τ) ((R τ)⁻¹+S.full.Rc) S.drift hC (energy_nonneg period S.full hN K e τ)
      (loss_nonneg period S.full hN K e τ) S.full.residual_pos.le
      (add_nonneg (inv_nonneg.mpr (S.full.radius_pos τ).le) S.full.Rc_nonneg) S.drift_nonneg
    have hh := h.trans h'
    change A (projIcc 0 T hT t) ≤ C*(X (projIcc 0 T hT t) +
      (X (projIcc 0 T hT t))^2+S.full.residual) +
      ((-2*C*(S.drift+Δ))/(ρ0-2*C*(S.drift+Δ)*t)+C*((ρ0-2*C*(S.drift+Δ)*t)⁻¹+S.full.Rc) *
        (S.drift+X (projIcc 0 T hT t)))*Y (projIcc 0 T hT t)
    rw [projIcc_of_mem hT ⟨ht.1,ht.2.le⟩]
    simpa only [hR τ,hRdot τ] using hh
  have hclosed := close_integral_energy_estimate (extendPath T hT X) (extendPath T hT A)
      (extendPath T hT Y)
    C S.drift Δ S.full.residual ρ0 T S.full.Rc hCp S.drift_nonneg hΔ hΔ1 S.full.residual_pos hρ0 hT
        S.full.Rc_nonneg hdecay hscale hsmall
    (extendPath_continuous T hT X).continuousOn (extendPath_continuous T hT A).continuousOn hinit
        hint
    (fun t _ => loss_nonneg period S.full hN K e (projIcc 0 T hT t)) hineq
  intro t
  have h := hclosed t.val t.property
  change X (projIcc 0 T hT t.val) ≤ _ ∧ X (projIcc 0 T hT t.val) ≤ _ at h
  rw [projIcc_of_mem hT t.property] at h
  simpa only [X,energyPath_apply] using h

end EulerDriftCorrectionBootstrap
