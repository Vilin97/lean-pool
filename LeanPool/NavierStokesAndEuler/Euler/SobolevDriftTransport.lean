/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevDriftNorm
public import LeanPool.NavierStokesAndEuler.Euler.GevreyPressureShifted
import LeanPool.NavierStokesAndEuler.Euler.DriftPreservingTransport
import LeanPool.NavierStokesAndEuler.Euler.HeatAllOrders

/-! Sharp drift-preserving transport and pressure estimates for actual finite Sobolev fields. -/

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
