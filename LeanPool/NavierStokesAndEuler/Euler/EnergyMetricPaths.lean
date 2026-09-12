/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EnergyWordCoordinates
public import LeanPool.NavierStokesAndEuler.Euler.GevreyMetricEstimate
public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordValueIdentity
public import LeanPool.NavierStokesAndEuler.Euler.SobolevEnergyPaths

/-! Actual metric Gevrey energy and radius loss as continuous paths, with exact
higher-representative compatibility. -/

@[expose] public section


noncomputable section

namespace EulerEnergyMetricPaths

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerEnergyWordCoordinates
  EulerGevreyMetricEstimate EulerGevreyMetricComparison EulerBaseWordMetric
      EulerMetricPathConvergence
  EulerRegularizedEnergyFamily EulerSobolevEnergyPaths EulerWeightedCylinderEnergy
      EulerSobolevWordValueIdentity
  EulerTimeLp EulerVolterraConvolution EulerRegularizedTopBlocks
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine finite Gevrey metric energy along an actual continuous Sobolev solution. -/
def energyPath {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q + 1) (T : ℝ)
    (R : C(Icc (0 : ℝ) T, ℝ)) (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, ℝ) :=
  weightedMetricPath T (fun I : ExternalWord N => gevreyWeightPath T R I.1.val) K
    (energyValueFamily period energyLength energyWord (energyLength_le hN) T e)

/-- The genuine radius-loss metric quantity along the same actual solution. -/
def lossPath {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q + 1) (T : ℝ)
    (R : C(Icc (0 : ℝ) T, ℝ)) (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) : C(Icc (0 : ℝ) T, ℝ) :=
  weightedMetricPath T (fun I : ExternalWord N => gevreyLossWeightPath T R I.1.val) K
    (energyValueFamily period energyLength energyWord (energyLength_le hN) T e)

/-- The continuous energy path is exactly the spatial metric norm at each time. -/
theorem energyPath_apply {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q + 1) (T : ℝ)
    (R : C(Icc (0 : ℝ) T, ℝ)) (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    energyPath period N hN T R K e t = energyNorm period N hN (R t) (K t) (e t) := by
  rw [energyPath, weightedMetricPath_apply]
  unfold energyNorm weightedMetricSum
  exact Finset.sum_congr rfl (fun I _ => congrArg (fun v => EulerPacketWeights.weight (R t) I.1.val
      *
    EulerFiniteMetricEnergy.familyMetricNorm (K t) v) (energyValueFamily_eq period 6 N hN T e I t))

/-- The continuous loss path is exactly the spatial metric radius loss at each time. -/
theorem lossPath_apply {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q + 1) (T : ℝ)
    (R : C(Icc (0 : ℝ) T, ℝ)) (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (t : Icc (0 : ℝ) T) :
    lossPath period N hN T R K e t = energyLoss period N hN (R t) (K t) (e t) := by
  rw [lossPath, weightedMetricPath_apply]
  unfold energyLoss weightedMetricLoss
  exact Finset.sum_congr rfl (fun I _ => congrArg (fun v => (I.1.val : ℝ)*EulerPacketWeights.weight
      (R t) I.1.val *
    EulerFiniteMetricEnergy.familyMetricNorm (K t) v) (energyValueFamily_eq period 6 N hN T e I t))

/-- Equal actual fields at adequate derivative orders have the same literal finite metric energy. -/
theorem energyNorm_of_value_eq {p q : ℕ} (N : ℕ) (hp : N + 6 ≤ p) (hq : N + 6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period p) (v : SobolevSpace period q)
    (huv : value period u = value period v) : energyNorm period N hp ρ K u = energyNorm period N hq
        ρ K v := by
  apply congrArg (weightedMetricSum ρ (fun I : ExternalWord N => I.1.val) K)
  funext I a
  rw [energyValues_eq_word, energyValues_eq_word]
  exact word_of_value_eq period u v huv (energyLength_le hp I a) (energyLength_le hq I a)
      (energyWord I a)

/-- The identical representative principle holds for the actual radius-loss energy. -/
theorem energyLoss_of_value_eq {p q : ℕ} (N : ℕ) (hp : N + 6 ≤ p) (hq : N + 6 ≤ q) (ρ : ℝ)
    (K : LiftL2 period →L[ℝ] LiftL2 period) (u : SobolevSpace period p) (v : SobolevSpace period q)
    (huv : value period u = value period v) : energyLoss period N hp ρ K u = energyLoss period N hq
        ρ K v := by
  apply congrArg (weightedMetricLoss ρ (fun I : ExternalWord N => I.1.val) K)
  funext I a
  rw [energyValues_eq_word, energyValues_eq_word]
  exact word_of_value_eq period u v huv (energyLength_le hp I a) (energyLength_le hq I a)
      (energyWord I a)

/-- Genuine maximal-regularity representatives have exactly the original metric energy and loss
almost everywhere in time. -/
theorem maximal_metric_paths {q : ℕ} (N : ℕ) (hN : N + 6 ≤ q + 1) (T : ℝ) (hT : 0 ≤ T)
    (R : C(Icc (0 : ℝ) T, ℝ)) (K : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (e : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (U : TimeLp T (SobolevSpace period (2 + q)))
    (hU : Filter.Tendsto (fun n => pathLp T hT (maximalApproximation period q T n e)) Filter.atTop
        (𝓝 U)) :
    ∀ᵐ t ∂timeMeasure T,
      energyNorm period N (by omega : N+6 ≤ (q+1)+1) (R (projIcc 0 T hT t)) (K (projIcc 0 T hT t))
        (reindexMaximalTime period q T U t) = energyPath period N hN T R K e (projIcc 0 T hT t) ∧
      energyLoss period N (by omega : N+6 ≤ (q+1)+1) (R (projIcc 0 T hT t)) (K (projIcc 0 T hT t))
        (reindexMaximalTime period q T U t) = lossPath period N hN T R K e (projIcc 0 T hT t) := by
  filter_upwards [reindexMaximalTime_restriction period T hT e U hU] with t ht
  have hv : value period (reindexMaximalTime period q T U t) = value period (e (projIcc 0 T hT t))
      := congrArg (value period) ht
  rw [energyPath_apply, lossPath_apply]
  exact ⟨energyNorm_of_value_eq period N (by omega) hN _ _ _ _ hv,
    energyLoss_of_value_eq period N (by omega) hN _ _ _ _ hv⟩

end EulerEnergyMetricPaths
