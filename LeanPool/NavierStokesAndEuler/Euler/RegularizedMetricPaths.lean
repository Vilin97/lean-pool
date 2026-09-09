/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.RegularizedEnergyFamily
public import LeanPool.NavierStokesAndEuler.Euler.SobolevEnergyPaths
public import LeanPool.NavierStokesAndEuler.Euler.WeightedCylinderEnergy

/-! Literal metric, loss, and forcing paths for the actual full-order word regularization. -/

@[expose] public section


noncomputable section

namespace EulerRegularizedMetricPaths

open MeasureTheory Set EulerLiftedGradientSpace EulerSpatialSobolevInverse EulerCylinderSobolevSpace
  EulerRegularizedEnergyFamily EulerMetricPathConvergence EulerWeightedForcingTime
      EulerSobolevEnergyPaths
  EulerFamilyNormTime EulerTimeLp EulerVolterraConvolution EulerPacketWeights
      EulerWeightedCylinderEnergy
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- A genuine continuous path of L² multipliers from the given actual smooth coefficient family. -/
def metricOperatorPath (T : ℝ) (K : Icc (0 : ℝ) T → SmoothCoefficient period)
    (hK : Continuous (fun t => (K t).operator)) : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2
        period) :=
  ⟨fun t => (K t).operator, hK⟩

omit [Fact (0 < period)] in
/-- The literal scalar metric-growth and radius-loss coefficients are integrable for continuous time
paths. -/
theorem coefficient_path_integrable (T : ℝ) (hT : 0 ≤ T)
    (w a b : C(Icc (0 : ℝ) T, ℝ)) (n : ℕ) :
    IntegrableOn (fun r => extendPath T hT w r * extendPath T hT a r +
      extendPath T hT b r * (n : ℝ) * extendPath T hT w r) (Icc 0 T) :=
  (((extendPath_continuous T hT w).mul (extendPath_continuous T hT a)).add
    (((extendPath_continuous T hT b).mul_const (n : ℝ)).mul (extendPath_continuous T hT
        w))).continuousOn.integrableOn_Icc

/-- The literal finite forcing coefficient is integrable for genuine continuous family paths. -/
theorem forcing_path_integrable {β : Type*} [Fintype β] (T : ℝ) (hT : 0 ≤ T)
    (w d : C(Icc (0 : ℝ) T, ℝ)) (f : C(Icc (0 : ℝ) T, β → LiftL2 period)) :
    IntegrableOn (fun r => extendPath T hT w r * (extendPath T hT d r *
      EulerFiniteMetricEnergy.familyNorm (extendPath T hT f r))) (Icc 0 T) :=
  ((extendPath_continuous T hT w).mul ((extendPath_continuous T hT d).mul
    (familyNorm_lipschitz.continuous.comp (extendPath_continuous T hT
        f)))).continuousOn.integrableOn_Icc

variable {α β : Type*} [Fintype α] [Fintype β] {q : ℕ}

/-- The computed metric path is exactly the actual factorial-weighted metric sum on the regularized
fields. -/
theorem regularized_metric_path_eq (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (order : α → ℕ) (R : C(Icc (0 : ℝ) T, ℝ))
    (K : Icc (0 : ℝ) T → SmoothCoefficient period) (hK : Continuous (fun t => (K t).operator))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (r : ℝ) :
    weightedMetricSum (extendPath T hT R r) order (K (projIcc 0 T hT r)).operator
      (fun i j => value period (extendPath T hT
        (EulerRegularizedWordEquation.regularizedWordPath period (hd i j) n (w i j) T u) r)) =
    extendPath T hT (weightedMetricPath T (fun i => gevreyWeightPath T R (order i))
      (metricOperatorPath period T K hK) (regularizedValueFamily period d w hd n T u)) r := by
  change _ = weightedMetricPath T _ _ _ (projIcc 0 T hT r)
  rw [weightedMetricPath_apply]
  rfl

/-- The computed radius-loss path is exactly the actual order-weighted metric sum. -/
theorem regularized_loss_path_eq (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (order : α → ℕ) (R : C(Icc (0 : ℝ) T, ℝ))
    (K : Icc (0 : ℝ) T → SmoothCoefficient period) (hK : Continuous (fun t => (K t).operator))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1))) (r : ℝ) :
    weightedMetricLoss (extendPath T hT R r) order (K (projIcc 0 T hT r)).operator
      (fun i j => value period (extendPath T hT
        (EulerRegularizedWordEquation.regularizedWordPath period (hd i j) n (w i j) T u) r)) =
    extendPath T hT (weightedMetricPath T (fun i => gevreyLossWeightPath T R (order i))
      (metricOperatorPath period T K hK) (regularizedValueFamily period d w hd n T u)) r := by
  change _ = weightedMetricPath T _ _ _ (projIcc 0 T hT r)
  rw [weightedMetricPath_apply]
  rfl

/-- The computed forcing path is exactly the actual weighted family norm of the regularized PDE
forcing. -/
theorem regularized_forcing_path_eq (d : α → β → ℕ) (w : ∀ i j, Fin (d i j) → Fin 4)
    (hd : ∀ i j, d i j ≤ q + 1) (n : ℕ) (T : ℝ) (hT : 0 ≤ T)
    (order : α → ℕ) (R : C(Icc (0 : ℝ) T, ℝ))
    (A : C(Icc (0 : ℝ) T, SobolevSpace period 1 →L[ℝ] LiftL2 period))
    (G : C(Icc (0 : ℝ) T, LiftL2 period →L[ℝ] LiftL2 period))
    (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (f p : C(Icc (0 : ℝ) T, SobolevSpace period q)) (r : ℝ) :
    weightedForcingSum (extendPath T hT R r) order
      (fun i j => extendPath T hT
        (EulerRegularizedForcingWord.forcingWordPath period (hd i j) n (w i j) T A G u f p) r) =
    extendPath T hT (weightedForcingPath T (fun i => gevreyWeightPath T R (order i))
      (regularizedForcingFamily period d w hd n T A G u f p)) r := by
  change _ = weightedForcingPath T _ _ (projIcc 0 T hT r)
  rw [weightedForcingPath_apply]
  rfl

end EulerRegularizedMetricPaths
