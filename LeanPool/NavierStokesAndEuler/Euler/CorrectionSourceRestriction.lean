/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
public import LeanPool.NavierStokesAndEuler.Euler.SobolevCorrectionCompatibility

@[expose] public section

/-! The actual nonlinear correction source is identical across compatible Sobolev levels. -/

noncomputable section

namespace EulerCorrectionSourceRestriction

open Set EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSpatialSobolevInverse EulerSobolevCoefficientPressure EulerSobolevTransport
    EulerAsymmetricTransport
  EulerSobolevNonlinearCompatibility EulerSobolevCorrectionCompatibility EulerCorrectionOperators
  EulerCorrectionLowerData EulerGevreyOrderZero
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual quadratic transport field restricts to the same lower-order transport. -/
theorem truncate_transport {q : ℕ} (hq : 6 ≤ q)
    (L : Fin 4 → Vector3 →L[ℝ] ℝ) (hL : ∀ i, ‖L i‖ ≤ 1)
    (u v : SobolevSpace period ((q+1)+1)) :
    truncateOperator period q (transportBilinear period (by omega : 6 ≤ q+1) L hL u v) =
      transportBilinear period hq L hL (truncateOperator period (q+1) u) (truncateOperator period
        (q+1) v) := by
  have h := restrict_asymmetricTransport period (by omega : 6 ≤ q+1) hq (by omega : q ≤ q+1)
    L hL (truncateOperator period (q+1) u) v
  rw [asymmetricTransport_eq period (by omega : 6 ≤ q+1) L hL u v] at h
  exact h.trans (asymmetricTransport_eq period hq L hL
    (truncateOperator period (q+1) u) (truncateOperator period (q+1) v))

/-- Restricting the literal nonlinear raw source gives the raw source of the actual lower data. -/
theorem truncate_rawSource {q : ℕ} (hq : 6 ≤ q) {T : ℝ}
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (t : Icc (0 : ℝ) T) (u : SobolevSpace period ((q+1)+1)) :
    truncateOperator period q (D.rawSource period (by omega : 6 ≤ q+1) t u) =
      (lowerData period D KG KL KQ hG hL hQ).rawSource period hq t (truncateOperator period (q+1)
        u) := by
  let L := velocityComponents D.κ D.direction
  have hL1 := velocityComponents_norm D.κ D.direction D.scale_bound D.direction_bound
  have ht := truncate_transport period hq L hL1 (D.approximation t+u) u
  have hf := restrict_orderZeroSource period (by omega : 6 ≤ q+1) hq (by omega : q ≤ q+1)
    L hL1 (D.linear.coefficient t) (D.linear.jet t) (KL t) (fun i => (D.quadratic i).coefficient t)
    (fun i => (D.quadratic i).jet t) (fun i => KQ i t) (D.approximation t) (D.residual t)
    (truncateOperator period (q+1) u)
  rw [correctionData_rawSource_split period D (by omega : 6 ≤ q+1),map_add]
  rw [correctionData_rawSource_split period (lowerData period D KG KL KQ hG hL hQ) hq]
  exact congrArg₂ (fun x y : SobolevSpace period q => x+y) ht hf

/-- The actual projected nonlinear mild source commutes exactly with Sobolev restriction. -/
theorem truncate_source {q : ℕ} (hq : 6 ≤ q) {T : ℝ}
    (D : CorrectionData period (q+1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (t : Icc (0 : ℝ) T) (u : SobolevSpace period ((q+1)+1)) :
    truncateOperator period q ((D.coefficients period (by omega : 6 ≤ q+1)).apply t u) =
      ((lowerData period D KG KL KQ hG hL hQ).coefficients period hq).apply t (truncateOperator
        period (q+1) u) := by
  change truncateOperator period q (-projectedSourceOperator period (D.metric.jet t) D.κ D.direction
    D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period (by omega : 6 ≤ q+1) t u)) =
    -projectedSourceOperator period (KG t) D.κ D.direction D.coercivity D.coercivity_pos
      (D.metric_pos t)
      ((lowerData period D KG KL KQ hG hL hQ).rawSource period hq t (truncateOperator period (q+1)
        u))
  rw [map_neg]
  have hp := restrict_projectedSource period (by omega : q ≤ q+1) (D.metric.jet t) (KG t)
    D.κ D.direction D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period (by omega :
      6 ≤ q+1) t u)
  exact (congrArg Neg.neg hp).trans
    (congrArg (fun v => -projectedSourceOperator period (KG t) D.κ D.direction D.coercivity
      D.coercivity_pos (D.metric_pos t) v)
      (truncate_rawSource period hq D KG KL KQ hG hL hQ t u))

end EulerCorrectionSourceRestriction
