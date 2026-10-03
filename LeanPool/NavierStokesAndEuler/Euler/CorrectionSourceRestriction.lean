/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionLowerData
import LeanPool.NavierStokesAndEuler.Euler.GevreyCorrectionSplit
import LeanPool.NavierStokesAndEuler.Euler.SobolevNonlinearCompatibility

/-! The actual nonlinear correction source is identical across compatible Sobolev levels. -/

@[expose] public section


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
    (u v : SobolevSpace period ((q + 1) + 1)) :
    truncateOperator period q (transportBilinear period (by omega : 6 ≤ q+1) L hL u v) =
      transportBilinear period hq L hL (truncateOperator period (q+1) u) (truncateOperator period
          (q+1) v) := by
  have h := restrict_asymmetricTransport period (by omega : 6 ≤ q+1) hq (by omega : q ≤ q+1)
    L hL (truncateOperator period (q+1) u) v
  apply ((congrArg (restrictOperator period (by omega : q ≤ q+1))
    (asymmetricTransport_eq period (by omega : 6 ≤ q+1) L hL u v)).symm.trans h).trans
    (asymmetricTransport_eq period hq L hL
      (truncateOperator period (q+1) u) (truncateOperator period (q+1) v))

/-- Restricting the literal nonlinear raw source gives the raw source of the actual lower data. -/
theorem truncate_rawSource {q : ℕ} (hq : 6 ≤ q) {T : ℝ}
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (t : Icc (0 : ℝ) T) (u : SobolevSpace period ((q + 1) + 1)) :
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

theorem restrictOperator_succ_eq_truncate {q : ℕ} (h : q ≤ q + 1)
    (u : SobolevSpace period (q + 1)) :
    restrictOperator period h u = truncateOperator period q u := by
  rw [← truncate_restrictOperator period (le_refl (q + 1)) u, restrictOperator_self]

theorem coefficients_apply_eq {q : ℕ} {T : Type*} [TopologicalSpace T]
    (D : CorrectionData period q T) (hq : 6 ≤ q) (t : T) (u : SobolevSpace period (q + 1)) :
    (D.coefficients period hq).apply t u =
      -projectedSourceOperator period (D.metric.jet t) D.κ D.direction D.coercivity
        D.coercivity_pos (D.metric_pos t) (D.rawSource period hq t u) := rfl

/-- The actual projected nonlinear mild source commutes exactly with Sobolev restriction. -/
theorem truncate_source {q : ℕ} (hq : 6 ≤ q) {T : ℝ}
    (D : CorrectionData period (q + 1) (Icc (0 : ℝ) T))
    (KG : ∀ t, CoefficientJet period standardDirection q (D.metric.coefficient t))
    (KL : ∀ t, CoefficientJet period standardDirection q (D.linear.coefficient t))
    (KQ : ∀ i t, CoefficientJet period standardDirection q ((D.quadratic i).coefficient t))
    (hG : Continuous (fun t => coefficientSobolevOperator period (KG t)))
    (hL : Continuous (fun t => coefficientSobolevOperator period (KL t)))
    (hQ : ∀ i, Continuous (fun t => coefficientSobolevOperator period (KQ i t)))
    (t : Icc (0 : ℝ) T) (u : SobolevSpace period ((q + 1) + 1)) :
    truncateOperator period q ((D.coefficients period (by omega : 6 ≤ q+1)).apply t u) =
      ((lowerData period D KG KL KQ hG hL hQ).coefficients period hq).apply t (truncateOperator
          period (q+1) u) := by
  rw [coefficients_apply_eq, coefficients_apply_eq, (truncateOperator period q).map_neg]
  have hp := restrict_projectedSource period (by omega : q ≤ q+1) (D.metric.jet t) (KG t)
    D.κ D.direction D.coercivity D.coercivity_pos (D.metric_pos t) (D.rawSource period (by
        omega : 6 ≤ q+1) t u)
  rw [restrictOperator_succ_eq_truncate, restrictOperator_succ_eq_truncate] at hp
  rw [hp, truncate_rawSource period hq D KG KL KQ hG hL hQ t u]
  rfl

end EulerCorrectionSourceRestriction
