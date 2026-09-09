/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderLiftedCorrection
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionSourceRestriction

@[expose] public section

/-! The actual nonlinear source and signed coercive pressure agree across the constructed Sobolev
  solutions. -/

noncomputable section

namespace EulerAllOrderPressureCoherence

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionLowerData EulerCorrectionSourceRestriction
  EulerAllOrderCorrectionData EulerAllOrderCorrectionBudget EulerAllOrderCorrectionFamily
  EulerAllOrderLiftedCorrection EulerSobolevCoefficientPressure
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- The actual continuous nonlinear raw source at a finite Sobolev order. -/
def rawSourcePath {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) : C(Icc (0 : ℝ) T,SobolevSpace period q) :=
  rawPath period hq (A.atOrder period q) (solution period hT A B q hq)

/-- The actual continuous signed coercive pressure at a finite Sobolev order. -/
def signedPressurePath {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) : C(Icc (0 : ℝ) T,SobolevSpace period q) :=
  pressurePath period hq (A.atOrder period q) (solution period hT A B q hq)

/-- The genuine raw sources of the constructed solutions restrict exactly across adjacent orders. -/
theorem rawSourcePath_truncate {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    truncateOperator period q (rawSourcePath period hT A B (q+1) (hq.trans (Nat.le_succ q)) t) =
      rawSourcePath period hT A B q hq t := by
  have h := truncate_rawSource period hq (A.atOrder period (q+1))
    (A.metric.jet q) (A.linear.jet q) (fun i => (A.quadratic i).jet q)
    (A.metric.continuous q) (A.linear.continuous q) (fun i => (A.quadratic i).continuous q)
    t (solution period hT A B (q+1) (hq.trans (Nat.le_succ q)) t)
  rw [A.lower_atOrder period q] at h
  have he := congrArg (fun f => f t) (solution_compatible period hT A B q hq)
  change truncateOperator period (q+1) (solution period hT A B (q+1) (hq.trans (Nat.le_succ q)) t)=
    solution period hT A B q hq t at he
  rw [he] at h
  exact h

/-- Adjacent genuine raw sources represent the same actual L² field. -/
theorem rawSourcePath_value_succ {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (rawSourcePath period hT A B (q+1) (hq.trans (Nat.le_succ q)) t)=
      value period (rawSourcePath period hT A B q hq t) :=
  congrArg (value period (q := q)) (rawSourcePath_truncate period hT A B q hq t)

/-- The actual signed coercive pressures represent the same L² field at adjacent Sobolev orders. -/
theorem signedPressurePath_value_succ {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period
  hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (signedPressurePath period hT A B (q+1) (hq.trans (Nat.le_succ q)) t)=
      value period (signedPressurePath period hT A B q hq t) := by
  change -value period (pressureSobolevOperator period (A.metric.jet (q+1) t) A.κ A.direction
    A.coercivity A.coercivity_pos (A.metric_pos t)
    (rawSourcePath period hT A B (q+1) (hq.trans (Nat.le_succ q)) t)) =
      -value period (pressureSobolevOperator period (A.metric.jet q t) A.κ A.direction
        A.coercivity A.coercivity_pos (A.metric_pos t) (rawSourcePath period hT A B q hq t))
  rw [pressureSobolevOperator_value,pressureSobolevOperator_value,rawSourcePath_value_succ]

/-- Every finite-order signed pressure represents the same actual base pressure. -/
theorem signedPressurePath_value_base {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period
  hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (signedPressurePath period hT A B q hq t)=
      value period (signedPressurePath period hT A B 6 le_rfl t) := by
  exact Nat.le_induction (P := fun n hn => value period (signedPressurePath period hT A B n hn t)=
      value period (signedPressurePath period hT A B 6 le_rfl t)) rfl
    (fun n hn ih => (signedPressurePath_value_succ period hT A B n hn t).trans ih) q hq

/-- The common actual signed pressure is a continuous L² path. -/
def commonPressure {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A) :
    C(Icc (0 : ℝ) T,LiftL2 period) :=
  (valueOperator period 6).compLeftContinuous ℝ (Icc (0 : ℝ) T) (signedPressurePath period hT A B 6
    le_rfl)

/-- Every finite-order pressure realizes the common pressure field. -/
theorem signedPressurePath_value_common {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period
  hT A)
    (q : ℕ) (hq : 6 ≤ q) (t : Icc (0 : ℝ) T) :
    value period (signedPressurePath period hT A B q hq t)=commonPressure period hT A B t :=
  signedPressurePath_value_base period hT A B q hq t

/-- The common actual correction pressure belongs to the closed lifted gradient subspace. -/
theorem commonPressure_gradient {T : ℝ} (hT : 0 < T) (A : Data period T) (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) : commonPressure period hT A B t ∈ gradientSpace period A.κ A.direction :=
  (A.atOrder period 6).pressure_mem_gradient period le_rfl t (solution period hT A B 6 le_rfl t)

end EulerAllOrderPressureCoherence
