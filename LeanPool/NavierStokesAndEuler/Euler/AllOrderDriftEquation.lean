/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftCorrection
public import LeanPool.NavierStokesAndEuler.Euler.AllOrderDriftPressure
public import LeanPool.NavierStokesAndEuler.Euler.CorrectionResidualCancellation

import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Actual residual cancellation for the constructed all-order correction

The drift-aware budget constructs the correction.  A separate, explicit input
below identifies the prescribed residual with the residual of the actual
approximation and its pressure.  Only after supplying that identity do we assert
that the corrected field solves the zero-residual lifted equation.

These results concern the genuine Sobolev paths and coefficients of `Data`.
They neither construct the approximate packet nor identify arbitrary coefficients
with the physical Euler equation in parent-flow coordinates.
-/

@[expose] public section


noncomputable section

namespace EulerAllOrderDriftCorrection

open MeasureTheory Set EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerAllOrderCorrectionData EulerCorrectionAssembly EulerCorrectionOperators
  EulerCorrectionResidualCancellation EulerVolterraConvolution
  EulerSobolevCoefficientPressure EulerGevreyMetricEstimate

variable (period : ℝ) [Fact (0 < period)]
variable {T : ℝ} {hT : 0 < T} {A : Data period T}

/-- The prescribed residual is the actual residual of the approximation with
this genuine all-order pressure.  This is a condition on the input approximation,
not an existence or equation assumption about the constructed correction. -/
structure ApproximationResidual (hT : 0 < T) (A : Data period T) where
  /-- The actual approximate pressure gradient, with coherent Sobolev realizations. -/
  pressure : FieldTower period T
  /-- The approximate pressure belongs to the same lifted gradient space. -/
  gradient : ∀ t, pressure.field t ∈ gradientSpace period A.κ A.direction
  /-- The literal residual identity holds at every finite construction order. -/
  equation : ∀ (q : ℕ) (hq : 6 ≤ q) t (ht : t ∈ Ioo 0 T),
    HasDerivAt (extendPath T hT.le (A.approximation.realization q))
      (A.residual.realization q ⟨t, ht.1.le, ht.2.le⟩ -
        nonlinearity period (A.atOrder period q) hq ⟨t, ht.1.le, ht.2.le⟩
          (A.approximation.realization (q+1) ⟨t, ht.1.le, ht.2.le⟩) -
        coefficientSobolevOperator period (A.metric.jet q ⟨t, ht.1.le, ht.2.le⟩)
          (pressure.realization q ⟨t, ht.1.le, ht.2.le⟩)) t

/-- The approximation plus the actually constructed correction, in every order. -/
def Budget.correctedFieldTower (B : Budget period hT A) : FieldTower period T where
  field := A.approximation.field + B.commonPath period
  realization q := A.approximation.realization q + (B.fieldTower period).realization q
  value_eq q t := by
    change value period (A.approximation.realization q t) +
      value period ((B.fieldTower period).realization q t) =
        A.approximation.field t + B.commonPath period t
    exact congrArg₂ (· + ·) (A.approximation.value_eq q t)
      ((B.fieldTower period).value_eq q t)

/-- The total pressure is the given approximate pressure plus the constructed
signed correction pressure, with no independent choice at different orders. -/
def Budget.correctedPressureTower (B : Budget period hT A)
    (R : ApproximationResidual period hT A) : FieldTower period T where
  field := R.pressure.field + (B.pressureTower period).field
  realization q := R.pressure.realization q + (B.pressureTower period).realization q
  value_eq q t := by
    change value period (R.pressure.realization q t) +
      value period ((B.pressureTower period).realization q t) =
        R.pressure.field t + (B.pressureTower period).field t
    rw [R.pressure.value_eq, (B.pressureTower period).value_eq]

/-- The corrected field has exactly the prescribed initial field at every order. -/
theorem Budget.correctedFieldTower_initial (B : Budget period hT A) (q : ℕ) :
    (B.correctedFieldTower period).realization q ⟨0, le_rfl, hT.le⟩ =
      A.approximation.realization q ⟨0, le_rfl, hT.le⟩ := by
  change A.approximation.realization q ⟨0, le_rfl, hT.le⟩ +
    (B.fieldTower period).realization q ⟨0, le_rfl, hT.le⟩ = _
  rw [B.fieldTower_initial period, add_zero]

/-- Addition preserves the actual closed lifted divergence constraint. -/
theorem Budget.correctedFieldTower_divergence (B : Budget period hT A)
    (t : Icc (0 : ℝ) T) :
    (B.correctedFieldTower period).field t ∈ divergenceFreeSpace period A.κ A.direction :=
  (divergenceFreeSpace period A.κ A.direction).add_mem
    (B.divergence t) (B.commonPath_divergence period t)

/-- The total pressure remains an actual lifted gradient. -/
theorem Budget.correctedPressureTower_gradient (B : Budget period hT A)
    (R : ApproximationResidual period hT A) (t : Icc (0 : ℝ) T) :
    (B.correctedPressureTower period R).field t ∈ gradientSpace period A.κ A.direction :=
  (gradientSpace period A.κ A.direction).add_mem (R.gradient t)
    ((B.family period).commonPressure_gradient period t)

/-- The exact solution differs from the approximation by precisely the small
correction, retaining both proved energy bounds at every external cutoff. -/
theorem Budget.correctedFieldTower_error_energy (B : Budget period hT A)
    (P : ℕ) (t : Icc (0 : ℝ) T) :
    energyNorm period P (by omega : P+6 ≤ (P+6)+1)
        (B.radius t) (B.metric.operatorPath period t)
        ((B.correctedFieldTower period).realization ((P+6)+1) t -
          A.approximation.realization ((P+6)+1) t) ≤
      2*(B.spatial (P+6) (by omega)).full.residual *
        Real.exp (3*B.growthCoefficient*t.val) ∧
    energyNorm period P (by omega : P+6 ≤ (P+6)+1)
        (B.radius t) (B.metric.operatorPath period t)
        ((B.correctedFieldTower period).realization ((P+6)+1) t -
          A.approximation.realization ((P+6)+1) t) ≤ B.delta/2 := by
  have heq : (B.correctedFieldTower period).realization ((P+6)+1) t -
      A.approximation.realization ((P+6)+1) t =
      (B.fieldTower period).realization ((P+6)+1) t := by
    change (A.approximation.realization ((P+6)+1) t +
      (B.fieldTower period).realization ((P+6)+1) t) -
      A.approximation.realization ((P+6)+1) t = _
    abel
  rw [heq]
  exact B.fieldTower_energy period P t

/-- The input residual identity and the proved correction equation give the
actual zero-residual nonlinear equation, with the actual total pressure.
There is no assumption of existence or an energy bound for the correction. -/
theorem Budget.correctedFieldTower_hasDerivAt (B : Budget period hT A)
    (R : ApproximationResidual period hT A) (q : ℕ) (hq : 6 ≤ q)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT.le ((B.correctedFieldTower period).realization q))
      (-nonlinearity period (A.atOrder period q) hq ⟨t, ht.1.le, ht.2.le⟩
        ((B.correctedFieldTower period).realization (q+1) ⟨t, ht.1.le, ht.2.le⟩) -
        coefficientSobolevOperator period (A.metric.jet q ⟨t, ht.1.le, ht.2.le⟩)
          ((B.correctedPressureTower period R).realization q ⟨t, ht.1.le, ht.2.le⟩)) t := by
  have he := B.fieldTower_hasDerivAt_pressure period q hq t ht
  have hz := R.equation q hq t ht
  have hcancel := residual_cancellation period (A.atOrder period q) hq
    ⟨t, ht.1.le, ht.2.le⟩
    ((B.fieldTower period).realization (q+1) ⟨t, ht.1.le, ht.2.le⟩)
    (R.pressure.realization q ⟨t, ht.1.le, ht.2.le⟩)
  have hsum := (hz.add he).congr_deriv hcancel
  have hp := B.pressure_eq_realization period q hq ⟨t, ht.1.le, ht.2.le⟩
  rw [B.solution_eq_realization period q hq] at hp
  rw [hp] at hsum
  exact hsum

/-- A single coherent exact lifted solution and total pressure are constructed
from the drift budget and the literal approximate residual identity. -/
theorem exists_exact_lifted_solution (B : Budget period hT A)
    (R : ApproximationResidual period hT A) :
    ∃ (Z Q : FieldTower period T),
      (∀ q, Z.realization q ⟨0, le_rfl, hT.le⟩ =
        A.approximation.realization q ⟨0, le_rfl, hT.le⟩) ∧
      (∀ t, Z.field t ∈ divergenceFreeSpace period A.κ A.direction) ∧
      (∀ t, Q.field t ∈ gradientSpace period A.κ A.direction) ∧
      (∀ (P : ℕ) t,
        energyNorm period P (by omega : P+6 ≤ (P+6)+1)
            (B.radius t) (B.metric.operatorPath period t)
            (Z.realization ((P+6)+1) t - A.approximation.realization ((P+6)+1) t) ≤
          2*(B.spatial (P+6) (by omega)).full.residual *
            Real.exp (3*B.growthCoefficient*t.val) ∧
        energyNorm period P (by omega : P+6 ≤ (P+6)+1)
            (B.radius t) (B.metric.operatorPath period t)
            (Z.realization ((P+6)+1) t - A.approximation.realization ((P+6)+1) t) ≤ B.delta/2) ∧
      ∀ (q : ℕ) (hq : 6 ≤ q) t (ht : t ∈ Ioo 0 T),
        HasDerivAt (extendPath T hT.le (Z.realization q))
          (-nonlinearity period (A.atOrder period q) hq ⟨t, ht.1.le, ht.2.le⟩
            (Z.realization (q+1) ⟨t, ht.1.le, ht.2.le⟩) -
            coefficientSobolevOperator period (A.metric.jet q ⟨t, ht.1.le, ht.2.le⟩)
              (Q.realization q ⟨t, ht.1.le, ht.2.le⟩)) t := by
  exact ⟨B.correctedFieldTower period, B.correctedPressureTower period R,
    B.correctedFieldTower_initial period, B.correctedFieldTower_divergence period,
    B.correctedPressureTower_gradient period R, B.correctedFieldTower_error_energy period,
    B.correctedFieldTower_hasDerivAt period R⟩

end EulerAllOrderDriftCorrection
