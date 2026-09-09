/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.AllOrderCorrectionData
public import LeanPool.NavierStokesAndEuler.Euler.GevreyStabilityBudget

@[expose] public section

/-! Actual finite correction families and input comparison bounds, independent of any Gevrey
  radius-loss budget. -/

noncomputable section

namespace EulerCorrectionAssembly

open MeasureTheory Set EulerLiftedGradientSpace EulerLiftedPressure EulerCylinderSobolevSpace
  EulerCorrectionOperators EulerCorrectionEnergyData EulerAllOrderCorrectionData
  EulerCorrectionStabilityBudget EulerGevreyStabilityBudget EulerVolterraConvolution

variable (period : ℝ) [Fact (0 < period)]

/-- One genuine inverse metric and actual base coefficient bounds provide stability at every finite Sobolev order.
No shrinking-radius condition or smallness of the approximate velocity is required. -/
def stabilityBudgetOfBase {T : ℝ} (hT : 0 < T) (A : Data period T)
    (K : MetricBudget period T hT.le (A.atOrder period 1))
    (R : C(Icc (0 : ℝ) T, ℝ))
    (S : SpatialBudget period (by norm_num : 6 ≤ 8) (A.atOrder period 8) 2 R)
    (q : ℕ) : StabilityBudget period hT.le (A.atOrder period q) where
  metric := K.metric
  continuous := K.continuous
  derivative := K.derivative
  hasDeriv := K.hasDeriv
  c := K.c
  c_pos := K.c_pos
  symmetric := K.symmetric
  coercive := K.coercive
  inverse := K.inverse
  bound := K.bound
  first := K.first
  time := K.time
  linear := S.A0
  quadratic := S.A2
  bound_le t := (coefficientOperator_norm_le (K.metric t).coefficient
    (K.metric t).measurable (K.metric t).bound (K.metric t).norm_bound).trans (K.bound_le t)
  first_le := K.first_le
  time_le := K.time_le
  linear_le t := (coefficient_bound_le_weighted period (A.linear.jet 8 t) 2 (R t)
    (S.radius_pos t)).trans (S.linear t)
  quadratic_le t := (Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    coefficient_bound_le_weighted period ((A.quadratic i).jet 8 t) 2 (R t)
      (S.radius_pos t))).trans (S.quadratic t)

/-- Genuine input bounds sufficient to compare any finite solutions of the same prescribed data.
This contains no correction, compatibility, solution-energy or radius-loss assumption. -/
structure ComparisonData {T : ℝ} (hT : 0 < T) (A : Data period T) where
  /-- The actual common inverse metric and its time derivative. -/
  metric : MetricBudget period T hT.le (A.atOrder period 1)
  /-- A radius used solely to state the actual base coefficient bounds. -/
  radius : C(Icc (0 : ℝ) T, ℝ)
  /-- Genuine base-order spatial bounds; their background bounds need not be small. -/
  spatial : SpatialBudget period (by norm_num : 6 ≤ 8) (A.atOrder period 8) 2 radius
  /-- The prescribed approximate solution obeys the actual lifted divergence constraint. -/
  divergence : ∀ t, A.approximation.field t ∈ divergenceFreeSpace period A.κ A.direction

/-- The supplied genuine comparison data construct a stability budget at any order. -/
def ComparisonData.stabilityBudget {T : ℝ} {hT : 0 < T} {A : Data period T}
    (C : ComparisonData period hT A) (q : ℕ) : StabilityBudget period hT.le (A.atOrder period q) :=
  stabilityBudgetOfBase period hT A C.metric C.radius C.spatial q

/-- An actual finite-order correction family supplied by separate finite-existence theorems.
Only its paths, zero initial data, divergence constraints and literal PDEs are inputs;
  compatibility is not assumed. -/
structure FiniteFamily {T : ℝ} (hT : 0 < T) (A : Data period T) where
  /-- A genuine continuous finite Sobolev correction at each order. -/
  solution : ∀ q, 6 ≤ q → C(Icc (0 : ℝ) T, SobolevSpace period (q+1))
  /-- Every correction starts from zero. -/
  initial : ∀ q hq, solution q hq ⟨0, le_rfl, hT.le⟩ = 0
  /-- Every correction satisfies the actual lifted divergence constraint. -/
  divergence : ∀ q hq t, value period (solution q hq t) ∈ divergenceFreeSpace period A.κ A.direction
  /-- Every correction satisfies the literal projected inviscid equation at interior times. -/
  equation : ∀ q hq t (ht : t ∈ Ioo 0 T),
    HasDerivAt (fun r => value period (extendPath T hT.le (solution q hq) r))
      (value period (((A.atOrder period q).coefficients period hq).apply
        ⟨t, ht.1.le, ht.2.le⟩ (solution q hq ⟨t, ht.1.le, ht.2.le⟩))) t

/-- Choose an actual finite correction family from proved finite-existence statements.
This is an assembly helper conditional on finite existence, not an independent source existence
  theorem. -/
def finiteFamilyOfExists {T : ℝ} (hT : 0 < T) (A : Data period T)
    (H : ∀ q (hq : 6 ≤ q), ∃ e : C(Icc (0 : ℝ) T, SobolevSpace period (q+1)),
      e ⟨0, le_rfl, hT.le⟩ = 0 ∧
      (∀ t, value period (e t) ∈ divergenceFreeSpace period A.κ A.direction) ∧
      ∀ t (ht : t ∈ Ioo 0 T),
        HasDerivAt (fun r => value period (extendPath T hT.le e r))
          (value period (((A.atOrder period q).coefficients period hq).apply
            ⟨t, ht.1.le, ht.2.le⟩ (e ⟨t, ht.1.le, ht.2.le⟩))) t) : FiniteFamily period hT A where
  solution q hq := Classical.choose (H q hq)
  initial q hq := (Classical.choose_spec (H q hq)).1
  divergence q hq := (Classical.choose_spec (H q hq)).2.1
  equation q hq := (Classical.choose_spec (H q hq)).2.2

end EulerCorrectionAssembly
