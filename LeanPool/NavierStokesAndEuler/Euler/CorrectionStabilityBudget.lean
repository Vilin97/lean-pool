/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionDifferenceMetric

@[expose] public section

/-! Concrete coefficient and inverse-metric data for actual vanishing-viscosity stability. -/

noncomputable section

namespace EulerCorrectionStabilityBudget

open MeasureTheory Set InnerProductSpace EulerLiftedGradientSpace EulerCylinderSobolevSpace
  EulerSpatialSobolevInverse EulerCorrectionOperators EulerCorrectionStabilityConstants
    EulerVolterraConvolution
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Actual coefficient and inverse-metric budgets for L² comparison; no PDE estimate or solution comparison is a field. -/
structure StabilityBudget {q : ℕ} {T : ℝ} (hT : 0 ≤ T) (D : CorrectionData period q (Icc (0 : ℝ)
  T)) where
  /-- The actual inverse metric coefficient. -/
  metric : Icc (0 : ℝ) T → SmoothCoefficient period
  /-- The actual metric multiplier is continuous in time. -/
  continuous : Continuous (fun t => (metric t).operator)
  /-- The genuine time derivative of the metric multiplier. -/
  derivative : C(Icc (0 : ℝ) T,LiftL2 period →L[ℝ] LiftL2 period)
  /-- Interior differentiation of the actual metric path. -/
  hasDeriv : ∀ t ∈ Ioo 0 T, HasDerivAt
    (fun s => (metric (projIcc 0 T hT s)).operator) (extendPath T hT derivative t) t
  /-- Positive square-root coercivity constant. -/
  c : ℝ
  /-- Strict coercivity. -/
  c_pos : 0 < c
  /-- Pointwise metric symmetry. -/
  symmetric : ∀ t x a b, ⟪(metric t).coefficient x a,b⟫_ℝ=⟪a,(metric t).coefficient x b⟫_ℝ
  /-- Pointwise positive lower bound. -/
  coercive : ∀ t x a, c^2*‖a‖^2 ≤ ⟪(metric t).coefficient x a,a⟫_ℝ
  /-- The actual metric inverts the pressure coefficient. -/
  inverse : ∀ t x a, (metric t).coefficient x ((D.metric.coefficient t).coefficient x a)=a
  /-- Uniform metric operator bound. -/
  bound : ℝ
  /-- Uniform metric first spatial derivative bound. -/
  first : ℝ
  /-- Uniform metric time derivative bound. -/
  time : ℝ
  /-- Uniform linear-coefficient bound. -/
  linear : ℝ
  /-- Uniform sum of quadratic-coefficient bounds. -/
  quadratic : ℝ
  /-- The actual metric operator satisfies its budget. -/
  bound_le : ∀ t, ‖(metric t).operator‖ ≤ bound
  /-- The actual first spatial derivative witness satisfies its budget. -/
  first_le : ∀ t, ((metric t).firstBound : ℝ) ≤ first
  /-- The actual time derivative satisfies its budget. -/
  time_le : ∀ t, ‖derivative t‖ ≤ time
  /-- The actual linear coefficient satisfies its budget. -/
  linear_le : ∀ t, ((D.linear.coefficient t).bound : ℝ) ≤ linear
  /-- The actual quadratic coefficients satisfy their common budget. -/
  quadratic_le : ∀ t, (∑ i : Fin 3, (((D.quadratic i).coefficient t).bound : ℝ)) ≤ quadratic

/-- The actual continuous metric multiplier path determined by the concrete budget. -/
def StabilityBudget.operatorPath {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period q (Icc (0 : ℝ) T)} (B : StabilityBudget period hT D) :
    C(Icc (0 : ℝ) T,LiftL2 period →L[ℝ] LiftL2 period) := ⟨fun t => (B.metric
      t).operator,B.continuous⟩

/-- The fixed squared-energy growth coefficient obtained from the actual background path and a solution norm bound. -/
def StabilityBudget.growth {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period q (Icc (0 : ℝ) T)} (B : StabilityBudget period hT D) (R : ℝ) : ℝ :=
  growthConstant B.c B.bound B.first B.time (velocityBound period q ‖D.approximation‖ R)
    (lowerConstant period q B.linear B.quadratic ‖D.approximation‖ R)

/-- The explicit finite-interval Lipschitz coefficient for viscosity in continuous L². -/
def StabilityBudget.comparisonConstant {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period q (Icc (0 : ℝ) T)} (B : StabilityBudget period hT D) (R : ℝ) : ℝ :=
  Real.sqrt (defectConstant B.bound R*T*Real.exp (B.growth period R*T))/B.c

/-- All budget signs follow from the actual norm bounds on the nonempty time interval. -/
theorem StabilityBudget.nonneg {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period q (Icc (0 : ℝ) T)} (B : StabilityBudget period hT D) :
    0 ≤ B.bound ∧ 0 ≤ B.first ∧ 0 ≤ B.time ∧ 0 ≤ B.linear ∧ 0 ≤ B.quadratic := by
  let t : Icc (0 : ℝ) T := ⟨0,le_rfl,hT⟩
  exact ⟨(norm_nonneg _).trans (B.bound_le t),
    (B.metric t).firstBound.coe_nonneg.trans (B.first_le t),
    (norm_nonneg _).trans (B.time_le t),
    (D.linear.coefficient t).bound.coe_nonneg.trans (B.linear_le t),
    (Finset.sum_nonneg (fun i _ => ((D.quadratic i).coefficient t).bound.coe_nonneg)).trans
      (B.quadratic_le t)⟩

/-- The actual fixed growth coefficient is nonnegative for every nonnegative solution bound. -/
theorem StabilityBudget.growth_nonneg {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period q (Icc (0 : ℝ) T)} (B : StabilityBudget period hT D) (R : ℝ) (hR : 0
      ≤ R) :
    0 ≤ B.growth period R := by
  obtain ⟨hb,hf,ht,hl,hq⟩ := B.nonneg period
  exact growthConstant_nonneg B.c B.bound B.first B.time _ _ hb hf ht
    (velocityBound_nonneg period q ‖D.approximation‖ R (norm_nonneg D.approximation) hR)
    (lowerConstant_nonneg period q B.linear B.quadratic ‖D.approximation‖ R hl hq (norm_nonneg
      D.approximation) hR)

/-- The explicit comparison coefficient is nonnegative. -/
theorem StabilityBudget.comparisonConstant_nonneg {q : ℕ} {T : ℝ} {hT : 0 ≤ T}
    {D : CorrectionData period q (Icc (0 : ℝ) T)} (B : StabilityBudget period hT D) (R : ℝ) :
    0 ≤ B.comparisonConstant period R := div_nonneg (Real.sqrt_nonneg _) B.c_pos.le

end EulerCorrectionStabilityBudget
