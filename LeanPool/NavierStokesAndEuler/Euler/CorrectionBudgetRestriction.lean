/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.CorrectionEnergyData
public import LeanPool.NavierStokesAndEuler.Euler.EulerCorrectionLocal

/-! Genuine coefficient and metric budgets persist under restriction to a partial time interval. -/

section

/-! Actual correction coefficient data restricted along continuous time maps. -/

@[expose] public section

noncomputable section

namespace EulerCorrectionOperators

open Set EulerCylinderSobolevSpace EulerSpatialSobolevInverse EulerSobolevCoefficientPressure
  EulerQuadraticSource
open scoped Topology

variable (period : ℝ) [Fact (0 < period)]

/-- Restrict the actual spatial coefficient and its jet along a continuous parameter map. -/
def CoefficientPath.comp {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (A : CoefficientPath period q T) (f : C(U, T)) : CoefficientPath period q U where
  coefficient t := A.coefficient (f t)
  jet t := A.jet (f t)
  continuous := A.continuous.comp f.continuous

/-- Restrict every actual coefficient, background field, and residual along the same time map. -/
def CorrectionData.comp {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (D : CorrectionData period q T) (f : C(U, T)) : CorrectionData period q U where
  κ := D.κ
  direction := D.direction
  scale_bound := D.scale_bound
  direction_bound := D.direction_bound
  metric := D.metric.comp period f
  coercivity := D.coercivity
  coercivity_pos := D.coercivity_pos
  metric_pos t := D.metric_pos (f t)
  linear := D.linear.comp period f
  quadratic i := (D.quadratic i).comp period f
  approximation := D.approximation.comp f
  residual := D.residual.comp f

/-- The restricted correction source is the original actual source at the restricted time. -/
theorem CorrectionData.comp_source {q : ℕ} {T U : Type*} [TopologicalSpace T] [TopologicalSpace U]
    (D : CorrectionData period q T) (f : C(U, T)) (hq : 6 ≤ q)
    (t : U) (u : SobolevSpace period (q + 1)) :
    ((D.comp period f).coefficients period hq).apply t u =
      (D.coefficients period hq).apply (f t) u := rfl

/-- Restricting the concrete data gives precisely the same nonlinear mild equation on a shorter
interval. -/
theorem CorrectionData.comp_quadraticDuhamel {q : ℕ} (hq : 6 ≤ q)
    (ν : ℝ) (hν : 0 < ν) {T S : ℝ} (hT : 0 ≤ T) (hTS : T ≤ S)
    (D : CorrectionData period q (Icc (0 : ℝ) S))
    (u₀ : SobolevSpace period (q + 1)) (u : C(Icc (0 : ℝ) T, SobolevSpace period (q + 1)))
    (t : Icc (0 : ℝ) T) :
    quadraticDuhamel period ν hν hT le_rfl
        ((D.comp period (timeInclusion hTS)).coefficients period hq) u₀ u t =
      quadraticDuhamel period ν hν hT hTS (D.coefficients period hq) u₀ u t := rfl

end EulerCorrectionOperators

end
end

end

@[expose] public section

noncomputable section

namespace EulerCorrectionBudgetRestriction

open Set EulerCorrectionOperators EulerCorrectionEnergyData EulerQuadraticSource
    EulerVolterraConvolution
open scoped Topology

/-- Clamped restriction agrees with the original continuous path at every time in the shorter
interval. -/
theorem extend_restriction_eq {E : Type*} [NormedAddCommGroup E] {T S : ℝ}
    (hT : 0 ≤ T) (hS : 0 ≤ S) (hTS : T ≤ S) (f : C(Icc (0 : ℝ) S, E))
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    extendPath T hT (f.comp (timeInclusion hTS)) t = extendPath S hS f t := by
  unfold extendPath
  simp only [projIcc_of_mem _ ht, projIcc_of_mem _ (show t ∈ Icc 0 S from ⟨ht.1,ht.2.trans hTS⟩)]
  rfl

/-- Restriction of a genuine time derivative gives the same genuine derivative in the shorter
interval. -/
theorem hasDerivAt_restriction {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {T S : ℝ} (hT : 0 ≤ T) (hS : 0 ≤ S) (hTS : T ≤ S)
    (f f' : C(Icc (0 : ℝ) S, E))
    (hf : ∀ t ∈ Ioo 0 S, HasDerivAt (extendPath S hS f) (extendPath S hS f' t) t)
    (t : ℝ) (ht : t ∈ Ioo 0 T) :
    HasDerivAt (extendPath T hT (f.comp (timeInclusion hTS)))
      (extendPath T hT (f'.comp (timeInclusion hTS)) t) t := by
  rw [extend_restriction_eq hT hS hTS f' t ⟨ht.1.le,ht.2.le⟩]
  apply (hf t ⟨ht.1,ht.2.trans_le hTS⟩).congr_of_eventuallyEq
  filter_upwards [Ioo_mem_nhds ht.1 ht.2] with r hr
  exact extend_restriction_eq hT hS hTS f r ⟨hr.1.le,hr.2.le⟩

variable (period : ℝ) [Fact (0 < period)]

/-- Every concrete spatial budget restricts with exactly the same numerical constants. -/
def SpatialBudget.restrict {q : ℕ} {T S : ℝ} {hq : 6 ≤ q + 1}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) S)} {N : ℕ} {R : C(Icc (0 : ℝ) S, ℝ)}
    (B : SpatialBudget period hq D N R) (hTS : T ≤ S) :
    SpatialBudget period hq (D.comp period (timeInclusion hTS)) N (R.comp (timeInclusion hTS)) where
  Rc := B.Rc
  M := B.M
  B := B.B
  B0 := B.B0
  B1 := B.B1
  A0 := B.A0
  A2 := B.A2
  residual := B.residual
  Rc_nonneg := B.Rc_nonneg
  M_one_le := B.M_one_le
  B_nonneg := B.B_nonneg
  B0_nonneg := B.B0_nonneg
  B1_nonneg := B.B1_nonneg
  A0_nonneg := B.A0_nonneg
  A2_nonneg := B.A2_nonneg
  residual_pos := B.residual_pos
  radius_pos t := B.radius_pos (timeInclusion hTS t)
  inverse_five t := B.inverse_five (timeInclusion hTS t)
  inverse_six t := B.inverse_six (timeInclusion hTS t)
  radius_small t := B.radius_small (timeInclusion hTS t)
  metric_derivatives t := B.metric_derivatives (timeInclusion hTS t)
  metric_base t := B.metric_base (timeInclusion hTS t)
  background t := B.background (timeInclusion hTS t)
  background_derivative t := B.background_derivative (timeInclusion hTS t)
  linear t := B.linear (timeInclusion hTS t)
  quadratic t := B.quadratic (timeInclusion hTS t)
  residual_bound t := B.residual_bound (timeInclusion hTS t)

/-- The actual inverse metric and its genuine derivative restrict with unchanged numerical budgets.
-/
def MetricBudget.restrict {q : ℕ} {T S : ℝ} {hS : 0 ≤ S}
    {D : CorrectionData period (q + 1) (Icc (0 : ℝ) S)}
    (K : MetricBudget period S hS D) (hT : 0 ≤ T) (hTS : T ≤ S) :
    MetricBudget period T hT (D.comp period (timeInclusion hTS)) where
  metric t := K.metric (timeInclusion hTS t)
  continuous := K.continuous.comp (timeInclusion hTS).continuous
  derivative := K.derivative.comp (timeInclusion hTS)
  hasDeriv t ht := hasDerivAt_restriction hT hS hTS (K.operatorPath period) K.derivative K.hasDeriv
      t ht
  c := K.c
  c_pos := K.c_pos
  symmetric t := K.symmetric (timeInclusion hTS t)
  coercive t := K.coercive (timeInclusion hTS t)
  inverse t := K.inverse (timeInclusion hTS t)
  bound := K.bound
  first := K.first
  time := K.time
  bound_nonneg := K.bound_nonneg
  first_nonneg := K.first_nonneg
  time_nonneg := K.time_nonneg
  bound_le t := K.bound_le (timeInclusion hTS t)
  first_le t := K.first_le (timeInclusion hTS t)
  time_le t := K.time_le (timeInclusion hTS t)

end EulerCorrectionBudgetRestriction
