/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.ContractiveResolvent
public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.ExponentialBounds
public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Basic


/-!
# Bounded Yosida approximations

For a contractive resolvent `R`, this file defines the bounded generator
`G_α = α (α R_α - I)` and its exponential contraction semigroup.  It also
records commutation and the exact formula on the range of a fixed resolvent.
-/

@[expose] public section

noncomputable section PortComputability

open Filter Topology
open NormedSpace

section

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/- Head-class caches for the operator type.  Every repeated closed instance
search in this file is rooted at `E →L[ℝ] E`; resolving each head class once
here stops the normed-hierarchy walk on `E` from being replayed at every `•`,
`exp` and `comp`. -/
private instance cacheSMulCLM : SMul ℝ (E →L[ℝ] E) := inferInstance
private instance cacheModuleCLM : Module ℝ (E →L[ℝ] E) := inferInstance
private instance cacheAlgebraCLM : Algebra ℝ (E →L[ℝ] E) := inferInstance
private instance cacheIsTopologicalRingCLM : IsTopologicalRing (E →L[ℝ] E) := inferInstance

/-- The bounded Yosida generator `G_α = α (α R_α - I)`. -/
def yosidaGenerator (R : ContractiveResolvent E) (α : PositiveShift) : E →L[ℝ] E :=
  (α : ℝ) • (R.scaledOperator α - ContinuousLinearMap.id ℝ E)

private theorem commute_smul_smul_of_comp_eq (A B : E →L[ℝ] E)
    (h : A.comp B = B.comp A) (a b : ℝ) :
    Commute (a • A) (b • B) := by
  change (a • A).comp (b • B) = (b • B).comp (a • A)
  ext x
  change a • A (b • B x) = b • B (a • A x)
  rw [map_smul, map_smul, smul_smul, smul_smul, mul_comm a b]
  exact congrArg (fun z : E ↦ (b * a) • z) (DFunLike.congr_fun h x)

section CompleteSpace

variable [CompleteSpace E]

instance normedAlgebraRatEnd : NormedAlgebra ℚ (E →L[ℝ] E) :=
  NormedAlgebra.restrictScalars ℚ ℝ (E →L[ℝ] E)

/-- The exponential of the bounded Yosida generator at nonnegative time. -/
def yosidaOperator (R : ContractiveResolvent E) (α : PositiveShift) (t : NNReal) :
    E →L[ℝ] E :=
  exp ((t : ℝ) • R.yosidaGenerator α)

omit [CompleteSpace E] in
@[simp]
theorem yosidaOperator_zero (R : ContractiveResolvent E) (α : PositiveShift) :
    R.yosidaOperator α 0 = ContinuousLinearMap.id ℝ E := by
  rw [yosidaOperator, NNReal.coe_zero, zero_smul, exp_zero]
  rfl

/-- The bounded Yosida exponential satisfies the semigroup law. -/
theorem yosidaOperator_add (R : ContractiveResolvent E) (α : PositiveShift) (s t : NNReal) :
    R.yosidaOperator α (s + t) =
      (R.yosidaOperator α s).comp (R.yosidaOperator α t) := by
  rw [yosidaOperator, yosidaOperator, yosidaOperator, NNReal.coe_add, add_smul]
  exact exp_add_of_commute
    (commute_smul_smul_of_comp_eq _ _ rfl (s : ℝ) (t : ℝ))

/-- Every bounded Yosida exponential is contractive in operator norm. -/
theorem norm_yosidaOperator_le_one (R : ContractiveResolvent E)
    (α : PositiveShift) (t : NNReal) :
    ‖R.yosidaOperator α t‖ ≤ 1 := by
  have htime : 0 ≤ (t : ℝ) * (α : ℝ) :=
    mul_nonneg t.property α.property.le
  rw [yosidaOperator, yosidaGenerator, smul_smul]
  exact norm_exp_continuousLinearMap_smul_sub_id_le_one htime
    (R.opNorm_scaledOperator_le_one α)

/-- Orbits of the bounded Yosida exponential are continuous in nonnegative time. -/
theorem continuous_yosidaOperator_apply (R : ContractiveResolvent E)
    (α : PositiveShift) (x : E) :
    Continuous (fun t : NNReal ↦ R.yosidaOperator α t x) := by
  unfold yosidaOperator
  fun_prop

/-- The exponential Yosida approximation as a strongly continuous contraction semigroup. -/
def yosidaSemigroup (R : ContractiveResolvent E) (α : PositiveShift) :
    StronglyContinuousContractionSemigroup E where
  operator := R.yosidaOperator α
  operator_zero := R.yosidaOperator_zero α
  operator_add := R.yosidaOperator_add α
  opNorm_le_one := R.norm_yosidaOperator_le_one α
  continuous_orbit := R.continuous_yosidaOperator_apply α

@[simp]
theorem yosidaSemigroup_apply (R : ContractiveResolvent E)
    (α : PositiveShift) (t : NNReal) :
    R.yosidaSemigroup α t = R.yosidaOperator α t :=
  rfl

end CompleteSpace

/-- Yosida generators at different shifts commute. -/
theorem yosidaGenerator_commute (R : ContractiveResolvent E) (α β : PositiveShift) :
    Commute (R.yosidaGenerator α) (R.yosidaGenerator β) := by
  have hscaled : Commute (R.scaledOperator α) (R.scaledOperator β) := by
    unfold scaledOperator
    exact commute_smul_smul_of_comp_eq _ _ (R.operator_comm α β) (α : ℝ) (β : ℝ)
  have hsub : Commute
      (R.scaledOperator α - ContinuousLinearMap.id ℝ E)
      (R.scaledOperator β - ContinuousLinearMap.id ℝ E) :=
    (hscaled.sub_right (Commute.one_right _)).sub_left (Commute.one_left _)
  exact commute_smul_smul_of_comp_eq _ _ hsub.eq (α : ℝ) (β : ℝ)

/-- Yosida exponential approximants at arbitrary shifts and times commute. -/
theorem yosidaOperator_commute (R : ContractiveResolvent E)
    (α β : PositiveShift) (s t : NNReal) :
    Commute (R.yosidaOperator α s) (R.yosidaOperator β t) := by
  exact (commute_smul_smul_of_comp_eq _ _ (R.yosidaGenerator_commute α β).eq
    (s : ℝ) (t : ℝ)).exp

/-- Exact action of a Yosida generator on the range of a fixed resolvent. -/
theorem yosidaGenerator_apply_operator (R : ContractiveResolvent E)
    (α μ : PositiveShift) (y : E) :
    R.yosidaGenerator α (R.operator μ y) =
      R.scaledOperator α ((μ : ℝ) • R.operator μ y - y) := by
  rw [yosidaGenerator]
  change
    (α : ℝ) •
        (R.scaledOperator α (R.operator μ y) - R.operator μ y) =
      R.scaledOperator α ((μ : ℝ) • R.operator μ y - y)
  rw [R.scaledOperator_apply_sub_on_range α μ y]
  rfl

/-- On a fixed resolvent range, bounded Yosida generators converge to the
corresponding core value. -/
theorem tendsto_yosidaGenerator_apply_operator (R : ContractiveResolvent E)
    (μ : PositiveShift) (y : E) :
    Tendsto (fun α : PositiveShift ↦ R.yosidaGenerator α (R.operator μ y))
      atTop (nhds ((μ : ℝ) • R.operator μ y - y)) := by
  simpa only [yosidaGenerator_apply_operator] using
    R.tendsto_scaledOperator_apply ((μ : ℝ) • R.operator μ y - y)

end ContractiveResolvent

end MarkovProcess.Semigroup

end

end PortComputability
