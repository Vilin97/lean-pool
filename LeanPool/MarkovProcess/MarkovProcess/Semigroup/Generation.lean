/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.YosidaStrongLimit
public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.Duhamel
public import LeanPool.MarkovProcess.MarkovProcess.Semigroup.OrbitContinuity


/-!
# Generation of a contraction semigroup from a contractive resolvent

This file packages the strong limit of the Yosida exponential approximations
as a strongly continuous contraction semigroup.  Strong continuity at zero is
first proved on the range of one resolvent and then extended by density.
-/

@[expose] public section

noncomputable section PortComputability

open Filter NormedSpace Set Topology

section

namespace MarkovProcess.Semigroup

namespace ContractiveResolvent

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- On the range of a fixed resolvent, the strong Yosida limit moves a vector
by at most time times a constant independent of time. -/
theorem exists_norm_yosidaStrongLimit_apply_sub_on_range_le
    (R : ContractiveResolvent E) (mu : PositiveShift) (y : E) :
    ∃ C : ℝ, ∀ t : NNReal,
      ‖R.yosidaStrongLimit t (R.operator mu y) - R.operator mu y‖ ≤ (t : ℝ) * C := by
  have hgen := R.cauchySeq_yosidaGenerator_naturalShift_apply_operator mu y
  obtain ⟨C, hC⟩ := hgen.isBounded_range.exists_norm_le
  refine ⟨C, fun t ↦ ?_⟩
  refine le_of_tendsto
    ((R.tendsto_yosidaOperator_naturalShift_apply t (R.operator mu y)).sub
      tendsto_const_nhds).norm ?_
  exact Eventually.of_forall fun n ↦ by
    have hcontract : ∀ s ∈ Icc (0 : ℝ) (t : ℝ),
        ‖exp (s • R.yosidaGenerator (naturalShift n))‖ ≤ 1 := by
      intro s hs
      have h := R.norm_yosidaOperator_le_one (naturalShift n) ⟨s, hs.1⟩
      simp only [yosidaOperator] at h
      exact h
    exact (norm_exp_apply_sub_le (R.yosidaGenerator (naturalShift n))
      (NNReal.coe_nonneg t) hcontract (R.operator mu y)).trans
        (mul_le_mul_of_nonneg_left
          (hC _ ⟨n, rfl⟩) (NNReal.coe_nonneg t))

/-- The strong Yosida limit converges to the identity at time zero on the
range of every fixed resolvent. -/
theorem tendsto_yosidaStrongLimit_apply_operator_zero
    (R : ContractiveResolvent E) (mu : PositiveShift) (y : E) :
    Tendsto (fun t : NNReal ↦ R.yosidaStrongLimit t (R.operator mu y))
      (nhds 0) (nhds (R.operator mu y)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  obtain ⟨C, hC⟩ := R.exists_norm_yosidaStrongLimit_apply_sub_on_range_le mu y
  refine squeeze_zero (fun t ↦ norm_nonneg _) hC ?_
  have hcoe : Tendsto (fun t : NNReal ↦ (t : ℝ)) (nhds 0) (nhds 0) :=
    NNReal.tendsto_coe.2 tendsto_id
  simpa only [NNReal.coe_zero, zero_mul] using
    (hcoe.mul (tendsto_const_nhds (x := C)))

/-- The strong Yosida limit converges to the identity at time zero on the
whole space. -/
theorem tendsto_yosidaStrongLimit_apply_zero
    (R : ContractiveResolvent E) (x : E) :
    Tendsto (fun t : NNReal ↦ R.yosidaStrongLimit t x) (nhds 0) (nhds x) := by
  let one : PositiveShift := ⟨1, by norm_num⟩
  exact MarkovProcess.tendsto_of_denseRange_of_opNorm_le_one
    R.yosidaStrongLimit (R.operator one) R.norm_yosidaStrongLimit_le_one
    (R.denseRange one) (R.tendsto_yosidaStrongLimit_apply_operator_zero one) x

/-- The strongly continuous contraction semigroup generated canonically by a
contractive resolvent through its Yosida approximations. -/
def generatedSemigroup (R : ContractiveResolvent E) :
    StronglyContinuousContractionSemigroup E :=
  StronglyContinuousContractionSemigroup.ofTendstoZero
    R.yosidaStrongLimit R.yosidaStrongLimit_zero R.yosidaStrongLimit_add
    R.norm_yosidaStrongLimit_le_one R.tendsto_yosidaStrongLimit_apply_zero

@[simp]
theorem generatedSemigroup_apply (R : ContractiveResolvent E) (t : NNReal) :
    R.generatedSemigroup t = R.yosidaStrongLimit t :=
  rfl

/-- The canonical bounded Yosida semigroups converge strongly to the generated
semigroup. -/
theorem tendsto_yosidaSemigroup_naturalShift_apply_generatedSemigroup
    (R : ContractiveResolvent E) (t : NNReal) (x : E) :
    Tendsto (fun n ↦ R.yosidaSemigroup (naturalShift n) t x) atTop
      (nhds (R.generatedSemigroup t x)) := by
  exact R.tendsto_yosidaOperator_naturalShift_apply t x

end ContractiveResolvent

end MarkovProcess.Semigroup

end

end PortComputability
