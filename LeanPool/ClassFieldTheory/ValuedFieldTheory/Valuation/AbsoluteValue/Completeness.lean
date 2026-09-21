/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.Analysis.Normed.Field.WithAbs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.Norm.Defs
import Mathlib.Topology.UniformSpace.AbsoluteValue
/-!
# Minimal absolute-value norm API

This file keeps only the lightweight explicit definitions used by the
current Section 4 formalization.  The old experimental completion and norm
formula development was removed because it duplicated mathlib APIs and no
longer compiled.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

/-- A valued field is complete if it is complete for the uniformity
induced by its absolute value. -/
def IsCompleteForAbsoluteValue {K : Type*} [Field K] (v : AbsoluteValue K ℝ) : Prop :=
  @CompleteSpace K v.uniformSpace

/-- The uniformity attached directly to an absolute value agrees with the
uniformity coming from the normed-field structure induced by that absolute
value. -/
theorem absoluteValue_uniformSpace_eq_toNormedField
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    v.uniformSpace = (AbsoluteValue.toNormedField v).toUniformSpace := by
  let : NormedField K := AbsoluteValue.toNormedField v
  ext s
  rw [(AbsoluteValue.hasBasis_uniformity v).mem_iff,
    Metric.uniformity_basis_dist.mem_iff]
  have hdist : ∀ p : K × K, dist p.1 p.2 = v (p.1 - p.2) := by
    intro p
    change v (-p.1 + p.2) = v (p.1 - p.2)
    simpa [sub_eq_add_neg, add_comm] using (v.map_sub p.1 p.2).symm
  simp [hdist, AbsoluteValue.map_sub]

/-- Completeness in the absolute-value uniformity is the same as
completeness of the corresponding `WithAbs` normed field. -/
theorem absoluteValueCompleteness_completeSpace_withAbs_iff_complete
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    CompleteSpace (WithAbs v) ↔ IsCompleteForAbsoluteValue v := by
  let : NormedField K := AbsoluteValue.toNormedField v
  let e : WithAbs v ≃ᵢ K :=
    { toEquiv := (WithAbs.equiv v).toEquiv
      isometry_toFun := by
        rw [isometry_iff_dist_eq]
        intro x y
        simp only [dist_eq_norm_sub,
          WithAbs.norm_eq_apply_ofAbs, WithAbs.ofAbs_sub]
        rfl }
  rw [e.completeSpace_iff]
  change @CompleteSpace K (AbsoluteValue.toNormedField v).toUniformSpace ↔
    @CompleteSpace K v.uniformSpace
  rw [← absoluteValue_uniformSpace_eq_toNormedField v]

/-- A complete valued field is complete as the corresponding `WithAbs`
normed field. -/
theorem completeSpace_withAbs_of_isCompleteForAbsoluteValue
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    (hcomplete : IsCompleteForAbsoluteValue v) :
    CompleteSpace (WithAbs v) :=
  (absoluteValueCompleteness_completeSpace_withAbs_iff_complete v).2 hcomplete

/-- Sequence form of the sequential completeness criterion: a complete valued field is exactly one
where every Cauchy sequence in the absolute-value topology converges. -/
theorem absoluteValueCompleteness_complete_iff_cauchySeq_converges
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    IsCompleteForAbsoluteValue v ↔
      ∀ u : ℕ → WithAbs v, CauchySeq u →
        ∃ a : WithAbs v, Filter.Tendsto u Filter.atTop (nhds a) := by
  constructor
  · intro hcomplete u hu
    let : CompleteSpace (WithAbs v) :=
      completeSpace_withAbs_of_isCompleteForAbsoluteValue v hcomplete
    exact cauchySeq_tendsto_of_complete hu
  · intro hseq
    exact (absoluteValueCompleteness_completeSpace_withAbs_iff_complete v).1
      (Metric.complete_of_cauchySeq_tendsto hseq)

/-- The nontrivial-valuation convention excludes the trivial valuation; this supplies the
corresponding mathlib `NontriviallyNormedField` instance for `WithAbs v`. -/
@[reducible]
def withAbsNontriviallyNormedField
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) (hv : v.IsNontrivial) :
    NontriviallyNormedField (WithAbs v) :=
  NontriviallyNormedField.ofNormNeOne
    (by
      rcases hv with ⟨x, hx0, hx1⟩
      refine ⟨(WithAbs.equiv v).symm x, ?_, ?_⟩
      · intro hx
        apply hx0
        simpa using congrArg (WithAbs.equiv v) hx
      · simpa [WithAbs.norm_eq_apply_ofAbs] using hx1)

/-- The finite-degree norm-formula candidate:
`x ↦ |N_{L/K}(x)|^{1/[L:K]}`. -/
def finiteExtensionNormFormulaValue
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) : ℝ :=
  Real.rpow (v (Algebra.norm K x)) (1 / (Module.finrank K L : ℝ))

/-- The finite-degree norm formula candidate is nonnegative. -/
theorem finiteExtensionNormFormulaValue_nonneg
    {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (x : L) :
    0 ≤ finiteExtensionNormFormulaValue v x :=
  Real.rpow_nonneg (v.nonneg _) _

end Valuations
end AlgebraicNumberTheory

end
