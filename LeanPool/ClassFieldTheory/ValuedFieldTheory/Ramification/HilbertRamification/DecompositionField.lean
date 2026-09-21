/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Ramification.HilbertRamification.DecompositionGroup
import Mathlib.FieldTheory.Galois.Infinite
/-!
# Decomposition field

The decomposition field is the fixed field of the decomposition group.  This
formulation uses absolute values and therefore includes the archimedean case.
-/

noncomputable section

universe u v

namespace HilbertRamification

open scoped Pointwise Topology

variable (K : Type u) {L : Type v} [Field K] [Field L] [Algebra K L]

/-- The decomposition-field definition: the decomposition field `Z_w` of a
absolute value `w` over `K`. -/
abbrev absoluteValueDecompositionField (w : AbsoluteValue L ℝ) :
    IntermediateField K L :=
  IntermediateField.fixedField (absoluteValueDecompositionGroup K w)

@[simp] theorem mem_absoluteValueDecompositionField_iff
    (w : AbsoluteValue L ℝ) (x : L) :
    x ∈ absoluteValueDecompositionField K w ↔
      ∀ σ ∈ absoluteValueDecompositionGroup K w, σ x = x :=
  IntermediateField.mem_fixedField_iff (H := absoluteValueDecompositionGroup K w) x

/-- The decomposition group is closed in the Krull topology.  A failure to
preserve the valuation class is witnessed by one element `x`; the coset of
the open subgroup fixing `K(x)` is then contained in the complement. -/
theorem absoluteValueDecompositionGroup_isClosed
    [Algebra.IsAlgebraic K L] (w : AbsoluteValue L ℝ) :
    IsClosed (absoluteValueDecompositionGroup K w : Set (L ≃ₐ[K] L)) where
  isOpen_compl := isOpen_iff_mem_nhds.mpr fun σ hσ => by
    rw [Set.mem_compl_iff, SetLike.mem_coe,
      mem_absoluteValueDecompositionGroup_iff] at hσ
    rcases Classical.not_forall.mp hσ with ⟨x, hx⟩
    let E : IntermediateField K L := IntermediateField.adjoin K {x}
    let : FiniteDimensional K E :=
      IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral x)
    apply mem_nhds_iff.mpr
    refine ⟨σ • (E.fixingSubgroup : Set (L ≃ₐ[K] L)), ?_, ?_, ?_⟩
    · intro τ hτ
      rcases Set.mem_smul_set.mp hτ with ⟨g, hg, rfl⟩
      rw [Set.mem_compl_iff, SetLike.mem_coe,
        mem_absoluteValueDecompositionGroup_iff]
      intro hmem
      apply hx
      have hgx : g x = x :=
        (IntermediateField.mem_fixingSubgroup_iff E g).mp hg x
          (IntermediateField.subset_adjoin (F := K) (S := {x}) (by simp))
      simpa [AlgEquiv.mul_apply, hgx] using hmem x
    · exact E.fixingSubgroup_isOpen.smul σ
    · exact ⟨1, E.fixingSubgroup.one_mem, by simp⟩

/-- For a finite or infinite Galois extension, the decomposition group is the
subgroup fixing its decomposition field. -/
theorem absoluteValueDecompositionField_fixingSubgroup_eq
    [IsGalois K L] (w : AbsoluteValue L ℝ) :
    (absoluteValueDecompositionField K w).fixingSubgroup =
      absoluteValueDecompositionGroup K w := by
  let H : ClosedSubgroup (L ≃ₐ[K] L) :=
    ⟨absoluteValueDecompositionGroup K w, absoluteValueDecompositionGroup_isClosed K w⟩
  exact InfiniteGalois.fixingSubgroup_fixedField H

end HilbertRamification
