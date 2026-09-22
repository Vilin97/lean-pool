/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, OpenAI GPT-5.6 Thinking
-/

import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.System
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.Core

/-!
# Singular systems with finite source and arbitrary Hilbert codomain

Mathlib's finite-dimensional `LinearMap.singularValues` API asks for finite-dimensional
source and codomain, although the right Gram operator `A†A` only lives on the source.
For a finite-dimensional source and arbitrary complete Hilbert codomain, this file factors
`A` through its finite-dimensional range and transports the existing singular-system API
back to the ambient codomain.

This is deliberately a separate layer: it does not install a false `FiniteDimensional`
instance on the ambient codomain and does not weaken the assumptions of the established
finite-dimensional singular-value files.
-/

namespace TauCeti
open Module _root_.TauCeti.LinearMap
open DavisKahan.ExactSinTheta
open scoped InnerProductSpace

variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
  [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

noncomputable section

noncomputable local instance finiteDimensional_range (A : E →L[ℂ] F) :
    FiniteDimensional ℂ A.range := by
  apply FiniteDimensional.of_surjective A.rangeRestrict.toLinearMap
  intro y
  rcases y.property with ⟨x, hx⟩
  exact ⟨x, Subtype.ext hx⟩

noncomputable local instance completeSpace_range (A : E →L[ℂ] F) :
    CompleteSpace A.range :=
  FiniteDimensional.complete ℂ A.range

/-- Singular values of a finite-source operator, computed after restricting the codomain to
its finite-dimensional range. -/
noncomputable def finiteSourceSingularValue (A : E →L[ℂ] F)
    (i : Fin (finrank ℂ E)) : ℝ :=
  A.rangeRestrict.toLinearMap.singularValues i

/-- The right singular basis of a finite-source operator. -/
noncomputable def finiteSourceRightSingularBasis (A : E →L[ℂ] F) :
    OrthonormalBasis (Fin (finrank ℂ E)) ℂ E :=
  rightSingularBasis A.rangeRestrict.toLinearMap

/-- The ambient left singular vector obtained by including the range-valued singular
vector into the original codomain. -/
noncomputable def finiteSourceLeftSingularVector (A : E →L[ℂ] F)
    (i : Fin (finrank ℂ E)) : F :=
  (leftSingularVector A.rangeRestrict.toLinearMap i : A.range)

omit [CompleteSpace F] in
/-- Finite-source singular values are nonnegative. -/
@[simp]
theorem finiteSourceSingularValue_nonneg (A : E →L[ℂ] F)
    (i : Fin (finrank ℂ E)) :
    0 ≤ finiteSourceSingularValue A i :=
  A.rangeRestrict.toLinearMap.singularValues_nonneg i

omit [CompleteSpace F] in
/-- The finite-source singular value equals the corresponding approximation singular value
of the original ambient-codomain operator. -/
theorem approximationSingularValue_eq_finiteSourceSingularValue
    (A : E →L[ℂ] F) (i : Fin (finrank ℂ E)) :
    approximationSingularValue i A = finiteSourceSingularValue A i := by
  let W : Submodule ℂ F := A.range
  let : FiniteDimensional ℂ W := by
    apply FiniteDimensional.of_surjective A.rangeRestrict.toLinearMap
    intro y
    rcases y.property with ⟨x, hx⟩
    exact ⟨x, Subtype.ext hx⟩
  let : CompleteSpace W := FiniteDimensional.complete ℂ W
  let : W.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace W
  let AW : E →L[ℂ] W := W.orthogonalProjectionOnto ∘L A
  have hA : ∀ x, A x ∈ W := by
    intro x
    exact ⟨x, rfl⟩
  have hAW : AW = A.rangeRestrict := by
    ext x
    change W.starProjection (A x) = A x
    exact W.starProjection_eq_self_iff.mpr (hA x)
  calc
    approximationSingularValue i A = approximationSingularValue i AW :=
      (approximationSingularValue_orthogonalProjectionOnto_comp_eq W A hA i).symm
    _ = AW.toLinearMap.singularValues i :=
      approximationSingularValue_eq_singularValues AW.toLinearMap i
    _ = finiteSourceSingularValue A i := by
      rw [hAW]
      rfl

omit [CompleteSpace F] in
/-- The right singular basis is orthonormal. -/
theorem finiteSourceRightSingularBasis_orthonormal (A : E →L[ℂ] F) :
    Orthonormal ℂ (finiteSourceRightSingularBasis A) :=
  (finiteSourceRightSingularBasis A).orthonormal

omit [CompleteSpace F] in
/-- The image of a finite-source right singular vector has norm equal to its singular
value. -/
theorem norm_apply_finiteSourceRightSingularBasis
    (A : E →L[ℂ] F) (i : Fin (finrank ℂ E)) :
    ‖A (finiteSourceRightSingularBasis A i)‖ = finiteSourceSingularValue A i := by
  have h := norm_apply_rightSingularBasis A.rangeRestrict.toLinearMap i
  simpa [finiteSourceRightSingularBasis, finiteSourceSingularValue] using h

omit [CompleteSpace F] in
/-- A zero finite-source singular value gives a zero image. -/
theorem apply_finiteSourceRightSingularBasis_eq_zero_of_singularValue_eq_zero
    (A : E →L[ℂ] F) {i : Fin (finrank ℂ E)}
    (hi : finiteSourceSingularValue A i = 0) :
    A (finiteSourceRightSingularBasis A i) = 0 := by
  have h := apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero
    A.rangeRestrict.toLinearMap hi
  exact congrArg Subtype.val h

omit [CompleteSpace F] in
/-- The finite-source singular relation `A vᵢ = σᵢ uᵢ`. -/
theorem apply_finiteSourceRightSingularBasis_eq_smul_leftSingularVector
    (A : E →L[ℂ] F) (i : Fin (finrank ℂ E)) :
    A (finiteSourceRightSingularBasis A i) =
      ((finiteSourceSingularValue A i : ℝ) : ℂ) •
        finiteSourceLeftSingularVector A i := by
  have h := apply_rightSingularBasis_eq_smul_leftSingularVector
    A.rangeRestrict.toLinearMap i
  exact congrArg Subtype.val h

omit [CompleteSpace F] in
/-- Every ambient left singular vector lies in the range of the original operator. -/
theorem finiteSourceLeftSingularVector_mem_range
    (A : E →L[ℂ] F) (i : Fin (finrank ℂ E)) :
    finiteSourceLeftSingularVector A i ∈ A.range :=
  (leftSingularVector A.rangeRestrict.toLinearMap i).property

omit [CompleteSpace F] in
/-- Ambient left singular vectors attached to nonzero singular values are orthonormal. -/
theorem orthonormal_finiteSourceLeftSingularVector_subtype (A : E →L[ℂ] F) :
    Orthonormal ℂ
      (fun i : {j : Fin (finrank ℂ E) // finiteSourceSingularValue A j ≠ 0} =>
        finiteSourceLeftSingularVector A i.1) := by
  classical
  have h := orthonormal_leftSingularVector_subtype A.rangeRestrict.toLinearMap
  rw [orthonormal_iff_ite] at h ⊢
  intro i j
  let i' : {k : Fin (finrank ℂ E) //
      A.rangeRestrict.toLinearMap.singularValues k ≠ 0} :=
    ⟨i.1, by simpa [finiteSourceSingularValue] using i.2⟩
  let j' : {k : Fin (finrank ℂ E) //
      A.rangeRestrict.toLinearMap.singularValues k ≠ 0} :=
    ⟨j.1, by simpa [finiteSourceSingularValue] using j.2⟩
  have hij := h i' j'
  by_cases heq : i = j
  · subst j
    simpa [finiteSourceLeftSingularVector, i', j'] using hij
  · have hne : i' ≠ j' := by
      intro h'
      apply heq
      apply Subtype.ext
      exact congrArg Subtype.val h'
    rw [ite_eq_right hne] at hij
    rw [ite_eq_right heq]
    simpa [finiteSourceLeftSingularVector, i', j'] using hij

/-- The ambient adjoint singular relation. -/
theorem adjoint_apply_finiteSourceLeftSingularVector
    (A : E →L[ℂ] F) {i : Fin (finrank ℂ E)}
    (hi : finiteSourceSingularValue A i ≠ 0) :
    A.adjoint (finiteSourceLeftSingularVector A i) =
      ((finiteSourceSingularValue A i : ℝ) : ℂ) •
        finiteSourceRightSingularBasis A i := by
  let Ar : E →L[ℂ] A.range := A.rangeRestrict
  let ur : A.range := leftSingularVector Ar.toLinearMap i
  have hur : Ar.toLinearMap.adjoint ur =
      ((finiteSourceSingularValue A i : ℝ) : ℂ) •
        finiteSourceRightSingularBasis A i := by
    simpa [Ar, ur, finiteSourceSingularValue, finiteSourceRightSingularBasis] using
      (adjoint_apply_leftSingularVector Ar.toLinearMap hi)
  have hu : finiteSourceLeftSingularVector A i = (ur : F) := by
    rfl
  apply ext_inner_right ℂ
  intro x
  rw [hu]
  calc
    ⟪A.adjoint (ur : F), x⟫_ℂ = ⟪(ur : F), A x⟫_ℂ :=
      ContinuousLinearMap.adjoint_inner_left A x (ur : F)
    _ = ⟪ur, Ar x⟫_ℂ := rfl
    _ = ⟪Ar.toLinearMap.adjoint ur, x⟫_ℂ :=
      (LinearMap.adjoint_inner_left Ar.toLinearMap x ur).symm
    _ = ⟪((finiteSourceSingularValue A i : ℝ) : ℂ) •
          finiteSourceRightSingularBasis A i, x⟫_ℂ := by rw [hur]

omit [CompleteSpace F] in
/-- A contraction has every finite-source singular value at most one. -/
theorem finiteSourceSingularValue_le_one_of_contraction
    (A : E →L[ℂ] F) (hA : ∀ x, ‖A x‖ ≤ ‖x‖)
    (i : Fin (finrank ℂ E)) :
    finiteSourceSingularValue A i ≤ 1 := by
  apply singularValues_le_one_of_contraction (A := A.rangeRestrict.toLinearMap)
  · intro x
    simpa using hA x
  · rfl

end

end TauCeti
