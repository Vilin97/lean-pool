/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT-5.6 High, Claude Fable 5
-/
module

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.RectangularSingularValues


/-!
# Intrinsic singular systems for rectangular linear maps

A reusable singular-vector layer stated directly for a linear map between finite-dimensional
`RCLike` inner-product spaces.  The right singular basis is the sorted orthonormal eigenbasis
of `A†A`; left singular vectors are the normalized images `σᵢ⁻¹ • A vᵢ`.

## Main results

* `TauCeti.apply_rightSingularBasis_eq_smul_leftSingularVector`: the singular relation
  `A vᵢ = σᵢ • uᵢ`, including the zero case;
* `TauCeti.orthonormal_leftSingularVector_subtype`: left singular vectors attached to
  nonzero singular values are orthonormal;
* `TauCeti.selfCompAdjoint_apply_leftSingularVector`: nonzero left singular vectors are
  eigenvectors of `AA†` with eigenvalue `σᵢ²`;
* `TauCeti.singular_reconstruction` and `TauCeti.eq_sum_singularValue_rankOne`: the
  intrinsic singular expansion of `A`;
* `TauCeti.exists_orthonormalBasis_extending_leftSingularVector`: the nonzero left
  singular family extends to an orthonormal basis of the codomain.

## Proof sources

The construction parallels the Apache-2.0 matrix-Euclidean development in
`vendor/lean/lean-stat-learning-theory/SingularSystemGram.excerpt.lean` (Zhang–Lee–Liu),
restated intrinsically for linear maps; the excerpt was used as a route map and no code was
copied verbatim.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib.Analysis.InnerProductSpace.SingularSystem`, moved to
  `ForTauCeti` in the Wave-1 staging migration; introduced at Davis--Kahan
  commit `82d20de`.
* Extraction class: **moved**.  The Wave-1 migration renamed the namespace
  `ForMathlib` to `TauCeti`; declaration names and proofs are unchanged.
* Original authors / copyright: Jon Crall, GPT-5.6 High, Claude Fable 5; Copyright (c) 2026
  Kitware, Inc.;
  Apache 2.0.
* Spectra influence: **none** — this module imports only Mathlib and sibling
  `ForTauCeti` staging modules.
-/

public section

namespace TauCeti

open Module LinearMap
open scoped InnerProductSpace

variable {𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

/-- The right singular basis, chosen as the sorted orthonormal eigenbasis of `A†A`. -/
noncomputable def rightSingularBasis (A : E →ₗ[𝕜] F) :
    OrthonormalBasis (Fin (finrank 𝕜 E)) 𝕜 E :=
  A.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl

/-- The total left singular-vector expression `σᵢ⁻¹ • A vᵢ`.

At a zero singular value this definition evaluates to zero because division in a field is
total. Orthonormality is asserted only on the subtype of nonzero singular values. -/
noncomputable def leftSingularVector (A : E →ₗ[𝕜] F)
    (i : Fin (finrank 𝕜 E)) : F :=
  (((A.singularValues i : ℝ) : 𝕜)⁻¹) • A (rightSingularBasis A i)

/-- The right singular basis diagonalizes `A†A`. -/
theorem adjointCompSelf_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) :
    (A.adjoint.comp A) (rightSingularBasis A i) =
      (((A.singularValues i : ℝ) ^ 2 : ℝ) : 𝕜) • rightSingularBasis A i := by
  have h := A.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis rfl i
  rw [← A.sq_singularValues_fin rfl i] at h
  exact h

/-- A right singular vector with zero singular value lies in the kernel of `A`. -/
theorem apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero
    (A : E →ₗ[𝕜] F) {i : Fin (finrank 𝕜 E)}
    (hi : A.singularValues i = 0) :
    A (rightSingularBasis A i) = 0 := by
  have hker : rightSingularBasis A i ∈ (A.adjoint ∘ₗ A).ker := by
    rw [LinearMap.mem_ker, adjointCompSelf_apply_rightSingularBasis A i, hi]
    simp
  rw [LinearMap.ker_adjoint_comp_self] at hker
  exact LinearMap.mem_ker.mp hker

/-- The singular relation `A vᵢ = σᵢ uᵢ`, including the zero case. -/
theorem apply_rightSingularBasis_eq_smul_leftSingularVector
    (A : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) :
    A (rightSingularBasis A i) =
      ((A.singularValues i : ℝ) : 𝕜) • leftSingularVector A i := by
  by_cases hi : A.singularValues i = 0
  · rw [apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi, hi]
    simp
  · have hσ : ((A.singularValues i : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hi
    rw [leftSingularVector, smul_smul, mul_inv_cancel₀ hσ, one_smul]

/-- Left singular vectors attached to nonzero singular values are orthonormal. -/
theorem orthonormal_leftSingularVector_subtype (A : E →ₗ[𝕜] F) :
    Orthonormal 𝕜
      (fun i : {j : Fin (finrank 𝕜 E) // A.singularValues j ≠ 0} =>
        leftSingularVector A i.1) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  have hconj : (starRingEnd 𝕜) (((A.singularValues i.1 : ℝ) : 𝕜)⁻¹) =
      ((A.singularValues i.1 : ℝ) : 𝕜)⁻¹ := by
    rw [map_inv₀, RCLike.conj_ofReal]
  simp only [leftSingularVector, inner_smul_left, inner_smul_right, hconj,
    ← LinearMap.adjoint_inner_right, ← LinearMap.comp_apply,
    adjointCompSelf_apply_rightSingularBasis,
    orthonormal_iff_ite.mp (rightSingularBasis A).orthonormal]
  rcases eq_or_ne i j with h | h
  · subst h
    rw [ite_eq_left rfl, ite_eq_left rfl]
    have hσ : ((A.singularValues i.1 : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr i.2
    rw [mul_one, RCLike.ofReal_pow]
    field_simp
  · rw [ite_eq_right (fun hc : (i.1 : Fin (finrank 𝕜 E)) = j.1 => h (Subtype.ext hc)),
      ite_eq_right h]
    ring

/-- The image of a right singular basis vector has norm equal to its singular value. -/
theorem norm_apply_rightSingularBasis
    (A : E →ₗ[𝕜] F) (i : Fin (finrank 𝕜 E)) :
    ‖A (rightSingularBasis A i)‖ = A.singularValues i := by
  by_cases hi : A.singularValues i = 0
  · rw [apply_rightSingularBasis_eq_zero_of_singularValue_eq_zero A hi, norm_zero, hi]
  · rw [apply_rightSingularBasis_eq_smul_leftSingularVector,
      norm_smul, RCLike.norm_ofReal, abs_of_nonneg (A.singularValues_nonneg i)]
    have hnorm : ‖leftSingularVector A i‖ = 1 :=
      (orthonormal_leftSingularVector_subtype A).norm_eq_one ⟨i, hi⟩
    rw [hnorm, mul_one]

/-- The adjoint singular relation for a nonzero singular value. -/
theorem adjoint_apply_leftSingularVector
    (A : E →ₗ[𝕜] F) {i : Fin (finrank 𝕜 E)}
    (hi : A.singularValues i ≠ 0) :
    A.adjoint (leftSingularVector A i) =
      ((A.singularValues i : ℝ) : 𝕜) • rightSingularBasis A i := by
  have hσ : ((A.singularValues i : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hi
  rw [leftSingularVector, map_smul,
    ← LinearMap.comp_apply,
    adjointCompSelf_apply_rightSingularBasis, smul_smul, RCLike.ofReal_pow]
  congr 1
  field_simp

/-- Every nonzero left singular vector is an eigenvector of `AA†` with eigenvalue `σᵢ²`. -/
theorem selfCompAdjoint_apply_leftSingularVector
    (A : E →ₗ[𝕜] F) {i : Fin (finrank 𝕜 E)}
    (hi : A.singularValues i ≠ 0) :
    (A.comp A.adjoint) (leftSingularVector A i) =
      (((A.singularValues i : ℝ) ^ 2 : ℝ) : 𝕜) • leftSingularVector A i := by
  have hσ : ((A.singularValues i : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hi
  have hadj : A.adjoint (leftSingularVector A i) =
      ((A.singularValues i : ℝ) : 𝕜) • rightSingularBasis A i := by
    rw [leftSingularVector, map_smul,
    ← LinearMap.comp_apply,
      adjointCompSelf_apply_rightSingularBasis, smul_smul, RCLike.ofReal_pow]
    congr 1
    field_simp
  calc (A.comp A.adjoint) (leftSingularVector A i)
      = A (A.adjoint (leftSingularVector A i)) := rfl
    _ = ((A.singularValues i : ℝ) : 𝕜) • A (rightSingularBasis A i) := by
        rw [hadj, map_smul]
    _ = (((A.singularValues i : ℝ) ^ 2 : ℝ) : 𝕜) • leftSingularVector A i := by
        rw [apply_rightSingularBasis_eq_smul_leftSingularVector, smul_smul,
          RCLike.ofReal_pow, sq]

/-- Intrinsic finite singular expansion of `A x`. -/
theorem singular_reconstruction (A : E →ₗ[𝕜] F) (x : E) :
    A x = ∑ i : Fin (finrank 𝕜 E),
      (inner 𝕜 (rightSingularBasis A i) x * ((A.singularValues i : ℝ) : 𝕜)) •
        leftSingularVector A i := by
  conv_lhs => rw [← (rightSingularBasis A).sum_repr x, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, apply_rightSingularBasis_eq_smul_leftSingularVector, smul_smul,
    (rightSingularBasis A).repr_apply_apply]

/-- Rank-one operator reconstruction of `A`. -/
theorem eq_sum_singularValue_rankOne (A : E →ₗ[𝕜] F) :
    A = ∑ i : Fin (finrank 𝕜 E),
      ((A.singularValues i : ℝ) : 𝕜) •
        (InnerProductSpace.rankOne 𝕜
          (leftSingularVector A i) (rightSingularBasis A i)).toLinearMap := by
  apply LinearMap.ext
  intro x
  rw [LinearMap.sum_apply, singular_reconstruction A x]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, ContinuousLinearMap.coe_coe, InnerProductSpace.rankOne_apply,
    smul_smul, mul_comm]

/-- The nonzero left singular family extends to an orthonormal basis of the codomain. -/
theorem exists_orthonormalBasis_extending_leftSingularVector
    (A : E →ₗ[𝕜] F) :
    ∃ b : OrthonormalBasis (Fin (finrank 𝕜 F)) 𝕜 F,
      Set.range
          (fun i : {j : Fin (finrank 𝕜 E) // A.singularValues j ≠ 0} =>
            leftSingularVector A i.1) ⊆ Set.range b := by
  classical
  have hon := orthonormal_leftSingularVector_subtype A
  have hsub : Orthonormal 𝕜 ((↑) : Set.range
      (fun i : {j : Fin (finrank 𝕜 E) // A.singularValues j ≠ 0} =>
        leftSingularVector A i.1) → F) := hon.toSubtypeRange
  obtain ⟨u, b, hvu, hb⟩ := hsub.exists_orthonormalBasis_extension
  have hcard : Fintype.card u = finrank 𝕜 F := by
    rw [Fintype.card_coe]
    exact (Module.finrank_eq_card_finset_basis b.toBasis).symm
  refine ⟨b.reindex (Fintype.equivFinOfCardEq hcard), ?_⟩
  intro y hy
  have hyu : y ∈ (u : Set F) := hvu hy
  refine ⟨Fintype.equivFinOfCardEq hcard ⟨y, hyu⟩, ?_⟩
  rw [OrthonormalBasis.reindex_apply, Equiv.symm_apply_apply, hb]

end TauCeti
