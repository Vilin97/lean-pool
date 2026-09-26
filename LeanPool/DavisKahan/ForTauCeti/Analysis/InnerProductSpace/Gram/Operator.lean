/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, GPT 5.6 High
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.InnerProductSpace.Singular.Subspace

/-!
# Gram operators of a linear map

For `A : E →ₗ[𝕜] F` the two *Gram operators* are `A⋆A` on `E` and `AA⋆` on `F`.
Both are symmetric and positive semidefinite, and their eigenvalues are the
squared singular values of `A` — which is what makes them the carrier of the
singular-subspace theory: a right singular subspace of `A` is a spectral
subspace of `A⋆A`, a left one a spectral subspace of `AA⋆`.

This module records the operators, their symmetry, and the two facts a
perturbation argument needs:

* an exact difference identity, `rightGram_sub_rightGram` and its dual, which
  splits `Â⋆Â - A⋆A` into two terms each carrying one factor of `Â - A`;
* the operator-norm bound that follows, `opNorm_rightGram_sub_le` and its dual:
  `‖Â⋆Â - A⋆A‖ ≤ (‖Â‖ + ‖A‖) ‖Â - A‖`.

The bound is stated with `toContinuousLinearMap` on both sides because the
operator norm is only available on the bundled continuous map; in finite
dimensions the two carry the same data.

## Sources

That `A⋆A` and `A A⋆` are positive with eigenvalues the squared singular values is
standard singular-value theory (Horn--Johnson, *Matrix Analysis*; distilled in
`prose/distilled_literature/HornJohnson2013_selected_matrix_analysis.tex`).  The
exact difference identity and the perturbation bound are shaped by the
singular-subspace argument that consumes them.

## Provenance

* Original module: `DavisKahan/Specialized/SingularSubspace.lean`, where this
  API sat alongside the paper-specific singular-subspace definitions.
* Extraction class: **relocation**, unchanged mathematics.  Migrated because it
  is generic — nothing here mentions a paper, a
  gap condition, or a spectral subspace — and its one non-Mathlib dependency,
  `norm_gram_sub_gram_apply_le`, already lives in
  `ForTauCeti/Analysis/InnerProductSpace/SingularSubspace.lean`.
* Deliberately **not** migrated with it: `rightSingularSubspace` and
  `leftSingularSubspace`, which depend on `pointSpectralSubspace` (still in
  `DavisKahan/FiniteDimensional/Core`), and the Hermitian-dilation block,
  which is unused outside its defining file.  (This note used to add that the
  name was homonymous with an unrelated bounded `hermitianDilation` in
  `TauCeti.DavisKahanExt`; no such declaration exists, so that half of the
  recorded reason is void.)
* Spectra influence: none.
-/

@[expose] public section

namespace TauCeti

open scoped InnerProductSpace BigOperators
open Module (finrank)

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E]
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [FiniteDimensional 𝕜 F]

/-- Right Gram operator `A⋆A`. -/
@[expose]
noncomputable def rightGram (A : E →ₗ[𝕜] F) : E →ₗ[𝕜] E :=
  A.adjoint ∘ₗ A

/-- The right Gram operator is symmetric and positive semidefinite. -/
theorem isSymmetric_rightGram (A : E →ₗ[𝕜] F) : (rightGram A).IsSymmetric := by
  simpa [rightGram] using A.isSymmetric_adjoint_comp_self

/-- Left Gram operator `AA⋆`. -/
@[expose]
noncomputable def leftGram (A : E →ₗ[𝕜] F) : F →ₗ[𝕜] F :=
  A ∘ₗ A.adjoint

/-- The left Gram operator is symmetric and positive semidefinite. -/
theorem isSymmetric_leftGram (A : E →ₗ[𝕜] F) : (leftGram A).IsSymmetric := by
  simpa [leftGram] using A.adjoint.isSymmetric_adjoint_comp_self

/-- **Gram perturbation identity.**  Each summand carries exactly one factor of
`Â - A`, which is what turns a first-order perturbation of `A` into a
first-order perturbation of `A⋆A`. -/
theorem rightGram_sub_rightGram (A Â : E →ₗ[𝕜] F) :
    rightGram Â - rightGram A =
      Â.adjoint ∘ₗ (Â - A) + (Â - A).adjoint ∘ₗ A := by
  ext x
  simp [rightGram, map_sub]

/-- Left-Gram perturbation identity, dual to `rightGram_sub_rightGram`. -/
theorem leftGram_sub_leftGram (A Â : E →ₗ[𝕜] F) :
    leftGram Â - leftGram A =
      (Â - A) ∘ₗ Â.adjoint + A ∘ₗ (Â - A).adjoint := by
  ext x
  simp [leftGram, map_sub]

/-- **Operator-norm Gram perturbation bound**, `‖Â⋆Â - A⋆A‖ ≤ (‖Â‖ + ‖A‖)‖Â - A‖`. -/
theorem opNorm_rightGram_sub_le (A Â : E →ₗ[𝕜] F) :
    ‖(rightGram Â - rightGram A).toContinuousLinearMap‖ ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  refine (rightGram Â - rightGram A).toContinuousLinearMap.opNorm_le_bound
    (by positivity) fun x => ?_
  have h := norm_gram_sub_gram_apply_le
    (a := ‖A.toContinuousLinearMap‖)
    (â := ‖Â.toContinuousLinearMap‖)
    (ε := ‖(Â - A).toContinuousLinearMap‖)
    (norm_nonneg _) (norm_nonneg _)
    (fun y => A.toContinuousLinearMap.le_opNorm y)
    (fun y => Â.toContinuousLinearMap.le_opNorm y)
    (fun y => (Â - A).toContinuousLinearMap.le_opNorm y) x
  simpa [rightGram, add_comm] using h

/-- Operator-norm perturbation bound for the left Gram operator. -/
theorem opNorm_leftGram_sub_le (A Â : E →ₗ[𝕜] F) :
    ‖(leftGram Â - leftGram A).toContinuousLinearMap‖ ≤
      (‖Â.toContinuousLinearMap‖ + ‖A.toContinuousLinearMap‖) *
        ‖(Â - A).toContinuousLinearMap‖ := by
  refine (leftGram Â - leftGram A).toContinuousLinearMap.opNorm_le_bound
    (by positivity) fun x => ?_
  -- The adjoint's operator norm is not needed: `norm_adjoint_apply_le` bounds
  -- `‖A⋆y‖` by `‖A‖‖y‖` directly, which is what keeps the stated bound in terms
  -- of `‖A‖` and `‖Â‖`.
  have hAadj : ∀ y, ‖A.adjoint y‖ ≤ ‖A.toContinuousLinearMap‖ * ‖y‖ :=
    fun y => norm_adjoint_apply_le (norm_nonneg _)
      (fun z => A.toContinuousLinearMap.le_opNorm z) y
  have hÂadj : ∀ y, ‖Â.adjoint y‖ ≤ ‖Â.toContinuousLinearMap‖ * ‖y‖ :=
    fun y => norm_adjoint_apply_le (norm_nonneg _)
      (fun z => Â.toContinuousLinearMap.le_opNorm z) y
  have hdiffadj : ∀ y,
      ‖(Â.adjoint - A.adjoint) y‖ ≤ ‖(Â - A).toContinuousLinearMap‖ * ‖y‖ :=
    fun y => by
      have h := norm_adjoint_apply_le (norm_nonneg _)
        (fun z => (Â - A).toContinuousLinearMap.le_opNorm z) y
      simpa [map_sub] using h
  have h := norm_gram_sub_gram_apply_le
    (A := A.adjoint) (Â := Â.adjoint)
    (a := ‖A.toContinuousLinearMap‖)
    (â := ‖Â.toContinuousLinearMap‖)
    (ε := ‖(Â - A).toContinuousLinearMap‖)
    (norm_nonneg _) (norm_nonneg _) hAadj hÂadj hdiffadj x
  simpa [leftGram, map_sub, add_comm] using h

end TauCeti
