/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.GramSquare
import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.SameSequence

/-!
# The compression sandwich bound behind Theorem 8.1(ii)

Printed Theorem 8.1(ii) compares the ordered eigenvalues of `A₁` with those of
`Λ₁` through the factor `‖C₁‖²`.  Part (i) supplies the operator inequality

  `A₁ - α ≤ C₁ (Λ₁ - α) C₁`,

so what part (ii) additionally needs is that a *cosine sandwich* cannot increase
the `k`-th singular value by more than `‖C₁‖²`:

  `aₙ(C⋆ M C) ≤ ‖C‖² · aₙ(M)`.

This is that estimate.

## Why approximation numbers rather than `singularValues`

`ContinuousLinearMap.approximationNumber` provides both one-sided composition bounds
for maps between different spaces. They apply directly to the cross-space sandwich:
`C₁` maps the old complement `Pᗮ` to the new one `Qᗮ`. This development uses
continuous linear maps throughout, so no transfer to finite-dimensional `LinearMap`
representatives is needed. The finite-dimensional singular-value bounds in
`ForTauCeti/Analysis/InnerProductSpace/KyFan.lean` also allow rectangular maps.

In finite dimensions the approximation numbers of an operator are its singular
values, so this is the printed statement's factor and not a weaker surrogate.

## The scalar field

The two sandwich bounds are `RCLike`-generic: they use only the adjoint, the
operator norm and the one-sided composition bounds, none of which knows the
field.

The Weyl step `approximationNumber_mono_of_form_le` is stated over `ℂ` only, and
the obstruction is *not* `CFC.sqrt` — that is available over any `RCLike` field
once the three functional-calculus hypotheses of
`ForTauCeti/Analysis/InnerProductSpace/OperatorModulus.lean` are carried.  It is
the squaring step `TauCeti.ApproximationNumber.approximationNumber_gramOperator_complex`
(`aₙ(X⋆X) = aₙ(X)²`), whose whole layer — `gramOperator`, `gramLinearPMap`,
`gramSpectralPVM` — is defined only for `InnerProductSpace ℂ`, because it runs
through the bounded projection-valued measure of a self-adjoint operator.  Since
`RCLike` carries no `ℝ`/`ℂ` discriminator, that cannot be worked around inside a
`𝕜`-generic proof.  The real-scalar consumers therefore descend from the complex
statement by complexification rather than re-elaborating this proof over `ℝ`;
see `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81ApproximationReal.lean`.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace

universe u v

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E : Type u} {F : Type v}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [CompleteSpace F]

/-- **The cosine-sandwich bound.**  Conjugating by a bounded map multiplies every
approximation number by at most `‖C‖²`.

This is the estimate Theorem 8.1(ii) needs on top of part (i), and it is exactly
the printed factor: the paper's `‖C₁‖₁²` is the squared *bound* norm. -/
theorem approximationNumber_adjoint_sandwich_le
    (M : F →L[𝕜] F) (C : E →L[𝕜] F) (n : ℕ) :
    (ContinuousLinearMap.adjoint C ∘L M ∘L C).approximationNumber n ≤
      ‖C‖ ^ 2 * M.approximationNumber n := by
  have hleft :
      (ContinuousLinearMap.adjoint C ∘L M ∘L C).approximationNumber n ≤
        ‖ContinuousLinearMap.adjoint C‖ * (M ∘L C).approximationNumber n :=
    ContinuousLinearMap.approximationNumber_comp_le_norm_mul
      (ContinuousLinearMap.adjoint C) (M ∘L C) n
  have hright : (M ∘L C).approximationNumber n ≤ M.approximationNumber n * ‖C‖ :=
    ContinuousLinearMap.approximationNumber_comp_le_mul_norm M C n
  have hadj : ‖ContinuousLinearMap.adjoint C‖ = ‖C‖ :=
    ContinuousLinearMap.adjoint.norm_map C
  calc (ContinuousLinearMap.adjoint C ∘L M ∘L C).approximationNumber n
      ≤ ‖ContinuousLinearMap.adjoint C‖ * (M ∘L C).approximationNumber n := hleft
    _ ≤ ‖ContinuousLinearMap.adjoint C‖ * (M.approximationNumber n * ‖C‖) := by
        gcongr
    _ = ‖C‖ ^ 2 * M.approximationNumber n := by rw [hadj]; ring

/-- The sandwich bound for a self-adjoint conjugator, the shape Theorem 8.1(ii)
instantiates: `C₁` there is a compression of an orthogonal projection. -/
theorem approximationNumber_sandwich_le_of_isSelfAdjoint
    {C : E →L[𝕜] E} (hC : IsSelfAdjoint C) (M : E →L[𝕜] E) (n : ℕ) :
    (C ∘L M ∘L C).approximationNumber n ≤ ‖C‖ ^ 2 * M.approximationNumber n := by
  have h := approximationNumber_adjoint_sandwich_le M C n
  rwa [ContinuousLinearMap.isSelfAdjoint_iff'.mp hC] at h

end Generic

/-! ### The Weyl step, dimension-free

Complex-only, and the module docstring records exactly which link is complex:
the Gram squaring identity, not the square root. -/

section ComplexWeylStep

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

open TauCeti.ApproximationNumber in
/-- If a positive operator dominates another in the quadratic-form order, it
dominates it in every approximation number.

This is the Weyl monotonicity step of Theorem 8.1(ii), and it is *not* the
`LinearMap` one: `LinearMap.IsSymmetric.eigenvalue_mono` needs a finite
dimension, while both sides of part (i) are positive (the `Pᗮ` form is at least
`α + δ`), and for positive operators the form order can be squared away.

The proof is the factorization: `‖√S x‖² = Re ⟪x, S x⟫`, so the form hypothesis
is exactly pointwise norm domination of the square roots, which
`approximationNumber_le_of_norm_apply_le` converts into domination of their
approximation numbers; then `approximationNumber_gramOperator_complex` squares it back,
since `S = (√S)⋆(√S)`.

Because it avoids min-max over subspaces of a fixed dimension, it holds in
arbitrary dimension -- which is the "natural infinite-dimensional extension" the
printed part (ii) mentions in passing. -/
theorem approximationNumber_mono_of_form_le
    {S T : E →L[ℂ] E} (hS : (0 : E →L[ℂ] E) ≤ S) (hT : (0 : E →L[ℂ] E) ≤ T)
    (h : ∀ x, RCLike.re ⟪x, S x⟫_ℂ ≤ RCLike.re ⟪x, T x⟫_ℂ) (n : ℕ) :
    S.approximationNumber n ≤ T.approximationNumber n := by
  have hsa : ∀ {R : E →L[ℂ] E}, (0 : E →L[ℂ] E) ≤ R → IsSelfAdjoint (CFC.sqrt R) :=
    fun {R} _ =>
      ((ContinuousLinearMap.nonneg_iff_isPositive (f := _)).mp (CFC.sqrt_nonneg R)).isSelfAdjoint
  have hnormsq : ∀ {R : E →L[ℂ] E}, (0 : E →L[ℂ] E) ≤ R → ∀ x : E,
      ‖CFC.sqrt R x‖ ^ 2 = RCLike.re ⟪x, R x⟫_ℂ := by
    intro R hR x
    have hRR : CFC.sqrt R * CFC.sqrt R = R := CFC.sqrt_mul_sqrt_self R hR
    have happ : CFC.sqrt R (CFC.sqrt R x) = R x := by
      have := congrArg (fun T : E →L[ℂ] E => T x) hRR
      simpa [mul_apply_eq_comp] using this
    have hadjeq : ContinuousLinearMap.adjoint (CFC.sqrt R) = CFC.sqrt R :=
      ContinuousLinearMap.isSelfAdjoint_iff'.mp (hsa hR)
    have hkey : ⟪CFC.sqrt R x, CFC.sqrt R x⟫_ℂ = ⟪x, R x⟫_ℂ := by
      nth_rewrite 1 [← hadjeq]
      rw [ContinuousLinearMap.adjoint_inner_left, happ]
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (CFC.sqrt R x), hkey]
  have hgram : ∀ {R : E →L[ℂ] E}, (0 : E →L[ℂ] E) ≤ R →
      gramOperator (CFC.sqrt R) = R := by
    intro R hR
    change ContinuousLinearMap.adjoint (CFC.sqrt R) ∘L CFC.sqrt R = R
    rw [← ContinuousLinearMap.star_eq_adjoint, (hsa hR).star_eq]
    exact CFC.sqrt_mul_sqrt_self R hR
  have hle : ∀ x : E, ‖CFC.sqrt S x‖ ≤ ‖CFC.sqrt T x‖ := by
    intro x
    have := (hnormsq hS x).trans_le ((h x).trans_eq (hnormsq hT x).symm)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this
  calc S.approximationNumber n
      = (gramOperator (CFC.sqrt S)).approximationNumber n := by rw [hgram hS]
    _ = (CFC.sqrt S).approximationNumber n ^ 2 :=
        approximationNumber_gramOperator_complex _ n
    _ ≤ (CFC.sqrt T).approximationNumber n ^ 2 := by
        gcongr
        · exact _root_.ContinuousLinearMap.approximationNumber_nonneg _ _
        · exact _root_.ContinuousLinearMap.approximationNumber_le_of_norm_apply_le _ _ hle n
    _ = (gramOperator (CFC.sqrt T)).approximationNumber n :=
        (approximationNumber_gramOperator_complex _ n).symm
    _ = T.approximationNumber n := by rw [hgram hT]

end ComplexWeylStep

end Section8
end DavisKahan1970
end TauCeti
