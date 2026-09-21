/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.BoundedOperator.BlockShift
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.CompressionApproximation
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.BranchRepulsion

/-! # Theorem81Approximation -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970, Theorem 8.1(ii)

The printed clause is

  `α_k - α ≤ ‖C₁‖₁² (λ_k - α)`

where `α_k` are the ordered eigenvalues of the unperturbed compression `A₁` on
`Pᗮ`, `λ_k` those of the perturbed compression `Λ₁` on `Qᗮ`, and `‖·‖₁` is the
bound norm.

## How this is assembled

Three ingredients, each proved separately:

* `theorem8_1_upperCompressionRepulsion` -- part (i) on the `Pᗮ` block,
  i.e. `A₁ - α ≤ C₁(Λ₁ - α)C₁` as quadratic forms;
* `approximationNumber_mono_of_form_le` -- the Weyl step, for positive operators
  and in arbitrary dimension;
* `approximationNumber_adjoint_sandwich_le` -- `aₙ(D⋆ M D) ≤ ‖D‖² aₙ(M)`.

## Why the statement is ambient

Both compressions are written as ambient operators cut down by the relevant
projection (`P_{Pᗮ} (A - α) P_{Pᗮ}` and `P_{Qᗮ} (A + K - α) P_{Qᗮ}`) rather than
as operators on the subtypes `↥Pᗮ` and `↥Qᗮ`.  That is deliberate: it keeps the
whole argument inside `H`, so no subspace-transfer machinery is needed, and the
cosine block appears directly as `D = P_{Qᗮ} P_{Pᗮ}`, whose norm is exactly the
paper's `‖C₁‖₁`.  Extending each compression by zero adds only zeros to the
approximation-number sequence, so the ordered comparison is unaffected.

## Ordering convention

`approximationNumber` is indexed in **decreasing** order, while the paper prints
`λ₁ ≤ λ₂ ≤ ⋯` increasing.  The printed family of inequalities is invariant under
reversing both lists together -- which is exactly what a global reindex does --
so this is the printed statement and not a reordering of it.  In finite
dimensions the approximation numbers of these positive operators are their
eigenvalues, which is the printed reading of `α_k` and `λ_k`.

Because the Weyl step used here is dimension-free, the theorem below is *not*
restricted to finite dimensions; the printed "In finite dimensions" rider is a
statement about where eigenvalues are available, not a limitation of the
estimate.

## Both blocks

The printed clause ends "with a similar relation for `Λ₀`".  That companion is
proved here too, as `theorem8_1_lowerApproximationRepulsion`, against the
mirrored objects `lowerBlockShift` and `lowerCosineBlock`.  The reflection
carrying one to the other is `A ↦ -A`, `α ↦ -(α + δ)`, which exchanges the two
sides of the printed gap; it turns `A₁ - α` into `(α + δ) - A₀` and `C₁` into
`C₀`.  Nothing in the lower proof is a second strategy -- each step is its upper
namesake with the reflected data.

## The scalar field

The **block algebra** of this module -- the four block definitions, their form
evaluations, self-adjointness, positivity and the sandwich positivity lemma --
is `RCLike`-generic, so it is available over a real Hilbert space at
unrestricted dimension.  Nothing in it mentions a spectral branch.

The **endpoints** stay pinned at `ℂ`, and for one reason only: they name
`canonicalLowBranch`, which is the bounded self-adjoint spectral subspace and is
complex by construction.  Their real companions are not re-elaborations; they
descend across `complexify` in `DavisKahan/Sources/DavisKahan1970/Section8/Theorem81ApproximationReal.lean`,
which is also where the block bridges
`complexify_upperBlockShift` and friends live.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

open scoped InnerProductSpace
open TauCeti.DavisKahan

universe u

/-! ### The branch endpoints

Everything below names `canonicalLowBranch`, the bounded self-adjoint spectral
subspace, and is complex for that reason alone. -/

section ComplexBranch

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- The perturbed upper block of the canonical branch is positive.

Theorem 8.1's existence half puts the branch `Q` in the same relative position
to `A + K` that `P` has to `A`: the form of `A + K` on `Qᗮ` is at least
`α + δ`.  Subtracting `α` therefore leaves a positive operator.

Part (iii) needs this separately from the estimate below, because the weak
majorization of a sandwich is stated for a *positive* middle factor. -/
theorem theorem8_1_perturbedUpperBlockShift_nonneg
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    (0 : H →L[ℂ] H) ≤
      upperBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha) alpha := by
  have hconc := theorem8_1_canonicalBranch A K P hdelta hA hK hAP hPlow hPhigh
    hKP hKPperp
  exact upperBlockShift_nonneg (A + K) _ hdelta.le (hA.add hK) hconc.branch_form_high

/-- **The Weyl step of Theorem 8.1, upper block.**

  `aₙ(A₁ - α) ≤ aₙ(C₁⋆ (Λ₁ - α) C₁)`.

This is the part of the argument that both (ii) and (iii) consume, and it is
everything the paper's proof supplies *before* any estimate on `C₁`: part (i)
gives the form domination `A₁ - α ≤ C₁(Λ₁ - α)C₁`, and
`approximationNumber_mono_of_form_le` turns the form order between two positive
operators into domination of every approximation number, in any dimension.

Part (ii) finishes by the coarse bound `aₙ(D⋆ M D) ≤ ‖D‖² aₙ(M)`, which discards
all but the largest singular value of `C₁`.  Part (iii) instead feeds the *same*
inequality into the weak-majorization sandwich theorem, which keeps the whole
sequence.  Neither clause may be derived from the other's final statement. -/
theorem theorem8_1_upperSandwichApproximation
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (upperBlockShift A P alpha).approximationNumber n ≤
      (ContinuousLinearMap.adjoint (cosineBlock P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)) ∘L
        upperBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha ∘L
        cosineBlock P (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha)).approximationNumber n := by
  set Q : Submodule ℂ H := canonicalLowBranch (A + K)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha
    with hQdef
  have : Q.HasOrthogonalProjection := by rw [hQdef]; infer_instance
  -- Positivity of the two blocks: both forms exceed `alpha` on the relevant
  -- complement, by hypothesis for `A` and by the branch for `A + K`.
  have hS : (0 : H →L[ℂ] H) ≤ upperBlockShift A P alpha :=
    upperBlockShift_nonneg A P hdelta.le hA hPhigh
  have hM : (0 : H →L[ℂ] H) ≤ upperBlockShift (A + K) Q alpha :=
    theorem8_1_perturbedUpperBlockShift_nonneg A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp
  have hT := nonneg_adjoint_sandwich hM (cosineBlock P Q)
  -- The form domination `S ≤ D⋆ M D`, which is part (i) at `P_{Pᗮ} x`.
  have hform : ∀ x : H, RCLike.re ⟪x, upperBlockShift A P alpha x⟫_ℂ ≤
      RCLike.re ⟪x, (ContinuousLinearMap.adjoint (cosineBlock P Q) ∘L
        upperBlockShift (A + K) Q alpha ∘L cosineBlock P Q) x⟫_ℂ := by
    intro x
    have hy : Pᗮ.starProjection x ∈ Pᗮ := Submodule.starProjection_apply_mem _ x
    have hpart := theorem8_1_upperCompressionRepulsion A K P hdelta hA hK
      hAP hPlow hPhigh hKP hKPperp hy
    -- Left side: the ambient form of `S` is the compression form at `P_{Pᗮ} x`.
    have hleft : RCLike.re ⟪x, upperBlockShift A P alpha x⟫_ℂ =
        RCLike.re ⟪Pᗮ.starProjection x, A (Pᗮ.starProjection x)⟫_ℂ -
          alpha * ‖Pᗮ.starProjection x‖ ^ 2 :=
      upperBlockShift_apply A P alpha x
    -- Right side: strip the adjoint, then read the perturbed block at `D x`.
    have hadj : ⟪x, (ContinuousLinearMap.adjoint (cosineBlock P Q) ∘L
        upperBlockShift (A + K) Q alpha ∘L cosineBlock P Q) x⟫_ℂ =
        ⟪cosineBlock P Q x,
          upperBlockShift (A + K) Q alpha (cosineBlock P Q x)⟫_ℂ := by
      change ⟪x, ContinuousLinearMap.adjoint (cosineBlock P Q)
        (upperBlockShift (A + K) Q alpha (cosineBlock P Q x))⟫_ℂ = _
      rw [ContinuousLinearMap.adjoint_inner_right]
    have hright := upperBlockShift_apply (A + K) Q alpha (cosineBlock P Q x)
    rw [starProjection_cosineBlock] at hright
    have hcb : cosineBlock P Q x = Qᗮ.starProjection (Pᗮ.starProjection x) := rfl
    rw [hleft, hadj, hright, hcb]
    exact hpart
  exact approximationNumber_mono_of_form_le hS hT hform n

/-- **Davis--Kahan 1970, Theorem 8.1(ii), upper block.**

The printed clause is

  `α_k - α ≤ ‖C₁‖₁² (λ_k - α)`,

and this is its dimension-free approximation-number form: the `k`-th
approximation number of the unperturbed upper block `A₁ - α` is at most
`‖C₁‖²` times that of the perturbed upper block `Λ₁ - α`, where the cosine
block `C₁ = P_{Qᗮ} P_{Pᗮ}` and `Q` is the canonical low branch of `A + K`
supplied by Theorem 8.1's existence half.

The proof is exactly the chain

  `aₙ(S) ≤ aₙ(D⋆ M D) ≤ ‖D‖² aₙ(M)`,

whose two steps are `approximationNumber_mono_of_form_le` (Weyl monotonicity
for positive operators, in arbitrary dimension) and
`approximationNumber_adjoint_sandwich_le` (the cosine-sandwich bound).  The
form hypothesis of the first step is part (i), i.e.
`theorem8_1_upperCompressionRepulsion`, evaluated at `P_{Pᗮ} x`. -/
theorem theorem8_1_upperApproximationRepulsion
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (upperBlockShift A P alpha).approximationNumber n ≤
      ‖cosineBlock P (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha)‖ ^ 2 *
        (upperBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha).approximationNumber n :=
  (theorem8_1_upperSandwichApproximation A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp n).trans
    (approximationNumber_adjoint_sandwich_le _ _ n)

/-! ### The lower block

Everything above is now mirrored.  The reflection carrying the upper clause to
the lower one is `A ↦ -A`, `α ↦ -(α + δ)`; under it `Pᗮ ↦ P`, `Qᗮ ↦ Q`,
`A₁ - α ↦ (α + δ) - A₀`, `Λ₁ - α ↦ (α + δ) - Λ₀`, and `C₁ ↦ C₀`.  So the printed
"with a similar relation for `Λ₀`" is the same statement about
`lowerBlockShift` and `lowerCosineBlock`, and no second proof strategy is
needed. -/

/-- The perturbed lower block of the canonical branch is positive.

The mirror of `theorem8_1_perturbedUpperBlockShift_nonneg`: Theorem 8.1's
existence half puts the form of `A + K` on the branch `Q` at most `α`, so
`(α + δ) - Λ₀` is positive.  Part (iii) needs this separately from the estimate,
because the weak majorization of a sandwich is stated for a *positive* middle
factor. -/
theorem theorem8_1_perturbedLowerBlockShift_nonneg
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P) :
    (0 : H →L[ℂ] H) ≤
      lowerBlockShift (A + K) (canonicalLowBranch (A + K)
        (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
          (hA.add hK)) alpha) alpha delta := by
  have hconc := theorem8_1_canonicalBranch A K P hdelta hA hK hAP hPlow hPhigh
    hKP hKPperp
  refine lowerBlockShift_nonneg (A + K) _ hdelta.le (hA.add hK) fun y hy => ?_
  have h := hconc.branch_form_low y hy
  have hswap : RCLike.re ⟪(A + K) y, y⟫_ℂ = RCLike.re ⟪y, (A + K) y⟫_ℂ :=
    inner_re_symm (𝕜 := ℂ) _ _
  linarith

/-- **The Weyl step of Theorem 8.1, lower block.**

  `aₙ((α + δ) - A₀) ≤ aₙ(C₀⋆ ((α + δ) - Λ₀) C₀)`.

The exact mirror of `theorem8_1_upperSandwichApproximation`: part (i)'s
printed lower companion supplies the form domination, and
`approximationNumber_mono_of_form_le` turns the form order between two positive
operators into domination of every approximation number, in any dimension.  As
in the upper block this is the step that both (ii) and (iii) consume. -/
theorem theorem8_1_lowerSandwichApproximation
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (lowerBlockShift A P alpha delta).approximationNumber n ≤
      (ContinuousLinearMap.adjoint (lowerCosineBlock P (canonicalLowBranch (A + K)
            (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
              (hA.add hK)) alpha)) ∘L
        lowerBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha delta ∘L
        lowerCosineBlock P (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha)).approximationNumber n := by
  set Q : Submodule ℂ H := canonicalLowBranch (A + K)
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (hA.add hK)) alpha
    with hQdef
  have : Q.HasOrthogonalProjection := by rw [hQdef]; infer_instance
  have hS : (0 : H →L[ℂ] H) ≤ lowerBlockShift A P alpha delta :=
    lowerBlockShift_nonneg A P hdelta.le hA hPlow
  have hM : (0 : H →L[ℂ] H) ≤ lowerBlockShift (A + K) Q alpha delta :=
    theorem8_1_perturbedLowerBlockShift_nonneg A K P hdelta hA hK hAP hPlow
      hPhigh hKP hKPperp
  have hT := nonneg_adjoint_sandwich hM (lowerCosineBlock P Q)
  have hform : ∀ x : H, RCLike.re ⟪x, lowerBlockShift A P alpha delta x⟫_ℂ ≤
      RCLike.re ⟪x, (ContinuousLinearMap.adjoint (lowerCosineBlock P Q) ∘L
        lowerBlockShift (A + K) Q alpha delta ∘L lowerCosineBlock P Q) x⟫_ℂ := by
    intro x
    have hy : P.starProjection x ∈ P := Submodule.starProjection_apply_mem _ x
    have hpart := theorem8_1_lowerCompressionRepulsion A K P hdelta hA hK
      hAP hPlow hPhigh hKP hKPperp hy
    have hleft : RCLike.re ⟪x, lowerBlockShift A P alpha delta x⟫_ℂ =
        (alpha + delta) * ‖P.starProjection x‖ ^ 2 -
          RCLike.re ⟪P.starProjection x, A (P.starProjection x)⟫_ℂ :=
      lowerBlockShift_apply A P alpha delta x
    have hadj : ⟪x, (ContinuousLinearMap.adjoint (lowerCosineBlock P Q) ∘L
        lowerBlockShift (A + K) Q alpha delta ∘L lowerCosineBlock P Q) x⟫_ℂ =
        ⟪lowerCosineBlock P Q x,
          lowerBlockShift (A + K) Q alpha delta (lowerCosineBlock P Q x)⟫_ℂ := by
      change ⟪x, ContinuousLinearMap.adjoint (lowerCosineBlock P Q)
        (lowerBlockShift (A + K) Q alpha delta (lowerCosineBlock P Q x))⟫_ℂ = _
      rw [ContinuousLinearMap.adjoint_inner_right]
    have hright := lowerBlockShift_apply (A + K) Q alpha delta
      (lowerCosineBlock P Q x)
    rw [starProjection_lowerCosineBlock] at hright
    have hcb : lowerCosineBlock P Q x = Q.starProjection (P.starProjection x) := rfl
    rw [hleft, hadj, hright, hcb]
    exact hpart
  exact approximationNumber_mono_of_form_le hS hT hform n

/-- **Davis--Kahan 1970, Theorem 8.1(ii), lower block.**

The printed "with a similar relation for `Λ₀`" reads

  `(α + δ) - α_k ≤ ‖C₀‖₁² ((α + δ) - λ_k)`,

and this is its dimension-free approximation-number form.  Proof: the lower Weyl
step followed by the same coarse cosine-sandwich bound
`aₙ(D⋆ M D) ≤ ‖D‖² aₙ(M)` used for the upper block. -/
theorem theorem8_1_lowerApproximationRepulsion
    (A K : H →L[ℂ] H) (P : Submodule ℂ H) [P.HasOrthogonalProjection]
    {alpha delta : ℝ} (hdelta : 0 < delta)
    (hA : IsSelfAdjoint A) (hK : IsSelfAdjoint K)
    (hAP : ∀ x ∈ P, A x ∈ P)
    (hPlow : ∀ x ∈ P, RCLike.re ⟪A x, x⟫_ℂ ≤ alpha * ‖x‖ ^ 2)
    (hPhigh : ∀ x ∈ Pᗮ, (alpha + delta) * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hKP : ∀ x ∈ P, K x ∈ Pᗮ) (hKPperp : ∀ x ∈ Pᗮ, K x ∈ P)
    (n : ℕ) :
    (lowerBlockShift A P alpha delta).approximationNumber n ≤
      ‖lowerCosineBlock P (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha)‖ ^ 2 *
        (lowerBlockShift (A + K) (canonicalLowBranch (A + K)
          (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp
            (hA.add hK)) alpha) alpha delta).approximationNumber n :=
  (theorem8_1_lowerSandwichApproximation A K P hdelta hA hK hAP hPlow
    hPhigh hKP hKPperp n).trans
    (approximationNumber_adjoint_sandwich_le _ _ n)

end ComplexBranch

end Section8
end DavisKahan1970
end TauCeti
