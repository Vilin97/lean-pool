/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.DoubleAngle.TanTwoThetaKyFanFiniteCarrier
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.TanTwoThetaBranchFreeInfinite
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.SineTheta.Norms.UnitaryInvariantNorm

/-!
# The unrestricted Section 2 `tan 2Θ` theorem at the source norm scope

Source anchor: Section 2, the `tan 2θ` statement `DK-tan2`; Section 7,
equation (7.6) and the paired-singular-vector argument that proves it.

## What the printed theorem assumes, and what it does not

The printed hypotheses are exactly

* `spectrum(A₀) ⊆ [β, α]` and `spectrum(A₁) ⊆ [α + δ, ∞)`, both conditions on
  the blocks of the **unperturbed** `A` for the trial splitting; and
* `H₀ = H₁ = 0`, i.e. `H` fully off-diagonal for that splitting.

The reducing subspace `Q` of `A + H` is **arbitrary**, and the conclusion is
the norm inequality `δ ‖tan 2Θ‖ ≤ 2 ‖H‖` alone.  Davis and Kahan say so at
the head of Section 8:

> The double-angle conclusions also allow angles close to `π/2`. … The
> explanation is that the double-angle theorems imposed no special choice of
> the reducing subspace `QH` of `A + H`.

`Θ < π/4` is Theorem 8.1's conclusion, earned from the *extra* hypothesis
that `P` and `Q` are the spectral projectors of `A` and `A + H` for the same
interval.  A theorem that assumes ordered form bounds on `A + H` restricted
to `V` and `Vᗮ`, or that concludes `IsQuarterAcute`, is a selected-branch
theorem and is not this one.

## Scope of the theorem in this module

* real **and** complex scalars, uniformly (`RCLike`);
* arbitrary Hilbert space, with a finite-dimensional trial subspace;
* every source unitarily invariant norm (`SymmetricNormingFunction`);
* the sharp constant two and the sharp gap factor `b - a`;
* **no branch hypothesis and no branch conclusion.**

The remaining scope difference from the printed statement is the
finite-dimensional trial subspace; the selected-branch endpoints
`sharp_symmetricNormingFunction` and `tanTwoTheta_selectedBranch_symmetricNorming`
remove that restriction, at the cost of selecting the branch.

## Representative freedom

`tan 2Θ` is presented as any operator whose approximation numbers are a
**rearrangement** of the branch-free double-angle tangents
`2 tⱼ / |1 - tⱼ²|`.  The rearrangement is forced and is not a weakening:
`t ↦ 2t/|1 - t²|` is increasing on `[0, 1)` and decreasing on `(1, ∞)`, so
along the antitone graph-coordinate singular values the branch-free tangents
are not antitone, while the approximation numbers of an operator always are.
A unitarily invariant norm sees only the multiset of singular values, which
is exactly the paper's own representative freedom for `tan 2Θ₀`.
-/

namespace TauCeti
namespace DavisKahan1970

open scoped InnerProductSpace
open DavisKahan.ExactSinTheta

noncomputable section

universe u v

/-- **Davis--Kahan 1970, the unrestricted Section 2 `tan 2Θ` theorem, every
source unitarily invariant norm.**

`(b - a) · N(tan 2Θ) ≤ 2 · N(H)` for a fully off-diagonal self-adjoint
perturbation across the form gap `[a, b]` of the unperturbed operator, on an
arbitrary Hilbert space over `ℝ` or `ℂ`, with a finite-dimensional trial
subspace.

**No branch is selected and none is assumed.**  There is no hypothesis
bounding the graph coordinate by one, no `IsQuarterAcute`, and no spectral
placement hypothesis on the blocks of `A + H`: the perturbed invariant
subspace is an arbitrary invariant graph over the trial subspace and may make
angles arbitrarily close to `π/2` with it. -/
theorem tanTwoTheta_branchFree_bounded_finiteSubspace_symmetricNorming_rclike
    {𝕜 : Type u} [RCLike 𝕜] {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (N : SymmetricNormingFunction)
    {A H T : E →L[𝕜] E} {U : Submodule 𝕜 E} [FiniteDimensional 𝕜 U]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_𝕜)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_𝕜 ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (tanTwoTheta : E →L[𝕜] E) (π : ℕ ≃ ℕ)
    (htan : ∀ n, approximationSingularValue (π n) tanTwoTheta =
      DavisKahan.TanTwoTheta.absDoubleAngleTangent (approximationSingularValue n T))
    (hHmem : N.Mem H) :
    N.Mem tanTwoTheta ∧
      (b - a) * N.gauge tanTwoTheta ≤ 2 * N.gauge H := by
  have hδ : (0 : ℝ) < (b - a) / 2 := by linarith
  have hscaled : ∀ k : ℕ,
      (b - a) / 2 * kyFanApproximationGauge k tanTwoTheta ≤
        kyFanApproximationGauge k H := by
    intro k
    have h := DavisKahan.TanTwoTheta.kyFan_absTanTwoTheta_le_of_finiteDimensional_invariantSubspace
      hA hH hAU hHU hHUperp hTmem hTzero hUb hUa hinv hab tanTwoTheta π htan k
    linarith
  obtain ⟨hmem, hgauge⟩ :=
    N.mul_gauge_le_of_all_mul_kyFan_le hδ hHmem hscaled
  exact ⟨hmem, by linarith⟩

/-- **Davis--Kahan 1970, the unrestricted Section 2 `tan 2Θ` theorem, every
source unitarily invariant norm, with an ARBITRARY trial subspace.**

`(b - a) · N(tan 2Θ) ≤ 2 · N(H)` for a fully off-diagonal self-adjoint
perturbation across the form gap `[a, b]` of the unperturbed operator, on an
arbitrary complex Hilbert space, with **no finite-dimensionality hypothesis on
the trial subspace or on the ambient space**.

This is `tanTwoTheta_branchFree_bounded_finiteSubspace_symmetricNorming_rclike` with `[FiniteDimensional 𝕜 U]`
removed.  `[U.HasOrthogonalProjection]` is the formal encoding of the paper's
"closed subspace", not a restriction.

**No branch is selected and none is assumed.**  There is no hypothesis bounding
the graph coordinate by one, no `IsQuarterAcute`, and no spectral placement
hypothesis on the blocks of `A + H`: the perturbed invariant subspace is an
arbitrary invariant graph over the trial subspace and may make angles
arbitrarily close to `π/2` with it.

**No uniform separation from the `π/4` pole is assumed either.**  It is derived
from the ordered gap by `DavisKahan.TanTwoTheta.penalty_le_of_paired_approximate` and
removed by the `ε → 0` passage in
`DavisKahan.TanTwoTheta.sum_absDoubleAngleTangent_le_of_invariantSubspace`. -/
theorem tanTwoTheta_branchFree_bounded_symmetricNorming_complex
    {E : Type v} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [CompleteSpace E]
    (N : SymmetricNormingFunction)
    {A H T : E →L[ℂ] E} {U : Submodule ℂ E} [U.HasOrthogonalProjection]
    {a b : ℝ}
    (hA : IsSelfAdjoint A) (hH : IsSelfAdjoint H)
    (hAU : ∀ x ∈ U, A x ∈ U)
    (hHU : ∀ x ∈ U, H x ∈ Uᗮ) (hHUperp : ∀ x ∈ Uᗮ, H x ∈ U)
    (hTmem : ∀ x, T x ∈ Uᗮ) (hTzero : ∀ x ∈ Uᗮ, T x = 0)
    (hab : a < b)
    (hUb : ∀ x ∈ U, b * ‖x‖ ^ 2 ≤ RCLike.re ⟪A x, x⟫_ℂ)
    (hUa : ∀ x ∈ Uᗮ, RCLike.re ⟪A x, x⟫_ℂ ≤ a * ‖x‖ ^ 2)
    (hinv : ∀ x ∈ U, ∃ y ∈ U, (A + H) (x + T x) = y + T y)
    (tanTwoTheta : E →L[ℂ] E) (π : ℕ ≃ ℕ)
    (htan : ∀ n, approximationSingularValue (π n) tanTwoTheta =
      DavisKahan.TanTwoTheta.absDoubleAngleTangent (approximationSingularValue n T))
    (hHmem : N.Mem H) :
    N.Mem tanTwoTheta ∧
      (b - a) * N.gauge tanTwoTheta ≤ 2 * N.gauge H := by
  have hδ : (0 : ℝ) < (b - a) / 2 := by linarith
  have hscaled : ∀ k : ℕ,
      (b - a) / 2 * kyFanApproximationGauge k tanTwoTheta ≤
        kyFanApproximationGauge k H := by
    intro k
    have h := DavisKahan.TanTwoTheta.kyFan_absTanTwoTheta_le_of_invariantSubspace
      hA hH hAU hHU hHUperp hTmem hTzero hUb hUa hinv hab tanTwoTheta π htan k
    linarith
  obtain ⟨hmem, hgauge⟩ :=
    N.mul_gauge_le_of_all_mul_kyFan_le hδ hHmem hscaled
  exact ⟨hmem, by linarith⟩

/-- The branch-free double-angle tangent scalar function
`t ↦ 2t/|1 - t²|`, meaningful on both sides of the quarter turn. -/
alias tanTwoTheta_absDoubleAngleTangent :=
  DavisKahan.TanTwoTheta.absDoubleAngleTangent

/-- **`cos 2θⱼ ≠ 0` from the spectral gap**: the first of the two moves the
printed Section 7 proof makes after equation (7.6). -/
alias tanTwoTheta_cos_ne_zero := DavisKahan.FiniteDimensional.singularValue_ne_one

/-- **Equation (7.6) in cleared, branch-free form.**  Multiplied through by
`1 - tan² θⱼ` rather than divided by it, so no branch is chosen. -/
alias tanTwoTheta_equation_7_6 :=
  DavisKahan.FiniteDimensional.paired_singularVector_gap_inequality

/-- The branch-free paired-singular-vector inequality: the printed sign
choice, giving `(b - a)|tan 2θⱼ| ≤ 2 |Re ⟪vⱼ, H uⱼ⟫|`. -/
alias tanTwoTheta_branchFree_scalar :=
  DavisKahan.FiniteDimensional.absDoubleAngleTangent_scalar

/-- The branch-free Ky Fan root over an arbitrary finite index set,
finite-dimensional form. -/
alias tanTwoTheta_branchFree_finiteDimensional_kyFan_rclike :=
  DavisKahan.FiniteDimensional.sum_absDoubleAngleTangent_le

/-- **The unrestricted `tan 2Θ` theorem, every rectangular unitarily
invariant norm**, finite-dimensional graph-coordinate form. -/
alias tanTwoTheta_branchFree_finiteDimensional_uiNorm_rclike :=
  DavisKahan.FiniteDimensional.absTanTwoTheta0_offDiagonal_le

/-- **The unrestricted `tan 2Θ` theorem, every Fan-dominant unitary-invariant
ideal, arbitrary Hilbert space** with a finite-dimensional trial subspace. -/
alias tanTwoTheta_branchFree_finiteSubspace_idealFamily_rclike :=
  DavisKahan.TanTwoTheta.absTanTwoTheta_offDiagonal_mem_and_gauge_le_of_finiteDimensional_invariantSubspace

/-! ## The arbitrary-trial-subspace layer

These are the same statements with `[FiniteDimensional 𝕜 U]` removed.  The
replacement for the singular-basis argument is the approximate-pair form of
equation (7.6) plus an `ε → 0` passage; see
`DavisKahan/DoubleAngle/TanTwoThetaApproximatePair.lean` and
`DavisKahan/Sources/DavisKahan1970/TanTwoThetaBranchFreeInfinite.lean`. -/

/-- **Equation (7.6) in cleared form for an approximate singular pair** -- the
dimension-free replacement for the matched-singular-pair computation. -/
alias tanTwoTheta_equation_7_6_approximate :=
  DavisKahan.TanTwoTheta.paired_approximate_gap_inequality

/-- **`cos 2θⱼ ≠ 0` for an approximate pair**, division-free. -/
alias tanTwoTheta_cos_ne_zero_approximate :=
  DavisKahan.TanTwoTheta.abs_one_sub_sq_pos_of_paired_approximate

/-- **The quantitative `π/4` pole separation**, derived from the ordered gap
rather than assumed. -/
alias tanTwoTheta_pole_separation :=
  DavisKahan.TanTwoTheta.penalty_le_of_paired_approximate

/-- **The branch-free Ky Fan root over an arbitrary finite index set, arbitrary
trial subspace.** -/
alias tanTwoTheta_branchFree_kyFan_complex :=
  DavisKahan.TanTwoTheta.sum_absDoubleAngleTangent_le_of_invariantSubspace

/-- **The branch-free `tan 2Θ` prefix bound for any representative, arbitrary
trial subspace.** -/
alias tanTwoTheta_branchFree_prefix_arbitrarySubspace :=
  DavisKahan.TanTwoTheta.kyFan_absTanTwoTheta_le_of_invariantSubspace

/-- **The unrestricted `tan 2Θ` theorem, every Fan-dominant unitary-invariant
ideal, arbitrary Hilbert space and arbitrary trial subspace.** -/
alias tanTwoTheta_branchFree_idealFamily_complex :=
  DavisKahan.TanTwoTheta.absTanTwoTheta_offDiagonal_mem_and_gauge_le_of_invariantSubspace

end

end DavisKahan1970
end TauCeti
