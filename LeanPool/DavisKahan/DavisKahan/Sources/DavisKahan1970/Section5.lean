/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.OperatorIdeal.ApproximationNumbers.ScalarGeneric
import LeanPool.DavisKahan.DavisKahan.Sylvester.Unbounded.OrderedEngineDirect
import LeanPool.DavisKahan.DavisKahan.Sylvester.RealUnbounded
-- the section's two displayed inequalities, (5.1) and (5.2)
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Sylvester.OperatorNormEstimate

/-!
# Davis--Kahan 1970, Section 5: the cutoff lemma and the ordered Sylvester theorem

Source-numbered names for Section 5.  Both results are already compiled, in a form more
general than the paper's; this file supplies the paper's numbering so the facade can cite
them, and records in each docstring exactly *how* the compiled statement is more general,
so nothing is silently overstated.

Theorem 5.2 is a hard prerequisite for the Section 2 unbounded-scope claim, which names it
as one of its two halves.
-/

namespace TauCeti
namespace DavisKahan1970

/-- **Davis--Kahan 1970, Lemma 5.1.**  If a net of orthogonal projections converges
strongly to the identity, then each approximation singular value of `K ∘ P i` converges to
the corresponding one of `K`.

Stronger than the printed lemma in two ways, both deliberate: the index is an arbitrary
filtered net rather than a sequence, and the scalar field is generic rather than complex
(the strong-cutoff hypothesis is carried as the class
`HasApproximationNumberStrongCutoff`).  The paper's statement is the specialization to a
sequence over `ℂ`. -/
alias lemma5_1 :=
  DavisKahan.ExactSinTheta.approximationSingularValue_comp_strongProjection_tendsto

section Lemma51

open Filter Topology
open TauCeti.ApproximationNumber
open TauCeti.DavisKahan.ExactSinTheta

universe v w

/-- **Davis--Kahan 1970, Lemma 5.1, over `ℂ`.**  If a net of orthogonal projections on a
complex Hilbert space converges strongly to the identity, then for each index `n` the
`n`-th approximation singular value of `K ∘ P i` converges to that of `K`.

This is the printed lemma's own scalar field, with **no capability class in the
signature**.  `lemma5_1` above is generic over `RCLike 𝕜` and carries
`HasApproximationNumberStrongCutoff 𝕜`, whose single field *is* this lemma; a reviewer
comparing the printed statement with a Lean type is entitled to see the lemma proved
rather than assumed, which is what this declaration and its real sibling do.  The index is
still an arbitrary filtered net rather than a sequence, which is a strengthening. -/
theorem lemma5_1_complex
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]
    {ι : Type w} {P : ι → E →L[ℂ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℂ E))
    (n : ℕ) (K : E →L[ℂ] F) :
    Tendsto (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  DavisKahan.ExactSinTheta.approximationSingularValue_comp_strongProjection_tendsto_complex
    hPproj hP n K

/-- **Davis--Kahan 1970, Lemma 5.1, over `ℝ`.**  The real sibling of `lemma5_1_complex`,
likewise with no capability class in the signature. -/
theorem lemma5_1_real
    {E F : Type v}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {ι : Type w} {P : ι → E →L[ℝ] E} {l : Filter ι}
    (hPproj : ∀ i, IsOrthogonalProjectionMap (P i))
    (hP : StronglyTendsto P l (ContinuousLinearMap.id ℝ E))
    (n : ℕ) (K : E →L[ℝ] F) :
    Tendsto (fun i => approximationSingularValue n (K ∘L P i))
      l (𝓝 (approximationSingularValue n K)) :=
  DavisKahan.ExactSinTheta.approximationSingularValue_comp_strongProjection_tendsto_real
    hPproj hP n K

end Lemma51

/-- **Davis--Kahan 1970, Theorem 5.2.**  For self-adjoint closed operators with the
source's ordering `A ≥ c + δ > c ≥ B`, a bounded solution of the Sylvester equation
`A X = X B + R` satisfies the sharp inequality `δ · N(X) ≤ N(R)` in every Fan-dominant
unitarily invariant ideal gauge, and `X` lies in the ideal whenever `R` does.

The ordering is the paper's: `TauCeti.LinearPMap.SemiboundedBelow A (c + δ)` and `TauCeti.LinearPMap.SemiboundedAbove B c`.  The
constant `δ` is sharp.  More general than the printed theorem in the scalar-ideal axis --
the conclusion is for an arbitrary `KyFanDominantIdealFamily`, not just a fixed unitarily
invariant norm -- and the operators are unbounded closed self-adjoint rather than bounded.

This is the *ordered* branch.  The interval/exterior separation hypothesis is a different
theorem, `unbounded_sylvester_intervalExterior_uiNorm_of_spectra`; do not substitute
one for the other. -/
alias theorem5_2 :=
  DavisKahan.Sylvester.directOrderedSylvesterEngine_lowerUpper

/-- **Davis--Kahan 1970, inequality (5.1).**  With `C = AX - XB` and the spectra of the
self-adjoint operators `A` and `B` pairwise at distance at least `δ`,
`δ ‖X‖_sq ≤ ‖C‖_sq` in the square (Hilbert--Schmidt) norm.

More general than the printed inequality on three axes: the operators are closed
self-adjoint rather than Hermitian matrices, the spaces are arbitrary complex Hilbert
spaces rather than finite dimensional, and Hilbert--Schmidt membership of `X` is a
conclusion rather than a hypothesis.  A real-scalar companion is
`hilbertSchmidt_sylvester_real_le_of_pairwiseSpectrumGap`. -/
alias Inequality5_1 :=
  DavisKahan.ExactSinTheta.hilbertSchmidt_sylvester_le_of_pairwiseSpectrumGap

/-- **Davis--Kahan 1970, inequality (5.2).**  Under the hypotheses of (5.1),
`δ ‖X‖₁ ≤ ‖C‖₁ √(rank C)` in the paper's subscript-one norm, which Section 1 fixes as the
*bound* (operator) norm and not the trace norm.

Stated against an upper bound `r` for `rank C`, which is what an arbitrary-dimensional
statement can carry; `opNorm_sylvester_le_finrank_range` is the same conclusion
with the genuine rank in finite dimensions.  The source's own `2 × 2` witness that the
constant `1` cannot replace `√(rank C)` is compiled as `sharp52_constant_one_too_small`.
Whether `rank C` may be replaced by a constant is the source's open question. -/
alias Inequality5_2 :=
  DavisKahan.ExactSinTheta.opNorm_sylvester_le_of_pairwiseSpectrumGap


/-- **Davis--Kahan 1970, Theorem 5.2 over `ℝ`, at an arbitrary Fan-dominant ideal gauge.**

The source-facing name for `TauCeti.DavisKahan.Sylvester.davisKahan1970_sylvester_real`, whose
own name carries the paper's number while living in the reusable Sylvester namespace.  It takes
the whole `FormBoundedSylvesterGap`, so both half-line orientations and the interval/exterior
branch are available, with the sharp constant.  Finding F6.4 of the 2026-09-04 hostile review. -/
alias theorem5_2_kyFanDominant_real :=
  DavisKahan.Sylvester.davisKahan1970_sylvester_real

end DavisKahan1970
end TauCeti
