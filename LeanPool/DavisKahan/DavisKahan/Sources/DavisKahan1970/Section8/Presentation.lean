/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem81AngleForms
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.TanTheta.ContinuationWitnessAPriori
import LeanPool.DavisKahan.DavisKahan.InfiniteDimensional.SinTheta.Continuation.WitnessGraph
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem82
import LeanPool.DavisKahan.DavisKahan.Sources.DavisKahan1970.Section8.Theorem82Real

/-! # Presentation -/

open TauCeti.DavisKahan.Sylvester

/-!
# Davis--Kahan 1970 Section 8: the production source surface

The final, dependency-safe facade for Section 8.  Every printed claim of the
section is reachable from here under a source-numbered name in

    `TauCeti.DavisKahan1970.Section8`.

## Why this module

Section 8's analytic content -- the canonical gap circle, the connectedness
bootstrap of Theorem 8.2, the Krein completion, the sandwich majorization --
lives downstream of Theorem 8.1 and the compression algebra, so those modules
cannot name it without creating an import cycle.  This module is the downstream
leaf where all of it is reachable at once.  The names that belong upstream are
declared upstream: Theorem 8.1's three paper-facing names in
`Section8/Theorem81.lean`, and the two algebraic cores of 8.1(i) in
`Section8/CompressionRepulsion.lean`.

Most of what this file used to hold was a list of aliases forwarding
`TauCeti.DavisKahan.Section8.X` to `X` in this namespace.  With the
Section 8 modules out of the retired `DavisKahan/Frontier/` those forwards became
self-aliases and are gone; the two entries below are genuine renames, and what
remains is the claim-by-claim map itself.

## The printed section, claim by claim

**Theorem 8.1, the characterization and the branch.**

* `theorem8_1` -- existence of the canonical branch `Q`, from the printed
  hypotheses alone: `A` self-adjoint, `P` reduces `A`, the `P` block below `α`,
  the `Pᗮ` block above `α + δ`, and `H` self-adjoint and fully off-diagonal.
  Delivers full spectral repulsion, both sharp form bounds, both spectral
  orientations, and the *strict* quarter-angle bound.
* `theorem8_1_characterization` -- the printed `iff` between the closed
  condition `Θ ≤ π/4` and `Λ₀ ≤ α`, `Λ₁ ≥ α + δ`.
* `theorem8_1_uniqueness` -- "there always exists a reducing projector
  `Q` with these properties" is sharpened: it is unique.

**Theorem 8.1(i).**  `theorem8_1_upperCompressionRepulsion` and
`theorem8_1_lowerCompressionRepulsion`, the printed
`A₁ - α ≤ C₁(Λ₁ - α)C₁` on the `Pᗮ` block and its mirror
`(α + δ) - A₀ ≤ C₀((α + δ) - Λ₀)C₀` on the `P` block.

**Theorem 8.1(ii).**  `theorem8_1_upperApproximationRepulsion` and
`theorem8_1_lowerApproximationRepulsion` in the dimension-free
approximation-number form, and
`theorem8_1_upperApproximationRepulsion_angle` /
`theorem8_1_lowerApproximationRepulsion_angle` with the printed factor
written as a principal cosine.  The printed "and natural infinite-dimensional
extensions" is delivered: the Weyl step used here is dimension-free, so the
approximation-number forms carry no finite-dimensionality hypothesis at all.

**Theorem 8.1(iii).**  `theorem8_1_upperSymmetricGaugeRepulsion_angle`
and `theorem8_1_lowerSymmetricGaugeRepulsion_angle`, quantified over
**every** symmetric gauge, with the printed right-hand side
`(λ_i - α) cos²θ_i`.  The underlying weak majorizations
(`theorem8_1_upperWeightedWeakMajorization` and its lower companion) are
stronger than any single gauge inequality and are exported too.  The paper's
increasing index order is available as the `..._rev_source` wrappers.

**Theorem 8.2.**  `theorem8_2_complex` is the whole printed theorem: both
`sin 2Θ` estimates and the strict quarter angle, under either printed smallness
alternative and the Section 1 standing convention (1.5).  The two alternatives
are separately available, and so is the strongest dimension-free form:

* `theorem8_2_branch_directed_complex` -- `directedGap P Q < √2/2` from the
  explicit printed hypotheses **alone**, with no dimension convention.  This is
  *not* superseded by `theorem8_2_complex`; see `Section8SourceTheorem82.lean`
  for why the symmetric reading needs a standing convention and why (1.5) at
  either reading does not by itself supply one.
* `theorem8_2_branch_maximalAngle_lt_of_crossedDefects` -- the printed
  `Θ < π/4` in **any** dimension, under Section 3's other standing assumption
  (3.5) in place of any dimension count.

## The source dictionary

Everything relating the ambient operators to the printed eigenvalues and angles
is compiled, not prose; see `Section8SourceDictionary.lean`.  Its three
identifications are re-exported here under source-facing names.
-/

namespace TauCeti
namespace DavisKahan1970
namespace Section8

/-! ### Theorem 8.1(i), both blocks -/

/-! ### Theorem 8.2

`theorem8_2_branch_directed_complex` is the strongest statement obtainable from
the explicit printed hypotheses; the `maximalAngle` forms add the Section 1
standing convention (1.5) and deliver the printed `Θ < π/4`.  The distinction is
deliberate and must not be collapsed. -/

/-! `theorem8_2_perturbationHalfGap_complex` and `theorem8_2_residualHalfGap_complex`
need no alias: they are declared in this namespace by
`Sources/DavisKahan1970/Section8/Theorem82Branch.lean`. -/

/-! ### Theorem 8.2 over a real Hilbert space

Standing assumption 1 of the source admits a real or complex Hilbert space.
Theorem 8.2 supplies both subspaces as data, so its real form is an exact
complexification transport and adds no hypothesis; see
`Sources/DavisKahan1970/Section8/Theorem82Real.lean`.  `theorem8_2_real`
is the whole printed theorem over `R`, and the two inherited `sin 2Theta`
estimates are available over `R` at the operator norm, the perturbation one also
at every source unitarily invariant norm -- exactly the scope available over
`C`. -/

/-- **Theorem 8.2's printed disjunction, dimension-free.**  Either smallness
alternative gives `directedGap P Q < √2/2`.  This is the strongest conclusion
available from the explicit printed hypotheses alone, and it is deliberately
distinct from the `maximalAngle` forms, which add the Section 1 standing
convention (1.5) to deliver the printed `Θ < π/4`. -/
alias theorem8_2_branch_directed_complex :=
  theorem8_2_branch

/-- **Krein's self-adjoint completion with the exact restriction norm**, the one
external ingredient the printed residual alternative names.  The statement is
generic Hilbert-space operator theory and is proved in
`ForTauCeti/Analysis/InnerProductSpace/Polar/SelfAdjointCompletion.lean`; this
alias is the source-facing name for it. -/
alias theorem8_2_krein_completion :=
  TauCeti.exists_selfAdjoint_completion_eq_norm_restriction

/-! ### Section 9's continuation-layer entry points

Both are conditional: they take the branch selection as caller-supplied data.
Section 9 uses them after the canonical spectral branch has been identified. -/

/-- The continuation-selected endpoint has a unique contractive graph
coordinate: the graph-theoretic form of selecting the side below the
quarter-turn pole. -/
alias theorem8_selectedEndpoint_existsUnique_contractiveAngularOperator :=
  TauCeti.DavisKahanExt.SpectralContinuationWitness.existsUnique_selectedEndpointAngularOperator

/-- The selected branch satisfies the witness-level a priori tangent bound once
off-diagonality and the ordered form gap are supplied. -/
alias theorem8_selectedBranch_tan_maximalAngle_le_div :=
  TauCeti.DavisKahanExt.SpectralContinuationWitness.tan_maximalAngle_selectedSpectralSubspaces_le_div


end Section8
end DavisKahan1970
end TauCeti
