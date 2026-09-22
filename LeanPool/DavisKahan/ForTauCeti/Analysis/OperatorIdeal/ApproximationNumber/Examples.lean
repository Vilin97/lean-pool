/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 5
-/
module

public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.MinMax
public import LeanPool.DavisKahan.ForTauCeti.Analysis.OperatorIdeal.ApproximationNumber.FiniteDimensional

/-!
# Approximation numbers of concrete operators

Staged for Tau Ceti, roadmap topic T09.  These are the **acceptance examples** the
roadmap makes a condition of acceptance: *the development is accepted only when its
abstractions compute correctly on concrete operators*, and *these examples are
theorem-level tests of the API, not merely `#eval` checks*
(`TauCetiRoadmap/OperatorTheory/OperatorIdeals/README.md`, Part A).

Each is proved from the public API alone — the defining infimum is never unfolded:

* `approximationNumber_id` — on an `r`-dimensional space the identity has
  `aₙ = 1` for `n < r` and `aₙ = 0` for `r ≤ n`.  Both halves come from
  characteristic lemmas: the lower bound from `le_approximationNumber_of_finrank_lt`
  on the whole space, the upper from `approximationNumber_le_norm` and `norm_id`,
  and the vanishing from `approximationNumber_eq_zero_of_rank_le`.

* `approximationNumber_starProjection` and
  `approximationNumber_starProjection_of_finrank_le` — an orthogonal projection onto
  a subspace of dimension `r` has the same profile, for the same two reasons, with
  the subspace itself as the witness of the lower bound.
* `approximationNumber_eq_zero_of_finrank_range_le` — the rank cutoff on a
  concrete map, stated in `finrank` rather than `Cardinal` form because that is
  what a consumer with an explicit map has.

The zero operator needs nothing: `approximationNumber_zero` already says every
`aₙ(0) = 0`.

**The diagonal example is proved, but in a sibling file.**
`ContinuousLinearMap.approximationNumber_diagOp` in `ApproximationNumber/DiagonalExample.lean`
gives `aᵢ (diagOp b x) = x i` for antitone nonnegative `x`.  It is not here because
this file is a `module` and `TauCeti.diagOp` is not: a `module` may only import
other `module`s, and nothing in `diagOp`'s neighbourhood has been converted.  That
file says to fold itself back in once `UnitarilyInvariantSeminorm.lean` becomes a
`module`.  Note the reason above is *not* the one this note used to give — the
singular values of a diagonal map (`TauCeti.singularValues_diagOp`) do exist; the
module boundary is the whole of what is left.

**What is not here yet**, from the same acceptance list: the *rectangular* diagonal
map with **unequal source and target dimensions**, the min–max example selecting
the span of the largest singular directions, and the compact diagonal operator with
`aₙ → 0`.  The first needs the singular values of a rectangular diagonal map, which
`singularValues_diagOp` does not give — it is square; the second needs the
orthogonal-tail equality; the third needs the finite-rank approximation
characterisation of compactness.

## Sources

*Follows nothing in particular*: these are tests of this library's own API against
the concrete operators the roadmap names.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForTauCeti`.
* Extraction class: **authored in place**, for Tau Ceti.
* Original authors / copyright: Jon Crall, Claude Opus 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — imports only Mathlib and sibling `ForTauCeti`
  modules.
-/

public section

namespace ContinuousLinearMap

open Module (finrank)
open scoped InnerProductSpace

variable {𝕜 : Type*} [RCLike 𝕜]
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]

omit [FiniteDimensional 𝕜 F] in
/-- **Acceptance example: the rank cutoff on a concrete map.**  The `Cardinal`-free
form of `ContinuousLinearMap.approximationNumber_eq_zero_of_rank_le`, which is what
a consumer holding an explicit finite-dimensional map has. -/
theorem approximationNumber_eq_zero_of_finrank_range_le (T : E →L[𝕜] F) {n : ℕ}
    (hT : finrank 𝕜 (LinearMap.range (T : E →ₗ[𝕜] F)) ≤ n) :
    T.approximationNumber n = 0 :=
  (T.approximationNumber_eq_zero_iff_finrank_range_le n).mpr hT

/-- **Acceptance example: the identity.**  On a space of dimension `r`, the first
`r` approximation numbers of the identity are `1` and the rest are `0`. -/
theorem approximationNumber_id [Nontrivial E] (n : ℕ) (hn : n < finrank 𝕜 E) :
    (ContinuousLinearMap.id 𝕜 E).approximationNumber n = 1 := by
  refine le_antisymm ?_ ?_
  · simpa [norm_id] using (ContinuousLinearMap.id 𝕜 E).approximationNumber_le_norm n
  · refine le_approximationNumber_of_finrank_lt _ n (⊤ : Submodule 𝕜 E) ?_ ?_
    · simpa using hn
    · intro x hx
      simpa using hx.ge

/-- **Acceptance example: the identity, past the dimension.**  Once `n` reaches the
dimension of the space there is nothing left to approximate. -/
theorem approximationNumber_id_of_finrank_le {n : ℕ} (hn : finrank 𝕜 E ≤ n) :
    (ContinuousLinearMap.id 𝕜 E).approximationNumber n = 0 := by
  refine approximationNumber_eq_zero_of_finrank_range_le _ ?_
  -- the range of the identity is the whole space
  have hrange : LinearMap.range (ContinuousLinearMap.id 𝕜 E : E →ₗ[𝕜] E) = ⊤ := by
    simp
  rw [hrange]
  simpa using hn

/-- **Acceptance example: an orthogonal projection.**  A projection onto a
subspace of dimension `r` has `aₙ = 1` for every `n < r`.

Same two arguments as the identity, with the subspace itself as the witness of the
lower bound: on `V` the projection is the identity, so it does not shrink any unit
vector there. -/
theorem approximationNumber_starProjection (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] (n : ℕ) (hn : n < finrank 𝕜 V) :
    V.starProjection.approximationNumber n = 1 := by
  refine le_antisymm ?_ ?_
  · refine le_trans (V.starProjection.approximationNumber_le_norm n) ?_
    exact V.starProjection_norm_le
  · refine le_approximationNumber_of_finrank_lt _ n V hn ?_
    intro x hx
    have hxV : V.starProjection (x : E) = (x : E) :=
      V.starProjection_eq_self_iff.mpr x.2
    rw [hxV, hx]

/-- **Acceptance example: an orthogonal projection, past its rank.**  Beyond the
dimension of the subspace there is nothing left to approximate. -/
theorem approximationNumber_starProjection_of_finrank_le (V : Submodule 𝕜 E)
    [V.HasOrthogonalProjection] {n : ℕ}
    (hn : finrank 𝕜 V ≤ n) :
    V.starProjection.approximationNumber n = 0 := by
  refine approximationNumber_eq_zero_of_finrank_range_le _ ?_
  have hrange : LinearMap.range (V.starProjection : E →ₗ[𝕜] E) = V :=
    V.range_starProjection
  rw [hrange]
  exact hn

end ContinuousLinearMap
