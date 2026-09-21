/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Opus 4.8

Staged for Tau Ceti, roadmap topic T19.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
addition to `Mathlib/Analysis/Matrix/Spectrum.lean`.

Formalized by Claude Opus 4.8 (claude-opus-4-8[1m]); golfed (drop unused
`set … with`, `intro;exact` → term mode) per the `mathlib-quality` rules.
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.Matrix.PosDef

/-! # Sorted eigenvalues of a Hermitian matrix

Mathlib indexes the eigenvalues of a Hermitian matrix twice: `eigenvalues₀`, sorted
decreasingly and indexed by `Fin (Fintype.card n)`, and `eigenvalues`, reusing the matrix
index `n`. The second is *defined* from the first along an index equivalence, but the
basic theory is currently stated only for `eigenvalues`: upstream `eigenvalues₀` carries
just `eigenvalues₀_antitone` and the characteristic-polynomial identities.

This file transports the two facts that the sorted indexing needs — the rank count and,
for a positive semidefinite matrix, nonnegativity — and deduces the vanishing tail of a
low-rank positive semidefinite matrix.

## Main results

* `TauCeti.Matrix.IsHermitian.rank_eq_card_non_zero_eigenvalues₀`: the rank counts the
  nonzero *sorted* eigenvalues. Positive semidefiniteness is not needed.
* `TauCeti.Matrix.PosSemidef.eigenvalues₀_nonneg`: sorted eigenvalues of a positive
  semidefinite matrix are nonnegative.
* `TauCeti.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_rank_le`: for `A.rank ≤ d` the sorted
  eigenvalues vanish at every index `≥ d`.

Positive semidefiniteness is essential for the last statement and not merely convenient: a
rank-one Hermitian matrix whose nonzero eigenvalue is negative sorts that eigenvalue
*last*, so its tail is not zero. It is inessential for the rank count, which is why the two
are separated here.

## Implementation notes

The counting argument is elementary: by antitonicity and nonnegativity, a nonzero sorted
eigenvalue at an index `≥ d` forces more than `d` nonzero sorted eigenvalues, whereas their
number is the rank.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: `ForMathlib/Analysis/Matrix/Spectrum.lean`
  at Davis--Kahan commit `fc38eb4`.
* Original declaration: `ForMathlib.Matrix.PosSemidef.eigenvalues₀_eq_zero_of_le`,
  renamed here to `eigenvalues₀_eq_zero_of_rank_le` and split so that the two supporting
  facts it proved inline are stated separately (backlog §9.2).
* Original authorship: formalized by Claude Opus 4.8 (`claude-opus-4-8[1m]`);
  staged for Mathlib (no separate copyright line in the source header), released
  under Apache 2.0.
* Extraction class: **copied**, converted to the Tau Ceti module system.
* Spectra influence: **none** (imports only Mathlib).
-/

public section

namespace TauCeti.Matrix

open scoped BigOperators ComplexOrder
open _root_.Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n] {A : Matrix n n 𝕜}

/-- `eigenvalues` is *defined* as `eigenvalues₀` reindexed along
`Fintype.equivOfCardEq (Fintype.card_fin _)`; this is that definition, read forwards.

Kept private: the equivalence is an implementation detail of Mathlib's `eigenvalues`, and
every result below is stated without it. -/
private theorem eigenvalues₀_eq_eigenvalues (hA : A.IsHermitian)
    (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k
      = hA.eigenvalues (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)) k) := by
  rw [Matrix.IsHermitian.eigenvalues, Equiv.symm_apply_apply]

/-- The rank of a Hermitian matrix is the number of its nonzero **sorted** eigenvalues.

This is `Matrix.IsHermitian.rank_eq_card_non_zero_eigs` for `eigenvalues₀`. -/
theorem IsHermitian.rank_eq_card_non_zero_eigenvalues₀ (hA : A.IsHermitian) :
    A.rank = Fintype.card {i // hA.eigenvalues₀ i ≠ 0} := by
  rw [hA.rank_eq_card_non_zero_eigs]
  exact (Fintype.card_congr (Equiv.subtypeEquiv
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)))
    fun k => by rw [eigenvalues₀_eq_eigenvalues hA k])).symm

/-- The sorted eigenvalues of a positive semidefinite matrix are nonnegative.

This is `Matrix.PosSemidef.eigenvalues_nonneg` for `eigenvalues₀`. -/
theorem PosSemidef.eigenvalues₀_nonneg (hA : A.PosSemidef) (i : Fin (Fintype.card n)) :
    0 ≤ hA.isHermitian.eigenvalues₀ i := by
  rw [eigenvalues₀_eq_eigenvalues]
  exact hA.eigenvalues_nonneg _

/--
**Vanishing tail of the sorted eigenvalues.** If `A` is positive semidefinite with
`A.rank ≤ d`, then its sorted (decreasing) eigenvalues vanish at every index `≥ d`.
-/
theorem PosSemidef.eigenvalues₀_eq_zero_of_rank_le (hA : A.PosSemidef) {d : ℕ}
    (hrank : A.rank ≤ d) {i : Fin (Fintype.card n)} (hi : d ≤ (i : ℕ)) :
    hA.isHermitian.eigenvalues₀ i = 0 := by
  by_contra hne
  -- By antitonicity, every index `≤ i` also carries a strictly positive eigenvalue.
  have hpos : ∀ k ≤ i, 0 < hA.isHermitian.eigenvalues₀ k := fun k hk =>
    ((PosSemidef.eigenvalues₀_nonneg hA i).lt_of_ne' hne).trans_le
      (hA.isHermitian.eigenvalues₀_antitone hk)
  -- So the `i + 1` leading indices all sit in the nonzero-eigenvalue finset, whose
  -- cardinality is the rank.
  have hcard : (i : ℕ) + 1 ≤ A.rank := by
    rw [IsHermitian.rank_eq_card_non_zero_eigenvalues₀ hA.isHermitian, Fintype.card_subtype,
      ← Fin.card_Iic]
    exact Finset.card_le_card fun k hk =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hpos k (Finset.mem_Iic.mp hk)).ne'⟩
  omega

end TauCeti.Matrix
