/-
Copyright (c) 2026 Kitware, Inc. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jon Crall, Claude Fable 5
-/
module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.Algebra.Module.Projective

/-! # Rank factorization

Every matrix over a field factors as `M = L * R` with inner dimension exactly
`M.rank` (the classical *rank factorization* / full-rank factorization), hence
through `Fin r` for any `r ≥ M.rank`; and conversely any product through `Fin r`
has rank at most `r`.

Mathlib has the rank API (`Matrix.rank`, `rank_mul_le`, …) but no factorization
realizing the rank as an inner dimension; this supplies the missing converse
making `M.rank ≤ r ↔ ∃ L R, M = L * R` an equivalence.

The construction: the columns of `M` span the column space
`LinearMap.range M.mulVecLin`, whose dimension is `M.rank`; choosing a basis of
the column space, `L` lists the basis vectors and `R` the coordinates of each
column of `M` in that basis.

## Main results

* `TauCeti.Matrix.exists_eq_mul_rank`: the exact rank factorization, inner
  dimension `Fin M.rank`.
* `TauCeti.Matrix.exists_eq_mul_of_rank_le`: zero-padded to `Fin r` for any
  `M.rank ≤ r`.
* `TauCeti.Matrix.rank_le_iff_exists_eq_mul`: the characterization
  `M.rank ≤ r ↔ ∃ L R, M = L * R`.

## Staging note

Staged for Tau Ceti, roadmap topic T21.  Mathlib is not the destination
(`ForTauCeti/README.md`); what follows is where this material would have gone on
the closed Mathlib track —
additions to `Mathlib/LinearAlgebra/Matrix/Rank.lean`
(rank factorization).
Formalized by Claude Fable 5 (claude-fable-5[1m]).

## `[DecidableEq n]`, and why it is gone

The three theorems below used to carry `[DecidableEq n]`.  It sat in their type and was
never used there — Mathlib's `linter.unusedDecidableInType` said exactly that, and its
advice is to drop the instance and call `classical` in the proof, which is what they now do.
Only `exists_eq_mul_rank` needs it at all, for the `Pi.single j 1` witness that puts column
`j` in the column space.

That advice was resisted for one reason.  The same three signatures were restated, with the
identical `variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n] [DecidableEq n]` line, in
`Challenge/RankFactorization/Conformance.lean`, and the two have to agree —
`Leaderboard.lean` names `TauCeti.Matrix.rank_le_iff_exists_eq_mul` in its dependency audit
and the comparator checks that challenge and solution export the same statement.  The
resolution is that a challenge statement **follows** the API rather than pinning it:
challenges validate an implementation through the comparator, they are not the target.  The
conformance statement moved in the same commit, so the two still export identically.

Three `set_option linter.unusedDecidableInType false in` lines went with the instance.  The
one that remains is on `eq_of_mul_left_cancel`, where `[Fintype p]` and `[DecidableEq p]`
really are used — by `*ᵥ` and `Pi.single` in the proof — and are quantified over `p`, not
over the `n` of the public signature.  That is a different question from the one the review
raised.

## Provenance

* Original repository: Davis--Kahan/DKPS formalization (Kitware, Inc.).
* Original module: authored directly in `ForMathlib` at Davis--Kahan commit
  `7bc63b8`; it has had no prior home.
* Extraction class: **authored in place**, for Tau Ceti — `ForMathlib` was
  retired on 2026-07-29 and `ForTauCeti` is the single staging library, whose
  destination is Tau Ceti and not Mathlib (`ForTauCeti/README.md`).
* Intended Mathlib home: additions to `Mathlib/LinearAlgebra/Matrix/Rank.
* Original authors / copyright: Jon Crall, Claude Fable 5; Copyright (c) 2026
  Kitware, Inc.; Apache 2.0.
* Spectra influence: **none** — the `ForTauCeti` import firewall admits only
  Mathlib, `TauCeti` and `ForTauCeti` (rule 2 of
  `scripts/check_dependency_layers.py`); this module imports Mathlib only.

## Provenance

*Moved, not restated.*  This file lived in the retired `ForMathlib` staging tree
before `ForMathlib` was retired entirely: its four
surviving modules moved here and the library, its root module and its directory
were deleted.  Statements, proofs and signatures are unchanged.

**FM-RETIRE was worked twice, and the two versions disagreed on the namespace.**
The `main` version (`c85510d6`) kept `namespace ForMathlib.Matrix` here, reasoning
that `Challenge/**/Conformance.lean` is immutable so its `ForMathlib.*` pins could
not be re-issued.  Reconciled on merge in favour of `TauCeti.Matrix`; the rationale
and the list of pins updated to match is recorded once, in
`ForTauCeti/Topology/Berge.lean`.

-/

@[expose] public section

/-!
### Provenance

Moved into `ForTauCeti/LinearAlgebra/Matrix/`
as part of the `ForMathlib` retirement.  The
namespace changed from `ForMathlib.Matrix` to `TauCeti.Matrix` to match the
destination package; declaration names, statements and proofs are unchanged.
-/

namespace TauCeti.Matrix

open Module (finrank)
open _root_.Matrix

variable {𝕜 m n : Type*} [Field 𝕜] [Fintype n]

/--
**Rank factorization (exact).** Every matrix factors as `M = L * R` with inner
dimension `Fin M.rank`: `L` lists a basis of the column space of `M` and `R` the
coordinates of each column of `M` in that basis.
-/
theorem exists_eq_mul_rank (M : Matrix m n 𝕜) :
    ∃ (L : Matrix m (Fin M.rank) 𝕜) (R : Matrix (Fin M.rank) n 𝕜), M = L * R := by
  -- `Pi.single` below needs `DecidableEq n`, which the statement does not.
  classical
  -- A basis of the column space, indexed by `Fin M.rank`.
  have hdim : finrank 𝕜 (LinearMap.range M.mulVecLin) = M.rank := rfl
  let b : Module.Basis (Fin M.rank) 𝕜 (LinearMap.range M.mulVecLin) :=
    Module.finBasisOfFinrankEq 𝕜 _ hdim
  -- Each column of `M` lies in the column space.
  have hcol : ∀ j : n, (fun i => M i j) ∈ LinearMap.range M.mulVecLin := by
    intro j
    refine ⟨Pi.single j 1, ?_⟩
    ext i
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  refine ⟨Matrix.of fun i k => (b k : m → 𝕜) i, Matrix.of fun k j => b.repr ⟨_, hcol j⟩ k, ?_⟩
  ext i j
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  -- Expand column `j` in the basis and evaluate the resulting identity at row `i`.
  have hrepr := congrArg Subtype.val (b.sum_repr ⟨_, hcol j⟩)
  rw [Submodule.coe_sum] at hrepr
  have := congrFun hrepr i
  simp only [Finset.sum_apply, SetLike.val_smul, Pi.smul_apply, smul_eq_mul] at this
  rw [Finset.sum_congr rfl fun k _ => mul_comm ((b k : m → 𝕜) i) (b.repr ⟨_, hcol j⟩ k)]
  exact this.symm

/--
**Rank factorization (padded).** A matrix `M` with `M.rank ≤ r` factors as
`M = L * R` with `L : Matrix m (Fin r) 𝕜` and `R : Matrix (Fin r) n 𝕜`
(the exact factorization, zero-padded to inner dimension `r`).
-/
theorem exists_eq_mul_of_rank_le (M : Matrix m n 𝕜) {r : ℕ} (h : M.rank ≤ r) :
    ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  obtain ⟨L₀, R₀, hM⟩ := exists_eq_mul_rank M
  refine ⟨Matrix.of fun i k => if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0,
    Matrix.of fun k j => if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0, ?_⟩
  ext i j
  -- Reduce the padded sum over `Fin r` to the exact sum over `Fin M.rank`.
  set f : ℕ → 𝕜 := fun k => if hk : k < M.rank then L₀ i ⟨k, hk⟩ * R₀ ⟨k, hk⟩ j else 0 with hf
  have hpad : ∀ k : Fin r,
      (if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0)
        * (if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0) = f (k : ℕ) := by
    intro k
    by_cases hk : (k : ℕ) < M.rank <;> simp [hf, hk]
  have hexact : ∀ k : Fin M.rank, L₀ i k * R₀ k j = f (k : ℕ) := by
    intro k
    simp [hf, k.isLt]
  have hsum : (∑ k : Fin r,
        (if hk : (k : ℕ) < M.rank then L₀ i ⟨k, hk⟩ else 0)
          * (if hk : (k : ℕ) < M.rank then R₀ ⟨k, hk⟩ j else 0))
      = ∑ k : Fin M.rank, L₀ i k * R₀ k j := by
    rw [Finset.sum_congr rfl fun k _ => hpad k, Fin.sum_univ_eq_sum_range f r,
      Finset.sum_congr rfl fun k _ => hexact k, Fin.sum_univ_eq_sum_range f M.rank]
    -- The padding terms vanish above `M.rank`.
    refine (Finset.sum_subset
      (fun x hx => Finset.mem_range.mpr ((Finset.mem_range.mp hx).trans_le h))
      fun k _ hk => dite_eq_right (by simpa using hk)).symm
  rw [Matrix.mul_apply]
  simp only [Matrix.of_apply]
  rw [hsum, ← Matrix.mul_apply, ← hM]

/--
**Rank-`r` factorization characterization.** A matrix has rank at most `r` if
and only if it factors through `Fin r`: `M.rank ≤ r ↔ ∃ L R, M = L * R`.
-/
theorem rank_le_iff_exists_eq_mul (M : Matrix m n 𝕜) (r : ℕ) :
    M.rank ≤ r ↔ ∃ (L : Matrix m (Fin r) 𝕜) (R : Matrix (Fin r) n 𝕜), M = L * R := by
  refine ⟨exists_eq_mul_of_rank_le M, ?_⟩
  rintro ⟨L, R, rfl⟩
  calc (L * R).rank ≤ L.rank := Matrix.rank_mul_le_left L R
    _ ≤ Fintype.card (Fin r) := L.rank_le_card_width
    _ = r := Fintype.card_fin r

/-! ### Uniqueness of a rank factorization

At the exact rank the two factors are determined up to a change of basis of the intermediate
space. The engine is `Module.projective_lifting_property`: `Fin r → 𝕜` is free, hence projective, so
a map into `range L.mulVecLin` lifts along `L`. -/

section Uniqueness

variable {r : ℕ}

/-- At the exact rank the left factor has trivial kernel: rank-nullity on `Fin r → 𝕜`. -/
theorem injective_mulVecLin_of_rank_eq {L : Matrix m (Fin r) 𝕜} (h : L.rank = r) :
    Function.Injective L.mulVecLin := by
  rw [← LinearMap.ker_eq_bot]
  have hrk := LinearMap.finrank_range_add_finrank_ker L.mulVecLin
  rw [show finrank 𝕜 (LinearMap.range L.mulVecLin) = r from h,
    Module.finrank_pi 𝕜, Fintype.card_fin] at hrk
  have : finrank 𝕜 (LinearMap.ker L.mulVecLin) = 0 := by omega
  exact Submodule.finrank_eq_zero.mp this

/-- A factorization at the exact rank forces the left factor to have that rank: it is at most
`r` because it has `r` columns, and at least `r` because it dominates `M`. -/
theorem rank_left_factor_eq {M : Matrix m n 𝕜} {L : Matrix m (Fin r) 𝕜}
    {R : Matrix (Fin r) n 𝕜} (hM : M.rank = r) (h : M = L * R) : L.rank = r := by
  refine le_antisymm (by simpa using L.rank_le_card_width) ?_
  calc r = M.rank := hM.symm
    _ = (L * R).rank := by rw [h]
    _ ≤ L.rank := Matrix.rank_mul_le_left L R

/-- At the exact rank the left factor spans the same column space as `M`. -/
theorem range_left_factor_eq {M : Matrix m n 𝕜} {L : Matrix m (Fin r) 𝕜}
    {R : Matrix (Fin r) n 𝕜} (hM : M.rank = r) (h : M = L * R) :
    LinearMap.range L.mulVecLin = LinearMap.range M.mulVecLin := by
  refine (Submodule.eq_of_le_of_finrank_eq ?_ ?_).symm
  · rw [h, Matrix.mulVecLin_mul]
    exact LinearMap.range_comp_le_range _ _
  · rw [show finrank 𝕜 (LinearMap.range M.mulVecLin) = M.rank from rfl,
      show finrank 𝕜 (LinearMap.range L.mulVecLin) = L.rank from rfl, hM,
      rank_left_factor_eq hM h]

omit [Fintype n] in
/-- **The lifting step.**  A matrix whose column space sits inside another's factors through
it. `Fin r → 𝕜` is free, hence projective, so `Module.projective_lifting_property` supplies the
factor directly. -/
theorem exists_mul_eq_of_range_le {L L' : Matrix m (Fin r) 𝕜}
    (h : LinearMap.range L'.mulVecLin ≤ LinearMap.range L.mulVecLin) :
    ∃ G : Matrix (Fin r) (Fin r) 𝕜, L * G = L' := by
  obtain ⟨φ, hφ⟩ := Module.projective_lifting_property L.mulVecLin.rangeRestrict
    (L'.mulVecLin.codRestrict (LinearMap.range L.mulVecLin) fun x => h ⟨x, rfl⟩)
    L.mulVecLin.surjective_rangeRestrict
  refine ⟨LinearMap.toMatrix' φ, ?_⟩
  have hcomp : L.mulVecLin ∘ₗ φ = L'.mulVecLin := by
    refine LinearMap.ext fun x => ?_
    have := congrArg (fun ψ : (Fin r → 𝕜) →ₗ[𝕜] LinearMap.range L.mulVecLin =>
      ((ψ x : LinearMap.range L.mulVecLin) : m → 𝕜)) hφ
    simpa using this
  have := congrArg LinearMap.toMatrix' hcomp
  rwa [← Matrix.toLin'_apply' L, ← Matrix.toLin'_apply' L', LinearMap.toMatrix'_comp,
    LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin'] at this

omit [Fintype n] in
-- `Fintype p` and `DecidableEq p` are used by `*ᵥ` and `Pi.single` in the proof but do not
-- appear in the statement, which is exactly what these two linters flag.
/-- Left cancellation against an injective factor. -/
theorem eq_of_mul_left_cancel {p : Type*} [Fintype p] [DecidableEq p]
    {L : Matrix m (Fin r) 𝕜} (hL : Function.Injective L.mulVecLin)
    {A B : Matrix (Fin r) p 𝕜} (hAB : L * A = L * B) : A = B := by
  have hmv : ∀ x, A *ᵥ x = B *ᵥ x := by
    intro x
    refine hL ?_
    have := congrArg (fun N : Matrix m p 𝕜 => N *ᵥ x) hAB
    simpa [← Matrix.mulVec_mulVec] using this
  ext i j
  have := congrFun (hmv (Pi.single j 1)) i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using this

/-- **Milestone A2 — uniqueness of a rank factorization.**

At the exact rank the two factors are determined up to the obvious `GL` action: `L' = L g`
and `R' = g⁻¹ R`. Stated as an existence over the group rather than through a quotient.

`r = M.rank` is load-bearing. Above the rank the extra columns are unconstrained and the
statement is false; the proof uses it twice, once for each factor's injectivity. -/
theorem exists_units_eq_mul_of_rank_factorization {M : Matrix m n 𝕜} (hM : M.rank = r)
    {L L' : Matrix m (Fin r) 𝕜} {R R' : Matrix (Fin r) n 𝕜}
    (h : M = L * R) (h' : M = L' * R') :
    ∃ g : (Matrix (Fin r) (Fin r) 𝕜)ˣ,
      L' = L * (g : Matrix (Fin r) (Fin r) 𝕜) ∧
        R' = ((g⁻¹ : (Matrix (Fin r) (Fin r) 𝕜)ˣ) : Matrix (Fin r) (Fin r) 𝕜) * R := by
  classical
  have hrange : LinearMap.range L'.mulVecLin = LinearMap.range L.mulVecLin := by
    rw [range_left_factor_eq hM h', range_left_factor_eq hM h]
  obtain ⟨G, hG⟩ := exists_mul_eq_of_range_le (L := L) (L' := L') hrange.le
  obtain ⟨G', hG'⟩ := exists_mul_eq_of_range_le (L := L') (L' := L) hrange.ge
  have hLinj := injective_mulVecLin_of_rank_eq (rank_left_factor_eq hM h)
  have hL'inj := injective_mulVecLin_of_rank_eq (rank_left_factor_eq hM h')
  have hGG' : G * G' = 1 := by
    refine eq_of_mul_left_cancel hLinj ?_
    rw [← Matrix.mul_assoc, hG, hG', Matrix.mul_one]
  have hG'G : G' * G = 1 := by
    refine eq_of_mul_left_cancel hL'inj ?_
    rw [← Matrix.mul_assoc, hG', hG, Matrix.mul_one]
  refine ⟨⟨G, G', hGG', hG'G⟩, hG.symm, ?_⟩
  -- `L R = M = L' R' = L G R'`, so `R = G R'` by injectivity of `L`.
  have hR : R = G * R' := by
    refine eq_of_mul_left_cancel hLinj ?_
    rw [← Matrix.mul_assoc, hG, ← h, h']
  rw [hR, ← Matrix.mul_assoc]
  simp [hG'G]

end Uniqueness

end TauCeti.Matrix
