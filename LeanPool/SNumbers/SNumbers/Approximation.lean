/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
import LeanPool.SNumbers.SNumbers.Helpers
import Mathlib.Analysis.Normed.Module.RieszLemma
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Approximation numbers

The approximation numbers are the *largest* example of an s-number sequence.
They are defined as

`a_n S = inf { ‖S - L‖ : L : X →L[𝕜] Y, rank L ≤ n }`.

In this file we prove that the approximation numbers satisfy all five
Pietsch axioms (S1)–(S5). In fact we prove the stronger normalisation
(S5') — `a_n (id_X) = 1` for every Banach space `X` with `dim X > n` —
via Riesz's lemma; (S5) on `ℓ₂^{n+1}` is the corresponding specialisation.
The argument requires `[CompleteSpace 𝕜]` (so that finite-dimensional
subspaces are closed) but is otherwise elementary.

We also prove here that the approximation numbers are the **largest**
s-number sequence (`sn_le_approximationNumber` : `sₙ(S) ≤ aₙ(S)` for every
s-number sequence `s`).

## Main definitions

* `SNumbers.approximationNumber S n` — the `n`-th approximation number of `S`.

## Main results

* `SNumbers.approximationNumber_zero_eq_norm` : `a_0 S = ‖S‖`              (S1a)
* `SNumbers.approximationNumber_antitone` : `a_{n+1} S ≤ a_n S`            (S1b)
* `SNumbers.approximationNumber_nonneg` : `0 ≤ a_n S`                      (S1c)
* `SNumbers.approximationNumber_add_le` : `a_n (S + T) ≤ a_n S + ‖T‖`      (S2)
* `SNumbers.approximationNumber_comp_comp_le` :
    `a_n (B ∘ S ∘ A) ≤ ‖B‖ * a_n S * ‖A‖`                                   (S3)
* `SNumbers.approximationNumber_eq_zero_of_rank_le` :
    `rank S ≤ n ⇒ a_n S = 0`                                                (S4)
* `SNumbers.approximationNumber_strict` :
    `dim X > n ⇒ a_n (id_X) = 1`                                            (S5')
* `SNumbers.approximationNumber_id_euclidean` :
    `a_n (id_{ℓ₂^{n+1}}) = 1`                                               (S5)
* `SNumbers.isStrictSNumberSequence_approximationNumber` :
    the approximation numbers form a *strict* s-number sequence.
* `SNumbers.sn_le_approximationNumber` : `s_n S ≤ a_n S` for every s-number
    sequence `s` — the approximation numbers are the largest.
-/

universe u

open scoped Cardinal
open ContinuousLinearMap

namespace SNumbers

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜]
variable {W X Y Z : Type u}
variable [NormedAddCommGroup W] [NormedSpace 𝕜 W]
variable [NormedAddCommGroup X] [NormedSpace 𝕜 X]
variable [NormedAddCommGroup Y] [NormedSpace 𝕜 Y]
variable [NormedAddCommGroup Z] [NormedSpace 𝕜 Z]

/-- The set of approximation residuals `‖S - L‖` over operators `L` of rank
at most `n`. -/
def approximationSet (S : X →L[𝕜] Y) (n : ℕ) : Set ℝ :=
  {r | ∃ L : X →L[𝕜] Y, L.rank ≤ (n : Cardinal) ∧ r = ‖S - L‖}

/-- The `n`-th **approximation number** of a continuous linear map: the
infimum of `‖S - L‖` over operators `L` of rank at most `n`. -/
noncomputable def approximationNumber (S : X →L[𝕜] Y) (n : ℕ) : ℝ :=
  sInf (approximationSet S n)

/-! ### Basic properties of `approximationSet` -/

/-- The approximation set is non-empty: take `L = 0`, which has rank `0`. -/
lemma approximationSet_nonempty (S : X →L[𝕜] Y) (n : ℕ) :
    (approximationSet S n).Nonempty :=
  ⟨‖S‖, 0, by simp, by simp⟩

/-- The approximation set is bounded below by `0`. -/
lemma bddBelow_approximationSet (S : X →L[𝕜] Y) (n : ℕ) :
    BddBelow (approximationSet S n) :=
  ⟨0, by rintro r ⟨L, _, rfl⟩; exact norm_nonneg _⟩

/-- Convenience: every operator `L` of rank ≤ n provides an upper bound for
the approximation number. -/
lemma approximationNumber_le_norm_sub {S : X →L[𝕜] Y} {n : ℕ}
    {L : X →L[𝕜] Y} (hL : L.rank ≤ (n : Cardinal)) :
    approximationNumber S n ≤ ‖S - L‖ :=
  csInf_le (bddBelow_approximationSet S n) ⟨L, hL, rfl⟩

/-! ### (S1c) Non-negativity -/

lemma approximationNumber_nonneg (S : X →L[𝕜] Y) (n : ℕ) :
    0 ≤ approximationNumber S n :=
  le_csInf (approximationSet_nonempty S n) <| by
    rintro r ⟨L, _, rfl⟩; exact norm_nonneg _

/-! ### (S1b) Monotonicity in `n` -/

/-- If `n ≤ m`, then `a_m S ≤ a_n S`. -/
lemma approximationNumber_antitone' {S : X →L[𝕜] Y} {n m : ℕ} (h : n ≤ m) :
    approximationNumber S m ≤ approximationNumber S n := by
  refine csInf_le_csInf (bddBelow_approximationSet S m) (approximationSet_nonempty S n) ?_
  rintro r ⟨L, hL, rfl⟩
  exact ⟨L, hL.trans (by exact_mod_cast h), rfl⟩

lemma approximationNumber_antitone (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S (n + 1) ≤ approximationNumber S n :=
  approximationNumber_antitone' (Nat.le_succ n)

/-! ### (S1a) Value at `n = 0` -/

/-- The approximation set at `n = 0` is the singleton `{‖S‖}`. -/
lemma approximationSet_zero (S : X →L[𝕜] Y) :
    approximationSet S 0 = {‖S‖} := by
  ext r; constructor
  · rintro ⟨L, hL, rfl⟩
    have : L = 0 := ContinuousLinearMap.eq_zero_of_rank_le_zero (by exact_mod_cast hL)
    simp [this]
  · rintro rfl
    exact ⟨0, by simp, by simp⟩

/-- (S1a) `a_0 S = ‖S‖`. -/
@[simp] lemma approximationNumber_zero_eq_norm (S : X →L[𝕜] Y) :
    approximationNumber S 0 = ‖S‖ := by
  simp [approximationNumber, approximationSet_zero]

/-- Upper bound by the operator norm: `a_n S ≤ ‖S‖`. -/
lemma approximationNumber_le_norm (S : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber S n ≤ ‖S‖ :=
  (antitone_nat_of_succ_le (approximationNumber_antitone S) (Nat.zero_le n)).trans_eq
    (approximationNumber_zero_eq_norm S)

/-! ### (S4) Vanishing on operators of rank at most `n` -/

/-- (S4) If `rank S ≤ n`, then `a_n S = 0`. -/
lemma approximationNumber_eq_zero_of_rank_le {S : X →L[𝕜] Y} {n : ℕ}
    (hS : S.rank ≤ (n : Cardinal)) :
    approximationNumber S n = 0 := by
  refine le_antisymm ?_ (approximationNumber_nonneg S n)
  -- `0 = ‖S - S‖ ∈ approximationSet S n`, hence the infimum is `≤ 0`.
  have h0 : (0 : ℝ) ∈ approximationSet S n := ⟨S, hS, by simp⟩
  exact csInf_le (bddBelow_approximationSet S n) h0

/-! ### (S2) Subadditivity -/

/-- (S2) `a_n (S + T) ≤ a_n S + ‖T‖`. -/
lemma approximationNumber_add_le (S T : X →L[𝕜] Y) (n : ℕ) :
    approximationNumber (S + T) n ≤ approximationNumber S n + ‖T‖ := by
  -- For each `L` with rank ≤ n we have `‖(S+T) - L‖ ≤ ‖S - L‖ + ‖T‖`, and
  -- the LHS is in the approximation set of `S+T`. Hence
  -- `a_n(S+T) ≤ ‖S - L‖ + ‖T‖`. Taking the infimum over `L` and using
  -- `csInf_le_iff`/`le_sub_iff_add_le` gives the bound.
  rw [← sub_le_iff_le_add]
  refine le_csInf (approximationSet_nonempty S n) ?_
  rintro r ⟨L, hL, rfl⟩
  have h1 : approximationNumber (S + T) n ≤ ‖(S + T) - L‖ :=
    approximationNumber_le_norm_sub hL
  have h2 : ‖(S + T) - L‖ ≤ ‖S - L‖ + ‖T‖ := by
    have eq : (S + T) - L = (S - L) + T := by abel
    rw [eq]; exact norm_add_le _ _
  linarith

/-! ### (S3) Ideal property -/

/--
**(S3) Ideal property** — `a_n (B ∘ S ∘ A) ≤ ‖B‖ * a_n S * ‖A‖`.

Proof outline (cf. Pietsch, *Eigenvalues and s-numbers*, Section 2.3):

1. For every `L : X →L[𝕜] Y` with `L.rank ≤ n`, the operator `B ∘ L ∘ A`
   has rank `≤ n` (lemma `ContinuousLinearMap.rank_comp_comp_le`).
2. By submultiplicativity of the operator norm,
   `‖B(S - L)A‖ ≤ ‖B‖ * ‖S - L‖ * ‖A‖`.
3. Therefore `a_n(BSA) ≤ ‖B‖ * ‖S - L‖ * ‖A‖` for every such `L`.
4. Taking the infimum over `L` and pulling out the non-negative factor
   `‖B‖ * ‖A‖` via `Real.sInf_smul_of_nonneg` yields the bound. -/
lemma approximationNumber_comp_comp_le
    (A : W →L[𝕜] X) (S : X →L[𝕜] Y) (B : Y →L[𝕜] Z) (n : ℕ) :
    approximationNumber (B.comp (S.comp A)) n ≤
      ‖B‖ * approximationNumber S n * ‖A‖ := by
  -- Step 1: for every approximant `L` of `S` with rank ≤ n, the operator
  -- `B ∘ L ∘ A` is itself an approximant of `B ∘ S ∘ A` of rank ≤ n. Bounding
  -- its residual by submultiplicativity gives the key inequality
  -- `a_n (B S A) ≤ ‖B‖ * ‖A‖ * ‖S - L‖` for every such `L`.
  have hkey : ∀ L : X →L[𝕜] Y, L.rank ≤ (n : Cardinal) →
      approximationNumber (B.comp (S.comp A)) n ≤ ‖B‖ * ‖A‖ * ‖S - L‖ := by
    intro L hL
    -- (a) `B ∘ L ∘ A` has rank ≤ rank L ≤ n, so it is an admissible approximant.
    have h_rank_le : (B.comp (L.comp A)).rank ≤ (n : Cardinal) :=
      (ContinuousLinearMap.rank_comp_comp_le A L B).trans hL
    -- (b) The residual of `B ∘ S ∘ A` against `B ∘ L ∘ A` factors as
    --     `B ∘ (S - L) ∘ A`.
    have h_eq : B.comp (S.comp A) - B.comp (L.comp A)
                  = B.comp ((S - L).comp A) := by simp
    -- (c) Two applications of operator-norm submultiplicativity:
    --     first peel off `B`, then peel off `A`.
    have h_norm_BSA : ‖B.comp ((S - L).comp A)‖ ≤ ‖B‖ * ‖(S - L).comp A‖ :=
      opNorm_comp_le _ _
    have h_norm_SA : ‖(S - L).comp A‖ ≤ ‖S - L‖ * ‖A‖ := opNorm_comp_le _ _
    have h_norm_BS : ‖B.comp ((S - L).comp A)‖ ≤ ‖B‖ * (‖S - L‖ * ‖A‖) :=
      h_norm_BSA.trans (mul_le_mul_of_nonneg_left h_norm_SA (norm_nonneg _))
    -- (d) Chain everything: `a_n (B S A) ≤ residual ≤ ‖B‖ * ‖A‖ * ‖S - L‖`.
    have h_residual : approximationNumber (B.comp (S.comp A)) n
                        ≤ ‖B.comp (S.comp A) - B.comp (L.comp A)‖ :=
      approximationNumber_le_norm_sub h_rank_le
    have h_residual' : approximationNumber (B.comp (S.comp A)) n
                        ≤ ‖B.comp ((S - L).comp A)‖ := by
      rw [h_eq] at h_residual; exact h_residual
    have h_chain : approximationNumber (B.comp (S.comp A)) n
                    ≤ ‖B‖ * (‖S - L‖ * ‖A‖) := h_residual'.trans h_norm_BS
    -- Reorder the right-hand side by `ring`.
    have h_reorder : ‖B‖ * (‖S - L‖ * ‖A‖) = ‖B‖ * ‖A‖ * ‖S - L‖ := by ring
    rw [h_reorder] at h_chain
    exact h_chain
  -- Step 2: take the infimum over `L`. The clever step is pulling the
  -- non-negative scalar `‖B‖ * ‖A‖` *inside* the infimum: rewriting
  -- `(‖B‖ * ‖A‖) * sInf S = sInf ((‖B‖ * ‖A‖) • S)` reduces the goal to a
  -- pointwise inequality on the image of the approximation set.
  have h_BA_nonneg : 0 ≤ ‖B‖ * ‖A‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h_inf : approximationNumber (B.comp (S.comp A)) n
                  ≤ ‖B‖ * ‖A‖ * approximationNumber S n := by
    -- Rewrite the right-hand side as a scalar action on the infimum.
    change _ ≤ (‖B‖ * ‖A‖) • sInf (approximationSet S n)
    rw [← Real.sInf_smul_of_nonneg h_BA_nonneg]
    -- Now the goal is `a_n (B S A) ≤ sInf ((‖B‖ * ‖A‖) • approximationSet S n)`.
    refine le_csInf ((approximationSet_nonempty S n).image _) ?_
    rintro _ ⟨_, ⟨L, hL, rfl⟩, rfl⟩
    exact hkey L hL
  -- Step 3: `‖B‖ * ‖A‖ * a_n S = ‖B‖ * a_n S * ‖A‖`.
  have h_reorder : ‖B‖ * ‖A‖ * approximationNumber S n
                    = ‖B‖ * approximationNumber S n * ‖A‖ := by ring
  exact h_inf.trans_eq h_reorder



/-! ### The approximation numbers are the largest s-number sequence -/

/-- For every `s`-number sequence and every operator `S : X → Y`,
`sₙ(S) ≤ aₙ(S)`: the approximation numbers are the largest `s`-numbers.
This is the easy half of Pietsch's sandwich theorem; it uses only axioms
(S2) and (S4) of `IsSNumberSequence`. -/
theorem sn_le_approximationNumber
    {s : Family 𝕜} (hs : IsSNumberSequence s) (S : X →L[𝕜] Y) (n : ℕ) :
    s S n ≤ approximationNumber S n := by
  refine le_csInf (approximationSet_nonempty S n) ?_
  rintro r ⟨A, hA, rfl⟩
  have hS_eq : S = A + (S - A) := by abel
  have h_low : s A n = 0 := hs.vanishes_on_low_rank A n hA
  calc s S n
      = s (A + (S - A)) n := by rw [← hS_eq]
    _ ≤ s A n + ‖S - A‖ := hs.subadditive A (S - A) n
    _ = ‖S - A‖ := by rw [h_low, zero_add]



/-! ### (S5') Strict normalisation `a_n (id_X) = 1` whenever `dim X > n`

We prove the stronger form (S5') directly via Riesz's lemma, avoiding both
SVD and Auerbach. The classical (S5) on `EuclideanSpace 𝕜 (Fin (n + 1))`
follows as a one-line specialisation.

Key idea:
* `≤ 1`: take `L = 0`. Then `‖id - 0‖ = ‖id‖ = 1` (since `dim X > 0`).
* `≥ 1`: for any `L` with `rank L ≤ n`, the range of `L` is a proper
  finite-dimensional, hence closed, subspace of `X`. Riesz's lemma gives,
  for any `r < 1`, an `x₀ ∉ range L` with `r * ‖x₀‖ ≤ ‖x₀ - L x₀‖`. The
  operator-norm sup characterisation then gives
  `‖id − L‖ ≥ ‖(id − L) x₀‖ / ‖x₀‖ ≥ r`. Letting `r → 1` yields `‖id − L‖ ≥ 1`,
  hence `a_n(id) ≥ 1`.-/
variable [CompleteSpace 𝕜]

/-- (S5') Strict normalisation: `approximationNumber (id_X) n = 1` whenever
`n < Module.finrank 𝕜 X`. -/
lemma approximationNumber_strict {X : Type u} [NormedAddCommGroup X]
    [NormedSpace 𝕜 X] (n : ℕ) (h : n < Module.finrank 𝕜 X) :
    approximationNumber (ContinuousLinearMap.id 𝕜 X) n = 1 := by
  -- Set up: `X` is finite-dimensional and nontrivial.
  have h_finrank_pos : 0 < Module.finrank 𝕜 X :=
    Nat.lt_of_le_of_lt (Nat.zero_le _) h
  have : FiniteDimensional 𝕜 X := .of_finrank_pos h_finrank_pos
  have : Nontrivial X := Module.nontrivial_of_finrank_pos h_finrank_pos
  have h_id_norm : ‖ContinuousLinearMap.id 𝕜 X‖ = 1 := norm_id
  set I := ContinuousLinearMap.id 𝕜 X with hI_def
  refine le_antisymm ?_ ?_
  · -- Upper bound: `a_n I ≤ ‖I − 0‖ = ‖I‖ = 1`.
    have h_zero_rank : (0 : X →L[𝕜] X).rank ≤ (n : Cardinal) := by simp
    calc approximationNumber I n
        ≤ ‖I - 0‖ := approximationNumber_le_norm_sub h_zero_rank
      _ = ‖I‖ := by rw [sub_zero]
      _ = 1 := h_id_norm
  · -- Lower bound: every `L` with `rank L ≤ n` satisfies `‖I − L‖ ≥ 1`.
    refine le_csInf (approximationSet_nonempty I n) ?_
    rintro _ ⟨L, hL, rfl⟩
    -- ===== Step A: `range L` is a closed proper subspace of `X`. =====
    set V : Submodule 𝕜 X := LinearMap.range (L : X →ₗ[𝕜] X) with hV_def
    -- `dim V ≤ rank L ≤ n < dim X`, so `V` cannot be all of `X`.
    have hV_finrank_le : Module.finrank 𝕜 V ≤ n := Module.finrank_le_of_rank_le hL
    have hV_finrank_lt : Module.finrank 𝕜 V < Module.finrank 𝕜 X :=
      lt_of_le_of_lt hV_finrank_le h
    have hV_ne_top : V ≠ ⊤ := by
      intro h_top
      rw [h_top, finrank_top] at hV_finrank_lt
      exact lt_irrefl _ hV_finrank_lt
    -- Finite-dimensional subspaces are closed (uses `[CompleteSpace 𝕜]`).
    have hV_closed : IsClosed (V : Set X) := V.closed_of_finiteDimensional
    -- Properness gives some point outside `V`.
    have hV_exists : ∃ x : X, x ∉ V := SetLike.exists_not_mem_of_ne_top V hV_ne_top
    -- ===== Steps B–D: for every `r ∈ (0, 1)`, show `r ≤ ‖I − L‖`. =====
    have h_aux : ∀ r : ℝ, 0 < r → r < 1 → r ≤ ‖I - L‖ := by
      intro r _ hr1
      -- ----- Step B: Riesz's lemma at level `r < 1` produces `x₀`. -----
      obtain ⟨x₀, hx₀_ne, hx₀_dist⟩ := riesz_lemma hV_closed hV_exists hr1
      -- `x₀ ∉ V`, in particular `x₀ ≠ 0`, so `‖x₀‖ > 0`.
      have hx₀_ne_zero : x₀ ≠ 0 := fun h0 => hx₀_ne (h0 ▸ V.zero_mem)
      have hx₀_norm_pos : 0 < ‖x₀‖ := norm_pos_iff.mpr hx₀_ne_zero
      -- ----- Step C: `r * ‖x₀‖ ≤ ‖(I − L) x₀‖`. -----
      -- Specialise the Riesz distance bound to `y = L x₀ ∈ range L`.
      have h_apply : (I - L) x₀ = x₀ - L x₀ := by
        simp [hI_def, sub_apply, ContinuousLinearMap.id_apply]
      have h_riesz : r * ‖x₀‖ ≤ ‖x₀ - L x₀‖ :=
        hx₀_dist (L x₀) (LinearMap.mem_range_self _ _)
      have h_witness : r * ‖x₀‖ ≤ ‖(I - L) x₀‖ := by
        rw [h_apply]; exact h_riesz
      -- ----- Step D: divide by `‖x₀‖` after the operator-norm bound. -----
      -- `‖(I − L) x₀‖ ≤ ‖I − L‖ * ‖x₀‖` is the operator-norm inequality.
      have h_op : ‖(I - L) x₀‖ ≤ ‖I - L‖ * ‖x₀‖ := (I - L).le_opNorm x₀
      have h_chain : r * ‖x₀‖ ≤ ‖I - L‖ * ‖x₀‖ := h_witness.trans h_op
      -- Cancel the positive factor `‖x₀‖`.
      exact le_of_mul_le_mul_right h_chain hx₀_norm_pos
    -- ===== Step E: ε → 1 via `le_of_forall_pos_le_add`. =====
    -- We have `(1 - ε) ≤ ‖I − L‖` for every small `ε > 0`. Rephrase as
    -- `1 ≤ ‖I − L‖ + ε`; the `ε ≥ 1` case is trivial (RHS ≥ 0 + 1).
    refine le_of_forall_pos_le_add fun ε hε => ?_
    by_cases hε1 : 1 ≤ ε
    · linarith [norm_nonneg (I - L)]
    have hε1' : ε < 1 := lt_of_not_ge hε1
    linarith [h_aux (1 - ε) (by linarith) (by linarith)]

/-- (S5) Normalisation on `id_{ℓ₂^{n+1}}`: a special case of (S5'). -/
lemma approximationNumber_id_euclidean (n : ℕ) :
    approximationNumber
      (ContinuousLinearMap.id 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1)))) n = 1 := by
  have h : n < Module.finrank 𝕜 (EuclideanSpace 𝕜 (Fin (n + 1))) := by
    rw [finrank_euclideanSpace_fin' (n + 1)]; exact Nat.lt_succ_self n
  exact approximationNumber_strict n h

/-! ### Summary: approximation numbers form a strict s-number sequence -/

/-- The approximation-numbers family. -/
private noncomputable def approxFamily : Family 𝕜 :=
  fun {_X _Y} _ _ _ _ S n => approximationNumber S n

/-- The approximation numbers form an s-number sequence in the sense of Pietsch. -/
theorem isSNumberSequence_approximationNumber :
    IsSNumberSequence (𝕜 := 𝕜) approxFamily where
  norm_at_zero := fun S => approximationNumber_zero_eq_norm S
  antitone := fun S n => approximationNumber_antitone S n
  nonneg := fun S n => approximationNumber_nonneg S n
  subadditive := fun S T n => approximationNumber_add_le S T n
  ideal := fun A S B n => approximationNumber_comp_comp_le A S B n
  vanishes_on_low_rank := fun _ _ h => approximationNumber_eq_zero_of_rank_le h
  normalised_at_id := fun n => approximationNumber_id_euclidean n

/-- Approximation numbers form a *strict* s-number sequence: in addition to
(S1)–(S5) they satisfy (S5'), the strong normalisation `a_n (id_X) = 1` for
every Banach space `X` with `dim X > n`. -/
theorem isStrictSNumberSequence_approximationNumber :
    IsStrictSNumberSequence (𝕜 := 𝕜) approxFamily where
  toIsSNumberSequence := isSNumberSequence_approximationNumber
  strictly_normalised_at_id := fun n h => approximationNumber_strict n h

end SNumbers

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
