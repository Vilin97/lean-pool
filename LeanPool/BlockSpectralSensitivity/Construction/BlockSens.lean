/-
Copyright (c) 2026 Alex Meiburg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Meiburg
-/
module

public import LeanPool.BlockSpectralSensitivity.Construction.Basic

/-!
# The block-sensitivity witness

Section 5 of `bs_lambda.txt` works at the all-zero input `0^V = zeroInput (Coord ι r)`.
Every certificate `C_i` requires the whole (nonempty) block `B_i` to be `1`, so
`f (0^V) = 0`.  Flipping exactly `B_i` sets
all of `B_i` to `1` while leaving every coordinate outside `B_i` — in particular every
outgoing gate coordinate of `C_i`, which lives in a block `B_j` with `j ≠ i` — equal to `0`.
Hence `(0^V)^{B_i} ∈ C_i` and `f ((0^V)^{B_i}) = 1`.

The blocks are pairwise disjoint, so they form a family of `|ι|` disjoint sensitive blocks
at `0^V`, giving `bs f ≥ |ι|`.

Adapted for Lean Pool from `Timeroot/BS_Lam` at commit
`7bd39a8d41ee7910d3296d0477ad18f8fff9d870`; ported to Lean Pool with proof and dependency cleanup.
-/

@[expose] public section

namespace BSLambda

namespace Construction

variable {ι : Type*} {r : ℕ}

/-- `f (0^V) = 0`: no certificate is satisfied by the all-zero input, because every
certificate requires its whole (nonempty) owner block to be `1` (Section 5). -/
theorem ind_zeroInput [Fintype ι] [DecidableEq ι] [NeZero r] (Arc : ι → ι → Bool)
    (γ : ι → ι → Fin r) : ind Arc γ (zeroInput (Coord ι r)) = false :=
  ind_eq_false_iff.2 fun _ hi ↦ by simpa using (sat_cert_iff.1 hi).1 0

variable {Arc : ι → ι → Bool} {γ : ι → ι → Fin r}

/-- Flipping exactly the owner block `B_i` at the all-zero input lands in `C_i`
(Section 5).  No irreflexivity hypothesis is needed: the gate coordinates of `C_i` lie in
blocks `B_j` with `j ≠ i`, which the flip does not touch. -/
theorem sat_cert_flipSet_block [DecidableEq ι] (i : ι) :
    (cert Arc γ i).Sat (flipSet (zeroInput (Coord ι r)) (block i)) :=
  sat_cert_iff.2 ⟨fun _ ↦ by simp, fun _ hji _ ↦ by simp [hji]⟩

/-- `f ((0^V)^{B_i}) = 1`: flipping the owner block `B_i` at the all-zero input lands in
`C_i`, hence in the union defining `f` (Section 5). -/
theorem ind_flipSet_block [Fintype ι] [DecidableEq ι] (i : ι) :
    ind Arc γ (flipSet (zeroInput (Coord ι r)) (block i)) = true :=
  ind_eq_true_of_sat (sat_cert_flipSet_block i)

/-- Each block `B_i` is a sensitive block of `f` at the all-zero input (Section 5). -/
theorem isSensitiveBlock_block [Fintype ι] [DecidableEq ι] [NeZero r] (i : ι) :
    IsSensitiveBlock (ind Arc γ) (zeroInput (Coord ι r)) (block i) :=
  isSensitiveBlock_of_eq_true (block_nonempty i) (ind_zeroInput Arc γ) (ind_flipSet_block i)

/-- **The block-sensitivity lower bound**: `bs f ≥ |ι|` (Section 5, `bs(f) ≥ k`).  The
blocks `B_i` are nonempty, pairwise disjoint and sensitive at the all-zero input. -/
theorem card_le_bs [Fintype ι] [DecidableEq ι] [NeZero r] :
    Fintype.card ι ≤ bs (ind Arc γ) := by
  rw [← Finset.card_univ (α := ι)]
  exact card_le_bs_of_blocks (fun i _ ↦ isSensitiveBlock_block i)
    fun _ _ _ _ hij ↦ block_disjoint hij

end Construction

end BSLambda
