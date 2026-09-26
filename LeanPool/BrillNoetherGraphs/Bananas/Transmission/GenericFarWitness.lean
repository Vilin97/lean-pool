/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Bananas.SameStrand.SameStrand

/-!
# A generic cross-strand far-mark rank witness

The corrected high-genus ledger separates the local rank calculation from the
global far-mark classification.  This file records the local calculation in
the coordinate language currently supported by `SameStrand`: two positive
chips are interior points on distinct strands, and the third position is an
explicit interior vertex distinct from both.

The conclusion is deliberately a rank pattern, not a `rankDelta` theorem.
The two-chip divisor has rank zero, while deleting the third chip from it
leaves a degree-one divisor of rank `-1`.  This is the verified generic
cross-strand ingredient; selecting that third position from a normalized
"far" hypothesis is a separate orientation/mark-selection bridge.
-/

@[expose] public section

namespace Bananas

open Utilities
open Utilities.Certificate SubdivisionGraph
open Utilities.Certificate.SubdivisionGraph.Spec

/-! ## Graph-generic ingredients

Stated for an abstract `CFGraph`.  Doing the rank bookkeeping here rather than
on a concrete banana keeps the unifier away from comparing divisors pointwise
(which unfolds `oneChip` and evaluates `DecidableEq` on the subdivision vertex
type); see the module docstring of `LengthTwoCrossMonotonicity.lean`. -/

section Generic

variable {G : CFGraph}

/-- Two chips make an effective divisor. -/
theorem effective_one_chip_add_one_chip (x y : G.V) :
    effective (oneChip x + oneChip y : CFDiv G) := by
  intro v
  simp only [Pi.add_apply, oneChip]
  split_ifs <;> omega

/-- Deleting a chip at a vertex carrying neither of the two chips puts that
vertex into debt. -/
theorem two_chip_sub_apply_neg (x y z : G.V) (hzx : z ≠ x) (hzy : z ≠ y) :
    (oneChip x + oneChip y - oneChip z : CFDiv G) z < 0 := by
  simp [Pi.sub_apply, Pi.add_apply, oneChip, hzx, hzy]

/-- An effective divisor with a rank `-1` one-chip deletion has rank exactly
zero. -/
theorem rank_eq_zero_of_effective_of_sub_one_chip_rank_neg_one
    (D : CFDiv G) (v : G.V) (hEff : effective D)
    (hSub : rank G (D - oneChip v) = -1) :
    rank G D = 0 := by
  have hNonneg : 0 ≤ rank G D :=
    (rank_geq_iff G D 0).mp
      ((rank_nonneg_iff_winnable G D).mpr (winnable_of_effective G D hEff))
  have hLt : rank G D < 1 := by
    by_contra hNot
    have hWin :=
      (rank_ge_one_iff_winnable_sub_one_chip G D).mp (by omega) v
    have hSubNonneg : 0 ≤ rank G (D - oneChip v) :=
      (rank_geq_iff G (D - oneChip v) 0).mp
        ((rank_nonneg_iff_winnable G (D - oneChip v)).mpr hWin)
    omega
  omega

end Generic

/-- A cross-strand two-chip divisor has rank zero when an explicit third
interior vertex makes its one-chip deletion reduced with debt.

The divisor in the second conjunct has two positive chips and one deleted
chip, i.e. it is the three-term witness used by the far-mark argument.  The
hypotheses name all vertex distinctness needed by the reducedness theorem;
no endpoint coordinate pair is treated as unique.
-/
theorem cross_strand_rank_zero_three_chip_witness
    {g : ℕ} (hg : 2 ≤ g) (B : Banana g)
    (α β γ : Fin (g + 1))
    (i : B.PathPosition α) (j : B.PathPosition β)
    (q : B.PathPosition γ)
    (hi : B.IsInteriorPosition α i)
    (hj : B.IsInteriorPosition β j)
    (hq : B.IsInteriorPosition γ q)
    (hαβ : α ≠ β)
    (hqx : B.pathVertex γ q ≠ B.pathVertex α i)
    (hqy : B.pathVertex γ q ≠ B.pathVertex β j) :
    rank B.graph
        (oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j)) = 0 ∧
      rank B.graph
        (oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j) -
          oneChip (B.pathVertex γ q)) = -1 := by
  -- Every divisor below is written out rather than abbreviated by a `let`, so
  -- that it matches `q_reduced_distinct_interior_path_strands` syntactically
  -- and no divisor-level unification is ever attempted.
  have hRed := q_reduced_distinct_interior_path_strands
    hg B α β γ i j q hi hj hq hαβ hqx hqy
  have hSubRank : rank B.graph
      (oneChip (B.pathVertex α i) + oneChip (B.pathVertex β j) -
        oneChip (B.pathVertex γ q)) = -1 :=
    rank_eq_neg_one_of_qReduced_debt B.graph (B.pathVertex γ q) _ hRed
      (two_chip_sub_apply_neg _ _ _ hqx hqy)
  refine ⟨?_, hSubRank⟩
  exact rank_eq_zero_of_effective_of_sub_one_chip_rank_neg_one _
    (B.pathVertex γ q) (effective_one_chip_add_one_chip _ _) hSubRank

end Bananas
