/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.IteratedSplitRefinement

/-!
# Ordered path refinements

`IteratedSplitRefinement` records arbitrary finite chains of canonical
positive bivalent splits.  This module supplies the list-shaped constructor
needed by emitted metric certificates: replace one positive subdivision slot
by an ordered nonempty list of positive segment lengths with the same total.

The construction is deliberately elementary.  Keep the first segment in the
named slot, put the remaining total in the fresh last slot, and recurse on that
fresh slot.  No graph search, quotient, or normalization enters.  A final
`LaplacianEquiv` is kept as an explicit presentation obligation, since an
external certificate generally orders its bivalent vertices and edge
occurrences differently from this canonical append-at-the-end convention.
-/

@[expose] public section

namespace Utilities.Certificate.IteratedSplitRefinement

open Utilities.Certificate.OneEdgeSplitRefinement

/-- The first canonical step in an ordered path split. -/
def pathHeadStep (source : PackedSpec) (slot : Fin source.p)
    (first : ℕ) (rest : List ℕ)
    (first_pos : 0 < first) (rest_sum_pos : 0 < rest.sum)
    (length_sum : source.spec.length slot = first + rest.sum) :
    CanonicalSplitStep source
      (splitPacked source slot first rest.sum first_pos rest_sum_pos) where
  splitSlot := slot
  firstLength := first
  secondLength := rest.sum
  firstLength_pos := first_pos
  secondLength_pos := rest_sum_pos
  length_sum := length_sum
  target_eq := rfl

/-- Proposition-level evidence that a retained split chain is exactly the
left-to-right recursion described by a segment list.  Keeping the chain as an
index lets `OrderedPathSplit` eliminate into computational transport data
without asking Lean to generate a `SizeOf` instance for a nested dependent
inductive family. -/
inductive OrderedPathSplitValid :
    (source : PackedSpec) → (slot : Fin source.p) → (segments : List ℕ) →
      (target : PackedSpec) → CanonicalSplitChain source target → Prop
  | singleton (source : PackedSpec) (slot : Fin source.p) :
      OrderedPathSplitValid source slot [source.spec.length slot] source .refl
  | cons (source : PackedSpec) (slot : Fin source.p)
      (first : ℕ) (rest : List ℕ)
      (first_pos : 0 < first) (rest_sum_pos : 0 < rest.sum)
      (length_sum : source.spec.length slot = first + rest.sum)
      {target : PackedSpec}
      {tailChain : CanonicalSplitChain
        (splitPacked source slot first rest.sum first_pos rest_sum_pos) target}
      (tail : OrderedPathSplitValid
        (splitPacked source slot first rest.sum first_pos rest_sum_pos)
        (secondSlot source.spec) rest target tailChain) :
      OrderedPathSplitValid source slot (first :: rest) target
        ((CanonicalSplitChain.single
          (pathHeadStep source slot first rest first_pos rest_sum_pos length_sum)).append
            tailChain)

/-- A canonical replacement of one slot by an ordered list of positive
segments.  The proof field pins the retained chain to the elementary
append-at-the-end construction. -/
structure OrderedPathSplit
    (source : PackedSpec) (slot : Fin source.p)
    (segments : List ℕ) (target : PackedSpec) where
  /-- The canonical split chain whose validity field certifies the prescribed ordered path
  segments. -/
  chain : CanonicalSplitChain source target
  valid : OrderedPathSplitValid source slot segments target chain

namespace OrderedPathSplit

variable {source target : PackedSpec} {slot : Fin source.p}
  {segments : List ℕ}

/-- Delete zero-length source segments before constructing a positive split
chain.  These are precisely the segments contracted on a closed DV cone
face. -/
def positiveSegments (segments : List ℕ) : List ℕ :=
  segments.filter fun length => 0 < length

@[simp] theorem sum_positiveSegments (segments : List ℕ) :
    (positiveSegments segments).sum = segments.sum := by
  unfold positiveSegments
  induction segments with
  | nil => simp
  | cons first rest ih =>
      by_cases hFirst : 0 < first
      · simp [hFirst, ih]
      · have hZero : first = 0 := by omega
        simp [hZero, ih]

theorem positiveSegments_all_pos (segments : List ℕ) :
    ∀ length ∈ positiveSegments segments, 0 < length := by
  intro length hLength
  exact of_decide_eq_true (List.mem_filter.mp hLength).2

theorem positiveSegments_ne_nil {segments : List ℕ} (hSum : 0 < segments.sum) :
    positiveSegments segments ≠ [] := by
  intro hEmpty
  have : (positiveSegments segments).sum = 0 := by rw [hEmpty]; rfl
  rw [sum_positiveSegments] at this
  omega

/-- The no-op path refinement by the original singleton length. -/
def singleton (source : PackedSpec) (slot : Fin source.p) :
    OrderedPathSplit source slot [source.spec.length slot] source where
  chain := .refl
  valid := .singleton source slot

/-- Prepend one segment by splitting off `first`, then follow a recursively
constructed refinement of the fresh remainder slot. -/
def cons (source : PackedSpec) (slot : Fin source.p)
    (first : ℕ) (rest : List ℕ)
    (first_pos : 0 < first) (rest_sum_pos : 0 < rest.sum)
    (length_sum : source.spec.length slot = first + rest.sum)
    {target : PackedSpec}
    (tail : OrderedPathSplit
      (splitPacked source slot first rest.sum first_pos rest_sum_pos)
      (secondSlot source.spec) rest target) :
    OrderedPathSplit source slot (first :: rest) target where
  chain := (CanonicalSplitChain.single
    (pathHeadStep source slot first rest first_pos rest_sum_pos length_sum)).append
      tail.chain
  valid := .cons source slot first rest first_pos rest_sum_pos length_sum tail.valid

/-- The listed segment lengths add to the original slot length. -/
theorem sum_eq (split : OrderedPathSplit source slot segments target) :
    segments.sum = source.spec.length slot := by
  cases split with
  | mk chain valid => induction valid with
  | singleton => simp
  | cons _ _ _ _ _ _ length_sum _ =>
      simpa using length_sum.symm

/-- Every segment in an ordered path split is positive. -/
theorem all_pos (split : OrderedPathSplit source slot segments target) :
    ∀ length ∈ segments, 0 < length := by
  cases split with
  | mk chain valid => induction valid with
  | singleton source slot =>
      intro length hLength
      simp only [List.mem_singleton] at hLength
      subst length
      exact source.spec.length_pos slot
  | cons _ _ first _ first_pos _ _ _ ih =>
      intro length hLength
      simp only [List.mem_cons] at hLength
      rcases hLength with rfl | hRest
      · exact first_pos
      · exact ih length hRest

/-- Construct the canonical ordered refinement from a positive nonempty list
whose sum is the named slot length. -/
noncomputable def ofList :
    (source : PackedSpec) → (slot : Fin source.p) → (segments : List ℕ) →
      segments ≠ [] →
      (∀ length ∈ segments, 0 < length) →
      segments.sum = source.spec.length slot →
      Σ target, OrderedPathSplit source slot segments target
  | source, slot, [], nonempty, _, _ => False.elim (nonempty rfl)
  | source, slot, [only], _, _, sum_eq => by
      have hOnly : only = source.spec.length slot := by simpa using sum_eq
      subst only
      exact ⟨source, .singleton source slot⟩
  | source, slot, first :: second :: rest, _, all_pos, sum_eq => by
      have hFirst : 0 < first := all_pos first (by simp)
      have hSecond : 0 < second := all_pos second (by simp)
      have hRestSum : 0 < (second :: rest).sum := by
        simp only [List.sum_cons]
        omega
      have hLength :
          source.spec.length slot = first + (second :: rest).sum := by
        simpa only [List.sum_cons] using sum_eq.symm
      let middle := splitPacked source slot first (second :: rest).sum
        hFirst hRestSum
      have hTailPos : ∀ length ∈ second :: rest, 0 < length := by
        intro length hLength
        exact all_pos length (List.mem_cons_of_mem first hLength)
      have hTailSum :
          (second :: rest).sum =
            middle.spec.length (secondSlot source.spec) := by
        change (second :: rest).sum =
          splitLength source.spec slot first (second :: rest).sum
            (secondSlot source.spec)
        exact (splitLength_second source.spec slot first (second :: rest).sum).symm
      let tail := ofList middle (secondSlot source.spec) (second :: rest)
        (by simp) hTailPos hTailSum
      exact ⟨tail.1,
        cons source slot first (second :: rest) hFirst hRestSum hLength tail.2⟩
termination_by source slot segments _ _ _ => segments.length

/-- Construct the positive canonical path refinement represented by a list
which may contain zero entries.  Zero entries disappear before splitting;
the final `RefinementPresentation.relabeling` is the explicit obligation that
identifies this positive canonical model with the contracted closed-face
presentation used by a certificate. -/
noncomputable def ofListWithZeros
    (source : PackedSpec) (slot : Fin source.p) (segments : List ℕ)
    (sum_eq : segments.sum = source.spec.length slot) :
    Σ target, OrderedPathSplit source slot (positiveSegments segments) target :=
  ofList source slot (positiveSegments segments)
    (positiveSegments_ne_nil (by rw [sum_eq]; exact source.spec.length_pos slot))
    (positiveSegments_all_pos segments)
    (by rw [sum_positiveSegments, sum_eq])

/-- Ordered path refinement preserves every Brill--Noether existence
statement. -/
theorem bnExists_iff (split : OrderedPathSplit source slot segments target)
    (r d : ℤ) :
    BNExists source.graph r d ↔ BNExists target.graph r d :=
  split.chain.bnExists_iff r d

end OrderedPathSplit

/-- A canonical positive refinement followed by an arbitrary checked
relabeling to the presentation used by an emitted certificate. -/
structure RefinementPresentation (source : PackedSpec) (presented : CFGraph) where
  /-- The subdivision specification reached after the canonical refinements. -/
  refined : PackedSpec
  /-- The checked sequence of canonical splits from the source to the refined specification. -/
  chain : CanonicalSplitChain source refined
  /-- The edge-multiplicity-preserving relabeling from the refined graph to the presented graph. -/
  relabeling : LaplacianEquiv refined.graph presented

namespace RefinementPresentation

variable {source : PackedSpec} {presented : CFGraph}

/-- Package a split chain and its final checked relabeling. -/
def ofChain {refined : PackedSpec}
    (chain : CanonicalSplitChain source refined)
    (relabeling : LaplacianEquiv refined.graph presented) :
    RefinementPresentation source presented where
  refined := refined
  chain := chain
  relabeling := relabeling

/-- Package one ordered path split and its final checked relabeling. -/
def ofOrderedPathSplit {slot : Fin source.p} {segments : List ℕ}
    {refined : PackedSpec}
    (split : OrderedPathSplit source slot segments refined)
    (relabeling : LaplacianEquiv refined.graph presented) :
    RefinementPresentation source presented :=
  ofChain split.chain relabeling

/-- The composite Laplacian equivalence from the stable subdivision to the
certificate presentation. -/
def laplacianEquiv (presentation : RefinementPresentation source presented) :
    LaplacianEquiv source.graph presented :=
  presentation.chain.laplacianEquiv.trans presentation.relabeling

/-- A checked positive refinement presentation preserves every
Brill--Noether existence statement, in both directions. -/
theorem bnExists_iff (presentation : RefinementPresentation source presented)
    (r d : ℤ) :
    BNExists source.graph r d ↔ BNExists presented r d :=
  presentation.laplacianEquiv.bnExists_iff r d

end RefinementPresentation

end Utilities.Certificate.IteratedSplitRefinement
