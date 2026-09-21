/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/

import LeanPool.BrillNoetherGraphs.Utilities.Certificate.CubicMatrixReplay
import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CoreRelabeling

/-!
# Canonical branch pruning for the cubic matrix replay

`Certificate/CubicMatrixExhaustive.lean` removed the generated tree, leaving
the leaf payloads as the whole remaining cost.  This module supplies the
machinery to cut those down, and to cut the traversal down with them.

Everything here is generic in the vertex count and the degree.  That is
deliberate: the genus-four instance at `n = 6` is a proof of concept for the
genus-five instance at `n = 8`, where the numbers are

```text
            connected leaves   + cut 0   + cut 0 and cut 1
n = 6                    640        46                  20
n = 8                168,840     4,470                 777
```

## The two cuts

A node's state is really `(S, residual capacity on V \ S)` with `S` the set of
processed vertices; the row-by-row scheme is the special case where `S` is a
prefix.  The freedom to choose which vertex to process next is exactly the
freedom to *sort by relabeling*, and that gives two cuts:

* **cut 0** — relabel `1 … n-1` so that row `0` is ascending;
* **cut 1** — then, within each maximal block of positions sharing a row-`0`
  value, relabel so that row `1` is ascending.  Such a permutation moves
  vertices only inside row-`0` level sets, so it preserves cut 0.

Both are witnessed by explicit permutations, so no canonical labeling happens
inside Lean.

Ascending is deliberate and is worth about 25 per cent over descending: cut 1
does not move position `1`, and ascending puts the smallest row-`0` value
there, leaving larger blocks for cut 1 to act on.

## What is here and what is not

`canonicalPrefix` is the decidable predicate, `prunedCheck` is the traversal
that skips non-canonical branches, and `prunedCheck_sound` is its soundness.
Because the predicate only inspects rows `0` and `1`, it is decided as soon as
those are chosen, so the pruning happens at the top of the tree where it saves
the most.

The remaining obligation is named `CanonicalRepresentative`: every candidate is
isomorphic to a canonical one.  **It is stated here and not proved.**  Its
empirical form was checked at `n = 6`, where the 20 canonical connected leaves
carry all six atlas indices; see
the accompanying analysis.
-/

namespace Utilities.Certificate.CubicMatrixReplay
open Utilities.Certificate
open Utilities
open Utilities.Certificate.CubicMatrixReplay

/-! ## The canonical predicate -/

/-- A list of naturals is ascending. -/
def SortedAsc : List ℕ → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => decide (a ≤ b) && SortedAsc (b :: rest)

/-- `BlocksSorted keys values` asks that `values` be ascending across every
adjacent pair whose `keys` agree.  With `keys` the tail of row `0` and
`values` row `1`, this is cut 1. -/
def BlocksSorted : List ℕ → List ℕ → Bool
  | a :: b :: keys, x :: y :: values =>
      (decide (a ≠ b) || decide (x ≤ y)) && BlocksSorted (b :: keys) (y :: values)
  | _, _ => true

/-- The canonical predicate on a row list.  It inspects only rows `0` and `1`,
so it is decided as soon as those two are chosen. -/
def canonicalPrefix (rows : List (List ℕ)) : Bool :=
  match rows with
  | [] => true
  | row0 :: rest =>
      SortedAsc row0 &&
        match rest with
        | [] => true
        | row1 :: _ => BlocksSorted row0.tail row1

/-- Only the first two rows matter, so extending a canonical row list on the
right cannot break canonicality. -/
theorem canonicalPrefix_append {rows extra : List (List ℕ)}
    (h : canonicalPrefix rows = true) :
    2 ≤ rows.length → canonicalPrefix (rows ++ extra) = true := by
  intro hLen
  match rows, hLen with
  | row0 :: row1 :: rest, _ => simpa [canonicalPrefix] using h

/-! ## Accepting along a path -/

/-- Every nonempty prefix of `rows`, read after `path`, is accepted.  This is
what a pruned traversal needs in order to reach a given row list. -/
def AcceptsAlong (accept : List (List ℕ) → Bool) :
    List (List ℕ) → List (List ℕ) → Prop
  | _, [] => True
  | path, row :: rest =>
      accept (path ++ [row]) = true ∧ AcceptsAlong accept (path ++ [row]) rest

/-! ## The pruned traversal -/

/-- Exhaustive check that skips branches the `accept` predicate rejects.  A
rejected branch is discharged immediately, so the subtree below it is never
traversed. -/
def prunedCheck (accept leafDecide : List (List ℕ) → Bool) :
    ℕ → List ℕ → List (List ℕ) → Bool
  | 0, _, _ => false
  | _ + 1, [], path => leafDecide path
  | fuel + 1, capacity :: capacities, path =>
      (boundedCompositions capacity capacities).all fun part =>
        !accept (path ++ [part]) ||
          prunedCheck accept leafDecide fuel
            (List.zipWith (· - ·) capacities part) (path ++ [part])

/-- **Soundness of the pruned traversal.**  A row list produced by the
branching whose prefixes are all accepted is accepted by `leafDecide`.  Rows
that fail `accept` somewhere are deliberately not covered; supplying them is
the job of `CanonicalRepresentative`. -/
theorem prunedCheck_sound (accept leafDecide : List (List ℕ) → Bool)
    {capacities : List ℕ} {rows : List (List ℕ)}
    (hFollows : Follows capacities rows) :
    ∀ (fuel : ℕ) (path : List (List ℕ)),
      prunedCheck accept leafDecide fuel capacities path = true →
      AcceptsAlong accept path rows →
      leafDecide (path ++ rows) = true := by
  induction hFollows with
  | nil =>
      intro fuel path hCheck _
      cases fuel with
      | zero => simp [prunedCheck] at hCheck
      | succ f =>
          rw [prunedCheck] at hCheck
          simpa using hCheck
  | cons hParts _hRows ih =>
      intro fuel path hCheck hAccepts
      cases fuel with
      | zero => simp [prunedCheck] at hCheck
      | succ f =>
          rw [prunedCheck, List.all_eq_true] at hCheck
          obtain ⟨hHead, hTail⟩ := hAccepts
          have hBranch := hCheck _ hParts
          rw [hHead] at hBranch
          simp only [Bool.not_true, Bool.false_or] at hBranch
          have := ih f _ hBranch hTail
          simpa using this

/-! ## Canonicality reaches every prefix -/

/-- Once rows `0` and `1` are fixed and canonical, every longer path stays
accepted, so a pruned traversal descends all the way. -/
theorem acceptsAlong_of_two (row0 row1 : List ℕ)
    (h : canonicalPrefix [row0, row1] = true) :
    ∀ (acc rest : List (List ℕ)),
      AcceptsAlong canonicalPrefix (row0 :: row1 :: acc) rest := by
  intro acc rest
  induction rest generalizing acc with
  | nil => trivial
  | cons row rest ih =>
      refine ⟨?_, ?_⟩
      · have := canonicalPrefix_append (rows := [row0, row1])
          (extra := acc ++ [row]) h (by simp)
        simpa using this
      · simpa using ih (acc ++ [row])

/-- A canonical row list is accepted along every one of its prefixes.  This is
the bridge from the predicate to what `prunedCheck_sound` consumes. -/
theorem acceptsAlong_canonicalPrefix (rows : List (List ℕ))
    (h : canonicalPrefix rows = true) :
    AcceptsAlong canonicalPrefix [] rows := by
  match rows with
  | [] => trivial
  | [row0] =>
      exact ⟨by simpa using h, trivial⟩
  | row0 :: row1 :: rest =>
      have hHead : canonicalPrefix [row0] = true := by
        simp only [canonicalPrefix, Bool.and_eq_true] at h ⊢
        exact ⟨h.1, trivial⟩
      have hTwo : canonicalPrefix [row0, row1] = true := by
        simp only [canonicalPrefix, Bool.and_eq_true] at h ⊢
        exact h
      refine ⟨by simpa using hHead, ?_⟩
      refine ⟨by simpa using hTwo, ?_⟩
      simpa using acceptsAlong_of_two row0 row1 hTwo [] rest


open Utilities.Certificate.CubicMatrixReplay

open ExplicitPotential

/-! ## From index-level inequalities to the Boolean predicates -/

/-- An ascending run of values over an arithmetic index range is `SortedAsc`. -/
theorem sortedAsc_map_range' (f : ℕ → ℕ) :
    ∀ len s : ℕ, (∀ k, s ≤ k → k + 1 < s + len → f k ≤ f (k + 1)) →
      SortedAsc ((List.range' s len).map f) = true := by
  intro len
  induction len with
  | zero => intro s _; simp [SortedAsc]
  | succ len ih =>
      intro s hStep
      cases len with
      | zero => simp [SortedAsc]
      | succ m =>
          have hTail : SortedAsc ((List.range' (s + 1) (m + 1)).map f) = true :=
            ih (s + 1) fun k hk hk2 => hStep k (by omega) (by omega)
          have hTailList : (List.range' (s + 1) (m + 1)).map f
              = f (s + 1) :: ((List.range' (s + 2) m).map f) := rfl
          rw [hTailList] at hTail
          have hHead : f s ≤ f (s + 1) := hStep s le_rfl (by omega)
          have hList : (List.range' s (m + 2)).map f
              = f s :: f (s + 1) :: ((List.range' (s + 2) m).map f) := rfl
          rw [hList]
          simp only [SortedAsc, hTail, hHead, decide_true, Bool.and_true]

/-- Values that ascend across every adjacent pair of equal keys, both read off
the same arithmetic index range, satisfy `BlocksSorted`. -/
theorem blocksSorted_map_range' (f g : ℕ → ℕ) :
    ∀ len s : ℕ,
      (∀ k, s ≤ k → k + 1 < s + len → f k = f (k + 1) → g k ≤ g (k + 1)) →
      BlocksSorted ((List.range' s len).map f) ((List.range' s len).map g)
        = true := by
  intro len
  induction len with
  | zero => intro s _; simp [BlocksSorted]
  | succ len ih =>
      intro s hStep
      cases len with
      | zero => simp [BlocksSorted]
      | succ m =>
          have hTail : BlocksSorted ((List.range' (s + 1) (m + 1)).map f)
              ((List.range' (s + 1) (m + 1)).map g) = true :=
            ih (s + 1) fun k hk hk2 hEq => hStep k (by omega) (by omega) hEq
          have hTailF : (List.range' (s + 1) (m + 1)).map f
              = f (s + 1) :: ((List.range' (s + 2) m).map f) := rfl
          have hTailG : (List.range' (s + 1) (m + 1)).map g
              = g (s + 1) :: ((List.range' (s + 2) m).map g) := rfl
          rw [hTailF, hTailG] at hTail
          have hListF : (List.range' s (m + 2)).map f
              = f s :: f (s + 1) :: ((List.range' (s + 2) m).map f) := rfl
          have hListG : (List.range' s (m + 2)).map g
              = g s :: g (s + 1) :: ((List.range' (s + 2) m).map g) := rfl
          rw [hListF, hListG]
          simp only [BlocksSorted, hTail, Bool.and_true, Bool.or_eq_true,
            decide_eq_true_eq]
          by_cases hEq : f s = f (s + 1)
          · exact Or.inr (hStep s le_rfl (by omega) hEq)
          · exact Or.inl hEq

/-- The two index-level cuts imply the Boolean canonical predicate on the whole
row list.  This is stated for an arbitrary matrix and vertex count, so the
small cases are discharged here rather than assumed away. -/
theorem canonicalPrefix_rowsOf (M : ℕ → ℕ → ℕ) (n : ℕ)
    (hCut0 : ∀ k, 1 ≤ k → k + 1 < n → M 0 k ≤ M 0 (k + 1))
    (hCut1 : ∀ k, 2 ≤ k → k + 1 < n → M 0 k = M 0 (k + 1) →
      M 1 k ≤ M 1 (k + 1)) :
    canonicalPrefix (rowsOf M 0 n) = true := by
  match n with
  | 0 => simp [rowsOf, canonicalPrefix]
  | 1 => simp [rowsOf, canonicalPrefix, SortedAsc]
  | (len + 2) =>
      have hRows : rowsOf M 0 (len + 2)
          = ((List.range' 1 (len + 1)).map fun j => M 0 j)
              :: ((List.range' 2 len).map fun j => M 1 j)
              :: rowsOf M 2 len := rfl
      have hTail : (((List.range' 1 (len + 1)).map fun j => M 0 j)).tail
          = (List.range' 2 len).map fun j => M 0 j := rfl
      rw [hRows]
      simp only [canonicalPrefix, hTail, Bool.and_eq_true]
      refine ⟨?_, ?_⟩
      · exact sortedAsc_map_range' (fun j => M 0 j) (len + 1) 1
          fun k hk hk2 => hCut0 k hk (by omega)
      · exact blocksSorted_map_range' (fun j => M 0 j) (fun j => M 1 j) len 2
          fun k hk hk2 hEq => hCut1 k hk (by omega) hEq

/-! ## A weighted key and the exchange step -/

/-- The weighted key of one row of a matrix: entry `j` carries weight `n - j`,
so the weights drop by exactly one at every step inside the range.  Minimizing
this is the same as minimizing the row lexicographically, but it needs no
lexicographic order on lists. -/
def weightKey (n : ℕ) (F : ℕ → ℕ) : ℕ :=
  ∑ j ∈ Finset.range n, (n - j) * F j

/-- Split the weighted key into the two positions `k`, `k + 1` and the rest. -/
theorem weightKey_split (n k : ℕ) (hk : k + 1 < n) (F : ℕ → ℕ) :
    weightKey n F
      = (∑ j ∈ Finset.range n \ {k, k + 1}, (n - j) * F j)
        + ((n - (k + 1)) * (F k + F (k + 1)) + F k) := by
  classical
  have hSub : ({k, k + 1} : Finset ℕ) ⊆ Finset.range n := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Finset.mem_range]
    rcases hx with h | h <;> omega
  have hSplit := Finset.sum_sdiff (f := fun j => (n - j) * F j) hSub
  rw [weightKey, ← hSplit, Finset.sum_pair (by omega : k ≠ k + 1)]
  have hWeight : n - k = (n - (k + 1)) + 1 := by omega
  rw [hWeight]
  ring

/-- **The exchange step.**  If `G` is `F` with the entries at `k` and `k + 1`
interchanged, then the weighted key drops exactly when `F` descends there, and
is unchanged exactly when `F` is flat there. -/
theorem weightKey_swap (n k : ℕ) (hk : k + 1 < n) (F G : ℕ → ℕ)
    (hOther : ∀ j, j < n → j ≠ k → j ≠ k + 1 → G j = F j)
    (hAt : G k = F (k + 1)) (hAt' : G (k + 1) = F k) :
    (F (k + 1) < F k → weightKey n G < weightKey n F) ∧
      (F k = F (k + 1) → weightKey n G = weightKey n F) := by
  classical
  have hRest : (∑ j ∈ Finset.range n \ {k, k + 1}, (n - j) * G j)
      = ∑ j ∈ Finset.range n \ {k, k + 1}, (n - j) * F j := by
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [Finset.mem_sdiff, Finset.mem_range] at hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    rw [hOther j hj.1 hj.2.1 hj.2.2]
  have hPair : G k + G (k + 1) = F k + F (k + 1) := by
    rw [hAt, hAt']; exact Nat.add_comm _ _
  rw [weightKey_split n k hk F, weightKey_split n k hk G, hRest, hPair, hAt]
  refine ⟨fun hLt => ?_, fun hEq => ?_⟩
  · exact Nat.add_lt_add_left (Nat.add_lt_add_left hLt _) _
  · rw [hEq]

/-! ## Transporting the matrix along a relabeling -/

/-- The multiplicity table of a relabeled core, read at the original vertices.
This is the only computation rule the exchange argument needs. -/
theorem matrixOf_relabel {n p : ℕ} (core : Core n p) (σ : Equiv.Perm (Fin n))
    (i j : ℕ) (hi : i < n) (hj : j < n) :
    matrixOf (core.relabel σ) i j
      = core.pairMultiplicity (σ⁻¹ ⟨i, hi⟩) (σ⁻¹ ⟨j, hj⟩) := by
  simp only [matrixOf, dif_pos hi, dif_pos hj]
  have := Core.pairMultiplicity_relabel core σ (σ⁻¹ ⟨i, hi⟩) (σ⁻¹ ⟨j, hj⟩)
  simpa using this

/-- The adjacent transposition of `k` and `k + 1`, as a map on indices. -/
def swapIdx (k i : ℕ) : ℕ :=
  if i = k then k + 1 else if i = k + 1 then k else i

theorem swapIdx_of_ne {k i : ℕ} (h : i ≠ k) (h' : i ≠ k + 1) :
    swapIdx k i = i := by simp [swapIdx, h, h']

theorem swapIdx_left (k : ℕ) : swapIdx k k = k + 1 := by simp [swapIdx]

theorem swapIdx_right (k : ℕ) : swapIdx k (k + 1) = k := by
  simp [swapIdx]

theorem swapIdx_lt {n k i : ℕ} (hk : k + 1 < n) (hi : i < n) :
    swapIdx k i < n := by
  unfold swapIdx
  split
  · omega
  · split <;> omega

/-- The value of the adjacent transposition, read through the `Fin` coercion. -/
theorem coe_swap_mk {n k : ℕ} (hk : k + 1 < n) (j : ℕ) (hj : j < n) :
    ((Equiv.swap (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ ⟨j, hj⟩ : Fin n) : ℕ)
      = swapIdx k j := by
  by_cases h1 : j = k
  · subst h1
    rw [show (⟨j, hj⟩ : Fin n) = ⟨j, by omega⟩ from rfl,
      Equiv.swap_apply_left]
    simp [swapIdx]
  · by_cases h2 : j = k + 1
    · subst h2
      rw [show (⟨k + 1, hj⟩ : Fin n) = ⟨k + 1, hk⟩ from rfl,
        Equiv.swap_apply_right]
      simp [swapIdx]
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega)
        (by simp [Fin.ext_iff]; omega)]
      simp [swapIdx, h1, h2]

/-- Relabeling by an extra adjacent transposition interchanges the two
corresponding rows and columns of the multiplicity table. -/
theorem matrixOf_relabel_swap {n p : ℕ} (core : Core n p)
    (σ : Equiv.Perm (Fin n)) {k : ℕ} (hk : k + 1 < n) (i j : ℕ)
    (hi : i < n) (hj : j < n) :
    matrixOf (core.relabel
        (Equiv.swap (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ * σ)) i j
      = matrixOf (core.relabel σ) (swapIdx k i) (swapIdx k j) := by
  rw [matrixOf_relabel core _ i j hi hj,
    matrixOf_relabel core σ (swapIdx k i) (swapIdx k j)
      (swapIdx_lt hk hi) (swapIdx_lt hk hj)]
  congr 1
  · rw [mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_inv]
    congr 1
    exact Fin.ext (by rw [coe_swap_mk hk i hi])
  · rw [mul_inv_rev, Equiv.Perm.mul_apply, Equiv.swap_inv]
    congr 1
    exact Fin.ext (by rw [coe_swap_mk hk j hj])

/-! ## The key of a relabeling -/

/-- The weighted key of row `row` of the multiplicity table of `core`
relabeled along `σ`. -/
def relabelKey {n p : ℕ} (core : Core n p) (row : ℕ)
    (σ : Equiv.Perm (Fin n)) : ℕ :=
  weightKey n fun j => matrixOf (core.relabel σ) row j

/-- **The exchange step, for a relabeling.**  Composing with the adjacent
transposition of `k` and `k + 1` interchanges those two entries of any row it
fixes, so it strictly lowers that row's key exactly when the row descends
there, and leaves the key alone when the row is flat there. -/
theorem relabelKey_swap {n p : ℕ} (core : Core n p) (σ : Equiv.Perm (Fin n))
    (row k : ℕ) (hk : k + 1 < n) (hRowLt : row < n) (hRow : row ≠ k)
    (hRow' : row ≠ k + 1) :
    (matrixOf (core.relabel σ) row (k + 1) < matrixOf (core.relabel σ) row k →
        relabelKey core row
            (Equiv.swap (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ * σ)
          < relabelKey core row σ) ∧
      (matrixOf (core.relabel σ) row k = matrixOf (core.relabel σ) row (k + 1) →
        relabelKey core row
            (Equiv.swap (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ * σ)
          = relabelKey core row σ) := by
  have hTransport : ∀ j, j < n →
      matrixOf (core.relabel
          (Equiv.swap (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ * σ)) row j
        = matrixOf (core.relabel σ) row (swapIdx k j) := by
    intro j hj
    rw [matrixOf_relabel_swap core σ hk row j hRowLt hj,
      swapIdx_of_ne hRow hRow']
  refine weightKey_swap n k hk (fun j => matrixOf (core.relabel σ) row j)
    (fun j => matrixOf (core.relabel
      (Equiv.swap (⟨k, by omega⟩ : Fin n) ⟨k + 1, hk⟩ * σ)) row j) ?_ ?_ ?_
  · intro j hj hjk hjk'
    rw [hTransport j hj, swapIdx_of_ne hjk hjk']
  · rw [hTransport k (by omega), swapIdx_left]
  · rw [hTransport (k + 1) (by omega), swapIdx_right]


/-! ## Canonical relabeling of a bare core -/

/-- Every connected regular ordered core is vertex-relabelled to a core whose
first two multiplicity rows satisfy \`canonicalPrefix\`. -/
theorem exists_canonical_relabel {n p degree : ℕ} (core : ExplicitPotential.Core n p)
    (hConnected : core.Connected)
    (hDegree : ∀ vertex : Fin n, core.incidenceDegree vertex = degree) :
    ∃ sigma : Equiv.Perm (Fin n),
      (core.relabel sigma).Connected ∧
      (∀ vertex : Fin n, (core.relabel sigma).incidenceDegree vertex = degree) ∧
      canonicalPrefix (rowsOf (matrixOf (core.relabel sigma)) 0 n) = true ∧
      ∀ i j : Fin n,
        core.pairMultiplicity i j =
          (core.relabel sigma).pairMultiplicity (sigma i) (sigma j) := by
  classical
  obtain ⟨best, -, hBest⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Equiv.Perm (Fin n)))
      (relabelKey core 0) ⟨1, Finset.mem_univ 1⟩
  obtain ⟨sigma, hSigmaMem, hSigmaMin⟩ :=
    Finset.exists_min_image
      (Finset.univ.filter fun tau : Equiv.Perm (Fin n) =>
        relabelKey core 0 tau = relabelKey core 0 best)
      (relabelKey core 1) ⟨best, by simp⟩
  rw [Finset.mem_filter] at hSigmaMem
  have hMin0 : ∀ tau, relabelKey core 0 sigma ≤ relabelKey core 0 tau := by
    intro tau
    rw [hSigmaMem.2]
    exact hBest tau (Finset.mem_univ tau)
  have hMin1 : ∀ tau, relabelKey core 0 tau = relabelKey core 0 sigma →
      relabelKey core 1 sigma ≤ relabelKey core 1 tau := by
    intro tau hTau
    refine hSigmaMin tau ?_
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ tau, hTau.trans hSigmaMem.2⟩
  have hCut0 : ∀ k, 1 ≤ k → k + 1 < n →
      matrixOf (core.relabel sigma) 0 k ≤
        matrixOf (core.relabel sigma) 0 (k + 1) := by
    intro k hk hk2
    rcases le_or_gt (matrixOf (core.relabel sigma) 0 k)
      (matrixOf (core.relabel sigma) 0 (k + 1)) with hLe | hContra
    · exact hLe
    exact absurd (hMin0 _)
      (Nat.not_le.mpr ((relabelKey_swap core sigma 0 k hk2 (by omega)
        (by omega) (by omega)).1 hContra))
  have hCut1 : ∀ k, 2 ≤ k → k + 1 < n →
      matrixOf (core.relabel sigma) 0 k =
          matrixOf (core.relabel sigma) 0 (k + 1) →
        matrixOf (core.relabel sigma) 1 k ≤
          matrixOf (core.relabel sigma) 1 (k + 1) := by
    intro k hk hk2 hFlat
    rcases le_or_gt (matrixOf (core.relabel sigma) 1 k)
      (matrixOf (core.relabel sigma) 1 (k + 1)) with hLe | hContra
    · exact hLe
    have hKeep :=
      (relabelKey_swap core sigma 0 k hk2 (by omega) (by omega) (by omega)).2
        hFlat
    have hDrop :=
      (relabelKey_swap core sigma 1 k hk2 (by omega) (by omega) (by omega)).1
        hContra
    exact absurd (hMin1 _ hKeep) (Nat.not_le.mpr hDrop)
  refine ⟨sigma, ExplicitPotential.Core.relabel_connected core sigma hConnected,
    ExplicitPotential.Core.incidenceDegree_relabel_apply core sigma hDegree,
    canonicalPrefix_rowsOf _ _ hCut0 hCut1, ?_⟩
  intro i j
  exact (ExplicitPotential.Core.pairMultiplicity_relabel core sigma i j).symm

end Utilities.Certificate.CubicMatrixReplay
