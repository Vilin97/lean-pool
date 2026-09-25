/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CorePairMultiplicity

/-!
# A row-by-row replay tree for loopless regular multiplicity matrices

A finite classifier for loopless regular cores can work with the unordered
vertex-pair multiplicity table.  This module supplies its generic
*completeness* device: a compact finite witness that some displayed list of
tables exhausts every table which can arise.

This module is that device, and nothing else.  It defines

* `boundedCompositions`, the weak compositions of one remaining degree into
  the capacities of the still-unvisited vertices;
* `Follows`, the statement that a list of strict-upper-triangular rows is
  produced by the row-by-row branching;
* `ReplayTree`, a fuelled sibling-chain tree whose branches are keyed by
  those compositions, with a Boolean checker `validCheck`;
* `rowsOf` / `entryOf`, the translation between a multiplicity matrix and its
  row list, and `matrixOf`, the multiplicity matrix of an ordered core;
* `MatrixConnected`, the decidable cut form of
  `ExplicitPotential.Core.Connected` read off the table.

The two results that matter are `validCheck_sound` — a tree passing the
Boolean check accepts *every* row list produced by the branching — and
`follows_capsOf_rowsOf` — every symmetric, zero-diagonal, constant-row-sum
matrix does follow the branching.  Exhaustiveness is proved from the
weak-composition membership characterization `mem_boundedCompositions`; there
is no `native_decide`, no `decide` over endpoint functions, and no search.

Nothing here is specific to eight vertices or to degree three.  The vertex
count and the common degree are parameters, so one generated tree shape serves
the genus-four (`6/9`) and genus-five (`8/12`) classifiers.

Disconnected tables satisfy the same row-sum conditions and therefore also
reach a leaf.  A generated leaf may carry no atlas target for those; the
decoding hypothesis of the composed statements only fires on tables satisfying
`MatrixConnected`.

This is the generic checker side only.  Application-specific datasets, leaf
decoders, and classifier handoff theorems belong in their application layer.
-/

@[expose] public section

namespace Utilities.Certificate.CubicMatrixReplay

open Utilities.Certificate
open Utilities
open ExplicitPotential
open Utilities.Certificate.CubicMatrixReplay

/-! ## Weak compositions with capacities -/

/-- All ways of splitting `total` into `capacities.length` natural summands,
in order, with the `k`-th summand bounded by the `k`-th capacity.  This is the
branch set of one vertex of the completion tree: the remaining degree of the
current vertex is distributed over the vertices that come after it. -/
def boundedCompositions (total : ℕ) : List ℕ → List (List ℕ)
  | [] => if total = 0 then [[]] else []
  | capacity :: capacities =>
      (List.range (min total capacity + 1)).flatMap fun part =>
        (boundedCompositions (total - part) capacities).map (part :: ·)

/-- `boundedCompositions` enumerates exactly the capacity-bounded weak
compositions.  This is the finite combinatorial fact that makes the tree
branching exhaustive. -/
theorem mem_boundedCompositions {total : ℕ} :
    ∀ {capacities parts : List ℕ},
      parts ∈ boundedCompositions total capacities ↔
        List.Forall₂ (· ≤ ·) parts capacities ∧ parts.sum = total := by
  intro capacities
  induction capacities generalizing total with
  | nil =>
      intro parts
      constructor
      · intro hMem
        by_cases hTotal : total = 0
        · subst hTotal
          have hNil : parts = [] := by
            simpa [boundedCompositions] using hMem
          subst hNil
          exact ⟨List.Forall₂.nil, rfl⟩
        · simp [boundedCompositions, hTotal] at hMem
      · rintro ⟨hForall, hSum⟩
        cases hForall
        simp only [List.sum_nil] at hSum
        simp [boundedCompositions, ← hSum]
  | cons capacity capacities ih =>
      intro parts
      simp only [boundedCompositions, List.mem_flatMap, List.mem_map,
        List.mem_range]
      constructor
      · rintro ⟨part, hPart, tail, hTail, rfl⟩
        rw [ih] at hTail
        obtain ⟨hForall, hSum⟩ := hTail
        have hMin : part ≤ min total capacity := Nat.lt_succ_iff.mp hPart
        have hCap : part ≤ capacity :=
          le_trans hMin (min_le_right total capacity)
        have hLe : part ≤ total := le_trans hMin (min_le_left total capacity)
        refine ⟨List.Forall₂.cons hCap hForall, ?_⟩
        simp only [List.sum_cons, hSum]
        omega
      · rintro ⟨hForall, hSum⟩
        cases parts with
        | nil => cases hForall
        | cons part tail =>
            cases hForall with
            | cons hHead hTail =>
                simp only [List.sum_cons] at hSum
                refine ⟨part, ?_, tail, ?_, rfl⟩
                · have hMin : part ≤ min total capacity :=
                    le_min (by omega) hHead
                  omega
                · rw [ih]
                  exact ⟨hTail, by omega⟩

/-! ## The branching relation -/

/-- `Follows capacities rows` says that `rows` is the strict-upper-triangular
row list of a matrix built by the row-by-row completion, starting from the
residual degree vector `capacities`.  The head capacity is the remaining
degree of the current vertex; the chosen row is a capacity-bounded weak
composition of it, and the tail capacities are decreased accordingly. -/
inductive Follows : List ℕ → List (List ℕ) → Prop
  | nil : Follows [] []
  | cons {remaining : ℕ} {capacities parts : List ℕ}
      {rows : List (List ℕ)}
      (hParts : parts ∈ boundedCompositions remaining capacities)
      (hRows : Follows (List.zipWith (· - ·) capacities parts) rows) :
      Follows (remaining :: capacities) (parts :: rows)

/-! ## The replay tree -/

/-- A fuelled row-by-row completion tree.  `branch` stores the composition
that keys this child together with the child itself and the next sibling, so
the sibling chain at one vertex is spelled out linearly; `reject` terminates a
sibling chain, and `accept` carries the payload of a completed matrix. -/
inductive ReplayTree (α : Type*) where
  | accept : α → ReplayTree α
  | reject : ReplayTree α
  | branch : List ℕ → ReplayTree α → ReplayTree α → ReplayTree α

/-- Check one sibling chain against the list `todo` of compositions it must
cover.  The chain must list them in exactly the enumeration order of
`boundedCompositions`; `sub` checks each child against the decreased
capacities and the extended path. -/
def chainCheck {α : Type*}
    (sub : ReplayTree α → List ℕ → List (List ℕ) → Bool)
    (capacities : List ℕ) (path : List (List ℕ)) :
    ReplayTree α → List (List ℕ) → Bool
  | _, [] => true
  | .branch key child sibling, part :: todo =>
      (decide (key = part) &&
          sub child (List.zipWith (· - ·) capacities part) (path ++ [part]))
        && chainCheck sub capacities path sibling todo
  | _, _ :: _ => false

/-- The Boolean replay check.  `fuel` bounds the number of vertices still to
be visited, `capacities` is the residual degree vector, and `path` records the
rows chosen so far.  At a completed matrix the caller-supplied `leafCheck`
inspects the path and the stored payload; at an unfinished vertex the tree
must be a sibling chain covering every capacity-bounded weak composition of
the head capacity. -/
def validCheck {α : Type*} (leafCheck : List (List ℕ) → α → Bool) :
    ℕ → ReplayTree α → List ℕ → List (List ℕ) → Bool
  | 0, _, _, _ => false
  | _ + 1, .accept value, [], path => leafCheck path value
  | _ + 1, _, [], _ => false
  | fuel + 1, tree, capacity :: capacities, path =>
      chainCheck (fun child caps subPath =>
          validCheck leafCheck fuel child caps subPath)
        capacities path tree (boundedCompositions capacity capacities)

/-- Every composition listed in `todo` is genuinely handled by a checked
sibling chain.  The argument is an induction along the chain, so no search
over the tree is performed. -/
theorem chainCheck_sound {α : Type*}
    {sub : ReplayTree α → List ℕ → List (List ℕ) → Bool}
    {Good : List (List ℕ) → Prop} {capacities : List ℕ}
    {path rows : List (List ℕ)} {part : List ℕ}
    (hSub : ∀ (child : ReplayTree α) (caps : List ℕ)
        (subPath : List (List ℕ)),
      sub child caps subPath = true → Follows caps rows →
        Good (subPath ++ rows))
    (hFollows : Follows (List.zipWith (· - ·) capacities part) rows) :
    ∀ (tree : ReplayTree α) (todo : List (List ℕ)),
      chainCheck sub capacities path tree todo = true → part ∈ todo →
        Good (path ++ part :: rows) := by
  intro tree todo
  induction todo generalizing tree with
  | nil => intro _ hMem; exact absurd hMem (List.not_mem_nil)
  | cons head todo ih =>
      intro hCheck hMem
      cases tree with
      | accept _ => simp [chainCheck] at hCheck
      | reject => simp [chainCheck] at hCheck
      | branch key child sibling =>
          simp only [chainCheck, Bool.and_eq_true,
            decide_eq_true_eq] at hCheck
          obtain ⟨⟨hKey, hChild⟩, hSibling⟩ := hCheck
          rcases List.mem_cons.mp hMem with hEq | hRest
          · subst hEq
            subst hKey
            have := hSub child _ _ hChild hFollows
            simpa using this
          · exact ih sibling hSibling hRest

/-- **Replay soundness.**  A tree passing `validCheck` accepts every row list
produced by the branching, and its leaf check succeeds on the corresponding
path.  Nothing about the tree's *shape* is assumed beyond the Boolean check;
in particular exhaustiveness of the branching comes entirely from
`mem_boundedCompositions`. -/
theorem validCheck_sound {α : Type*} (leafCheck : List (List ℕ) → α → Bool) :
    ∀ (rows : List (List ℕ)) (fuel : ℕ) (tree : ReplayTree α)
      (capacities : List ℕ) (path : List (List ℕ)),
      validCheck leafCheck fuel tree capacities path = true →
      Follows capacities rows →
        ∃ value : α, leafCheck (path ++ rows) value = true := by
  intro rows
  induction rows with
  | nil =>
      intro fuel tree capacities path hValid hFollows
      cases hFollows
      cases fuel with
      | zero => simp [validCheck] at hValid
      | succ fuel =>
          cases tree with
          | accept value =>
              exact ⟨value, by simpa [validCheck] using hValid⟩
          | reject => simp [validCheck] at hValid
          | branch _ _ _ => simp [validCheck] at hValid
  | cons parts rows ih =>
      intro fuel tree capacities path hValid hFollows
      cases hFollows with
      | cons hParts hRows =>
          rename_i remaining capacities
          cases fuel with
          | zero => simp [validCheck] at hValid
          | succ fuel =>
              refine chainCheck_sound (Good := fun p =>
                  ∃ value : α, leafCheck p value = true)
                (fun child caps subPath hChild hCaps =>
                  ih fuel child caps subPath hChild hCaps)
                hRows tree (boundedCompositions remaining capacities)
                ?_ hParts
              simpa [validCheck] using hValid

/-! ## Multiplicity matrices and their row lists -/

/-- The finite conditions defining a loopless `deg`-regular multiplicity
matrix on the vertex set `{0, …, n-1}`.  Entries outside that range are
ignored, so the matrix may be given as a total function. -/
structure Conditions (n deg : ℕ) (M : ℕ → ℕ → ℕ) : Prop where
  /-- The table is symmetric. -/
  symm : ∀ i j, i < n → j < n → M i j = M j i
  /-- No vertex carries a loop. -/
  diag : ∀ i, i < n → M i i = 0
  /-- Every vertex has degree `deg`. -/
  rowSum : ∀ i, i < n → ∑ j ∈ Finset.range n, M i j = deg

/-- The strict-upper-triangular row list of `M`: `rowsOf M i len` lists the
rows of vertices `i, …, i + len - 1`, each row recording the multiplicities to
the strictly later vertices in that range. -/
def rowsOf (M : ℕ → ℕ → ℕ) : ℕ → ℕ → List (List ℕ)
  | _, 0 => []
  | i, len + 1 =>
      ((List.range' (i + 1) len).map fun j => M i j) :: rowsOf M (i + 1) len

/-- The residual degree vector of vertices `i, …, i + len - 1` after the rows
of vertices `0, …, i - 1` have been fixed. -/
def capsOf (deg : ℕ) (M : ℕ → ℕ → ℕ) (i len : ℕ) : List ℕ :=
  (List.range' i len).map fun j => deg - ∑ j' ∈ Finset.range i, M j' j

/-- At the root the residual degree vector is constant. -/
theorem capsOf_zero (deg : ℕ) (M : ℕ → ℕ → ℕ) (n : ℕ) :
    capsOf deg M 0 n = List.replicate n deg := by
  simp [capsOf, List.map_const']

/-- Pointwise `zipWith` of two maps over one list. -/
private theorem zipWith_map_map {α β γ δ : Type*} (f : β → γ → δ)
    (g : α → β) (h : α → γ) (l : List α) :
    List.zipWith f (l.map g) (l.map h) = l.map fun x => f (g x) (h x) := by
  induction l with
  | nil => rfl
  | cons a l ih => simp [ih]

/-- Pointwise `Forall₂` of two maps over one list. -/
private theorem forall₂_map_map {α β γ : Type*} (R : β → γ → Prop)
    (g : α → β) (h : α → γ) (l : List α) (hR : ∀ x ∈ l, R (g x) (h x)) :
    List.Forall₂ R (l.map g) (l.map h) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a l ih =>
      exact List.Forall₂.cons (hR a (List.mem_cons_self ..))
        (ih fun x hx => hR x (List.mem_cons_of_mem _ hx))

/-- The sum of a function over an arithmetic range list is the corresponding
`Finset.Ico` sum. -/
private theorem sum_map_range' (f : ℕ → ℕ) :
    ∀ (b a : ℕ), ((List.range' a b).map f).sum
      = ∑ j ∈ Finset.Ico a (a + b), f j := by
  intro b
  induction b with
  | zero => intro a; simp
  | succ b ih =>
      intro a
      rw [List.range'_succ]
      simp only [List.map_cons, List.sum_cons, ih (a + 1)]
      have hSplit : ∑ j ∈ Finset.Ico a (a + (b + 1)), f j
          = f a + ∑ j ∈ Finset.Ico (a + 1) (a + (b + 1)), f j :=
        Finset.sum_eq_sum_Ico_succ_bot (by omega) f
      have hIndex : a + 1 + b = a + (b + 1) := by omega
      rw [hSplit, hIndex]

/-- Column sums agree with row sums, by symmetry. -/
private theorem colSum {n deg : ℕ} {M : ℕ → ℕ → ℕ} (h : Conditions n deg M)
    (j : ℕ) (hj : j < n) : ∑ j' ∈ Finset.range n, M j' j = deg := by
  rw [← h.rowSum j hj]
  exact Finset.sum_congr rfl fun j' hj' =>
    h.symm j' j (Finset.mem_range.mp hj') hj

/-- A partial column sum never exceeds the common degree. -/
private theorem partialColSum_le {n deg : ℕ} {M : ℕ → ℕ → ℕ}
    (h : Conditions n deg M) (i j : ℕ) (hi : i ≤ n) (hj : j < n) :
    ∑ j' ∈ Finset.range i, M j' j ≤ deg := by
  have hSubset : Finset.range i ⊆ Finset.range n := by
    intro x hx
    rw [Finset.mem_range] at hx ⊢
    omega
  rw [← colSum h j hj]
  exact Finset.sum_le_sum_of_subset hSubset

/-- **Branching completeness.**  Every loopless `deg`-regular multiplicity
matrix follows the row-by-row branching, starting from any prefix position.
This is the statement that the tree's branch sets miss nothing. -/
theorem follows_capsOf_rowsOf {n deg : ℕ} {M : ℕ → ℕ → ℕ}
    (h : Conditions n deg M) :
    ∀ (len i : ℕ), i + len = n →
      Follows (capsOf deg M i len) (rowsOf M i len) := by
  intro len
  induction len with
  | zero => intro i _; simp [capsOf, rowsOf]; exact Follows.nil
  | succ len ih =>
      intro i hSum
      have hi : i < n := by omega
      have hEnd : i + 1 + len = n := by omega
      have hCaps : capsOf deg M i (len + 1)
          = (deg - ∑ j' ∈ Finset.range i, M j' i) ::
              (List.range' (i + 1) len).map
                (fun j => deg - ∑ j' ∈ Finset.range i, M j' j) := by
        simp [capsOf, List.range'_succ]
      have hRows : rowsOf M i (len + 1)
          = ((List.range' (i + 1) len).map fun j => M i j)
              :: rowsOf M (i + 1) len := rfl
      rw [hCaps, hRows]
      -- membership in the branch set of vertex `i`
      have hMemRange : ∀ j ∈ List.range' (i + 1) len, i < j ∧ j < n := by
        intro j hj
        rw [List.mem_range'_1] at hj
        omega
      have hBound : List.Forall₂ (· ≤ ·)
          ((List.range' (i + 1) len).map fun j => M i j)
          ((List.range' (i + 1) len).map
            fun j => deg - ∑ j' ∈ Finset.range i, M j' j) := by
        refine forall₂_map_map _ _ _ _ fun j hj => ?_
        obtain ⟨hij, hjn⟩ := hMemRange j hj
        have hPartial : ∑ j' ∈ Finset.range (i + 1), M j' j ≤ deg :=
          partialColSum_le h (i + 1) j (by omega) hjn
        rw [Finset.sum_range_succ] at hPartial
        omega
      have hRowSum : ((List.range' (i + 1) len).map fun j => M i j).sum
          = deg - ∑ j' ∈ Finset.range i, M j' i := by
        rw [sum_map_range' (fun j => M i j) len (i + 1), hEnd]
        have hSplit : ∑ j ∈ Finset.Ico 0 i, M i j
            + ∑ j ∈ Finset.Ico i n, M i j = ∑ j ∈ Finset.Ico 0 n, M i j :=
          Finset.sum_Ico_consecutive _ (Nat.zero_le i) (le_of_lt hi)
        have hBot : ∑ j ∈ Finset.Ico i n, M i j
            = M i i + ∑ j ∈ Finset.Ico (i + 1) n, M i j :=
          Finset.sum_eq_sum_Ico_succ_bot hi _
        have hDiag : M i i = 0 := h.diag i hi
        have hTotal : ∑ j ∈ Finset.Ico 0 n, M i j = deg := by
          rw [← Finset.range_eq_Ico]; exact h.rowSum i hi
        have hLower : ∑ j' ∈ Finset.range i, M j' i
            = ∑ j ∈ Finset.Ico 0 i, M i j := by
          rw [Finset.range_eq_Ico]
          exact Finset.sum_congr rfl fun j' hj' =>
            h.symm j' i (by
              have := Finset.mem_Ico.mp hj'
              omega) hi
        rw [hLower]
        omega
      have hStep : List.zipWith (· - ·)
          ((List.range' (i + 1) len).map
            fun j => deg - ∑ j' ∈ Finset.range i, M j' j)
          ((List.range' (i + 1) len).map fun j => M i j)
          = capsOf deg M (i + 1) len := by
        rw [zipWith_map_map]
        refine List.map_congr_left fun j _ => ?_
        rw [Finset.sum_range_succ, Nat.sub_sub]
      refine Follows.cons ?_ ?_
      · rw [mem_boundedCompositions]
        exact ⟨hBound, hRowSum⟩
      · rw [hStep]
        exact ih (i + 1) hEnd

/-! ## Reading a matrix entry back off the row list -/

/-- The entry of a symmetric matrix recovered from its strict-upper-triangular
row list. -/
def entryOf (rows : List (List ℕ)) (i j : ℕ) : ℕ :=
  if i < j then (rows.getD i []).getD (j - i - 1) 0
  else if j < i then (rows.getD j []).getD (i - j - 1) 0
  else 0

/-- The `k`-th row of `rowsOf M a len`. -/
private theorem getD_rowsOf (M : ℕ → ℕ → ℕ) :
    ∀ (len a k : ℕ), k < len →
      (rowsOf M a len).getD k []
        = (List.range' (a + k + 1) (len - 1 - k)).map
            fun j => M (a + k) j := by
  intro len
  induction len with
  | zero => intro a k hk; omega
  | succ len ih =>
      intro a k hk
      cases k with
      | zero => simp [rowsOf]
      | succ k =>
          have hkk : k < len := by omega
          have hStep : (rowsOf M a (len + 1)).getD (k + 1) []
              = (rowsOf M (a + 1) len).getD k [] := rfl
          rw [hStep, ih (a + 1) k hkk]
          have hIndex : a + 1 + k = a + (k + 1) := by omega
          have hLen : len - 1 - k = len + 1 - 1 - (k + 1) := by omega
          rw [hIndex, hLen]

/-- Reading an arithmetic range list at a valid offset. -/
private theorem getD_map_range' (f : ℕ → ℕ) (a b t : ℕ) (ht : t < b) :
    (((List.range' a b).map f).getD t 0) = f (a + t) := by
  have hLen : t < ((List.range' a b).map f).length := by
    simpa using ht
  rw [List.getD_eq_getElem _ _ hLen]
  simp

/-- **Round trip.**  On the vertex range the row list determines the matrix.
A generated leaf may therefore be checked against the path alone. -/
theorem entryOf_rowsOf {n deg : ℕ} {M : ℕ → ℕ → ℕ} (h : Conditions n deg M)
    (i j : ℕ) (hi : i < n) (hj : j < n) :
    entryOf (rowsOf M 0 n) i j = M i j := by
  rcases lt_trichotomy i j with hlt | heq | hgt
  · have hRow : (rowsOf M 0 n).getD i []
        = (List.range' (0 + i + 1) (n - 1 - i)).map fun j => M (0 + i) j :=
      getD_rowsOf M n 0 i hi
    have hOffset : j - i - 1 < n - 1 - i := by omega
    simp only [entryOf, if_pos hlt, hRow, Nat.zero_add]
    rw [getD_map_range' _ _ _ _ hOffset]
    have hIndex : i + 1 + (j - i - 1) = j := by omega
    rw [hIndex]
  · subst heq
    simp only [entryOf, lt_self_iff_false, if_false]
    exact (h.diag i hi).symm
  · have hRow : (rowsOf M 0 n).getD j []
        = (List.range' (0 + j + 1) (n - 1 - j)).map fun i => M (0 + j) i :=
      getD_rowsOf M n 0 j hj
    have hOffset : i - j - 1 < n - 1 - j := by omega
    simp only [entryOf, if_neg (by omega : ¬ i < j), if_pos hgt, hRow,
      Nat.zero_add]
    rw [getD_map_range' _ _ _ _ hOffset]
    have hIndex : j + 1 + (i - j - 1) = i := by omega
    rw [hIndex]
    exact (h.symm i j hi hj).symm

/-! ## Multiplicity matrix of an ordered core -/

/-- The unordered vertex-pair multiplicity table of an ordered core, as a
total function on `ℕ`. -/
def matrixOf {n p : ℕ} (core : Core n p) (i j : ℕ) : ℕ :=
  if hi : i < n then
    if hj : j < n then core.pairMultiplicity ⟨i, hi⟩ ⟨j, hj⟩ else 0
  else 0

/-- The multiplicity table of a loopless `deg`-regular ordered core satisfies
the finite matrix conditions. -/
theorem conditions_matrixOf {n p deg : ℕ} (core : Core n p)
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge)
    (hDegree : ∀ vertex : Fin n, core.incidenceDegree vertex = deg) :
    Conditions n deg (matrixOf core) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hi hj
    simp only [matrixOf, dif_pos hi, dif_pos hj]
    exact Core.pairMultiplicity_comm core ⟨i, hi⟩ ⟨j, hj⟩
  · intro i hi
    simp only [matrixOf, dif_pos hi]
    exact Core.pairMultiplicity_self_eq_zero core hLoopless ⟨i, hi⟩
  · intro i hi
    have hRange : ∑ j ∈ Finset.range n, matrixOf core i j
        = ∑ j : Fin n, matrixOf core i (j : ℕ) :=
      (Fin.sum_univ_eq_sum_range (fun j => matrixOf core i j) n).symm
    rw [hRange]
    have hEntry : ∀ j : Fin n,
        matrixOf core i (j : ℕ) = core.pairMultiplicity ⟨i, hi⟩ j := by
      intro j
      simp only [matrixOf, dif_pos hi, dif_pos j.isLt]
    simp only [hEntry]
    rw [sum_pairMultiplicity_eq_incidenceDegree core hLoopless ⟨i, hi⟩]
    exact hDegree ⟨i, hi⟩

/-! ## Connectedness at the level of the table

Disconnected matrices also satisfy `Conditions` and therefore also follow the
branching, so the tree must reach them too.  A generated leaf is allowed to
carry no atlas target in that case; the decoding hypothesis below is only
required to fire on connected tables.  `MatrixConnected` is the cut form of
`ExplicitPotential.Core.Connected` transported to the multiplicity table. -/

/-- Cut connectedness of a multiplicity table on the vertex range.  Cuts range
over `(Finset.range size).powerset` rather than over all of `Finset ℕ`, so the
predicate is decidable and a generated leaf record may discharge it by
evaluation. -/
def MatrixConnected (size : ℕ) (M : ℕ → ℕ → ℕ) : Prop :=
  ∀ S ∈ (Finset.range size).powerset,
    (∃ v ∈ S, ∃ w ∈ Finset.range size, w ∉ S) →
      ∃ i ∈ S, ∃ j ∈ Finset.range size, j ∉ S ∧ 0 < M i j

/-- Cut connectedness of a bounded table is a finite check. -/
instance decidableMatrixConnected (size : ℕ) (M : ℕ → ℕ → ℕ) :
    Decidable (MatrixConnected size M) := by
  unfold MatrixConnected
  infer_instance

/-- Cut connectedness only reads entries inside the vertex range. -/
theorem matrixConnected_congr {size : ℕ} {M M' : ℕ → ℕ → ℕ}
    (hEntries : ∀ i j, i < size → j < size → M i j = M' i j)
    (hM : MatrixConnected size M) : MatrixConnected size M' := by
  intro S hSubset hWitness
  obtain ⟨i, hi, j, hj, hjS, hPos⟩ := hM S hSubset hWitness
  have hiRange : i < size :=
    Finset.mem_range.mp (Finset.mem_powerset.mp hSubset hi)
  have hjRange : j < size := Finset.mem_range.mp hj
  exact ⟨i, hi, j, hj, hjS, by rwa [hEntries i j hiRange hjRange] at hPos⟩

/-- Core cut connectedness transports to the multiplicity table. -/
theorem matrixConnected_matrixOf {n p : ℕ} (core : Core n p)
    (hConnected : core.Connected) : MatrixConnected n (matrixOf core) := by
  classical
  intro S hSubset hWitness
  obtain ⟨v, hv, w, hw, hwS⟩ := hWitness
  have hvRange : v < n :=
    Finset.mem_range.mp (Finset.mem_powerset.mp hSubset hv)
  have hwRange : w < n := Finset.mem_range.mp hw
  set T : Finset (Fin n) := Finset.univ.filter fun x : Fin n => (x : ℕ) ∈ S
    with hT
  have hvT : (⟨v, hvRange⟩ : Fin n) ∈ T := by simp [hT, hv]
  have hwT : (⟨w, hwRange⟩ : Fin n) ∉ T := by simp [hT, hwS]
  obtain ⟨edge, hEdge⟩ := hConnected T ⟨⟨v, hvRange⟩, ⟨w, hwRange⟩, hvT, hwT⟩
  have hMem : ∀ x : Fin n, x ∈ T ↔ (x : ℕ) ∈ S := by
    intro x; simp [hT]
  rcases hEdge with ⟨hIn, hOut⟩ | ⟨hIn, hOut⟩
  · refine ⟨(core.tail edge : ℕ), (hMem _).mp hIn, (core.head edge : ℕ),
      Finset.mem_range.mpr (core.head edge).isLt,
      fun hAbsurd => hOut ((hMem _).mpr hAbsurd), ?_⟩
    simpa [matrixOf, (core.tail edge).isLt, (core.head edge).isLt] using
      pairMultiplicity_endpoints_pos core edge
  · refine ⟨(core.head edge : ℕ), (hMem _).mp hIn, (core.tail edge : ℕ),
      Finset.mem_range.mpr (core.tail edge).isLt,
      fun hAbsurd => hOut ((hMem _).mpr hAbsurd), ?_⟩
    have hPos := pairMultiplicity_endpoints_pos core edge
    rw [Core.pairMultiplicity_comm] at hPos
    simpa [matrixOf, (core.tail edge).isLt, (core.head edge).isLt] using hPos

end Utilities.Certificate.CubicMatrixReplay
