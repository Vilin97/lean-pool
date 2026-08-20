/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie and Jack McCarthy
-/
import LeanPool.ClassificationOfSurfaces.FiniteCyclicWordReduction

/-!
# Terminal finite-cyclic word normalization

This file discharges the final completed-block seam of the Gallier--Xu normalization argument.
Boundary loops are commuted behind the closed-surface blocks, handles are converted to crosscaps
when a crosscap is present, and the resulting ordered word is signed-relabelled to the single
project-owned `NormalForm.canonicalPresentation`.
-/

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

open SurfaceCellComplex

namespace WordReduction

namespace Pairing

namespace CompletedBlock

/-- The distinct-name spine respects block-sequence concatenation. -/
@[simp]
theorem sequenceNames_append {n : ℕ}
    (left right : List (CompletedBlock n)) :
    sequenceNames (left ++ right) =
      sequenceNames left ++ sequenceNames right := by
  simp [sequenceNames]

/-- A name occurs in the exact block word precisely when it occurs in the block name spine. -/
@[simp]
theorem mem_sequenceWord_edge_iff_mem_sequenceNames {n : ℕ}
    (blocks : List (CompletedBlock n)) (edge : Fin n) :
    edge ∈ (sequenceWord blocks).map edgeOfDart ↔
      edge ∈ sequenceNames blocks := by
  induction blocks with
  | nil =>
      simp
  | cons block blocks ih =>
      simp [ih, mem_map_edgeOfDart_word_iff,
        mem_names_iff_mem_edges]

/-- Permuting completed blocks permutes their exact concatenated words. -/
theorem sequenceWord_perm {n : ℕ}
    {left right : List (CompletedBlock n)}
    (hperm : left.Perm right) :
    (sequenceWord left).Perm (sequenceWord right) := by
  simpa [sequenceWord] using
    (hperm.map word).flatten

/-- Permuting completed blocks permutes their distinct-name spines. -/
theorem sequenceNames_perm {n : ℕ}
    {left right : List (CompletedBlock n)}
    (hperm : left.Perm right) :
    (sequenceNames left).Perm (sequenceNames right) := by
  simpa [sequenceNames] using
    (hperm.map names).flatten

/-- Permuting completed blocks preserves the unoriented edge-occurrence multiset. -/
theorem sequenceEdgeWord_perm {n : ℕ}
    {left right : List (CompletedBlock n)}
    (hperm : left.Perm right) :
    ((sequenceWord left).map edgeOfDart).Perm
      ((sequenceWord right).map edgeOfDart) :=
  (sequenceWord_perm hperm).map edgeOfDart

/-- Surface validity transports across a permutation of completed blocks. -/
theorem sequenceWord_isSurfaceValid_of_perm {n : ℕ}
    {left right : List (CompletedBlock n)}
    (hperm : left.Perm right)
    (valid :
      (Dyck.oneFace (sequenceWord left)).IsSurfaceValid) :
    (Dyck.oneFace (sequenceWord right)).IsSurfaceValid :=
  Dyck.oneFace_isSurfaceValid_of_edgePerm
    (sequenceEdgeWord_perm hperm) valid

end CompletedBlock

namespace TerminalNormalization

/-- Boolean classifier for completed boundary-loop blocks. -/
abbrev isBoundary {n : ℕ} : CompletedBlock n → Bool
  | .boundary _ _ _ _ => true
  | _ => false

/-- Boolean classifier for completed crosscap blocks. -/
abbrev isCrosscap {n : ℕ} : CompletedBlock n → Bool
  | .crosscap _ _ => true
  | _ => false

/-- Boolean classifier for completed handle blocks. -/
abbrev isHandle {n : ℕ} : CompletedBlock n → Bool
  | .handle _ _ => true
  | _ => false

/-- Closed-surface blocks, retaining their original relative order. -/
def closedBlocks {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    List (CompletedBlock n) :=
  blocks.filter fun block => !isBoundary block

/-- Boundary-loop blocks, retaining their original relative order. -/
def boundaryBlocks {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    List (CompletedBlock n) :=
  blocks.filter isBoundary

/-- Stable partition with every boundary-loop block placed last. -/
def boundariesLast {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    List (CompletedBlock n) :=
  closedBlocks blocks ++ boundaryBlocks blocks

/-- Replace every completed handle block by the two crosscap blocks contributed in the presence
of a fixed ambient crosscap. -/
def handlesToCrosscaps {n : ℕ} :
    List (CompletedBlock n) → List (CompletedBlock n)
  | [] => []
  | .handle first second :: blocks =>
      .crosscap second false ::
        .crosscap first false ::
          handlesToCrosscaps blocks
  | block :: blocks =>
      block :: handlesToCrosscaps blocks

/-- Canonical orientable edge names in the same order as the canonical handle and boundary
blocks. -/
def orientableTargetNames (p n : ℕ) :
    List (NormalForm.OrientableEdge p n) :=
  (List.ofFn fun i : Fin p =>
      [NormalForm.OrientableEdge.a i,
        NormalForm.OrientableEdge.b i]).flatten ++
    (List.ofFn fun i : Fin n =>
      [NormalForm.OrientableEdge.c i,
        NormalForm.OrientableEdge.h i]).flatten

/-- Canonical nonorientable edge names in crosscap-then-boundary order. -/
def nonOrientableTargetNames (p n : ℕ) :
    List (NormalForm.NonOrientableEdge p n) :=
  (List.ofFn fun i : Fin p =>
      [NormalForm.NonOrientableEdge.a i]).flatten ++
    (List.ofFn fun i : Fin n =>
      [NormalForm.NonOrientableEdge.c i,
        NormalForm.NonOrientableEdge.h i]).flatten

/-- The canonical orientable name enumeration contains no duplicate edge. -/
theorem orientableTargetNames_nodup (p n : ℕ) :
    (orientableTargetNames p n).Nodup := by
  classical
  unfold orientableTargetNames
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_flatten]
    constructor
    · intro names hnames
      simp only [List.mem_ofFn] at hnames
      rcases hnames with ⟨i, rfl⟩
      simp
    · rw [List.pairwise_ofFn]
      intro i j hij
      simp only [List.Disjoint, List.mem_cons, List.not_mem_nil, or_false, imp_false, not_or,
        forall_eq_or_imp, NormalForm.OrientableEdge.a.injEq, reduceCtorEq, not_false_eq_true,
        and_true, forall_eq, NormalForm.OrientableEdge.b.injEq, true_and, and_self]
      exact Fin.ne_of_lt hij
  · rw [List.nodup_flatten]
    constructor
    · intro names hnames
      simp only [List.mem_ofFn] at hnames
      rcases hnames with ⟨i, rfl⟩
      simp
    · rw [List.pairwise_ofFn]
      intro i j hij
      simp only [List.Disjoint, List.mem_cons, List.not_mem_nil, or_false, imp_false, not_or,
        forall_eq_or_imp, NormalForm.OrientableEdge.c.injEq, reduceCtorEq, not_false_eq_true,
        and_true, forall_eq, NormalForm.OrientableEdge.h.injEq, true_and, and_self]
      exact Fin.ne_of_lt hij
  · intro x hx y hy
    simp only [List.mem_flatten, List.mem_ofFn] at hx hy
    rcases hx with ⟨names, ⟨i, hi⟩, hx⟩
    subst names
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hy with ⟨names, ⟨j, hj⟩, hy⟩
    subst names
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hx with rfl | rfl <;>
      rcases hy with rfl | rfl <;>
      simp

/-- Every canonical orientable edge occurs in its name enumeration. -/
theorem mem_orientableTargetNames (p n : ℕ)
    (edge : NormalForm.OrientableEdge p n) :
    edge ∈ orientableTargetNames p n := by
  cases edge <;>
    simp [orientableTargetNames]

/-- The canonical nonorientable name enumeration contains no duplicate edge. -/
theorem nonOrientableTargetNames_nodup (p n : ℕ) :
    (nonOrientableTargetNames p n).Nodup := by
  classical
  unfold nonOrientableTargetNames
  rw [List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · rw [List.nodup_flatten]
    constructor
    · intro names hnames
      simp only [List.mem_ofFn] at hnames
      rcases hnames with ⟨i, rfl⟩
      simp
    · rw [List.pairwise_ofFn]
      intro i j hij
      simp only [List.Disjoint, List.mem_cons, List.not_mem_nil, or_false, imp_false, forall_eq,
        NormalForm.NonOrientableEdge.a.injEq]
      exact Fin.ne_of_lt hij
  · rw [List.nodup_flatten]
    constructor
    · intro names hnames
      simp only [List.mem_ofFn] at hnames
      rcases hnames with ⟨i, rfl⟩
      simp
    · rw [List.pairwise_ofFn]
      intro i j hij
      simp only [List.Disjoint, List.mem_cons, List.not_mem_nil, or_false, imp_false, not_or,
        forall_eq_or_imp, NormalForm.NonOrientableEdge.c.injEq, reduceCtorEq, not_false_eq_true,
        and_true, forall_eq, NormalForm.NonOrientableEdge.h.injEq, true_and, and_self]
      exact Fin.ne_of_lt hij
  · intro x hx y hy
    simp only [List.mem_flatten, List.mem_ofFn] at hx hy
    rcases hx with ⟨names, ⟨i, hi⟩, hx⟩
    subst names
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hy with ⟨names, ⟨j, hj⟩, hy⟩
    subst names
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
    subst x
    rcases hy with rfl | rfl <;>
      simp

/-- Every canonical nonorientable edge occurs in its name enumeration. -/
theorem mem_nonOrientableTargetNames (p n : ℕ)
    (edge : NormalForm.NonOrientableEdge p n) :
    edge ∈ nonOrientableTargetNames p n := by
  cases edge <;>
    simp [nonOrientableTargetNames]

@[simp]
theorem orientableTargetNames_length (p n : ℕ) :
    (orientableTargetNames p n).length =
      2 * p + 2 * n := by
  simp [orientableTargetNames, List.sum_ofFn,
    Nat.mul_comm]

@[simp]
theorem nonOrientableTargetNames_length (p n : ℕ) :
    (nonOrientableTargetNames p n).length =
      p + 2 * n := by
  simp [nonOrientableTargetNames, List.sum_ofFn,
    Nat.mul_comm]

/-- The stable boundary partition is a permutation of the original block sequence. -/
theorem boundariesLast_perm {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    (boundariesLast blocks).Perm blocks := by
  unfold boundariesLast closedBlocks boundaryBlocks
  simpa only [Bool.not_not] using
    (List.filter_append_perm
      (fun block : CompletedBlock n => !isBoundary block)
      blocks)

/-- Boundary partitioning remains a permutation in arbitrary list context. -/
theorem boundariesLastInContext_perm {n : ℕ}
    (before blocks after : List (CompletedBlock n)) :
    (before ++ boundariesLast blocks ++ after).Perm
      (before ++ blocks ++ after) := by
  simpa [List.append_assoc] using
    (List.Perm.append_right after
      (List.Perm.append_left before
        (boundariesLast_perm blocks)))

/-- The recursive crosscap count is the corresponding Boolean list count. -/
theorem crosscapCount_eq_countP {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    CompletedBlock.crosscapCount blocks =
      blocks.countP isCrosscap := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simp [CompletedBlock.crosscapCount,
          isCrosscap, ih, Nat.add_comm]

/-- The recursive handle count is the corresponding Boolean list count. -/
theorem handleCount_eq_countP {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    CompletedBlock.handleCount blocks =
      blocks.countP isHandle := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simp [CompletedBlock.handleCount,
          isHandle, ih, Nat.add_comm]

/-- The recursive boundary count is the corresponding Boolean list count. -/
theorem boundaryCount_eq_countP {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    CompletedBlock.boundaryCount blocks =
      blocks.countP isBoundary := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simp [CompletedBlock.boundaryCount,
          isBoundary, ih, Nat.add_comm]

/-- The distinct-name spine has one name per crosscap, two per handle, and two per boundary
loop. -/
theorem sequenceNames_length {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    (CompletedBlock.sequenceNames blocks).length =
      CompletedBlock.crosscapCount blocks +
        2 * CompletedBlock.handleCount blocks +
        2 * CompletedBlock.boundaryCount blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simp [CompletedBlock.sequenceNames,
          CompletedBlock.names,
          CompletedBlock.crosscapCount,
          CompletedBlock.handleCount,
          CompletedBlock.boundaryCount] at ih ⊢ <;>
        omega

/-- Block permutation preserves all three normal-form block counts. -/
theorem counts_eq_of_perm {n : ℕ}
    {left right : List (CompletedBlock n)}
    (hperm : left.Perm right) :
    CompletedBlock.crosscapCount left =
        CompletedBlock.crosscapCount right ∧
      CompletedBlock.handleCount left =
        CompletedBlock.handleCount right ∧
      CompletedBlock.boundaryCount left =
        CompletedBlock.boundaryCount right := by
  refine ⟨?_, ?_, ?_⟩
  · rw [crosscapCount_eq_countP,
      crosscapCount_eq_countP]
    exact hperm.countP_eq isCrosscap
  · rw [handleCount_eq_countP,
      handleCount_eq_countP]
    exact hperm.countP_eq isHandle
  · rw [boundaryCount_eq_countP,
      boundaryCount_eq_countP]
    exact hperm.countP_eq isBoundary

/-- Permuting completed blocks does not change the selected normal form. -/
theorem normalForm_eq_of_perm {n : ℕ}
    {left right : List (CompletedBlock n)}
    (hperm : left.Perm right) :
    CompletedBlock.normalForm left =
      CompletedBlock.normalForm right := by
  rcases counts_eq_of_perm hperm with
    ⟨hcrosscap, hhandle, hboundary⟩
  simp only [CompletedBlock.normalForm]
  rw [hcrosscap, hhandle, hboundary]

/-- Ordinary validity forces every ambient `Fin` edge to occur in the terminal name spine. -/
theorem TerminalCompletedWord.allNamesMem
    (terminal : TerminalCompletedWord)
    (edge : Fin terminal.edgeCount) :
    edge ∈
      CompletedBlock.sequenceNames terminal.blocks := by
  have hmultiplicity :=
    terminal.valid.2.2.2 edge
  rw [Dyck.oneFace_edgeMultiplicity] at hmultiplicity
  apply
    (CompletedBlock.mem_sequenceWord_edge_iff_mem_sequenceNames
      terminal.blocks edge).mp
  apply List.count_pos_iff.mp
  rcases hmultiplicity with h | h <;> omega

/-- Equivalence obtained by pairing two duplicate-free exhaustive name enumerations position by
position. -/
noncomputable def edgeEquivOfNameLists
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (sourceNames : List Source)
    (targetNames : List Target)
    (sourceNodup : sourceNames.Nodup)
    (sourceAll : ∀ source : Source, source ∈ sourceNames)
    (targetNodup : targetNames.Nodup)
    (targetAll : ∀ target : Target, target ∈ targetNames)
    (length_eq : sourceNames.length = targetNames.length) :
    Source ≃ Target :=
  (sourceNodup.getEquivOfForallMemList
      sourceNames sourceAll).symm |>.trans
    ((finCongr length_eq).trans
      (targetNodup.getEquivOfForallMemList
        targetNames targetAll))

/-- The enumeration equivalence maps the entire source name list to the target list exactly. -/
theorem map_edgeEquivOfNameLists
    {Source Target : Type*}
    [DecidableEq Source] [DecidableEq Target]
    (sourceNames : List Source)
    (targetNames : List Target)
    (sourceNodup : sourceNames.Nodup)
    (sourceAll : ∀ source : Source, source ∈ sourceNames)
    (targetNodup : targetNames.Nodup)
    (targetAll : ∀ target : Target, target ∈ targetNames)
    (length_eq : sourceNames.length = targetNames.length) :
    sourceNames.map
        (edgeEquivOfNameLists sourceNames targetNames
          sourceNodup sourceAll targetNodup targetAll
          length_eq) =
      targetNames := by
  apply List.ext_get
  · simpa using length_eq
  · intro index hsource htarget
    have hsource' :
        index < sourceNames.length := by
      simpa using hsource
    have hindex :
        sourceNames.idxOf sourceNames[index] = index := by
      simpa using
        List.get_idxOf sourceNodup
          (⟨index, hsource'⟩ :
            Fin sourceNames.length)
    simp only [List.get_eq_getElem,
      List.getElem_map]
    simp [edgeEquivOfNameLists, hindex]

/-- Shape of one completed normal-form block. -/
inductive BlockKind
  | crosscap
  | handle
  | boundary
  deriving DecidableEq, Repr

/-- Forget the edge names and signs of one completed block. -/
def blockKind {n : ℕ} : CompletedBlock n → BlockKind
  | .crosscap _ _ => .crosscap
  | .handle _ _ => .handle
  | .boundary _ _ _ _ => .boundary

/-- Shape sequence of a completed block word. -/
def blockKinds {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    List BlockKind :=
  blocks.map blockKind

/-- Final orientation bit assigned to each edge name by its unique completed block. -/
def reverseForBlocks {n : ℕ} :
    List (CompletedBlock n) → Fin n → Bool
  | [], _ => false
  | .crosscap anchor negative :: blocks, edge =>
      if edge = anchor then negative
      else reverseForBlocks blocks edge
  | .handle first second :: blocks, edge =>
      if edge = first then false
      else if edge = second then false
      else reverseForBlocks blocks edge
  | .boundary carrier hole
        carrierNegative holeNegative :: blocks, edge =>
      if edge = carrier then carrierNegative
      else if edge = hole then holeNegative
      else reverseForBlocks blocks edge

/-- Positively normalized spelling of one completed block after applying an edge equivalence. -/
def normalizedBlockWord {n : ℕ} {Edge : Type*}
    (edgeEquiv : Fin n ≃ Edge) :
    CompletedBlock n → List (SignedDart Edge)
  | .crosscap anchor _ =>
      [.pos (edgeEquiv anchor),
        .pos (edgeEquiv anchor)]
  | .handle first second =>
      [.pos (edgeEquiv first),
        .pos (edgeEquiv second),
        .neg (edgeEquiv first),
        .neg (edgeEquiv second)]
  | .boundary carrier hole _ _ =>
      [.pos (edgeEquiv carrier),
        .pos (edgeEquiv hole),
        .neg (edgeEquiv carrier)]

/-- Positively normalize a full completed block sequence. -/
def normalizedSequenceWord {n : ℕ} {Edge : Type*}
    (edgeEquiv : Fin n ≃ Edge) :
    List (CompletedBlock n) → List (SignedDart Edge)
  | [] => []
  | block :: blocks =>
      normalizedBlockWord edgeEquiv block ++
        normalizedSequenceWord edgeEquiv blocks

/-- Reconstruct a positively oriented block word from a shape list and its flat edge-name
spine. Malformed shape/name pairs are assigned the empty word; completed block sequences always
land in the exact-shape cases. -/
def wordFromKinds {Edge : Type*} :
    List BlockKind → List Edge → List (SignedDart Edge)
  | [], _ => []
  | .crosscap :: kinds, edge :: names =>
      [.pos edge, .pos edge] ++ wordFromKinds kinds names
  | .handle :: kinds, first :: second :: names =>
      [.pos first, .pos second, .neg first, .neg second] ++
        wordFromKinds kinds names
  | .boundary :: kinds, carrier :: hole :: names =>
      [.pos carrier, .pos hole, .neg carrier] ++
        wordFromKinds kinds names
  | _, _ => []

/-- Positive normalization is determined entirely by the block shapes and mapped name spine. -/
theorem normalizedSequenceWord_eq_wordFromKinds
    {n : ℕ} {Edge : Type*}
    (edgeEquiv : Fin n ≃ Edge)
    (blocks : List (CompletedBlock n)) :
    normalizedSequenceWord edgeEquiv blocks =
      wordFromKinds (blockKinds blocks)
        ((CompletedBlock.sequenceNames blocks).map edgeEquiv) := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simp [normalizedSequenceWord, normalizedBlockWord,
          blockKinds, blockKind, CompletedBlock.sequenceNames,
          CompletedBlock.names, wordFromKinds, ih]

/-- Filtering out the boundary blocks leaves exactly one boundary shape per boundary count. -/
theorem blockKinds_boundaryBlocks {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    blockKinds (boundaryBlocks blocks) =
      List.replicate (CompletedBlock.boundaryCount blocks)
        BlockKind.boundary := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block with
      | crosscap anchor negative =>
          simpa [boundaryBlocks, blockKinds, isBoundary,
            CompletedBlock.boundaryCount] using ih
      | handle first second =>
          simpa [boundaryBlocks, blockKinds, isBoundary,
            CompletedBlock.boundaryCount] using ih
      | boundary carrier hole carrierNegative holeNegative =>
          change
            BlockKind.boundary ::
                blockKinds (boundaryBlocks blocks) =
              List.replicate
                (1 + CompletedBlock.boundaryCount blocks)
                BlockKind.boundary
          rw [show
            1 + CompletedBlock.boundaryCount blocks =
              (CompletedBlock.boundaryCount blocks).succ by omega,
            List.replicate_succ]
          exact congrArg (List.cons BlockKind.boundary) ih

/-- With no crosscaps, the closed portion consists of exactly the counted handles. -/
theorem blockKinds_closedBlocks_of_crosscapCount_eq_zero {n : ℕ}
    (blocks : List (CompletedBlock n))
    (hzero : CompletedBlock.crosscapCount blocks = 0) :
    blockKinds (closedBlocks blocks) =
      List.replicate (CompletedBlock.handleCount blocks)
        BlockKind.handle := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block with
      | crosscap anchor negative =>
          simp [CompletedBlock.crosscapCount] at hzero
      | handle first second =>
          simp only [CompletedBlock.crosscapCount] at hzero
          change
            BlockKind.handle ::
                blockKinds (closedBlocks blocks) =
              List.replicate
                (1 + CompletedBlock.handleCount blocks)
                BlockKind.handle
          rw [show
            1 + CompletedBlock.handleCount blocks =
              (CompletedBlock.handleCount blocks).succ by omega,
            List.replicate_succ]
          exact
            congrArg (List.cons BlockKind.handle)
              (ih hzero)
      | boundary carrier hole carrierNegative holeNegative =>
          simp only [CompletedBlock.crosscapCount] at hzero
          simpa [closedBlocks, blockKinds, isBoundary,
            CompletedBlock.handleCount] using ih hzero

/-- With no handles, the closed portion consists of exactly the counted crosscaps. -/
theorem blockKinds_closedBlocks_of_handleCount_eq_zero {n : ℕ}
    (blocks : List (CompletedBlock n))
    (hzero : CompletedBlock.handleCount blocks = 0) :
    blockKinds (closedBlocks blocks) =
      List.replicate (CompletedBlock.crosscapCount blocks)
        BlockKind.crosscap := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block with
      | crosscap anchor negative =>
          simp only [CompletedBlock.handleCount] at hzero
          change
            BlockKind.crosscap ::
                blockKinds (closedBlocks blocks) =
              List.replicate
                (1 + CompletedBlock.crosscapCount blocks)
                BlockKind.crosscap
          rw [show
            1 + CompletedBlock.crosscapCount blocks =
              (CompletedBlock.crosscapCount blocks).succ by omega,
            List.replicate_succ]
          exact
            congrArg (List.cons BlockKind.crosscap)
              (ih hzero)
      | handle first second =>
          simp [CompletedBlock.handleCount] at hzero
      | boundary carrier hole carrierNegative holeNegative =>
          simp only [CompletedBlock.handleCount] at hzero
          simpa [closedBlocks, blockKinds, isBoundary,
            CompletedBlock.crosscapCount] using ih hzero

/-- After stable boundary partitioning, an orientable block list has exactly the canonical
handle-then-boundary shape. -/
theorem blockKinds_boundariesLast_of_crosscapCount_eq_zero
    {n : ℕ}
    (blocks : List (CompletedBlock n))
    (hzero : CompletedBlock.crosscapCount blocks = 0) :
    blockKinds (boundariesLast blocks) =
      List.replicate (CompletedBlock.handleCount blocks)
          BlockKind.handle ++
        List.replicate (CompletedBlock.boundaryCount blocks)
          BlockKind.boundary := by
  rw [boundariesLast]
  simp only [blockKinds, List.map_append]
  rw [show
      (closedBlocks blocks).map blockKind =
        List.replicate (CompletedBlock.handleCount blocks)
          BlockKind.handle by
      simpa only [blockKinds] using
        blockKinds_closedBlocks_of_crosscapCount_eq_zero
          blocks hzero,
    show
      (boundaryBlocks blocks).map blockKind =
        List.replicate (CompletedBlock.boundaryCount blocks)
          BlockKind.boundary by
      simpa only [blockKinds] using
        blockKinds_boundaryBlocks blocks]

/-- After stable boundary partitioning, a handle-free block list has exactly the canonical
crosscap-then-boundary shape. -/
theorem blockKinds_boundariesLast_of_handleCount_eq_zero
    {n : ℕ}
    (blocks : List (CompletedBlock n))
    (hzero : CompletedBlock.handleCount blocks = 0) :
    blockKinds (boundariesLast blocks) =
      List.replicate (CompletedBlock.crosscapCount blocks)
          BlockKind.crosscap ++
        List.replicate (CompletedBlock.boundaryCount blocks)
          BlockKind.boundary := by
  rw [boundariesLast]
  simp only [blockKinds, List.map_append]
  rw [show
      (closedBlocks blocks).map blockKind =
        List.replicate (CompletedBlock.crosscapCount blocks)
          BlockKind.crosscap by
      simpa only [blockKinds] using
        blockKinds_closedBlocks_of_handleCount_eq_zero
          blocks hzero,
    show
      (boundaryBlocks blocks).map blockKind =
        List.replicate (CompletedBlock.boundaryCount blocks)
          BlockKind.boundary by
      simpa only [blockKinds] using
        blockKinds_boundaryBlocks blocks]

/-- Consume an arbitrary list of named handle blocks before a remaining shape/name context. -/
theorem wordFromKinds_handles_append
    {Index Edge : Type*}
    (indices : List Index)
    (first second : Index → Edge)
    (kinds : List BlockKind)
    (names : List Edge) :
    wordFromKinds
        (List.replicate indices.length BlockKind.handle ++
          kinds)
        ((indices.map fun i => [first i, second i]).flatten ++
          names) =
      (indices.map fun i =>
        [.pos (first i), .pos (second i),
          .neg (first i), .neg (second i)]).flatten ++
        wordFromKinds kinds names := by
  induction indices with
  | nil =>
      rfl
  | cons index indices ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.cons_append, List.map_cons, List.flatten_cons]
      simp [wordFromKinds, ih]

/-- Consume an arbitrary list of named crosscap blocks before a remaining shape/name context. -/
theorem wordFromKinds_crosscaps_append
    {Index Edge : Type*}
    (indices : List Index)
    (edge : Index → Edge)
    (kinds : List BlockKind)
    (names : List Edge) :
    wordFromKinds
        (List.replicate indices.length BlockKind.crosscap ++
          kinds)
        ((indices.map fun i => [edge i]).flatten ++ names) =
      (indices.map fun i =>
        [.pos (edge i), .pos (edge i)]).flatten ++
        wordFromKinds kinds names := by
  induction indices with
  | nil =>
      rfl
  | cons index indices ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.cons_append, List.map_cons, List.flatten_cons]
      simp [wordFromKinds, ih]

/-- Consume a complete list of named boundary blocks. -/
theorem wordFromKinds_boundaries
    {Index Edge : Type*}
    (indices : List Index)
    (carrier hole : Index → Edge) :
    wordFromKinds
        (List.replicate indices.length BlockKind.boundary)
        (indices.map fun i => [carrier i, hole i]).flatten =
      (indices.map fun i =>
        [.pos (carrier i), .pos (hole i),
          .neg (carrier i)]).flatten := by
  induction indices with
  | nil =>
      rfl
  | cons index indices ih =>
      simp only [List.length_cons, List.replicate_succ,
        List.map_cons, List.flatten_cons]
      simp [wordFromKinds, ih]

/-- The canonical orientable name spine and shape list reconstruct the existing canonical word
exactly. -/
theorem wordFromKinds_orientableTarget
    (p n : ℕ) :
    wordFromKinds
        (List.replicate p BlockKind.handle ++
          List.replicate n BlockKind.boundary)
        (orientableTargetNames p n) =
      NormalForm.orientableBoundaryWord p n := by
  let pIndices := List.ofFn (fun i : Fin p => i)
  let nIndices := List.ofFn (fun i : Fin n => i)
  calc
    _ =
        (pIndices.map fun i =>
          [.pos (NormalForm.OrientableEdge.a i),
            .pos (NormalForm.OrientableEdge.b i),
            .neg (NormalForm.OrientableEdge.a i),
            .neg (NormalForm.OrientableEdge.b i)]).flatten ++
          wordFromKinds
            (List.replicate n BlockKind.boundary)
            (nIndices.map fun i =>
              [NormalForm.OrientableEdge.c i,
                NormalForm.OrientableEdge.h i]).flatten := by
      simpa [orientableTargetNames, pIndices, nIndices,
        List.map_ofFn, Function.comp_def] using
        wordFromKinds_handles_append
          pIndices
          (fun i => NormalForm.OrientableEdge.a i)
          (fun i => NormalForm.OrientableEdge.b i)
          (List.replicate n BlockKind.boundary)
          ((nIndices.map fun i =>
            [NormalForm.OrientableEdge.c i,
              NormalForm.OrientableEdge.h i]).flatten)
    _ =
        (pIndices.map fun i =>
          [.pos (NormalForm.OrientableEdge.a i),
            .pos (NormalForm.OrientableEdge.b i),
            .neg (NormalForm.OrientableEdge.a i),
            .neg (NormalForm.OrientableEdge.b i)]).flatten ++
          (nIndices.map fun i =>
            [.pos (NormalForm.OrientableEdge.c i),
              .pos (NormalForm.OrientableEdge.h i),
              .neg (NormalForm.OrientableEdge.c i)]).flatten := by
      simpa [nIndices] using
        congrArg
          (fun tail =>
            (pIndices.map fun i =>
              [.pos (NormalForm.OrientableEdge.a i),
                .pos (NormalForm.OrientableEdge.b i),
                .neg (NormalForm.OrientableEdge.a i),
                .neg (NormalForm.OrientableEdge.b i)]).flatten ++
              tail)
          (wordFromKinds_boundaries
            nIndices
            (fun i => NormalForm.OrientableEdge.c i)
            (fun i => NormalForm.OrientableEdge.h i))
    _ = NormalForm.orientableBoundaryWord p n := by
      simp [NormalForm.orientableBoundaryWord,
        NormalForm.orientableHandleBlock,
        NormalForm.orientableBoundaryBlock,
        pIndices, nIndices, List.map_ofFn,
        Function.comp_def]

/-- The canonical nonorientable name spine and shape list reconstruct the existing canonical word
exactly. -/
theorem wordFromKinds_nonOrientableTarget
    (p n : ℕ) :
    wordFromKinds
        (List.replicate p BlockKind.crosscap ++
          List.replicate n BlockKind.boundary)
        (nonOrientableTargetNames p n) =
      NormalForm.nonOrientableBoundaryWord p n := by
  let pIndices := List.ofFn (fun i : Fin p => i)
  let nIndices := List.ofFn (fun i : Fin n => i)
  calc
    _ =
        (pIndices.map fun i =>
          [.pos (NormalForm.NonOrientableEdge.a i),
            .pos (NormalForm.NonOrientableEdge.a i)]).flatten ++
          wordFromKinds
            (List.replicate n BlockKind.boundary)
            (nIndices.map fun i =>
              [NormalForm.NonOrientableEdge.c i,
                NormalForm.NonOrientableEdge.h i]).flatten := by
      simpa [nonOrientableTargetNames, pIndices, nIndices,
        List.map_ofFn, Function.comp_def] using
        wordFromKinds_crosscaps_append
          pIndices
          (fun i => NormalForm.NonOrientableEdge.a i)
          (List.replicate n BlockKind.boundary)
          ((nIndices.map fun i =>
            [NormalForm.NonOrientableEdge.c i,
              NormalForm.NonOrientableEdge.h i]).flatten)
    _ =
        (pIndices.map fun i =>
          [.pos (NormalForm.NonOrientableEdge.a i),
            .pos (NormalForm.NonOrientableEdge.a i)]).flatten ++
          (nIndices.map fun i =>
            [.pos (NormalForm.NonOrientableEdge.c i),
              .pos (NormalForm.NonOrientableEdge.h i),
              .neg (NormalForm.NonOrientableEdge.c i)]).flatten := by
      simpa [nIndices] using
        congrArg
          (fun tail =>
            (pIndices.map fun i =>
              [.pos (NormalForm.NonOrientableEdge.a i),
                .pos (NormalForm.NonOrientableEdge.a i)]).flatten ++
              tail)
          (wordFromKinds_boundaries
            nIndices
            (fun i => NormalForm.NonOrientableEdge.c i)
            (fun i => NormalForm.NonOrientableEdge.h i))
    _ = NormalForm.nonOrientableBoundaryWord p n := by
      simp [NormalForm.nonOrientableBoundaryWord,
        NormalForm.nonOrientableCrosscapBlock,
        NormalForm.nonOrientableBoundaryBlock,
        pIndices, nIndices, List.map_ofFn,
        Function.comp_def]

/-- A name belonging to the tail is not captured by the head block's orientation lookup. -/
theorem reverseForBlocks_cons_of_mem_tail {n : ℕ}
    (block : CompletedBlock n)
    (blocks : List (CompletedBlock n))
    (edge : Fin n)
    (hdisjoint :
      ∀ head ∈ block.names,
        ∀ tail ∈ CompletedBlock.sequenceNames blocks,
          head ≠ tail)
    (hedge :
      edge ∈ CompletedBlock.sequenceNames blocks) :
    reverseForBlocks (block :: blocks) edge =
      reverseForBlocks blocks edge := by
  cases block with
  | crosscap anchor negative =>
      have hne : edge ≠ anchor := by
        intro h
        subst edge
        exact hdisjoint anchor
          (by simp [CompletedBlock.names])
          anchor hedge rfl
      simp [reverseForBlocks, hne]
  | handle first second =>
      have hfirst : edge ≠ first := by
        intro h
        subst edge
        exact hdisjoint first
          (by simp [CompletedBlock.names])
          first hedge rfl
      have hsecond : edge ≠ second := by
        intro h
        subst edge
        exact hdisjoint second
          (by simp [CompletedBlock.names])
          second hedge rfl
      simp [reverseForBlocks, hfirst, hsecond]
  | boundary carrier hole
      carrierNegative holeNegative =>
      have hcarrier : edge ≠ carrier := by
        intro h
        subst edge
        exact hdisjoint carrier
          (by simp [CompletedBlock.names])
          carrier hedge rfl
      have hhole : edge ≠ hole := by
        intro h
        subst edge
        exact hdisjoint hole
          (by simp [CompletedBlock.names])
          hole hedge rfl
      simp [reverseForBlocks, hcarrier, hhole]

/-- The signed relabeling selected by the unique block-name spine positively normalizes every
completed block. -/
theorem map_sequenceWord_signedRelabeling_normalized
    {n : ℕ} {Edge : Type*}
    (edgeEquiv : Fin n ≃ Edge)
    (blocks : List (CompletedBlock n))
    (hnames :
      (CompletedBlock.sequenceNames blocks).Nodup) :
    (CompletedBlock.sequenceWord blocks).map
        (signedRelabeling edgeEquiv
          (reverseForBlocks blocks)).mapDart =
      normalizedSequenceWord edgeEquiv blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      rw [CompletedBlock.sequenceNames_cons,
        List.nodup_append] at hnames
      rcases hnames with
        ⟨hblockNodup, htailNodup, hdisjoint⟩
      have htailMap :
          (CompletedBlock.sequenceWord blocks).map
              (signedRelabeling edgeEquiv
                (reverseForBlocks (block :: blocks))).mapDart =
            (CompletedBlock.sequenceWord blocks).map
              (signedRelabeling edgeEquiv
                (reverseForBlocks blocks)).mapDart := by
        apply List.map_congr_left
        intro dart hdart
        have hedge :
            edgeOfDart dart ∈
              CompletedBlock.sequenceNames blocks := by
          apply
            (CompletedBlock.mem_sequenceWord_edge_iff_mem_sequenceNames
              blocks (edgeOfDart dart)).mp
          exact List.mem_map.mpr ⟨dart, hdart, rfl⟩
        have hreverse :=
          reverseForBlocks_cons_of_mem_tail
            block blocks (edgeOfDart dart)
            hdisjoint hedge
        cases dart with
        | pos edge =>
            have hreverse' :
                reverseForBlocks (block :: blocks) edge =
                  reverseForBlocks blocks edge := by
              simpa only [edgeOfDart] using hreverse
            simp [signedRelabeling,
              EdgeRelabeling.mapDart, hreverse']
            rfl
        | neg edge =>
            have hreverse' :
                reverseForBlocks (block :: blocks) edge =
                  reverseForBlocks blocks edge := by
              simpa only [edgeOfDart] using hreverse
            simp [signedRelabeling,
              EdgeRelabeling.mapDart, hreverse']
            rfl
      have hheadMap :
          block.word.map
              (signedRelabeling edgeEquiv
                (reverseForBlocks (block :: blocks))).mapDart =
            normalizedBlockWord edgeEquiv block := by
        cases block with
        | crosscap anchor negative =>
            apply
              ExtractedBlock.map_word_crosscap_normalized
                edgeEquiv
                  (reverseForBlocks
                    (CompletedBlock.crosscap anchor negative ::
                      blocks))
                  anchor negative
            simp [reverseForBlocks]
        | handle first second =>
            apply
              ExtractedBlock.map_word_handle_normalized
                edgeEquiv
                  (reverseForBlocks
                    (CompletedBlock.handle first second ::
                      blocks))
                  first second
            · simp [reverseForBlocks]
            · simp [reverseForBlocks]
        | boundary carrier hole
            carrierNegative holeNegative =>
            have hcarrierHole : carrier ≠ hole := by
              simpa [CompletedBlock.names] using hblockNodup
            apply map_boundaryLoopWord_normalized
              edgeEquiv
                (reverseForBlocks
                  (CompletedBlock.boundary carrier hole
                    carrierNegative holeNegative ::
                    blocks))
                carrier hole carrierNegative holeNegative
            · simp [reverseForBlocks]
            · simp [reverseForBlocks,
                hcarrierHole.symm]
      rw [CompletedBlock.sequenceWord_cons,
        List.map_append, hheadMap, htailMap,
        ih htailNodup]
      rfl

/-- An already ordered orientable completed word relabels exactly to the existing canonical
orientable finite-cyclic presentation. -/
noncomputable def orientableOrderedResult
    (terminal : TerminalCompletedWord)
    (hcrosscap :
      CompletedBlock.crosscapCount terminal.blocks = 0)
    (hshape :
      blockKinds terminal.blocks =
        List.replicate
            (CompletedBlock.handleCount terminal.blocks)
            BlockKind.handle ++
          List.replicate
            (CompletedBlock.boundaryCount terminal.blocks)
            BlockKind.boundary) :
    NormalizationResult terminal.validPresentation := by
  let p := CompletedBlock.handleCount terminal.blocks
  let n := CompletedBlock.boundaryCount terminal.blocks
  have hlength :
      (CompletedBlock.sequenceNames terminal.blocks).length =
        (orientableTargetNames p n).length := by
    rw [sequenceNames_length,
      orientableTargetNames_length]
    simp only [p, n]
    omega
  let edgeEquiv :
      Fin terminal.edgeCount ≃
        NormalForm.OrientableEdge p n :=
    edgeEquivOfNameLists
      (CompletedBlock.sequenceNames terminal.blocks)
      (orientableTargetNames p n)
      terminal.namesNodup
      (TerminalNormalization.TerminalCompletedWord.allNamesMem
        terminal)
      (orientableTargetNames_nodup p n)
      (mem_orientableTargetNames p n)
      hlength
  have hnamesMap :
      (CompletedBlock.sequenceNames terminal.blocks).map
          edgeEquiv =
        orientableTargetNames p n := by
    exact
      map_edgeEquivOfNameLists
        (CompletedBlock.sequenceNames terminal.blocks)
        (orientableTargetNames p n)
        terminal.namesNodup
        (TerminalNormalization.TerminalCompletedWord.allNamesMem
          terminal)
        (orientableTargetNames_nodup p n)
        (mem_orientableTargetNames p n)
        hlength
  have hmapped :
      (CompletedBlock.sequenceWord terminal.blocks).map
          (signedRelabeling edgeEquiv
            (reverseForBlocks terminal.blocks)).mapDart =
        NormalForm.orientableBoundaryWord p n := by
    rw [map_sequenceWord_signedRelabeling_normalized
      edgeEquiv terminal.blocks terminal.namesNodup]
    rw [normalizedSequenceWord_eq_wordFromKinds]
    rw [hshape]
    simp only [p, n] at hnamesMap ⊢
    rw [hnamesMap, wordFromKinds_orientableTarget]
  have hrotated :
      ((CompletedBlock.sequenceWord terminal.blocks).map
          (signedRelabeling edgeEquiv
            (reverseForBlocks terminal.blocks)).mapDart).IsRotated
        (NormalForm.orientableBoundaryWord p n) := by
    rw [hmapped]
  have hnormalForm :
      terminal.normalForm =
        NormalForm.orientable p n := by
    simp [TerminalCompletedWord.normalForm,
      CompletedBlock.normalForm, p, n, hcrosscap]
  have hadmissible :
      (NormalForm.orientable p n).IsEvalAdmissible := by
    rw [← hnormalForm]
    exact terminal.admissible
  let result :=
    orientableNormalizationResultOfSignedRotated
      (CompletedBlock.sequenceWord terminal.blocks)
      (signedRelabeling edgeEquiv
        (reverseForBlocks terminal.blocks))
      hrotated terminal.valid hadmissible
  have hresultNormalForm :
      result.normalForm =
        NormalForm.orientable p n :=
    rfl
  have htarget :
      canonicalValidPresentation result.normalForm
          result.admissible =
        canonicalValidPresentation terminal.normalForm
          terminal.admissible := by
    apply ValidPresentation.ext
    simp only [canonicalValidPresentation_presentation]
    exact congrArg NormalForm.canonicalPresentation
      (hresultNormalForm.trans hnormalForm.symm)
  exact
    { normalForm := terminal.normalForm
      admissible := terminal.admissible
      equivalent := by
        rw [← htarget]
        exact result.equivalent }

/-- The ordered orientable construction retains the terminal word's computed normal form. -/
@[simp]
private theorem orientableOrderedResult_normalForm
    (terminal : TerminalCompletedWord)
    (hcrosscap : CompletedBlock.crosscapCount terminal.blocks = 0)
    (hshape :
      blockKinds terminal.blocks =
        List.replicate (CompletedBlock.handleCount terminal.blocks) BlockKind.handle ++
          List.replicate (CompletedBlock.boundaryCount terminal.blocks) BlockKind.boundary) :
    (orientableOrderedResult terminal hcrosscap hshape).normalForm = terminal.normalForm :=
  rfl

/-- An already ordered nonorientable completed word relabels exactly to the existing canonical
nonorientable finite-cyclic presentation. -/
noncomputable def nonOrientableOrderedResult
    (terminal : TerminalCompletedWord)
    (hhandle :
      CompletedBlock.handleCount terminal.blocks = 0)
    (hcrosscap :
      CompletedBlock.crosscapCount terminal.blocks ≠ 0)
    (hshape :
      blockKinds terminal.blocks =
        List.replicate
            (CompletedBlock.crosscapCount terminal.blocks)
            BlockKind.crosscap ++
          List.replicate
            (CompletedBlock.boundaryCount terminal.blocks)
            BlockKind.boundary) :
    NormalizationResult terminal.validPresentation := by
  let p := CompletedBlock.crosscapCount terminal.blocks
  let n := CompletedBlock.boundaryCount terminal.blocks
  have hlength :
      (CompletedBlock.sequenceNames terminal.blocks).length =
        (nonOrientableTargetNames p n).length := by
    rw [sequenceNames_length,
      nonOrientableTargetNames_length]
    simp only [p, n]
    omega
  let edgeEquiv :
      Fin terminal.edgeCount ≃
        NormalForm.NonOrientableEdge p n :=
    edgeEquivOfNameLists
      (CompletedBlock.sequenceNames terminal.blocks)
      (nonOrientableTargetNames p n)
      terminal.namesNodup
      (TerminalNormalization.TerminalCompletedWord.allNamesMem
        terminal)
      (nonOrientableTargetNames_nodup p n)
      (mem_nonOrientableTargetNames p n)
      hlength
  have hnamesMap :
      (CompletedBlock.sequenceNames terminal.blocks).map
          edgeEquiv =
        nonOrientableTargetNames p n := by
    exact
      map_edgeEquivOfNameLists
        (CompletedBlock.sequenceNames terminal.blocks)
        (nonOrientableTargetNames p n)
        terminal.namesNodup
        (TerminalNormalization.TerminalCompletedWord.allNamesMem
          terminal)
        (nonOrientableTargetNames_nodup p n)
        (mem_nonOrientableTargetNames p n)
        hlength
  have hmapped :
      (CompletedBlock.sequenceWord terminal.blocks).map
          (signedRelabeling edgeEquiv
            (reverseForBlocks terminal.blocks)).mapDart =
        NormalForm.nonOrientableBoundaryWord p n := by
    rw [map_sequenceWord_signedRelabeling_normalized
      edgeEquiv terminal.blocks terminal.namesNodup]
    rw [normalizedSequenceWord_eq_wordFromKinds]
    rw [hshape]
    simp only [p, n] at hnamesMap ⊢
    rw [hnamesMap, wordFromKinds_nonOrientableTarget]
  have hrotated :
      ((CompletedBlock.sequenceWord terminal.blocks).map
          (signedRelabeling edgeEquiv
            (reverseForBlocks terminal.blocks)).mapDart).IsRotated
        (NormalForm.nonOrientableBoundaryWord p n) := by
    rw [hmapped]
  have hnormalForm :
      terminal.normalForm =
        NormalForm.nonOrientable p n := by
    simp [TerminalCompletedWord.normalForm,
      CompletedBlock.normalForm, p, n,
      hhandle, hcrosscap]
  have hadmissible :
      (NormalForm.nonOrientable p n).IsEvalAdmissible := by
    rw [← hnormalForm]
    exact terminal.admissible
  let result :=
    nonOrientableNormalizationResultOfSignedRotated
      (CompletedBlock.sequenceWord terminal.blocks)
      (signedRelabeling edgeEquiv
        (reverseForBlocks terminal.blocks))
      hrotated terminal.valid hadmissible
  have hresultNormalForm :
      result.normalForm =
        NormalForm.nonOrientable p n :=
    rfl
  have htarget :
      canonicalValidPresentation result.normalForm
          result.admissible =
        canonicalValidPresentation terminal.normalForm
          terminal.admissible := by
    apply ValidPresentation.ext
    simp only [canonicalValidPresentation_presentation]
    exact congrArg NormalForm.canonicalPresentation
      (hresultNormalForm.trans hnormalForm.symm)
  exact
    { normalForm := terminal.normalForm
      admissible := terminal.admissible
      equivalent := by
        rw [← htarget]
        exact result.equivalent }

/-- Handle conversion merely permutes the distinct edge-name spine. -/
theorem handlesToCrosscaps_sequenceNames_perm {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    (CompletedBlock.sequenceNames
      (handlesToCrosscaps blocks)).Perm
      (CompletedBlock.sequenceNames blocks) := by
  induction blocks with
  | nil =>
      exact List.Perm.refl _
  | cons block blocks ih =>
      cases block with
      | crosscap carrier negative =>
          simpa [handlesToCrosscaps,
            CompletedBlock.names] using ih.cons carrier
      | boundary carrier hole
          carrierNegative holeNegative =>
          simpa [handlesToCrosscaps,
            CompletedBlock.names] using
            (ih.cons hole |>.cons carrier)
      | handle first second =>
          simp only [handlesToCrosscaps,
            CompletedBlock.sequenceNames_cons,
            CompletedBlock.names]
          exact
            (List.Perm.swap first second
              (CompletedBlock.sequenceNames
                (handlesToCrosscaps blocks))).trans
              (ih.cons second |>.cons first)

/-- Handle conversion preserves the unoriented edge-occurrence multiset of the exact word. -/
theorem handlesToCrosscaps_sequenceEdgeWord_perm {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    ((CompletedBlock.sequenceWord
      (handlesToCrosscaps blocks)).map edgeOfDart).Perm
      ((CompletedBlock.sequenceWord blocks).map edgeOfDart) := by
  induction blocks with
  | nil =>
      exact List.Perm.refl _
  | cons block blocks ih =>
      cases block with
      | crosscap carrier negative =>
          simpa [handlesToCrosscaps,
            CompletedBlock.word] using
            (ih.cons carrier |>.cons carrier)
      | boundary carrier hole
          carrierNegative holeNegative =>
          simpa [handlesToCrosscaps,
            CompletedBlock.word, boundaryLoopWord] using
            (ih.cons carrier |>.cons hole |>.cons carrier)
      | handle first second =>
          have hlocal :
              ([second, second, first, first] : List (Fin n)).Perm
                [first, second, first, second] := by
            rw [List.perm_iff_count]
            intro edge
            simp only [List.count_cons,
              List.count_nil]
            omega
          have hwithTargetTail :=
            List.Perm.append_right
              ((CompletedBlock.sequenceWord
                (handlesToCrosscaps blocks)).map edgeOfDart)
              hlocal
          have htail :=
            List.Perm.append_left
              ([first, second, first, second] : List (Fin n))
              ih
          simpa [handlesToCrosscaps,
            CompletedBlock.word,
            List.append_assoc] using
            hwithTargetTail.trans htail

/-- Converting all handles produces no remaining handle block. -/
theorem handleCount_handlesToCrosscaps_eq_zero {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    CompletedBlock.handleCount
      (handlesToCrosscaps blocks) = 0 := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simp [handlesToCrosscaps,
          CompletedBlock.handleCount, ih]

/-- Each converted handle contributes exactly two completed crosscaps. -/
theorem crosscapCount_handlesToCrosscaps {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    CompletedBlock.crosscapCount
        (handlesToCrosscaps blocks) =
      CompletedBlock.crosscapCount blocks +
        2 * CompletedBlock.handleCount blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simp [handlesToCrosscaps,
          CompletedBlock.crosscapCount,
          CompletedBlock.handleCount, ih] <;>
        omega

/-- Handle conversion leaves the number of boundary-loop blocks unchanged. -/
theorem boundaryCount_handlesToCrosscaps {n : ℕ}
    (blocks : List (CompletedBlock n)) :
    CompletedBlock.boundaryCount
        (handlesToCrosscaps blocks) =
      CompletedBlock.boundaryCount blocks := by
  induction blocks with
  | nil =>
      rfl
  | cons block blocks ih =>
      cases block <;>
        simp [handlesToCrosscaps,
          CompletedBlock.boundaryCount, ih]

/-- Convert one displayed handle in the presence of a positive anchor crosscap. -/
theorem exists_convertPositiveAnchorHandle {n : ℕ}
    (anchor first second : Fin n)
    (before after : List (CompletedBlock n))
    (hnames :
      (CompletedBlock.sequenceNames
        (CompletedBlock.crosscap anchor false ::
          before ++
            CompletedBlock.handle first second ::
            after)).Nodup)
    (validSource :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (CompletedBlock.crosscap anchor false ::
            before ++
              CompletedBlock.handle first second ::
              after))).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor false ::
              before ++
                CompletedBlock.crosscap second false ::
                CompletedBlock.crosscap first false ::
                after))).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor false ::
              before ++
                CompletedBlock.handle first second ::
                after)),
          validSource⟩
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor false ::
              before ++
                CompletedBlock.crosscap second false ::
                CompletedBlock.crosscap first false ::
                after)),
          validTarget⟩ := by
  let beforeWord :=
    CompletedBlock.sequenceWord before
  let afterWord :=
    CompletedBlock.sequenceWord after
  have hnames' :
      (anchor ::
        (CompletedBlock.sequenceNames before ++
          first :: second ::
            CompletedBlock.sequenceNames after)).Nodup := by
    simpa [CompletedBlock.names,
      List.append_assoc] using hnames
  rcases List.nodup_cons.mp hnames' with
    ⟨hanchorTail, htailNodup⟩
  have hanchorBeforeNames :
      anchor ∉
        CompletedBlock.sequenceNames before := by
    intro h
    exact hanchorTail (by simp [h])
  have hanchorFirst : anchor ≠ first := by
    intro h
    exact hanchorTail (by simp [h])
  have hanchorSecond : anchor ≠ second := by
    intro h
    exact hanchorTail (by simp [h])
  have hanchorAfterNames :
      anchor ∉
        CompletedBlock.sequenceNames after := by
    intro h
    exact hanchorTail (by simp [h])
  rcases List.nodup_append.mp htailNodup with
    ⟨_, hdistinguishedNodup, hbeforeDistinguished⟩
  rcases List.nodup_cons.mp hdistinguishedNodup with
    ⟨hfirstTail, hsecondTailNodup⟩
  rcases List.nodup_cons.mp hsecondTailNodup with
    ⟨hsecondAfterNames, _⟩
  have hfirstSecond : first ≠ second := by
    intro h
    exact hfirstTail (by simp [h])
  have hfirstAfterNames :
      first ∉
        CompletedBlock.sequenceNames after := by
    intro h
    exact hfirstTail (by simp [h])
  have hfirstBeforeNames :
      first ∉
        CompletedBlock.sequenceNames before := by
    intro h
    exact hbeforeDistinguished first h first
      (by simp) rfl
  have hsecondBeforeNames :
      second ∉
        CompletedBlock.sequenceNames before := by
    intro h
    exact hbeforeDistinguished second h second
      (by simp) rfl
  have hanchorBefore :
      anchor ∉ beforeWord.map edgeOfDart := by
    simpa [beforeWord] using hanchorBeforeNames
  have hanchorAfter :
      anchor ∉ afterWord.map edgeOfDart := by
    simpa [afterWord] using hanchorAfterNames
  have hfirstBefore :
      first ∉ beforeWord.map edgeOfDart := by
    simpa [beforeWord] using hfirstBeforeNames
  have hfirstAfter :
      first ∉ afterWord.map edgeOfDart := by
    simpa [afterWord] using hfirstAfterNames
  have hsecondBefore :
      second ∉ beforeWord.map edgeOfDart := by
    simpa [beforeWord] using hsecondBeforeNames
  have hsecondAfter :
      second ∉ afterWord.map edgeOfDart := by
    simpa [afterWord] using hsecondAfterNames
  have hedgePerm :
      ((CompletedBlock.sequenceWord
        (CompletedBlock.crosscap anchor false ::
          before ++
            CompletedBlock.handle first second ::
            after)).map edgeOfDart).Perm
        ((CompletedBlock.sequenceWord
          (CompletedBlock.crosscap anchor false ::
            before ++
              CompletedBlock.crosscap second false ::
              CompletedBlock.crosscap first false ::
              after)).map edgeOfDart) := by
    rw [List.perm_iff_count]
    intro edge
    simp only [
      CompletedBlock.sequenceWord_cons,
      CompletedBlock.sequenceWord_append,
      CompletedBlock.word,
      dart,
      List.map_append, List.map_cons,
      List.map_nil, edgeOfDart,
      List.count_append, List.count_cons,
      List.count_nil]
    omega
  let validTarget :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (CompletedBlock.crosscap anchor false ::
            before ++
              CompletedBlock.crosscap second false ::
              CompletedBlock.crosscap first false ::
              after))).IsSurfaceValid :=
    Dyck.oneFace_isSurfaceValid_of_edgePerm
      hedgePerm validSource
  have htargetRotated :
      (HandleToCrosscaps.target anchor first second
        beforeWord afterWord).boundary 0 |>.IsRotated
        (CompletedBlock.sequenceWord
          (CompletedBlock.crosscap anchor false ::
            before ++
              CompletedBlock.crosscap second false ::
              CompletedBlock.crosscap first false ::
              after)) := by
    simpa [beforeWord, afterWord,
      CompletedBlock.word, dart,
      List.append_assoc] using
      (HandleToCrosscaps.target_boundary_isRotated_crosscaps
        anchor first second beforeWord afterWord)
  let targetIso :=
    Dyck.oneFaceSignedIsoOfIsRotated htargetRotated
  let validRawTarget :
      (HandleToCrosscaps.target anchor first second
        beforeWord afterWord).IsSurfaceValid :=
    targetIso.symm.isSurfaceValid validTarget
  let validRawSource :
      (HandleToCrosscaps.source anchor first second
        beforeWord afterWord).IsSurfaceValid := by
    simpa [HandleToCrosscaps.source,
      Crosscap.adjacentSource,
      beforeWord, afterWord,
      CompletedBlock.word, dart,
      List.append_assoc] using validSource
  have hraw :=
    HandleToCrosscaps.normalizationEquivalent
      anchor first second beforeWord afterWord
      hanchorFirst hanchorSecond hfirstSecond
      hanchorBefore hanchorAfter
      hfirstBefore hfirstAfter
      hsecondBefore hsecondAfter
      validRawSource validRawTarget
  refine ⟨validTarget, ?_⟩
  have htarget :
      NormalizationEquivalent
        ⟨HandleToCrosscaps.target anchor first second
            beforeWord afterWord,
          validRawTarget⟩
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor false ::
              before ++
                CompletedBlock.crosscap second false ::
                CompletedBlock.crosscap first false ::
                after)),
          validTarget⟩ :=
    NormalizationEquivalent.ofSignedIso targetIso
  have hchain := hraw.trans htarget
  simpa [HandleToCrosscaps.source,
    Crosscap.adjacentSource,
    beforeWord, afterWord,
    CompletedBlock.word, dart,
    List.append_assoc] using hchain

/-- Recursively convert every handle following a fixed positive anchor crosscap. -/
theorem exists_convertHandlesAfterAnchor {n : ℕ}
    (anchor : Fin n)
    (before remaining : List (CompletedBlock n))
    (hnames :
      (CompletedBlock.sequenceNames
        (CompletedBlock.crosscap anchor false ::
          before ++ remaining)).Nodup)
    (validSource :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (CompletedBlock.crosscap anchor false ::
            before ++ remaining))).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor false ::
              before ++ handlesToCrosscaps remaining))).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor false ::
              before ++ remaining)),
          validSource⟩
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor false ::
              before ++ handlesToCrosscaps remaining)),
          validTarget⟩ := by
  induction remaining generalizing before with
  | nil =>
      refine
        ⟨by simpa [handlesToCrosscaps] using validSource,
          ?_⟩
      simpa [handlesToCrosscaps] using
        (NormalizationEquivalent.refl
          (⟨Dyck.oneFace
            (CompletedBlock.sequenceWord
              (CompletedBlock.crosscap anchor false ::
                before ++
                  ([] : List (CompletedBlock n)))),
            validSource⟩ :
            ValidPresentation))
  | cons block remaining ih =>
      cases block with
      | crosscap carrier negative =>
          let block : CompletedBlock n :=
            .crosscap carrier negative
          let witness :=
            ih (before ++ [block])
              (by
                simpa [block, List.append_assoc] using hnames)
              (by
                simpa [block, List.append_assoc] using validSource)
          let validTarget :=
            Classical.choose witness
          have hequivalent :=
            Classical.choose_spec witness
          refine
            ⟨by
              simpa [block, handlesToCrosscaps,
                List.append_assoc] using validTarget,
              ?_⟩
          simpa [block, handlesToCrosscaps,
            List.append_assoc] using hequivalent
      | boundary carrier hole
          carrierNegative holeNegative =>
          let block : CompletedBlock n :=
            .boundary carrier hole
              carrierNegative holeNegative
          let witness :=
            ih (before ++ [block])
              (by
                simpa [block, List.append_assoc] using hnames)
              (by
                simpa [block, List.append_assoc] using validSource)
          let validTarget :=
            Classical.choose witness
          have hequivalent :=
            Classical.choose_spec witness
          refine
            ⟨by
              simpa [block, handlesToCrosscaps,
                List.append_assoc] using validTarget,
              ?_⟩
          simpa [block, handlesToCrosscaps,
            List.append_assoc] using hequivalent
      | handle first second =>
          let firstWitness :=
            exists_convertPositiveAnchorHandle
              anchor first second before remaining
              (by simpa [List.append_assoc] using hnames)
              (by simpa [List.append_assoc] using validSource)
          let validFirst :=
            Classical.choose firstWitness
          have hfirst :=
            Classical.choose_spec firstWitness
          have hnamePerm :
              (CompletedBlock.sequenceNames
                (CompletedBlock.crosscap anchor false ::
                  before ++
                    CompletedBlock.handle first second ::
                    remaining)).Perm
                (CompletedBlock.sequenceNames
                  (CompletedBlock.crosscap anchor false ::
                    before ++
                      CompletedBlock.crosscap second false ::
                      CompletedBlock.crosscap first false ::
                      remaining)) := by
            let nameBefore :=
              [anchor] ++
                CompletedBlock.sequenceNames before
            have hlocal :=
              (List.Perm.swap first second
                (CompletedBlock.sequenceNames remaining)).symm
            simpa [nameBefore, CompletedBlock.names,
              List.append_assoc] using
              (List.Perm.append_left nameBefore hlocal)
          have hfirstNames :
              (CompletedBlock.sequenceNames
                (CompletedBlock.crosscap anchor false ::
                  before ++
                    CompletedBlock.crosscap second false ::
                    CompletedBlock.crosscap first false ::
                    remaining)).Nodup :=
            hnamePerm.nodup
              (by simpa [List.append_assoc] using hnames)
          let restWitness :=
            ih
              (before ++
                [CompletedBlock.crosscap second false,
                  CompletedBlock.crosscap first false])
              (by
                simpa [List.append_assoc] using hfirstNames)
              (by
                simpa [List.append_assoc] using validFirst)
          let validTarget :=
            Classical.choose restWitness
          have hrest :=
            Classical.choose_spec restWitness
          let validTarget' :
              (Dyck.oneFace
                (CompletedBlock.sequenceWord
                  (CompletedBlock.crosscap anchor false ::
                    before ++
                      handlesToCrosscaps
                        (CompletedBlock.handle first second ::
                          remaining)))).IsSurfaceValid := by
            simpa [handlesToCrosscaps,
              List.append_assoc] using validTarget
          have hrest' :
              NormalizationEquivalent
                ⟨Dyck.oneFace
                  (CompletedBlock.sequenceWord
                    (CompletedBlock.crosscap anchor false ::
                      before ++
                        CompletedBlock.crosscap second false ::
                        CompletedBlock.crosscap first false ::
                        remaining)),
                  validFirst⟩
                ⟨Dyck.oneFace
                  (CompletedBlock.sequenceWord
                    (CompletedBlock.crosscap anchor false ::
                      before ++
                        handlesToCrosscaps
                          (CompletedBlock.handle first second ::
                            remaining))),
                  validTarget'⟩ := by
            simpa [handlesToCrosscaps,
              List.append_assoc] using hrest
          refine ⟨validTarget', ?_⟩
          have hchain := hfirst.trans hrest'
          simpa [List.append_assoc] using hchain

/-- Expose one completed crosscap whenever the recursive crosscap count is nonzero. -/
theorem exists_crosscap_decomposition {n : ℕ}
    (blocks : List (CompletedBlock n))
    (hcrosscap :
      CompletedBlock.crosscapCount blocks ≠ 0) :
    ∃ before anchor negative after,
      blocks =
        before ++
          CompletedBlock.crosscap anchor negative ::
          after := by
  induction blocks with
  | nil =>
      exact (hcrosscap rfl).elim
  | cons block blocks ih =>
      cases block with
      | crosscap anchor negative =>
          exact ⟨[], anchor, negative, blocks, rfl⟩
      | handle first second =>
          have htail :
              CompletedBlock.crosscapCount blocks ≠ 0 := by
            simpa [CompletedBlock.crosscapCount] using hcrosscap
          rcases ih htail with
            ⟨before, anchor, negative, after, hdecomp⟩
          exact
            ⟨CompletedBlock.handle first second :: before,
              anchor, negative, after, by
                simp [hdecomp]⟩
      | boundary carrier hole
          carrierNegative holeNegative =>
          have htail :
              CompletedBlock.crosscapCount blocks ≠ 0 := by
            simpa [CompletedBlock.crosscapCount] using hcrosscap
          rcases ih htail with
            ⟨before, anchor, negative, after, hdecomp⟩
          exact
            ⟨CompletedBlock.boundary carrier hole
                carrierNegative holeNegative :: before,
              anchor, negative, after, by
                simp [hdecomp]⟩

/-- Reverse a negative crosscap at the head of a completed block sequence. -/
def negativeCrosscapHeadSignedIso {n : ℕ}
    (anchor : Fin n)
    (tail : List (CompletedBlock n))
    (hanchorTail :
      anchor ∉
        (CompletedBlock.sequenceWord tail).map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (CompletedBlock.crosscap anchor true :: tail)))
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (CompletedBlock.crosscap anchor false :: tail))) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling anchor
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro face
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [CompletedBlock.sequenceWord_cons,
      CompletedBlock.word, List.map_append,
      List.map_cons, List.map_nil, dart,
      Dyck.reverseEdgeRelabeling_neg]
    rw [Dyck.reverseEdgeRelabeling_word
      anchor (CompletedBlock.sequenceWord tail)
      hanchorTail]

/-- Normalize the sign of a displayed head crosscap without changing the remaining block word. -/
theorem exists_normalizeCrosscapHeadOrientation {n : ℕ}
    (anchor : Fin n) (negative : Bool)
    (tail : List (CompletedBlock n))
    (hnames :
      (CompletedBlock.sequenceNames
        (CompletedBlock.crosscap anchor negative ::
          tail)).Nodup)
    (validSource :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (CompletedBlock.crosscap anchor negative ::
            tail))).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor false ::
              tail))).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor negative ::
              tail)),
          validSource⟩
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (CompletedBlock.crosscap anchor false ::
              tail)),
          validTarget⟩ := by
  cases negative with
  | false =>
      exact
        ⟨validSource,
          NormalizationEquivalent.refl _⟩
  | true =>
      have hnames' :
          (anchor ::
            CompletedBlock.sequenceNames tail).Nodup := by
        simpa [CompletedBlock.names] using hnames
      have hanchorTailNames :=
        (List.nodup_cons.mp hnames').1
      have hanchorTail :
          anchor ∉
            (CompletedBlock.sequenceWord tail).map edgeOfDart := by
        simpa using hanchorTailNames
      let iso :=
        negativeCrosscapHeadSignedIso
          anchor tail hanchorTail
      let validTarget :=
        iso.isSurfaceValid validSource
      exact
        ⟨validTarget,
          NormalizationEquivalent.ofSignedIso iso⟩

/-- Result of converting every handle after choosing an existing crosscap anchor. -/
structure CrosscapConversionResult
    (terminal : TerminalCompletedWord) where
  /-- The `target` declaration. -/
  target : TerminalCompletedWord
  equivalent :
    NormalizationEquivalent terminal.validPresentation
      target.validPresentation
  handleCount_eq_zero :
    CompletedBlock.handleCount target.blocks = 0
  crosscapCount_eq :
    CompletedBlock.crosscapCount target.blocks =
      CompletedBlock.crosscapCount terminal.blocks +
        2 * CompletedBlock.handleCount terminal.blocks
  boundaryCount_eq :
    CompletedBlock.boundaryCount target.blocks =
      CompletedBlock.boundaryCount terminal.blocks

/-- Type-valued crosscap decomposition used by the constructive conversion result. -/
structure CrosscapDecomposition {n : ℕ}
    (blocks : List (CompletedBlock n)) where
  /-- The `before` declaration. -/
  before : List (CompletedBlock n)
  /-- The `anchor` declaration. -/
  anchor : Fin n
  /-- The `negative` declaration. -/
  negative : Bool
  /-- The `after` declaration. -/
  after : List (CompletedBlock n)
  blocks_eq :
    blocks =
      before ++
        CompletedBlock.crosscap anchor negative ::
        after

/-- Select one crosscap decomposition from a nonzero crosscap count. -/
noncomputable def chooseCrosscapDecomposition {n : ℕ}
    (blocks : List (CompletedBlock n))
    (hcrosscap :
      CompletedBlock.crosscapCount blocks ≠ 0) :
    CrosscapDecomposition blocks :=
  Classical.choice (by
    rcases exists_crosscap_decomposition
        blocks hcrosscap with
      ⟨before, anchor, negative, after, hdecomp⟩
    exact
      ⟨{ before := before
         anchor := anchor
         negative := negative
         after := after
         blocks_eq := hdecomp }⟩)

/-- The selected crosscap decomposition reconstructs the original completed-block sequence. -/
private theorem chooseCrosscapDecomposition_blocks_eq {n : ℕ}
    (blocks : List (CompletedBlock n))
    (hcrosscap : CompletedBlock.crosscapCount blocks ≠ 0) :
    blocks =
      (chooseCrosscapDecomposition blocks hcrosscap).before ++
        CompletedBlock.crosscap
            (chooseCrosscapDecomposition blocks hcrosscap).anchor
            (chooseCrosscapDecomposition blocks hcrosscap).negative ::
          (chooseCrosscapDecomposition blocks hcrosscap).after :=
  (chooseCrosscapDecomposition blocks hcrosscap).blocks_eq

/-- In the presence of a crosscap, rotate one crosscap to the head, normalize its sign, and
convert every handle into two additional crosscaps. -/
noncomputable def convertHandlesOfCrosscap
    (terminal : TerminalCompletedWord)
    (hcrosscap :
      CompletedBlock.crosscapCount terminal.blocks ≠ 0) :
    CrosscapConversionResult terminal := by
  let decomposition :=
    chooseCrosscapDecomposition
      terminal.blocks hcrosscap
  let before := decomposition.before
  let anchor := decomposition.anchor
  let negative := decomposition.negative
  let after := decomposition.after
  have hdecomp :
      terminal.blocks =
        before ++
          CompletedBlock.crosscap anchor negative ::
          after :=
    decomposition.blocks_eq
  let tail := after ++ before
  let rotatedBlocks :=
    CompletedBlock.crosscap anchor negative :: tail
  have hblockPerm :
      terminal.blocks.Perm rotatedBlocks := by
    rw [hdecomp]
    simpa [tail, rotatedBlocks,
      List.append_assoc] using
      (List.isRotated_append
        (l := before)
        (l' :=
          CompletedBlock.crosscap anchor negative ::
            after)).perm
  have hwordRotated :
      (CompletedBlock.sequenceWord terminal.blocks).IsRotated
        (CompletedBlock.sequenceWord rotatedBlocks) := by
    rw [hdecomp]
    simpa [tail, rotatedBlocks,
      List.append_assoc] using
      (List.isRotated_append
        (l := CompletedBlock.sequenceWord before)
        (l' :=
          (CompletedBlock.crosscap anchor negative).word ++
            CompletedBlock.sequenceWord after))
  let rotation :=
    Dyck.oneFaceSignedIsoOfIsRotated hwordRotated
  let validRotated :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord rotatedBlocks)).IsSurfaceValid :=
    rotation.isSurfaceValid terminal.valid
  have hrotatedNames :
      (CompletedBlock.sequenceNames rotatedBlocks).Nodup :=
    (CompletedBlock.sequenceNames_perm hblockPerm).nodup
      terminal.namesNodup
  let orientationWitness :=
    exists_normalizeCrosscapHeadOrientation
      anchor negative tail
      (by
        simpa [rotatedBlocks] using hrotatedNames)
      (by
        simpa [rotatedBlocks] using validRotated)
  let validPositive :=
    Classical.choose orientationWitness
  have horientation :=
    Classical.choose_spec orientationWitness
  have hpositiveNames :
      (CompletedBlock.sequenceNames
        (CompletedBlock.crosscap anchor false ::
          tail)).Nodup := by
    simpa [rotatedBlocks, CompletedBlock.names] using
      hrotatedNames
  let conversionWitness :=
    exists_convertHandlesAfterAnchor
      anchor [] tail
      (by simpa using hpositiveNames)
      (by simpa using validPositive)
  let validConverted :=
    Classical.choose conversionWitness
  have hconversion :=
    Classical.choose_spec conversionWitness
  let convertedBlocks :=
    CompletedBlock.crosscap anchor false ::
      handlesToCrosscaps tail
  have hconvertedNames :
      (CompletedBlock.sequenceNames convertedBlocks).Nodup := by
    have hperm :=
      (handlesToCrosscaps_sequenceNames_perm tail).cons
        anchor
    have hpositiveNames' :
        (anchor ::
          CompletedBlock.sequenceNames tail).Nodup := by
      simpa [CompletedBlock.names] using hpositiveNames
    have htargetNames :=
      hperm.symm.nodup hpositiveNames'
    simpa [convertedBlocks, CompletedBlock.names] using
      htargetNames
  let target : TerminalCompletedWord :=
    { edgeCount := terminal.edgeCount
      blocks := convertedBlocks
      blocksNonempty := by
        simp [convertedBlocks]
      namesNodup := hconvertedNames
      valid := by
        simpa [convertedBlocks] using validConverted }
  have hrotate :
      NormalizationEquivalent terminal.validPresentation
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord rotatedBlocks),
          validRotated⟩ := by
    exact NormalizationEquivalent.ofSignedIso rotation
  have htarget :
      (⟨Dyck.oneFace
          (CompletedBlock.sequenceWord convertedBlocks),
        (by
          simpa [convertedBlocks] using validConverted)⟩ :
        ValidPresentation) =
        target.validPresentation := by
    apply ValidPresentation.ext
    rfl
  have hequivalent :
      NormalizationEquivalent terminal.validPresentation
        target.validPresentation := by
    have hchain :=
      hrotate.trans
        (horientation.trans hconversion)
    rw [← htarget]
    simpa [rotatedBlocks, convertedBlocks,
      TerminalCompletedWord.validPresentation] using hchain
  have hcounts :=
    counts_eq_of_perm hblockPerm
  refine
    { target := target
      equivalent := hequivalent
      handleCount_eq_zero := ?_
      crosscapCount_eq := ?_
      boundaryCount_eq := ?_ }
  · simpa [target, convertedBlocks,
      CompletedBlock.handleCount] using
      handleCount_handlesToCrosscaps_eq_zero tail
  · rcases hcounts with
      ⟨hcrosscapCount, hhandleCount, _⟩
    simp only [target, convertedBlocks,
      CompletedBlock.crosscapCount,
      crosscapCount_handlesToCrosscaps]
    simp only [rotatedBlocks,
      CompletedBlock.crosscapCount,
      CompletedBlock.handleCount] at hcrosscapCount hhandleCount
    simp only [tail] at hcrosscapCount hhandleCount ⊢
    omega
  · rcases hcounts with
      ⟨_, _, hboundaryCount⟩
    simp only [target, convertedBlocks,
      CompletedBlock.boundaryCount,
      boundaryCount_handlesToCrosscaps]
    simpa [rotatedBlocks, tail,
      CompletedBlock.boundaryCount] using
      hboundaryCount.symm

/-- The constructive crosscap conversion eliminates every handle block. -/
@[simp]
private theorem convertHandlesOfCrosscap_handleCount_eq_zero
    (terminal : TerminalCompletedWord)
    (hcrosscap : CompletedBlock.crosscapCount terminal.blocks ≠ 0) :
    CompletedBlock.handleCount
        (convertHandlesOfCrosscap terminal hcrosscap).target.blocks = 0 :=
  (convertHandlesOfCrosscap terminal hcrosscap).handleCount_eq_zero

/-- A raw one-face context containing one completed boundary loop. -/
def boundaryContextWord {n : ℕ}
    (before after : List (SignedDart (Fin n)))
    (carrier hole : Fin n)
    (carrierNegative holeNegative : Bool) :
    List (SignedDart (Fin n)) :=
  before ++
    (CompletedBlock.boundary carrier hole
      carrierNegative holeNegative).word ++
    after

/-- Reversing only a boundary carrier identifies its negative- and positive-carrier spellings
while fixing a context that avoids that carrier. -/
def negativeBoundaryContextSignedIso {n : ℕ}
    (before after : List (SignedDart (Fin n)))
    (carrier hole : Fin n) (holeNegative : Bool)
    (hcarrierHole : carrier ≠ hole)
    (hcarrierBefore : carrier ∉ before.map edgeOfDart)
    (hcarrierAfter : carrier ∉ after.map edgeOfDart) :
    SignedPresentationIso
      (Dyck.oneFace
        (boundaryContextWord before after
          carrier hole true holeNegative))
      (Dyck.oneFace
        (boundaryContextWord before after
          carrier hole false holeNegative)) where
  edgeRelabeling := Dyck.reverseEdgeRelabeling carrier
  faceEquiv := Equiv.refl _
  boundary_rotated := by
    intro face
    rw [Dyck.oneFace_boundary, Dyck.oneFace_boundary]
    simp only [boundaryContextWord,
      CompletedBlock.word, boundaryLoopWord,
      List.map_append, List.map_cons, List.map_nil]
    rw [
      Dyck.reverseEdgeRelabeling_word carrier
        before hcarrierBefore,
      Dyck.reverseEdgeRelabeling_word carrier
        after hcarrierAfter]
    cases holeNegative with
    | false =>
        have hhole :=
          Dyck.reverseEdgeRelabeling_of_ne
            carrier hole hcarrierHole.symm false
        simp only [Bool.false_eq_true, if_false] at hhole
        simp only [dart, Bool.not_true,
          Dyck.reverseEdgeRelabeling_neg,
          Dyck.reverseEdgeRelabeling_pos] at ⊢
        rw [hhole]
        exact List.IsRotated.refl _
    | true =>
        have hhole :=
          Dyck.reverseEdgeRelabeling_of_ne
            carrier hole hcarrierHole.symm true
        simp only [if_true] at hhole
        simp only [dart, Bool.not_true,
          Dyck.reverseEdgeRelabeling_neg,
          Dyck.reverseEdgeRelabeling_pos] at ⊢
        rw [hhole]
        exact List.IsRotated.refl _

/-- Commute one positive-carrier boundary loop past the following completed block, in arbitrary
cyclic context. -/
theorem exists_commutePositiveBoundaryAdjacent {n : ℕ}
    (before after : List (CompletedBlock n))
    (carrier hole : Fin n) (holeNegative : Bool)
    (block : CompletedBlock n)
    (hcarrierHole : carrier ≠ hole)
    (hcarrierBefore :
      carrier ∉
        (CompletedBlock.sequenceWord before).map edgeOfDart)
    (hcarrierBlock :
      carrier ∉ block.word.map edgeOfDart)
    (hcarrierAfter :
      carrier ∉
        (CompletedBlock.sequenceWord after).map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (before ++
            CompletedBlock.boundary carrier hole false holeNegative ::
            block :: after))).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ block ::
              CompletedBlock.boundary carrier hole false holeNegative ::
              after))).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++
              CompletedBlock.boundary carrier hole false holeNegative ::
              block :: after)),
          validSource⟩
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ block ::
              CompletedBlock.boundary carrier hole false holeNegative ::
              after)),
          validTarget⟩ := by
  let boundary :=
    CompletedBlock.boundary carrier hole false holeNegative
  let loopBody : List (SignedDart (Fin n)) :=
    [dart hole holeNegative]
  let separating := block.word
  let moved :=
    CompletedBlock.sequenceWord after ++
      CompletedBlock.sequenceWord before
  have hblocks :
      (before ++ boundary :: block :: after).Perm
        (before ++ block :: boundary :: after) := by
    apply List.Perm.append_left
    exact List.Perm.swap block boundary after
  let validTarget :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (before ++ block :: boundary :: after))).IsSurfaceValid :=
    CompletedBlock.sequenceWord_isSurfaceValid_of_perm
      hblocks validSource
  have hsourceRotated :
      CompletedBlock.sequenceWord
          (before ++ boundary :: block :: after) |>.IsRotated
        ((LoopGrouping.source carrier
          loopBody separating moved).boundary 0) := by
    simpa [boundary, loopBody, separating, moved,
      CompletedBlock.word, boundaryLoopWord,
      dart,
      LoopGrouping.source, Dyck.oneFace_boundary_zero,
      List.cons_append, List.append_assoc] using
      (List.isRotated_append
        (l := CompletedBlock.sequenceWord before)
        (l' :=
          boundary.word ++ block.word ++
            CompletedBlock.sequenceWord after))
  let sourceRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated hsourceRotated
  let validLoopSource :
      (LoopGrouping.source carrier
        loopBody separating moved).IsSurfaceValid :=
    sourceRotation.isSurfaceValid validSource
  have hgrouped :=
    LoopGrouping.target_boundary_isRotated_grouped
      carrier loopBody separating moved
  have htargetWordRotated :
      (boundary.word ++
          CompletedBlock.sequenceWord after ++
          CompletedBlock.sequenceWord before ++ block.word).IsRotated
        (CompletedBlock.sequenceWord before ++ block.word ++
          boundary.word ++
          CompletedBlock.sequenceWord after) := by
    simpa [List.append_assoc] using
      (List.isRotated_append
        (l :=
          boundary.word ++
            CompletedBlock.sequenceWord after)
        (l' :=
          CompletedBlock.sequenceWord before ++ block.word))
  have htargetRotated :
      (LoopGrouping.target carrier
          loopBody separating moved).boundary 0 |>.IsRotated
        (CompletedBlock.sequenceWord
          (before ++ block :: boundary :: after)) := by
    apply hgrouped.trans
    simpa [boundary, loopBody, separating, moved,
      CompletedBlock.word, boundaryLoopWord,
      dart,
      List.cons_append, List.append_assoc] using
      htargetWordRotated
  let targetRotation :=
    Dyck.oneFaceSignedIsoOfIsRotated htargetRotated
  let validLoopTarget :
      (LoopGrouping.target carrier
        loopBody separating moved).IsSurfaceValid :=
    targetRotation.symm.isSurfaceValid validTarget
  have hcarrierBody :
      carrier ∉ loopBody.map edgeOfDart := by
    simp [loopBody, hcarrierHole]
  have hcarrierSeparating :
      carrier ∉ separating.map edgeOfDart := by
    simpa [separating] using hcarrierBlock
  have hcarrierMoved :
      carrier ∉ moved.map edgeOfDart := by
    simp [moved, hcarrierAfter, hcarrierBefore]
  have hcommute :=
    LoopGrouping.normalizationEquivalent carrier
      loopBody separating moved
      hcarrierBody hcarrierSeparating hcarrierMoved
      validLoopSource validLoopTarget
  exact
    ⟨validTarget,
      (NormalizationEquivalent.ofSignedIso sourceRotation).trans
        (hcommute.trans
          (NormalizationEquivalent.ofSignedIso targetRotation))⟩

/-- Commute a completed boundary loop of either carrier orientation past the following block. -/
theorem exists_commuteBoundaryAdjacent {n : ℕ}
    (before after : List (CompletedBlock n))
    (carrier hole : Fin n)
    (carrierNegative holeNegative : Bool)
    (block : CompletedBlock n)
    (hcarrierHole : carrier ≠ hole)
    (hcarrierBefore :
      carrier ∉
        (CompletedBlock.sequenceWord before).map edgeOfDart)
    (hcarrierBlock :
      carrier ∉ block.word.map edgeOfDart)
    (hcarrierAfter :
      carrier ∉
        (CompletedBlock.sequenceWord after).map edgeOfDart)
    (validSource :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (before ++
            CompletedBlock.boundary carrier hole
              carrierNegative holeNegative ::
            block :: after))).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ block ::
              CompletedBlock.boundary carrier hole
                carrierNegative holeNegative ::
              after))).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++
              CompletedBlock.boundary carrier hole
                carrierNegative holeNegative ::
              block :: after)),
          validSource⟩
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ block ::
              CompletedBlock.boundary carrier hole
                carrierNegative holeNegative ::
              after)),
          validTarget⟩ := by
  cases carrierNegative with
  | false =>
      simpa using
        exists_commutePositiveBoundaryAdjacent
          before after carrier hole holeNegative block
          hcarrierHole hcarrierBefore hcarrierBlock
          hcarrierAfter validSource
  | true =>
      let sourceIso :=
        negativeBoundaryContextSignedIso
          (CompletedBlock.sequenceWord before)
          (block.word ++
            CompletedBlock.sequenceWord after)
          carrier hole holeNegative hcarrierHole
          hcarrierBefore (by
            simp [hcarrierBlock, hcarrierAfter])
      let validPositiveSource :
          (Dyck.oneFace
            (CompletedBlock.sequenceWord
              (before ++
                CompletedBlock.boundary carrier hole
                  false holeNegative ::
                block :: after))).IsSurfaceValid := by
        have hvalid :=
          sourceIso.isSurfaceValid (by
            simpa [boundaryContextWord,
              List.append_assoc] using validSource)
        simpa [boundaryContextWord,
          List.append_assoc] using hvalid
      let positiveWitness :=
        exists_commutePositiveBoundaryAdjacent
          before after carrier hole holeNegative block
          hcarrierHole hcarrierBefore hcarrierBlock
          hcarrierAfter validPositiveSource
      let validPositiveTarget :=
        Classical.choose positiveWitness
      have hpositive :=
        Classical.choose_spec positiveWitness
      let targetIso :=
        negativeBoundaryContextSignedIso
          (CompletedBlock.sequenceWord before ++ block.word)
          (CompletedBlock.sequenceWord after)
          carrier hole holeNegative hcarrierHole
          (by simp [hcarrierBefore, hcarrierBlock])
          hcarrierAfter
      let validTarget :
          (Dyck.oneFace
            (CompletedBlock.sequenceWord
              (before ++ block ::
                CompletedBlock.boundary carrier hole
                  true holeNegative ::
                after))).IsSurfaceValid := by
        have hvalid :=
          targetIso.symm.isSurfaceValid (by
            simpa [boundaryContextWord,
              List.append_assoc] using validPositiveTarget)
        simpa [boundaryContextWord,
          List.append_assoc] using hvalid
      refine ⟨validTarget, ?_⟩
      have hsource :
          NormalizationEquivalent
            ⟨Dyck.oneFace
              (CompletedBlock.sequenceWord
                (before ++
                  CompletedBlock.boundary carrier hole
                    true holeNegative ::
                  block :: after)),
              validSource⟩
            ⟨Dyck.oneFace
              (CompletedBlock.sequenceWord
                (before ++
                  CompletedBlock.boundary carrier hole
                    false holeNegative ::
                  block :: after)),
              validPositiveSource⟩ := by
        let validRawSource :
            (Dyck.oneFace
              (boundaryContextWord
                (CompletedBlock.sequenceWord before)
                (block.word ++
                  CompletedBlock.sequenceWord after)
                carrier hole true holeNegative)).IsSurfaceValid := by
          simpa [boundaryContextWord,
            List.append_assoc] using validSource
        let validRawTarget :
            (Dyck.oneFace
              (boundaryContextWord
                (CompletedBlock.sequenceWord before)
                (block.word ++
                  CompletedBlock.sequenceWord after)
                carrier hole false holeNegative)).IsSurfaceValid := by
          simpa [boundaryContextWord,
            List.append_assoc] using validPositiveSource
        have hraw :
            NormalizationEquivalent
              ⟨Dyck.oneFace
                (boundaryContextWord
                  (CompletedBlock.sequenceWord before)
                  (block.word ++
                    CompletedBlock.sequenceWord after)
                  carrier hole true holeNegative),
                validRawSource⟩
              ⟨Dyck.oneFace
                (boundaryContextWord
                  (CompletedBlock.sequenceWord before)
                  (block.word ++
                    CompletedBlock.sequenceWord after)
                  carrier hole false holeNegative),
                validRawTarget⟩ :=
          NormalizationEquivalent.ofSignedIso sourceIso
        simpa [boundaryContextWord,
          List.append_assoc] using
          hraw
      have htarget :
          NormalizationEquivalent
            ⟨Dyck.oneFace
              (CompletedBlock.sequenceWord
                (before ++ block ::
                  CompletedBlock.boundary carrier hole
                    false holeNegative ::
                  after)),
              validPositiveTarget⟩
            ⟨Dyck.oneFace
              (CompletedBlock.sequenceWord
                (before ++ block ::
                  CompletedBlock.boundary carrier hole
                    true holeNegative ::
                  after)),
              validTarget⟩ := by
        let validRawNegative :
            (Dyck.oneFace
              (boundaryContextWord
                (CompletedBlock.sequenceWord before ++ block.word)
                (CompletedBlock.sequenceWord after)
                carrier hole true holeNegative)).IsSurfaceValid := by
          simpa [boundaryContextWord,
            List.append_assoc] using validTarget
        let validRawPositive :
            (Dyck.oneFace
              (boundaryContextWord
                (CompletedBlock.sequenceWord before ++ block.word)
                (CompletedBlock.sequenceWord after)
                carrier hole false holeNegative)).IsSurfaceValid := by
          simpa [boundaryContextWord,
            List.append_assoc] using validPositiveTarget
        have hraw :
            NormalizationEquivalent
              ⟨Dyck.oneFace
                (boundaryContextWord
                  (CompletedBlock.sequenceWord before ++ block.word)
                  (CompletedBlock.sequenceWord after)
                  carrier hole false holeNegative),
                validRawPositive⟩
              ⟨Dyck.oneFace
                (boundaryContextWord
                  (CompletedBlock.sequenceWord before ++ block.word)
                  (CompletedBlock.sequenceWord after)
                  carrier hole true holeNegative),
                validRawNegative⟩ :=
          (NormalizationEquivalent.ofSignedIso
            (P := ⟨_, validRawNegative⟩)
            (Q := ⟨_, validRawPositive⟩)
            targetIso).symm
        simpa [boundaryContextWord,
          List.append_assoc] using
          hraw
      exact hsource.trans (hpositive.trans htarget)

/-- The duplicate-free block invariant supplies every freshness condition needed by an adjacent
boundary commute. -/
theorem exists_commuteBoundaryAdjacent_of_namesNodup {n : ℕ}
    (before after : List (CompletedBlock n))
    (carrier hole : Fin n)
    (carrierNegative holeNegative : Bool)
    (block : CompletedBlock n)
    (hnames :
      (CompletedBlock.sequenceNames
        (before ++
          CompletedBlock.boundary carrier hole
            carrierNegative holeNegative ::
          block :: after)).Nodup)
    (validSource :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (before ++
            CompletedBlock.boundary carrier hole
              carrierNegative holeNegative ::
            block :: after))).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ block ::
              CompletedBlock.boundary carrier hole
                carrierNegative holeNegative ::
              after))).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++
              CompletedBlock.boundary carrier hole
                carrierNegative holeNegative ::
              block :: after)),
          validSource⟩
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ block ::
              CompletedBlock.boundary carrier hole
                carrierNegative holeNegative ::
              after)),
          validTarget⟩ := by
  have hnames' :
      (CompletedBlock.sequenceNames before ++
        carrier :: hole ::
          (block.names ++
            CompletedBlock.sequenceNames after)).Nodup := by
    simpa [CompletedBlock.names,
      List.append_assoc] using hnames
  rcases List.nodup_append.mp hnames' with
    ⟨_, htailNodup, hbeforeTail⟩
  have hcarrierBeforeNames :
      carrier ∉
        CompletedBlock.sequenceNames before := by
    intro hcarrier
    exact hbeforeTail carrier hcarrier carrier
      (by simp) rfl
  have hcarrierTail :=
    (List.nodup_cons.mp htailNodup).1
  have hcarrierHole : carrier ≠ hole := by
    intro h
    exact hcarrierTail (by simp [h])
  have hcarrierBlockNames :
      carrier ∉ block.names := by
    intro hcarrier
    exact hcarrierTail (by
      simp [hcarrier])
  have hcarrierAfterNames :
      carrier ∉
        CompletedBlock.sequenceNames after := by
    intro hcarrier
    exact hcarrierTail (by
      simp [hcarrier])
  apply exists_commuteBoundaryAdjacent
    before after carrier hole
      carrierNegative holeNegative block
      hcarrierHole
  · simpa only [
      CompletedBlock.mem_sequenceWord_edge_iff_mem_sequenceNames] using
      hcarrierBeforeNames
  · simpa only [
      CompletedBlock.mem_map_edgeOfDart_word_iff,
      CompletedBlock.mem_names_iff_mem_edges] using
      hcarrierBlockNames
  · simpa only [
      CompletedBlock.mem_sequenceWord_edge_iff_mem_sequenceNames] using
      hcarrierAfterNames

/-- Commute one completed boundary loop across an arbitrary finite block interval. -/
theorem exists_moveBoundaryAcross {n : ℕ}
    (before middle after : List (CompletedBlock n))
    (carrier hole : Fin n)
    (carrierNegative holeNegative : Bool)
    (hnames :
      (CompletedBlock.sequenceNames
        (before ++
          CompletedBlock.boundary carrier hole
            carrierNegative holeNegative ::
          middle ++ after)).Nodup)
    (validSource :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (before ++
            CompletedBlock.boundary carrier hole
              carrierNegative holeNegative ::
            middle ++ after))).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ middle ++
              CompletedBlock.boundary carrier hole
                carrierNegative holeNegative ::
              after))).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++
              CompletedBlock.boundary carrier hole
                carrierNegative holeNegative ::
              middle ++ after)),
          validSource⟩
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ middle ++
              CompletedBlock.boundary carrier hole
                carrierNegative holeNegative ::
              after)),
          validTarget⟩ := by
  induction middle generalizing before with
  | nil =>
      refine ⟨?_, ?_⟩
      · simpa using validSource
      · simpa using
          (NormalizationEquivalent.refl
            (⟨Dyck.oneFace
              (CompletedBlock.sequenceWord
                (before ++
                  [CompletedBlock.boundary carrier hole
                    carrierNegative holeNegative] ++
                  after)),
              validSource⟩ :
              ValidPresentation))
  | cons block middle ih =>
      let boundary :=
        CompletedBlock.boundary carrier hole
          carrierNegative holeNegative
      let firstWitness :=
        exists_commuteBoundaryAdjacent_of_namesNodup
          before (middle ++ after)
          carrier hole carrierNegative holeNegative block
          (by
            simpa [boundary, List.append_assoc] using hnames)
          (by
            simpa [boundary, List.append_assoc] using validSource)
      let validFirst :=
        Classical.choose firstWitness
      have hfirst :=
        Classical.choose_spec firstWitness
      have hblocks :
          (before ++ boundary :: block :: middle ++ after).Perm
            (before ++ block :: boundary :: middle ++ after) := by
        simpa [List.append_assoc] using
          (List.Perm.append_left before
            (List.Perm.swap block boundary
              (middle ++ after)))
      have hfirstNames :
          (CompletedBlock.sequenceNames
            (before ++ block :: boundary :: middle ++ after)).Nodup :=
        (CompletedBlock.sequenceNames_perm hblocks).nodup
          (by
            simpa [boundary, List.append_assoc] using hnames)
      let restWitness :=
        ih (before ++ [block])
          (by
            simpa [boundary, List.append_assoc] using hfirstNames)
          (by
            simpa [boundary, List.append_assoc] using validFirst)
      let validTarget :=
        Classical.choose restWitness
      have hrest :=
        Classical.choose_spec restWitness
      let validTarget' :
          (Dyck.oneFace
            (CompletedBlock.sequenceWord
              (before ++ block :: middle ++
                boundary :: after))).IsSurfaceValid := by
        simpa [boundary, List.append_assoc] using validTarget
      have hrest' :
          NormalizationEquivalent
            ⟨Dyck.oneFace
              (CompletedBlock.sequenceWord
                (before ++ block ::
                  CompletedBlock.boundary carrier hole
                    carrierNegative holeNegative ::
                  (middle ++ after))),
              validFirst⟩
            ⟨Dyck.oneFace
              (CompletedBlock.sequenceWord
                (before ++ block :: middle ++
                  boundary :: after)),
              validTarget'⟩ := by
        simpa [boundary, List.append_assoc] using hrest
      refine ⟨validTarget', ?_⟩
      have hchain := hfirst.trans hrest'
      simpa [boundary, List.append_assoc] using hchain

/-- Stably partition every completed boundary loop behind all closed-surface blocks, in arbitrary
cyclic context. -/
theorem exists_sortBoundariesInContext {n : ℕ}
    (before blocks after : List (CompletedBlock n))
    (hnames :
      (CompletedBlock.sequenceNames
        (before ++ blocks ++ after)).Nodup)
    (validSource :
      (Dyck.oneFace
        (CompletedBlock.sequenceWord
          (before ++ blocks ++ after))).IsSurfaceValid) :
    ∃ validTarget :
        (Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ boundariesLast blocks ++
              after))).IsSurfaceValid,
      NormalizationEquivalent
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ blocks ++ after)),
          validSource⟩
        ⟨Dyck.oneFace
          (CompletedBlock.sequenceWord
            (before ++ boundariesLast blocks ++
              after)),
          validTarget⟩ := by
  induction blocks generalizing before with
  | nil =>
      refine
        ⟨by
          simpa [boundariesLast, closedBlocks,
            boundaryBlocks] using validSource,
          ?_⟩
      simpa [boundariesLast, closedBlocks,
        boundaryBlocks] using
        (NormalizationEquivalent.refl
          (⟨Dyck.oneFace
            (CompletedBlock.sequenceWord
              (before ++ ([] : List (CompletedBlock n)) ++
                after)),
            validSource⟩ :
            ValidPresentation))
  | cons block blocks ih =>
      cases block with
      | crosscap carrier negative =>
          let block : CompletedBlock n :=
            .crosscap carrier negative
          let witness :=
            ih (before ++ [block])
              (by
                simpa [block, List.append_assoc] using hnames)
              (by
                simpa [block, List.append_assoc] using validSource)
          let validTarget :=
            Classical.choose witness
          have hequivalent :=
            Classical.choose_spec witness
          refine
            ⟨by
              simpa [block, boundariesLast, closedBlocks,
                boundaryBlocks, isBoundary,
                List.append_assoc] using validTarget,
              ?_⟩
          simpa [block, boundariesLast, closedBlocks,
            boundaryBlocks, isBoundary,
            List.append_assoc] using hequivalent
      | handle first second =>
          let block : CompletedBlock n :=
            .handle first second
          let witness :=
            ih (before ++ [block])
              (by
                simpa [block, List.append_assoc] using hnames)
              (by
                simpa [block, List.append_assoc] using validSource)
          let validTarget :=
            Classical.choose witness
          have hequivalent :=
            Classical.choose_spec witness
          refine
            ⟨by
              simpa [block, boundariesLast, closedBlocks,
                boundaryBlocks, isBoundary,
                List.append_assoc] using validTarget,
              ?_⟩
          simpa [block, boundariesLast, closedBlocks,
            boundaryBlocks, isBoundary,
            List.append_assoc] using hequivalent
      | boundary carrier hole carrierNegative holeNegative =>
          let boundary : CompletedBlock n :=
            .boundary carrier hole
              carrierNegative holeNegative
          let tailWitness :=
            ih (before ++ [boundary])
              (by
                simpa [boundary, List.append_assoc] using hnames)
              (by
                simpa [boundary, List.append_assoc] using validSource)
          let validTail :=
            Classical.choose tailWitness
          have htail :=
            Classical.choose_spec tailWitness
          have hcontextPerm :
              (before ++ boundary :: blocks ++ after).Perm
                ((before ++ [boundary]) ++
                  boundariesLast blocks ++ after) := by
            simpa [List.append_assoc] using
              (boundariesLastInContext_perm
                (before ++ [boundary]) blocks after).symm
          have htailNames :
              (CompletedBlock.sequenceNames
                ((before ++ [boundary]) ++
                  boundariesLast blocks ++ after)).Nodup :=
            (CompletedBlock.sequenceNames_perm hcontextPerm).nodup
              (by
                simpa [boundary, List.append_assoc] using hnames)
          let moveWitness :=
            exists_moveBoundaryAcross
              before (closedBlocks blocks)
              (boundaryBlocks blocks ++ after)
              carrier hole carrierNegative holeNegative
              (by
                simpa [boundary, boundariesLast,
                  List.append_assoc] using htailNames)
              (by
                simpa [boundary, boundariesLast,
                  List.append_assoc] using validTail)
          let validTarget :=
            Classical.choose moveWitness
          have hmove :=
            Classical.choose_spec moveWitness
          let validTarget' :
              (Dyck.oneFace
                (CompletedBlock.sequenceWord
                  (before ++
                    boundariesLast
                      (CompletedBlock.boundary carrier hole
                        carrierNegative holeNegative ::
                        blocks) ++
                    after))).IsSurfaceValid := by
            simpa [boundary, boundariesLast, closedBlocks,
              boundaryBlocks, isBoundary,
              List.append_assoc] using validTarget
          have hmove' :
              NormalizationEquivalent
                ⟨Dyck.oneFace
                  (CompletedBlock.sequenceWord
                    ((before ++ [boundary]) ++
                      boundariesLast blocks ++ after)),
                  validTail⟩
                ⟨Dyck.oneFace
                  (CompletedBlock.sequenceWord
                    (before ++
                      boundariesLast
                        (CompletedBlock.boundary carrier hole
                          carrierNegative holeNegative ::
                          blocks) ++
                      after)),
                  validTarget'⟩ := by
            simpa [boundary, boundariesLast, closedBlocks,
              boundaryBlocks, isBoundary,
              List.append_assoc] using hmove
          refine ⟨validTarget', ?_⟩
          have hchain := htail.trans hmove'
          simpa [boundary, List.append_assoc] using hchain

/-- The stable boundary partition as another completed terminal word. -/
noncomputable def boundariesLastWord
    (terminal : TerminalCompletedWord) :
    TerminalCompletedWord where
  edgeCount := terminal.edgeCount
  blocks := boundariesLast terminal.blocks
  blocksNonempty := by
    intro hnil
    apply terminal.blocksNonempty
    have hperm :=
      boundariesLast_perm terminal.blocks
    rw [hnil] at hperm
    exact hperm.symm.eq_nil
  namesNodup := by
    exact
      (CompletedBlock.sequenceNames_perm
        (boundariesLast_perm terminal.blocks).symm).nodup
          terminal.namesNodup
  valid := by
    exact
      CompletedBlock.sequenceWord_isSurfaceValid_of_perm
        (boundariesLast_perm terminal.blocks).symm
        terminal.valid

/-- Boundary sorting preserves the exact normal form selected by block counts. -/
theorem boundariesLastWord_normalForm
    (terminal : TerminalCompletedWord) :
    (boundariesLastWord terminal).normalForm =
      terminal.normalForm :=
  normalForm_eq_of_perm
    (boundariesLast_perm terminal.blocks)

/-- Every completed terminal word is normalization-equivalent to its stable boundary partition. -/
theorem normalizationEquivalent_boundariesLastWord
    (terminal : TerminalCompletedWord) :
    NormalizationEquivalent terminal.validPresentation
      (boundariesLastWord terminal).validPresentation := by
  let witness :=
    exists_sortBoundariesInContext
      ([] : List (CompletedBlock terminal.edgeCount))
      terminal.blocks []
      (by simpa using terminal.namesNodup)
      (by simpa using terminal.valid)
  let validTarget :=
    Classical.choose witness
  have hequivalent :=
    Classical.choose_spec witness
  simpa [TerminalCompletedWord.validPresentation,
    boundariesLastWord] using hequivalent

/-- Handle conversion preserves the exact normal form selected by the original nonorientable
completed word. -/
theorem crosscapConversionResult_normalForm_eq
    (terminal : TerminalCompletedWord)
    (hcrosscap :
      CompletedBlock.crosscapCount terminal.blocks ≠ 0)
    (conversion : CrosscapConversionResult terminal) :
    conversion.target.normalForm =
      terminal.normalForm := by
  simp [TerminalCompletedWord.normalForm,
    CompletedBlock.normalForm, hcrosscap,
    conversion.handleCount_eq_zero,
    conversion.crosscapCount_eq,
    conversion.boundaryCount_eq]

/-- The completed-block terminal seam: stable-sort boundary blocks, convert all handles when a
crosscap is present, normalize every edge orientation, and relabel positionally to the single
canonical finite-cyclic presentation selected by `TerminalCompletedWord.normalForm`. -/
theorem terminalCompletedNormalizer :
    TerminalCompletedNormalizer where
  equivalent terminal := by
    by_cases hcrosscap :
        CompletedBlock.crosscapCount terminal.blocks = 0
    · let ordered := boundariesLastWord terminal
      have hcounts :
          CompletedBlock.crosscapCount ordered.blocks =
              CompletedBlock.crosscapCount terminal.blocks ∧
            CompletedBlock.handleCount ordered.blocks =
              CompletedBlock.handleCount terminal.blocks ∧
            CompletedBlock.boundaryCount ordered.blocks =
              CompletedBlock.boundaryCount terminal.blocks := by
        simpa [ordered, boundariesLastWord] using
          counts_eq_of_perm
            (boundariesLast_perm terminal.blocks)
      have horderedCrosscap :
          CompletedBlock.crosscapCount ordered.blocks = 0 := by
        rw [hcounts.1, hcrosscap]
      have hshape :
          blockKinds ordered.blocks =
            List.replicate
                (CompletedBlock.handleCount ordered.blocks)
                BlockKind.handle ++
              List.replicate
                (CompletedBlock.boundaryCount ordered.blocks)
                BlockKind.boundary := by
        change
          blockKinds (boundariesLast terminal.blocks) =
            List.replicate
                (CompletedBlock.handleCount
                  (boundariesLast terminal.blocks))
                BlockKind.handle ++
              List.replicate
                (CompletedBlock.boundaryCount
                  (boundariesLast terminal.blocks))
                BlockKind.boundary
        rw [(counts_eq_of_perm
              (boundariesLast_perm terminal.blocks)).2.1,
          (counts_eq_of_perm
              (boundariesLast_perm terminal.blocks)).2.2]
        exact
          blockKinds_boundariesLast_of_crosscapCount_eq_zero
            terminal.blocks hcrosscap
      let result :=
        orientableOrderedResult ordered
          horderedCrosscap hshape
      have hresultNormalForm :
          result.normalForm = terminal.normalForm := by
        change ordered.normalForm = terminal.normalForm
        exact boundariesLastWord_normalForm terminal
      have htarget :
          canonicalValidPresentation result.normalForm
              result.admissible =
            canonicalValidPresentation terminal.normalForm
              terminal.admissible := by
        apply ValidPresentation.ext
        simp only [canonicalValidPresentation_presentation]
        exact congrArg NormalForm.canonicalPresentation
          hresultNormalForm
      have horderedEquivalent :
          NormalizationEquivalent ordered.validPresentation
            (canonicalValidPresentation terminal.normalForm
              terminal.admissible) := by
        rw [← htarget]
        exact result.equivalent
      exact
        (normalizationEquivalent_boundariesLastWord terminal).trans
          horderedEquivalent
    · let conversion :=
        convertHandlesOfCrosscap terminal hcrosscap
      let ordered :=
        boundariesLastWord conversion.target
      have hcounts :
          CompletedBlock.crosscapCount ordered.blocks =
              CompletedBlock.crosscapCount
                conversion.target.blocks ∧
            CompletedBlock.handleCount ordered.blocks =
              CompletedBlock.handleCount
                conversion.target.blocks ∧
            CompletedBlock.boundaryCount ordered.blocks =
              CompletedBlock.boundaryCount
                conversion.target.blocks := by
        simpa [ordered, boundariesLastWord] using
          counts_eq_of_perm
            (boundariesLast_perm conversion.target.blocks)
      have horderedHandle :
          CompletedBlock.handleCount ordered.blocks = 0 := by
        rw [hcounts.2.1]
        exact conversion.handleCount_eq_zero
      have horderedCrosscap :
          CompletedBlock.crosscapCount ordered.blocks ≠ 0 := by
        rw [hcounts.1, conversion.crosscapCount_eq]
        omega
      have hshape :
          blockKinds ordered.blocks =
            List.replicate
                (CompletedBlock.crosscapCount ordered.blocks)
                BlockKind.crosscap ++
              List.replicate
                (CompletedBlock.boundaryCount ordered.blocks)
                BlockKind.boundary := by
        change
          blockKinds (boundariesLast conversion.target.blocks) =
            List.replicate
                (CompletedBlock.crosscapCount
                  (boundariesLast conversion.target.blocks))
                BlockKind.crosscap ++
              List.replicate
                (CompletedBlock.boundaryCount
                  (boundariesLast conversion.target.blocks))
                BlockKind.boundary
        rw [(counts_eq_of_perm
              (boundariesLast_perm
                conversion.target.blocks)).1,
          (counts_eq_of_perm
              (boundariesLast_perm
                conversion.target.blocks)).2.2]
        exact
          blockKinds_boundariesLast_of_handleCount_eq_zero
            conversion.target.blocks
            conversion.handleCount_eq_zero
      let result :=
        nonOrientableOrderedResult ordered
          horderedHandle horderedCrosscap hshape
      have hconversionNormalForm :
          conversion.target.normalForm =
            terminal.normalForm :=
        crosscapConversionResult_normalForm_eq
          terminal hcrosscap conversion
      have hresultNormalForm :
          result.normalForm = terminal.normalForm := by
        change ordered.normalForm = terminal.normalForm
        exact
          (boundariesLastWord_normalForm
            conversion.target).trans hconversionNormalForm
      have htarget :
          canonicalValidPresentation result.normalForm
              result.admissible =
            canonicalValidPresentation terminal.normalForm
              terminal.admissible := by
        apply ValidPresentation.ext
        simp only [canonicalValidPresentation_presentation]
        exact congrArg NormalForm.canonicalPresentation
          hresultNormalForm
      have horderedEquivalent :
          NormalizationEquivalent ordered.validPresentation
            (canonicalValidPresentation terminal.normalForm
              terminal.admissible) := by
        rw [← htarget]
        exact result.equivalent
      exact
        conversion.equivalent.trans
          ((normalizationEquivalent_boundariesLastWord
            conversion.target).trans horderedEquivalent)

/-- The fully discharged token-level terminal normalizer consumed by the terminating marked-word
recursion. -/
noncomputable def terminalMarkedNormalizer :
    TerminalMarkedNormalizer :=
  TerminalProtectedNormalizer.toTerminalMarkedNormalizer
    (TerminalCompletedNormalizer.toTerminalProtectedNormalizer
      terminalCompletedNormalizer)

end TerminalNormalization

end Pairing

end WordReduction

/-- Normalize any valid connected finite-cyclic surface presentation to the one canonical
presentation selected by an admissible `NormalForm`. -/
noncomputable def normalizeConnectedToCanonical
    (P : ValidPresentation)
    (connectedP : P.presentation.IsConnected) :
    NormalizationResult P :=
  WordReduction.Pairing.normalizeConnectedOfTerminal
    WordReduction.Pairing.TerminalNormalization.terminalMarkedNormalizer
    P connectedP

/-- Universal Gallier--Xu normalization theorem at the faithful polygonal-realization interface:
every surface-valid connected finite-cyclic presentation is polygonally equivalent to the
existing canonical presentation of an Eval-admissible normal form. -/
theorem exists_admissible_normalForm_polygonallyEquivalent
    (P : FiniteCyclicPresentation)
    (validP : P.IsSurfaceValid)
    (connectedP : P.IsConnected) :
    ∃ N : NormalForm,
      ∃ hN : N.IsEvalAdmissible,
        P.PolygonallyEquivalent
          N.canonicalPresentation validP
          (N.canonicalPresentation_isSurfaceValid hN) := by
  let result :=
    normalizeConnectedToCanonical
      ⟨P, validP⟩ connectedP
  exact
    ⟨result.normalForm, result.admissible,
      result.polygonallyEquivalent⟩

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
