/-
Copyright (c) 2026 Juliane Trianon Fraga and Vinicius de Oliveira Rodrigues. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Juliane Trianon Fraga, Vinicius de Oliveira Rodrigues
-/

import LeanPool.Wallace.MathlibFoundations
import LeanPool.Wallace.FiniteCombinatorics

/-!
# Triangular coding and block preprocessing

This file supplies the unconditional set-theoretic bookkeeping that precedes the character
construction.  The index set is the canonical well-order of cardinality continuum.  All
injective sequences in the corresponding free Abelian group are coded, and their codes are
assigned distinct indices strictly above every coordinate in the sequence.  The second half of
the file constructs a genuine subsequence whose prescribed finite blocks are bounded-independent.
-/

open Set
open scoped Cardinal

namespace Wallace
namespace TriangularPreprocess

noncomputable section

/-! ## The continuum initial ordinal and its free group -/

/-- The canonical well-ordered index type of cardinality continuum. -/
abbrev ContinuumIndex := (Cardinal.ord (𝔠 : Cardinal.{0})).ToType

/-- The free Abelian group on the canonical continuum index. -/
abbrev ContinuumFreeGroup := ContinuumIndex →₀ ℤ

/-- The type of all injective sequences in the free group. -/
abbrev InjectiveSequences :=
  {s : ℕ → ContinuumFreeGroup // Function.Injective s}

theorem mk_continuumIndex : #ContinuumIndex = 𝔠 := by
  exact Cardinal.mk_ord_toType 𝔠

theorem continuumIndex_infinite : Infinite ContinuumIndex := by
  exact Cardinal.aleph0_le_mk_iff.mp <| by
    simpa only [mk_continuumIndex] using Cardinal.aleph0_le_continuum

theorem mk_continuumFreeGroup : #ContinuumFreeGroup = 𝔠 := by
  let : Infinite ContinuumIndex := continuumIndex_infinite
  change #(ContinuumIndex →₀ ℤ) = 𝔠
  rw [Cardinal.mk_finsupp_of_infinite, mk_continuumIndex, Cardinal.mk_int]
  exact max_eq_left Cardinal.aleph0_le_continuum

theorem mk_continuumFreeGroup_sequences : #(ℕ → ContinuumFreeGroup) = 𝔠 := by
  change #(ℕ → (ContinuumIndex →₀ ℤ)) = 𝔠
  rw [Cardinal.mk_arrow, mk_continuumFreeGroup, Cardinal.mk_nat]
  simpa only [Cardinal.lift_id] using Cardinal.continuum_power_aleph0

/-- An injective ray along one basis vector. -/
def basisRay (i : ContinuumIndex) (n : ℕ) : ContinuumFreeGroup :=
  Finsupp.single i (n : ℤ)

theorem basisRay_injective (i : ContinuumIndex) : Function.Injective (basisRay i) := by
  intro m n h
  have hi := congrArg (fun z : ContinuumFreeGroup => z i) h
  simpa [basisRay] using hi

theorem basisRay_family_injective :
    Function.Injective (fun i : ContinuumIndex =>
      (⟨basisRay i, basisRay_injective i⟩ : InjectiveSequences)) := by
  intro i j hij
  have hfun : basisRay i = basisRay j := congrArg Subtype.val hij
  have hi := congrArg (fun s : ℕ → ContinuumFreeGroup => s 1 i) hfun
  by_contra hne
  simp [basisRay, hne] at hi

theorem mk_injectiveSequences : #InjectiveSequences = 𝔠 := by
  apply le_antisymm
  · exact (Cardinal.mk_subtype_le _).trans_eq mk_continuumFreeGroup_sequences
  · rw [← mk_continuumIndex]
    exact Cardinal.mk_le_of_injective basisRay_family_injective

/-- A fixed equivalence between the canonical continuum index and all injective sequences. -/
def sequenceCodeEquiv : ContinuumIndex ≃ InjectiveSequences :=
  Classical.choice <| Cardinal.eq.mp <| mk_continuumIndex.trans mk_injectiveSequences.symm

/-- The sequence represented by a code. -/
def codedSequence (a : ContinuumIndex) : ℕ → ContinuumFreeGroup :=
  (sequenceCodeEquiv a).1

theorem codedSequence_injective (a : ContinuumIndex) :
    Function.Injective (codedSequence a) :=
  (sequenceCodeEquiv a).2

/-! ## Countable supports have strict upper bounds -/

/-- All coordinates that occur in a sequence. -/
def sequenceSupport (s : ℕ → ContinuumFreeGroup) : Set ContinuumIndex :=
  {i | ∃ n, i ∈ (s n).support}

theorem sequenceSupport_countable (s : ℕ → ContinuumFreeGroup) :
    (sequenceSupport s).Countable := by
  rw [show sequenceSupport s = ⋃ n, ((s n).support : Set ContinuumIndex) by
    ext i
    simp [sequenceSupport]]
  exact Set.countable_iUnion fun n => (s n).support.finite_toSet.countable

/-- Every countable set of continuum indices is strictly bounded. -/
theorem exists_strict_upperBound_of_countable
    {S : Set ContinuumIndex} (hS : S.Countable) :
    ∃ i : ContinuumIndex, ∀ j ∈ S, j < i := by
  have hcard : #S < Order.cof ContinuumIndex := by
    calc
      #S ≤ ℵ₀ := Cardinal.le_aleph0_iff_set_countable.mpr hS
      _ < (𝔠 : Cardinal).ord.cof := Wallace.aleph0_lt_cof_continuum
      _ = Order.cof ContinuumIndex := (Ordinal.cof_toType _).symm
  have hncof : ¬ IsCofinal S := by
    intro hcof
    exact hcard.2 (Order.cof_le hcof)
  exact not_isCofinal_iff.mp hncof

/-- A chosen strict upper bound for the support of each coded sequence. -/
def supportBound (a : ContinuumIndex) : ContinuumIndex :=
  Classical.choose <| exists_strict_upperBound_of_countable
    (sequenceSupport_countable (codedSequence a))

theorem support_lt_supportBound (a : ContinuumIndex) {n : ℕ} {i : ContinuumIndex}
    (hi : i ∈ (codedSequence a n).support) : i < supportBound a := by
  exact (Classical.choose_spec <| exists_strict_upperBound_of_countable
    (sequenceSupport_countable (codedSequence a))) i ⟨n, hi⟩

/-! ## Fresh indices above all supports -/

theorem exists_fresh_above
    (bound : ContinuumIndex → ContinuumIndex) (a : ContinuumIndex)
    (previous : ∀ b, b < a → ContinuumIndex) :
    ∃ i, bound a < i ∧ ∀ b (h : b < a), previous b h ≠ i := by
  let prior : Set ContinuumIndex :=
    Set.range fun b : Set.Iio a => previous b b.property
  let excluded : Set ContinuumIndex := Set.Iic (bound a) ∪ prior
  have hIic : #(Set.Iic (bound a)) < #ContinuumIndex := by
    apply Cardinal.mk_Iic_lt
    · simp
    · simpa only [mk_continuumIndex] using Cardinal.aleph0_le_continuum
  have hprior : #prior < #ContinuumIndex := by
    change #(Set.range fun b : Set.Iio a => previous b b.property) < #ContinuumIndex
    exact Cardinal.mk_range_le.trans_lt (Cardinal.mk_Iio_lt a (by simp))
  have hexcluded : #excluded < #ContinuumIndex := by
    apply (Cardinal.mk_union_le _ _).trans_lt
    exact Cardinal.add_lt_of_lt
      (by simpa only [mk_continuumIndex] using Cardinal.aleph0_le_continuum)
      hIic hprior
  have hne : excluded ≠ Set.univ := by
    intro heq
    have : #excluded = #ContinuumIndex := by rw [heq, Cardinal.mk_univ]
    exact hexcluded.ne this
  obtain ⟨i, hi⟩ := (Set.ne_univ_iff_exists_notMem excluded).mp hne
  refine ⟨i, ?_, ?_⟩
  · exact lt_of_not_ge fun h => hi (Set.mem_union_left prior h)
  · intro b hb hbi
    apply hi
    apply Set.mem_union_right (Set.Iic (bound a))
    exact ⟨⟨b, hb⟩, hbi⟩

/-- Transfinite fresh-index assignment.  At stage `a`, it avoids all values assigned below `a`
and lies strictly above `bound a`. -/
def freshIndex (bound : ContinuumIndex → ContinuumIndex) :
    ContinuumIndex → ContinuumIndex :=
  WellFoundedLT.fix fun a previous =>
    Classical.choose (exists_fresh_above bound a previous)

theorem freshIndex_spec (bound : ContinuumIndex → ContinuumIndex) (a : ContinuumIndex) :
    bound a < freshIndex bound a ∧
      ∀ b (_h : b < a), freshIndex bound b ≠ freshIndex bound a := by
  rw [freshIndex, WellFoundedLT.fix_eq]
  exact Classical.choose_spec (exists_fresh_above bound a fun b _ => freshIndex bound b)

theorem freshIndex_injective (bound : ContinuumIndex → ContinuumIndex) :
    Function.Injective (freshIndex bound) := by
  apply Function.Injective.of_lt_imp_ne
  intro a b hab
  exact (freshIndex_spec bound b).2 a hab

/-- The injective index assigned to every sequence code. -/
def codeIndex : ContinuumIndex ↪ ContinuumIndex :=
  ⟨freshIndex supportBound, freshIndex_injective supportBound⟩

theorem codedSequence_supportedBelow (a : ContinuumIndex) :
    FiniteCombinatorics.SupportedBelow (codedSequence a) (codeIndex a) := by
  intro n i hi
  exact (support_lt_supportBound a hi).trans (freshIndex_spec supportBound a).1

/-! ## Blockwise bounded-independence selection -/

open FiniteCombinatorics

/-- Bounded independence is inherited by finite subsets. -/
theorem boundedIndependent_mono
    {G : Type*} [AddCommGroup G] {M : ℕ} {X Y : Finset G}
    (hY : BoundedIndependent M Y) (hXY : X ⊆ Y) :
    BoundedIndependent M X := by
  classical
  intro c hc hsum
  let c' : G → ℤ := fun z => if z ∈ X then c z else 0
  have hc' : ∀ y ∈ Y, Int.natAbs (c' y) ≤ M := by
    intro y hy
    by_cases hyX : y ∈ X
    · simpa [c', hyX] using hc y hyX
    · simp [c', hyX]
  have hsum' : (∑ y ∈ Y, c' y • y) = 0 := by
    rw [← hsum]
    calc
      ∑ y ∈ Y, c' y • y = ∑ x ∈ X, c' x • x := by
        symm
        apply Finset.sum_subset hXY
        intro y hyY hyX
        simp [c', hyX]
      _ = ∑ x ∈ X, c x • x := by
        apply Finset.sum_congr rfl
        intro x hx
        simp [c', hx]
  have hz := hY c' hc' hsum'
  intro x hx
  simpa [c', hx] using hz x (hXY hx)

/-- An injective sequence has arbitrarily late terms outside any fixed finite set. -/
theorem exists_index_gt_avoiding_finset
    {G : Type*} {u : ℕ → G} (hu : Function.Injective u)
    (B : Finset G) (k : ℕ) :
    ∃ m, k < m ∧ u m ∉ B := by
  let bad : Set ℕ := u ⁻¹' (B : Set G)
  have hbad : bad.Finite := B.finite_toSet.preimage hu.injOn
  obtain ⟨m, hmk, hm⟩ := (Set.Ioi_infinite k).exists_notMem_finite hbad
  exact ⟨m, hmk, hm⟩

/-- State of the recursive block selector.  `values l` contains the values already selected in
block `l`; `last` is the last source index used. -/
private structure BlockSelectionState (G : Type*) where
  last : ℕ
  values : ℕ → Finset G

private def initialBlockSelectionState (G : Type*) : BlockSelectionState G where
  last := 0
  values := fun _ => ∅

private noncomputable def excludedAt
    {G : Type*} [AddCommGroup G] (M block : ℕ → ℕ) (n : ℕ)
    (st : BlockSelectionState G) : Finset G := by
  classical
  exact st.values (block n) ∪
    forbiddenFinset (M (block n)) (st.values (block n))

/-- The next source index: strictly later than the previous one and outside both the values
already used in this block and every bounded forbidden equation over them. -/
private def nextBlockIndex
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (n : ℕ) (st : BlockSelectionState G) : ℕ :=
  Classical.choose <|
    exists_index_gt_avoiding_finset hu (excludedAt M block n st) st.last

private theorem nextBlockIndex_spec
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (n : ℕ) (st : BlockSelectionState G) :
    st.last < nextBlockIndex u hu M block n st ∧
      u (nextBlockIndex u hu M block n st) ∉ excludedAt M block n st :=
  Classical.choose_spec <|
    exists_index_gt_avoiding_finset hu (excludedAt M block n st) st.last

private theorem nextBlockIndex_not_mem_values
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (n : ℕ) (st : BlockSelectionState G) :
    u (nextBlockIndex u hu M block n st) ∉ st.values (block n) := by
  classical
  exact fun h => (nextBlockIndex_spec u hu M block n st).2
    (Finset.mem_union_left _ h)

private theorem nextBlockIndex_not_forbidden
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G]
    (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (n : ℕ) (st : BlockSelectionState G) :
    ¬ Forbidden (M (block n)) (st.values (block n))
      (u (nextBlockIndex u hu M block n st)) := by
  classical
  intro h
  exact (nextBlockIndex_spec u hu M block n st).2
    (Finset.mem_union_right _ <| forbidden_mem_forbiddenFinset h)

private noncomputable def blockSelectionStep
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (n : ℕ) (st : BlockSelectionState G) :
    BlockSelectionState G := by
  classical
  let k := nextBlockIndex u hu M block n st
  exact
    { last := k
      values := Function.update st.values (block n)
        (insert (u k) (st.values (block n))) }

/-- States after the first `n` positions of the new sequence have been selected. -/
private def blockSelectionStates
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) : ℕ → BlockSelectionState G
  | 0 => initialBlockSelectionState G
  | n + 1 => blockSelectionStep u hu M block n (blockSelectionStates u hu M block n)

/-- The actual source-index subsequence selected by the state recursion. -/
def blockSubsequenceIndex
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (n : ℕ) : ℕ :=
  (blockSelectionStates u hu M block (n + 1)).last

private theorem blockSelectionStates_last_lt_succ
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (n : ℕ) :
    (blockSelectionStates u hu M block n).last <
      (blockSelectionStates u hu M block (n + 1)).last := by
  rw [blockSelectionStates]
  exact nextBlockIndex_spec u hu M block n (blockSelectionStates u hu M block n) |>.1

theorem blockSubsequenceIndex_strictMono
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) :
    StrictMono (blockSubsequenceIndex u hu M block) := by
  apply strictMono_nat_of_lt_succ
  intro n
  exact blockSelectionStates_last_lt_succ u hu M block (n + 1)

private theorem blockSelectionStates_boundedIndependent
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G]
    (u : ℕ → G) (hu : Function.Injective u) (M block : ℕ → ℕ)
    (n l : ℕ) :
    BoundedIndependent (M l) ((blockSelectionStates u hu M block n).values l) := by
  classical
  induction n with
  | zero =>
      intro c hc hsum x hx
      simp [blockSelectionStates, initialBlockSelectionState] at hx
  | succ n ih =>
      rw [blockSelectionStates]
      by_cases hl : l = block n
      · subst l
        simp only [blockSelectionStep]
        simp only [Function.update_self]
        exact boundedIndependent_insert_of_not_forbidden ih
          (nextBlockIndex_not_mem_values u hu M block n
            (blockSelectionStates u hu M block n))
          (nextBlockIndex_not_forbidden u hu M block n
            (blockSelectionStates u hu M block n))
      · simp only [blockSelectionStep, ne_eq, hl, not_false_eq_true, Function.update_of_ne]
        exact ih

private theorem blockSelectionStates_values_mono_succ
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (n l : ℕ) :
    (blockSelectionStates u hu M block n).values l ⊆
      (blockSelectionStates u hu M block (n + 1)).values l := by
  classical
  rw [blockSelectionStates]
  by_cases hl : l = block n
  · subst l
    simp [blockSelectionStep]
  · simp [blockSelectionStep, hl]

private theorem blockSelectionStates_values_monotone
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (l : ℕ) :
    Monotone fun n => (blockSelectionStates u hu M block n).values l :=
  monotone_nat_of_le_succ fun n =>
    blockSelectionStates_values_mono_succ u hu M block n l

private theorem selected_value_mem_state
    {G : Type*} [AddCommGroup G] (u : ℕ → G) (hu : Function.Injective u)
    (M block : ℕ → ℕ) (n : ℕ) :
    u (blockSubsequenceIndex u hu M block n) ∈
      (blockSelectionStates u hu M block (n + 1)).values (block n) := by
  classical
  simp [blockSubsequenceIndex, blockSelectionStates, blockSelectionStep]

/-- A cutoff beyond every position in a finite set. -/
def finsetCutoff (B : Finset ℕ) : ℕ :=
  B.sup fun n => n + 1

theorem add_one_le_finsetCutoff {B : Finset ℕ} {n : ℕ} (hn : n ∈ B) :
    n + 1 ≤ finsetCutoff B := by
  exact Finset.le_sup (s := B) (f := fun k => k + 1) hn

/-- Generic block preprocessing.  `block n` specifies which finite block contains output
position `n`.  Each block may have any prescribed positive finite size; only finiteness is
needed by the selection argument. -/
theorem exists_blockwise_boundedIndependent_subsequence
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (u : ℕ → G) (hu : Function.Injective u)
    (block M : ℕ → ℕ)
    (hfinite : ∀ l, {n | block n = l}.Finite) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ l, BoundedIndependent (M l)
        ((hfinite l).toFinset.image fun n => u (φ n)) := by
  classical
  let φ := blockSubsequenceIndex u hu M block
  refine ⟨φ, blockSubsequenceIndex_strictMono u hu M block, ?_⟩
  intro l
  let B : Finset ℕ := (hfinite l).toFinset
  let K : ℕ := finsetCutoff B
  apply boundedIndependent_mono
    (blockSelectionStates_boundedIndependent u hu M block K l)
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨n, hnB, rfl⟩
  have hnblock : block n = l := by
    exact (Set.Finite.mem_toFinset (hfinite l)).mp hnB
  have hmem := selected_value_mem_state u hu M block n
  rw [hnblock] at hmem
  exact blockSelectionStates_values_monotone u hu M block l
    (add_one_le_finsetCutoff hnB) hmem

/-! ## The consecutive block partition used in the paper -/

/-- The first position of block `l`, namely `∑ j < l, N j`.  This is the paper's `S_l`. -/
def blockStart (N : ℕ → ℕ) (l : ℕ) : ℕ :=
  ∑ j ∈ Finset.range l, N j

@[simp]
theorem blockStart_zero (N : ℕ → ℕ) : blockStart N 0 = 0 := by
  simp [blockStart]

theorem blockStart_succ (N : ℕ → ℕ) (l : ℕ) :
    blockStart N (l + 1) = blockStart N l + N l := by
  simp [blockStart, Finset.sum_range_succ]

theorem blockStart_strictMono (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) :
    StrictMono (blockStart N) := by
  apply strictMono_nat_of_lt_succ
  intro l
  rw [blockStart_succ]
  exact Nat.lt_add_of_pos_right (hN l)

theorem index_le_blockStart (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) :
    ∀ l, l ≤ blockStart N l := by
  intro l
  induction l with
  | zero => simp
  | succ l ih =>
      rw [blockStart_succ]
      have hpos := hN l
      omega

private theorem exists_lt_next_blockStart
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (n : ℕ) :
    ∃ l, n < blockStart N (l + 1) := by
  refine ⟨n, ?_⟩
  have h := index_le_blockStart N hN (n + 1)
  omega

/-- The unique block label whose consecutive half-open interval contains `n`. -/
def blockOf (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (n : ℕ) : ℕ :=
  Nat.find (exists_lt_next_blockStart N hN n)

theorem blockOf_spec (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (n : ℕ) :
    blockStart N (blockOf N hN n) ≤ n ∧
      n < blockStart N (blockOf N hN n + 1) := by
  let hex := exists_lt_next_blockStart N hN n
  have hupper : n < blockStart N (blockOf N hN n + 1) := by
    exact Nat.find_spec hex
  refine ⟨?_, hupper⟩
  cases hb : blockOf N hN n with
  | zero => simp
  | succ l =>
      have hminimal : ¬ n < blockStart N (l + 1) := by
        have hfind : Nat.find hex = l + 1 := by
          simpa only [blockOf] using hb
        have hlt : l < Nat.find hex := by
          rw [hfind]
          exact Nat.lt_succ_self l
        exact Nat.find_min hex hlt
      simpa only [hb] using Nat.le_of_not_gt hminimal

/-- The finite interval `I_l = [S_l, S_l + N_l)` used in the paper. -/
def blockPositions (N : ℕ → ℕ) (_hN : ∀ l, 0 < N l) (l : ℕ) : Finset ℕ :=
  Finset.Ico (blockStart N l) (blockStart N (l + 1))

theorem mem_blockPositions_iff
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) {l n : ℕ} :
    n ∈ blockPositions N hN l ↔ blockOf N hN n = l := by
  constructor
  · intro hn
    have hnIco : blockStart N l ≤ n ∧ n < blockStart N (l + 1) := by
      simpa only [blockPositions, Finset.mem_Ico] using hn
    obtain ⟨hblo, hbhi⟩ := blockOf_spec N hN n
    by_contra hne
    rcases lt_or_gt_of_ne hne with hbl | hlb
    · have hstarts : blockStart N (blockOf N hN n + 1) ≤ blockStart N l :=
        (blockStart_strictMono N hN).monotone (Nat.add_one_le_iff.mpr hbl)
      omega
    · have hstarts : blockStart N (l + 1) ≤ blockStart N (blockOf N hN n) :=
        (blockStart_strictMono N hN).monotone (Nat.add_one_le_iff.mpr hlb)
      omega
  · rintro rfl
    simpa only [blockPositions, Finset.mem_Ico] using blockOf_spec N hN n

theorem blockPositions_card
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (l : ℕ) :
    (blockPositions N hN l).card = N l := by
  simp [blockPositions, blockStart_succ]

theorem blockFiber_finite
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (l : ℕ) :
    {n | blockOf N hN n = l}.Finite := by
  have heq : {n | blockOf N hN n = l} = (blockPositions N hN l : Set ℕ) := by
    ext n
    exact (mem_blockPositions_iff N hN).symm
  rw [heq]
  exact (blockPositions N hN l).finite_toSet

/-- Block preprocessing for any prescribed sequence of positive finite sizes. -/
theorem exists_boundedIndependent_subsequence_for_sizes
    {G : Type*} [AddCommGroup G] [IsAddTorsionFree G] [DecidableEq G]
    (u : ℕ → G) (hu : Function.Injective u)
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∀ l, (blockPositions N hN l).card = N l ∧
        BoundedIndependent (M l)
          ((blockPositions N hN l).image fun n => u (φ n)) := by
  classical
  let hfinite : ∀ l, {n | blockOf N hN n = l}.Finite :=
    blockFiber_finite N hN
  obtain ⟨φ, hφ, hind⟩ :=
    exists_blockwise_boundedIndependent_subsequence u hu (blockOf N hN) M hfinite
  refine ⟨φ, hφ, fun l => ⟨blockPositions_card N hN l, ?_⟩⟩
  have hfinset : (hfinite l).toFinset = blockPositions N hN l := by
    ext n
    simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, mem_blockPositions_iff]
  simpa only [hfinset] using hind l

/-! ## The paper's shifted coded sequences -/

/-- The basis vector attached to a code's fresh index. -/
def codeBasisVector (a : ContinuumIndex) : ContinuumFreeGroup :=
  Finsupp.single (codeIndex a) 1

/-- The sequence to which finite bounded-independence extraction is applied. -/
def codedDifference (a : ContinuumIndex) (n : ℕ) : ContinuumFreeGroup :=
  codedSequence a n - codeBasisVector a

theorem codedDifference_injective (a : ContinuumIndex) :
    Function.Injective (codedDifference a) := by
  intro m n hmn
  apply codedSequence_injective a
  have h := congrArg (fun z => z + codeBasisVector a) hmn
  simpa [codedDifference] using h

/-- **Full block preprocessing.**  For every triangular code and every prescribed positive block
size sequence `N` and coefficient-bound sequence `M`, a genuine subsequence is chosen so that
the shifted values in each block have exactly size `N l` and are `M l`-independent.  The original
strict support bound is preserved by passage to the subsequence. -/
theorem triangular_block_preprocess
    (a : ContinuumIndex)
    (N : ℕ → ℕ) (hN : ∀ l, 0 < N l) (M : ℕ → ℕ) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      (∀ l, (blockPositions N hN l).card = N l ∧
        BoundedIndependent (M l)
          ((blockPositions N hN l).image fun n =>
            codedSequence a (φ n) - codeBasisVector a)) ∧
      FiniteCombinatorics.SupportedBelow (codedSequence a ∘ φ) (codeIndex a) := by
  obtain ⟨φ, hφ, hblocks⟩ :=
    exists_boundedIndependent_subsequence_for_sizes
      (codedDifference a) (codedDifference_injective a) N hN M
  refine ⟨φ, hφ, ?_, ?_⟩
  · simpa only [codedDifference] using hblocks
  · intro n i hi
    exact codedSequence_supportedBelow a (φ n) i hi

end
end TriangularPreprocess
end Wallace
