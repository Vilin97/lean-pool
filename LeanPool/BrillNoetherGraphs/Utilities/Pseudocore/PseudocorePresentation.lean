/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionIso
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.UnitSubdivisionPresentation
public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocoreCompatible
public import LeanPool.BrillNoetherGraphs.Utilities.Pseudocore.PseudocoreRelabeling
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.LeafReduction
public import LeanPool.BrillNoetherGraphs.Utilities.Gluing.CycleRigidity

/-!
# WP-A: the pseudocore presentation theorem

This module builds, for an arbitrary connected leafless graph, a subdivision
presentation over a *small* core: one in which every core vertex either has
core valence at least three, or is a bivalent marker whose two slots run to a
common neighbour.  That shape is exactly the loopless split of a loop-aware
pseudocore, which is what `Certificate/PseudocoreSplitGlue.lean` consumes.

The construction is genus-generic.  Its engine is a single *merge* step at the
level of subdivision specifications:

* `mergeSpec` — given a specification with a core vertex carrying exactly two
  slot ends whose far endpoints are distinct, produce a specification with one
  fewer core vertex and one fewer slot, presenting the *same* graph;
* `exists_reduced` — iterate the merge step until no core vertex is
  mergeable.

Both are proved by exhibiting the larger specification as a
`SubdivisionGraph.Spec.Relabeling` of the canonical one-slot split
(`OneEdgeSplitRefinement.splitSpec`) of the smaller one, so no new
vertex/unit-step bijection has to be built by hand: the split's own
`canonicalSplitLaplacianEquiv` supplies it.
-/

@[expose] public section
namespace Utilities.Certificate.PseudocorePresentation

open Finset
open ExplicitPotential
open SubdivisionGraph
open Utilities.Certificate.GenusFourPseudocore
open Utilities.Certificate.GenusFourPseudocore.Pseudocore

universe u

/-! ## Shrinking `Fin (m + 1)` away from its last element -/

/-- A total left inverse of `Fin.castSucc`, defaulting to `0`. -/
def shrink {m : ℕ} (hm : 0 < m) (x : Fin (m + 1)) : Fin m :=
  if h : x.val < m then ⟨x.val, h⟩ else ⟨0, hm⟩

@[simp] theorem shrink_castSucc {m : ℕ} (hm : 0 < m) (y : Fin m) :
    shrink hm (Fin.castSucc y) = y := by
  have hy : (Fin.castSucc y).val < m := y.isLt
  simp only [shrink, dif_pos hy]
  exact Fin.ext rfl

theorem castSucc_shrink {m : ℕ} (hm : 0 < m) {x : Fin (m + 1)}
    (hx : x ≠ Fin.last m) : Fin.castSucc (shrink hm x) = x := by
  have hlt : x.val < m := by
    have := x.isLt
    rcases Nat.lt_or_ge x.val m with h | h
    · exact h
    · exact absurd (Fin.ext (by omega : x.val = m)) hx
  simp only [shrink, dif_pos hlt]
  exact Fin.ext rfl

theorem shrink_injective_of_ne_last {m : ℕ} (hm : 0 < m) {x y : Fin (m + 1)}
    (hx : x ≠ Fin.last m) (hy : y ≠ Fin.last m)
    (h : shrink hm x = shrink hm y) : x = y := by
  rw [← castSucc_shrink hm hx, ← castSucc_shrink hm hy, h]

/-! ## Slot ends at a core vertex -/

/-- The set of slot *ends* at a core vertex.  `(edge, true)` is the head end of
`edge` and `(edge, false)` its tail end. -/
def slotEnds {n p : ℕ} (core : Core n p) (vertex : Fin n) :
    Finset (Fin p × Bool) :=
  Finset.univ.filter fun x =>
    if x.2 then core.head x.1 = vertex else core.tail x.1 = vertex

/-- Core valence: the number of slot ends at a core vertex. -/
def slotValence {n p : ℕ} (core : Core n p) (vertex : Fin n) : ℕ :=
  (slotEnds core vertex).card

theorem mem_slotEnds {n p : ℕ} (core : Core n p) (vertex : Fin n)
    (x : Fin p × Bool) :
    x ∈ slotEnds core vertex ↔
      (if x.2 then core.head x.1 = vertex else core.tail x.1 = vertex) := by
  simp [slotEnds]

/-- The far endpoint of a slot end. -/
def farEnd {n p : ℕ} (core : Core n p) (x : Fin p × Bool) : Fin n :=
  if x.2 then core.tail x.1 else core.head x.1

/-! ## The merge step -/

/-- Swapping a vertex with the last index moves nothing else onto the last
index. -/
theorem swap_ne_last {m : ℕ} (v : Fin (m + 1)) {x : Fin (m + 1)} (hx : x ≠ v) :
    Equiv.swap v (Fin.last m) x ≠ Fin.last m := by
  intro hEq
  apply hx
  have hApply := congrArg (Equiv.swap v (Fin.last m)) hEq
  rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at hApply

section Merge

variable {n p : ℕ}

/-- Witness that a core vertex carries exactly two slot ends, lying on two
distinct slots whose far endpoints differ.  Such a vertex is a genuine
subdivision point and can be suppressed. -/
structure MergeData (core : Core n p) where
  /-- The degree-two core vertex to suppress by merging its two incident slots. -/
  vertex : Fin n
  /-- The first incident slot end at the suppressed vertex, including its orientation flag. -/
  first : Fin p × Bool
  /-- The second incident slot end; its slot differs from the first and together they exhaust
  the incident ends. -/
  second : Fin p × Bool
  first_mem : first ∈ slotEnds core vertex
  second_mem : second ∈ slotEnds core vertex
  slots_ne : first.1 ≠ second.1
  exhaustive : ∀ x ∈ slotEnds core vertex, x = first ∨ x = second
  far_ne : farEnd core first ≠ farEnd core second

namespace MergeData

variable {core : Core n p} (data : MergeData core)

theorem slot_eq_of_tail (_hLoopless : ∀ edge, core.tail edge ≠ core.head edge)
    {edge : Fin p} (hEdge : core.tail edge = data.vertex) :
    edge = data.first.1 ∨ edge = data.second.1 := by
  rcases data.exhaustive (edge, false) (by simp [mem_slotEnds, hEdge]) with h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)

theorem slot_eq_of_head (_hLoopless : ∀ edge, core.tail edge ≠ core.head edge)
    {edge : Fin p} (hEdge : core.head edge = data.vertex) :
    edge = data.first.1 ∨ edge = data.second.1 := by
  rcases data.exhaustive (edge, true) (by simp [mem_slotEnds, hEdge]) with h | h
  · exact Or.inl (congrArg Prod.fst h)
  · exact Or.inr (congrArg Prod.fst h)

end MergeData

variable (spec : Spec (n + 1) (p + 1))

private theorem exists_mergeGeometry (spec : Spec (n + 1) (p + 1))
    (data : MergeData spec.core) :
    ∃ (v a b : Fin (n + 1)) (e₁ e₂ : Fin (p + 1)), e₁ ≠ e₂ ∧
      ((spec.core.tail e₁ = v ∧ a = spec.core.head e₁) ∨
        (spec.core.head e₁ = v ∧ a = spec.core.tail e₁)) ∧
      ((spec.core.tail e₂ = v ∧ b = spec.core.head e₂) ∨
        (spec.core.head e₂ = v ∧ b = spec.core.tail e₂)) ∧
      a ≠ v ∧ b ≠ v ∧ a ≠ b ∧
      (∀ E : Fin (p + 1), E ≠ e₁ → E ≠ e₂ →
        spec.core.tail E ≠ v ∧ spec.core.head E ≠ v) := by
  classical
  set v : Fin (n + 1) := data.vertex with hv
  set e₁ : Fin (p + 1) := data.first.1 with he₁
  set e₂ : Fin (p + 1) := data.second.1 with he₂
  have hSlots : e₁ ≠ e₂ := data.slots_ne
  have hLoopless := spec.core_loopless
  -- membership facts for the two ends
  have hFirst : if data.first.2 then spec.core.head e₁ = v
      else spec.core.tail e₁ = v := by
    have := (mem_slotEnds spec.core v data.first).mp data.first_mem
    simpa [he₁] using this
  have hSecond : if data.second.2 then spec.core.head e₂ = v
      else spec.core.tail e₂ = v := by
    have := (mem_slotEnds spec.core v data.second).mp data.second_mem
    simpa [he₂] using this
  set a : Fin (n + 1) := farEnd spec.core data.first with ha
  set b : Fin (n + 1) := farEnd spec.core data.second with hb
  have hFirstCase : (spec.core.tail e₁ = v ∧ a = spec.core.head e₁) ∨
      (spec.core.head e₁ = v ∧ a = spec.core.tail e₁) := by
    rcases hSide : data.first.2 with _ | _
    · exact Or.inl ⟨by simpa [hSide] using hFirst, by simp [ha, farEnd, ← he₁, hSide]⟩
    · exact Or.inr ⟨by simpa [hSide] using hFirst, by simp [ha, farEnd, ← he₁, hSide]⟩
  have hSecondCase : (spec.core.tail e₂ = v ∧ b = spec.core.head e₂) ∨
      (spec.core.head e₂ = v ∧ b = spec.core.tail e₂) := by
    rcases hSide : data.second.2 with _ | _
    · exact Or.inl ⟨by simpa [hSide] using hSecond, by simp [hb, farEnd, ← he₂, hSide]⟩
    · exact Or.inr ⟨by simpa [hSide] using hSecond, by simp [hb, farEnd, ← he₂, hSide]⟩
  have haNe : a ≠ v := by
    rcases hFirstCase with ⟨hT, hA⟩ | ⟨hH, hA⟩
    · rw [hA, ← hT]; exact fun hEq => hLoopless e₁ hEq.symm
    · rw [hA, ← hH]; exact hLoopless e₁
  have hbNe : b ≠ v := by
    rcases hSecondCase with ⟨hT, hB⟩ | ⟨hH, hB⟩
    · rw [hB, ← hT]; exact fun hEq => hLoopless e₂ hEq.symm
    · rw [hB, ← hH]; exact hLoopless e₂
  have habNe : a ≠ b := data.far_ne
  -- other slots avoid the merged vertex
  have hAvoid : ∀ E : Fin (p + 1), E ≠ e₁ → E ≠ e₂ →
      spec.core.tail E ≠ v ∧ spec.core.head E ≠ v := by
    intro E hE₁ hE₂
    constructor
    · intro hEq
      rcases data.slot_eq_of_tail hLoopless hEq with h | h
      · exact hE₁ h
      · exact hE₂ h
    · intro hEq
      rcases data.slot_eq_of_head hLoopless hEq with h | h
      · exact hE₁ h
      · exact hE₂ h
  exact ⟨v, a, b, e₁, e₂, hSlots, hFirstCase, hSecondCase,
    haNe, hbNe, habNe, hAvoid⟩

private theorem exists_mergeIndices (hp : 0 < p) (v : Fin (n + 1))
    (e₁ e₂ : Fin (p + 1)) (hSlots : e₁ ≠ e₂) :
    ∃ (σ : Equiv.Perm (Fin (n + 1))) (τ : Equiv.Perm (Fin (p + 1)))
      (split : Fin p) (pre : Fin p → Fin (p + 1)),
      σ v = Fin.last n ∧
      (∀ x : Fin (n + 1), x ≠ v → σ x ≠ Fin.last n) ∧
      τ e₂ = Fin.last p ∧
      (∀ E : Fin (p + 1), E ≠ e₂ → τ E ≠ Fin.last p) ∧
      τ e₁ = Fin.castSucc split ∧
      (∀ edge : Fin p, τ (pre edge) = Fin.castSucc edge) ∧
      pre split = e₁ ∧
      (∀ edge : Fin p, pre edge ≠ e₂) ∧
      (∀ edge : Fin p, edge ≠ split → pre edge ≠ e₁) ∧
      (∀ E : Fin (p + 1), E = e₂ ∨ E = e₁ ∨
        ∃ edge : Fin p, edge ≠ split ∧ τ E = Fin.castSucc edge ∧ pre edge = E) := by
  classical
  -- index normalizations
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap v (Fin.last n) with hσ
  set τ : Equiv.Perm (Fin (p + 1)) := Equiv.swap e₂ (Fin.last p) with hτ
  have hσv : σ v = Fin.last n := by simp [hσ]
  have hσNe : ∀ x : Fin (n + 1), x ≠ v → σ x ≠ Fin.last n := by
    intro x hx; exact swap_ne_last v hx
  have hτe₂ : τ e₂ = Fin.last p := by simp [hτ]
  have hτNe : ∀ E : Fin (p + 1), E ≠ e₂ → τ E ≠ Fin.last p := by
    intro E hE; exact swap_ne_last e₂ hE
  set split : Fin p := shrink hp (τ e₁) with hsplit
  have hτe₁ : τ e₁ = Fin.castSucc split := (castSucc_shrink hp (hτNe e₁ hSlots)).symm
  set pre : Fin p → Fin (p + 1) := fun edge => τ.symm (Fin.castSucc edge) with hpre
  have hτpre : ∀ edge : Fin p, τ (pre edge) = Fin.castSucc edge := by
    intro edge; simp [hpre]
  have hpreSplit : pre split = e₁ := by
    have : τ (pre split) = τ e₁ := by rw [hτpre, hτe₁]
    exact τ.injective this
  have hpreNe₂ : ∀ edge : Fin p, pre edge ≠ e₂ := by
    intro edge hEq
    have : Fin.castSucc edge = Fin.last p := by rw [← hτpre edge, hEq, hτe₂]
    exact absurd this (Fin.castSucc_ne_last edge)
  have hpreNe₁ : ∀ edge : Fin p, edge ≠ split → pre edge ≠ e₁ := by
    intro edge hEdge hEq
    apply hEdge
    have : τ (pre edge) = τ (pre split) := by rw [hEq, hpreSplit]
    rw [hτpre, hτpre] at this
    exact Fin.castSucc_injective p this
  -- assemble the relabeling
  have hCase : ∀ E : Fin (p + 1), E = e₂ ∨ E = e₁ ∨
      (∃ edge : Fin p, edge ≠ split ∧ τ E = Fin.castSucc edge ∧ pre edge = E) := by
    intro E
    by_cases hE₂ : E = e₂
    · exact Or.inl hE₂
    by_cases hE₁ : E = e₁
    · exact Or.inr (Or.inl hE₁)
    refine Or.inr (Or.inr ⟨shrink hp (τ E), ?_, ?_, ?_⟩)
    · intro hEq
      apply hE₁
      have hcast : τ E = Fin.castSucc (shrink hp (τ E)) :=
        (castSucc_shrink hp (hτNe E hE₂)).symm
      have : τ E = τ e₁ := by rw [hcast, hEq, hτe₁]
      exact τ.injective this
    · exact (castSucc_shrink hp (hτNe E hE₂)).symm
    · have hcast : τ E = Fin.castSucc (shrink hp (τ E)) :=
        (castSucc_shrink hp (hτNe E hE₂)).symm
      have : τ (pre (shrink hp (τ E))) = τ E := by rw [hτpre, ← hcast]
      exact τ.injective this
  exact ⟨σ, τ, split, pre, hσv, hσNe, hτe₂, hτNe, hτe₁, hτpre,
    hpreSplit, hpreNe₂, hpreNe₁, hCase⟩

/-- Suppressing a bivalent core vertex preserves the subdivided graph.  The
smaller specification is obtained by concatenating the two slots at the
vertex; the equality of graphs is read off from the canonical one-slot split
of the smaller specification. -/
theorem exists_merge (hn : 0 < n) (hp : 0 < p)
    (data : MergeData spec.core) :
    ∃ spec' : Spec n p, Nonempty (LaplacianEquiv spec.graph spec'.graph) := by
  classical
  obtain ⟨v, a, b, e₁, e₂, hSlots, hFirstCase, hSecondCase,
    haNe, hbNe, habNe, hAvoid⟩ := exists_mergeGeometry spec data
  have hLoopless := spec.core_loopless
  obtain ⟨σ, τ, split, pre, hσv, hσNe, hτe₂, hτNe, hτe₁, hτpre,
    hpreSplit, hpreNe₂, hpreNe₁, hCase⟩ := exists_mergeIndices hp v e₁ e₂ hSlots
  -- the merged specification
  set L₁ : ℕ := spec.length e₁ with hL₁
  set L₂ : ℕ := spec.length e₂ with hL₂
  set sourceCore : Core n p :=
    { tail := fun edge => if edge = split then shrink hn (σ a)
        else shrink hn (σ (spec.core.tail (pre edge)))
      head := fun edge => if edge = split then shrink hn (σ b)
        else shrink hn (σ (spec.core.head (pre edge))) } with hsourceCore
  have hsourceLoopless : ∀ edge : Fin p, sourceCore.tail edge ≠ sourceCore.head edge := by
    intro edge
    by_cases hEdge : edge = split
    · simp only [hsourceCore, hEdge]
      intro hEq
      exact habNe (σ.injective (shrink_injective_of_ne_last hn
        (hσNe a haNe) (hσNe b hbNe) hEq))
    · simp only [hsourceCore, if_neg hEdge]
      obtain ⟨hTail, hHead⟩ := hAvoid (pre edge) (hpreNe₁ edge hEdge) (hpreNe₂ edge)
      intro hEq
      exact hLoopless (pre edge) (σ.injective (shrink_injective_of_ne_last hn
        (hσNe _ hTail) (hσNe _ hHead) hEq))
  set source : Spec n p :=
    { core := sourceCore
      length := fun edge => if edge = split then L₁ + L₂ else spec.length (pre edge)
      core_nonempty := hn
      core_loopless := hsourceLoopless
      length_pos := by
        intro edge
        by_cases hEdge : edge = split
        · rw [if_pos hEdge]
          exact Nat.add_pos_left (spec.length_pos e₁) L₂
        · rw [if_neg hEdge]
          exact spec.length_pos (pre edge) } with hsource
  have hL₁pos : 0 < L₁ := spec.length_pos e₁
  have hL₂pos : 0 < L₂ := spec.length_pos e₂
  have hLengthSplit : source.length split = L₁ + L₂ := by simp [hsource]
  set target : Spec (n + 1) (p + 1) :=
    OneEdgeSplitRefinement.splitSpec source split L₁ L₂ hL₁pos hL₂pos with htarget
  -- the relabeling from `spec` onto the split of the merged specification
  have hTargetLength : ∀ E : Fin (p + 1), spec.length E = target.length (τ E) := by
    intro E
    by_cases hE₂ : E = e₂
    · subst hE₂
      rw [hτe₂]
      simp [htarget, OneEdgeSplitRefinement.splitSpec,
        OneEdgeSplitRefinement.splitLength, hL₂]
    · have hNotLast := hτNe E hE₂
      set edge : Fin p := shrink hp (τ E) with hedge
      have hcast : τ E = Fin.castSucc edge := (castSucc_shrink hp hNotLast).symm
      have hpreE : pre edge = E := by
        have : τ (pre edge) = τ E := by rw [hτpre, hcast]
        exact τ.injective this
      rw [hcast]
      by_cases hE₁ : E = e₁
      · have hEdgeSplit : edge = split := by
          apply Fin.castSucc_injective p
          rw [← hcast, hE₁, hτe₁]
        simp [htarget, OneEdgeSplitRefinement.splitSpec,
          OneEdgeSplitRefinement.splitLength, hEdgeSplit, hE₁, hL₁]
      · have hEdgeSplit : edge ≠ split := by
          intro hEq
          exact hE₁ (by rw [← hpreE, hEq, hpreSplit])
        simp [htarget, OneEdgeSplitRefinement.splitSpec,
          OneEdgeSplitRefinement.splitLength, hEdgeSplit, hsource, hpreE]
  -- the reversal flags
  set rev : Fin (p + 1) → Bool := fun E =>
    if E = e₂ then decide (spec.core.head E = v)
    else decide (spec.core.tail E = v) with hrev
  have hRevOther : ∀ E : Fin (p + 1), E ≠ e₁ → E ≠ e₂ → rev E = false := by
    intro E hE₁ hE₂
    simp only [hrev, if_neg hE₂, decide_eq_false_iff_not]
    exact (hAvoid E hE₁ hE₂).1
  have hσa : Fin.castSucc (shrink hn (σ a)) = σ a := castSucc_shrink hn (hσNe a haNe)
  have hσb : Fin.castSucc (shrink hn (σ b)) = σ b := castSucc_shrink hn (hσNe b hbNe)
  -- endpoint bookkeeping at the second merged slot
  have hSecondPair :
      (if rev e₂ = true then σ (spec.core.head e₂) else σ (spec.core.tail e₂))
          = Fin.last n ∧
        (if rev e₂ = true then σ (spec.core.tail e₂) else σ (spec.core.head e₂))
          = σ b := by
    have hrev₂ : rev e₂ = decide (spec.core.head e₂ = v) := by
      simp only [hrev, if_pos rfl]
    rcases hSecondCase with ⟨hT, hB⟩ | ⟨hH, hB⟩
    · have hHeadNe : spec.core.head e₂ ≠ v := by
        rw [← hT]; exact fun hEq => hLoopless e₂ hEq.symm
      have hFlag : rev e₂ = false := by rw [hrev₂]; simp [hHeadNe]
      rw [hFlag]
      exact ⟨by simp [hT, hσv], by simp [hB]⟩
    · have hFlag : rev e₂ = true := by rw [hrev₂, hH]; simp
      rw [hFlag]
      exact ⟨by simp [hH, hσv], by simp [hB]⟩
  have hFirstPair :
      (if rev e₁ = true then σ (spec.core.head e₁) else σ (spec.core.tail e₁))
          = σ a ∧
        (if rev e₁ = true then σ (spec.core.tail e₁) else σ (spec.core.head e₁))
          = Fin.last n := by
    have hrev₁ : rev e₁ = decide (spec.core.tail e₁ = v) := by
      simp only [hrev, if_neg hSlots]
    rcases hFirstCase with ⟨hT, hA⟩ | ⟨hH, hA⟩
    · have hFlag : rev e₁ = true := by rw [hrev₁, hT]; simp
      rw [hFlag]
      exact ⟨by simp [hA], by simp [hT, hσv]⟩
    · have hTailNe : spec.core.tail e₁ ≠ v := by rw [← hH]; exact hLoopless e₁
      have hFlag : rev e₁ = false := by rw [hrev₁]; simp [hTailNe]
      rw [hFlag]
      exact ⟨by simp [hA], by simp [hH, hσv]⟩
  -- the split core, evaluated slot by slot
  have hTgtTailSecond : target.core.tail (Fin.last p) = Fin.last n := by
    simp [htarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
      OneEdgeSplitRefinement.splitVertex]
  have hTgtHeadSecond : target.core.head (Fin.last p) = σ b := by
    have : target.core.head (Fin.last p) = Fin.castSucc (source.core.head split) := by
      simp [htarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
        OneEdgeSplitRefinement.oldVertex]
    rw [this]
    have hHead : source.core.head split = shrink hn (σ b) := by
      simp [hsource, hsourceCore]
    rw [hHead, hσb]
  have hTgtTailFirst : target.core.tail (Fin.castSucc split) = σ a := by
    have : target.core.tail (Fin.castSucc split) = Fin.castSucc (source.core.tail split) := by
      simp [htarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
        OneEdgeSplitRefinement.oldVertex]
    rw [this]
    have hTail : source.core.tail split = shrink hn (σ a) := by
      simp [hsource, hsourceCore]
    rw [hTail, hσa]
  have hTgtHeadFirst : target.core.head (Fin.castSucc split) = Fin.last n := by
    simp [htarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
      OneEdgeSplitRefinement.splitVertex]
  have hTgtTailOther : ∀ edge : Fin p, edge ≠ split →
      target.core.tail (Fin.castSucc edge) = σ (spec.core.tail (pre edge)) := by
    intro edge hEdge
    have hStep : target.core.tail (Fin.castSucc edge)
        = Fin.castSucc (source.core.tail edge) := by
      simp [htarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
        OneEdgeSplitRefinement.oldVertex]
    rw [hStep]
    have hTail : source.core.tail edge = shrink hn (σ (spec.core.tail (pre edge))) := by
      simp [hsource, hsourceCore, hEdge]
    rw [hTail]
    exact castSucc_shrink hn
      (hσNe _ (hAvoid (pre edge) (hpreNe₁ edge hEdge) (hpreNe₂ edge)).1)
  have hTgtHeadOther : ∀ edge : Fin p, edge ≠ split →
      target.core.head (Fin.castSucc edge) = σ (spec.core.head (pre edge)) := by
    intro edge hEdge
    have hStep : target.core.head (Fin.castSucc edge)
        = Fin.castSucc (source.core.head edge) := by
      simp [htarget, OneEdgeSplitRefinement.splitSpec, OneEdgeSplitRefinement.splitCore,
        OneEdgeSplitRefinement.oldVertex, hEdge]
    rw [hStep]
    have hHead : source.core.head edge = shrink hn (σ (spec.core.head (pre edge))) := by
      simp [hsource, hsourceCore, hEdge]
    rw [hHead]
    exact castSucc_shrink hn
      (hσNe _ (hAvoid (pre edge) (hpreNe₁ edge hEdge) (hpreNe₂ edge)).2)
  refine ⟨source, ⟨(Spec.laplacianEquiv spec target
    { coreEquiv := σ
      slotEquiv := τ
      reversed := rev
      length_eq := hTargetLength
      tail_eq := by
        intro E
        rcases hCase E with hE | hE | ⟨edge, hEdge, hCast, hPre⟩
        · subst hE
          rw [hτe₂, hTgtTailSecond]
          exact hSecondPair.1.symm
        · subst hE
          rw [hτe₁, hTgtTailFirst]
          exact hFirstPair.1.symm
        · rw [hCast, hTgtTailOther edge hEdge, hPre]
          have hE₁ : E ≠ e₁ := by rw [← hPre]; exact hpreNe₁ edge hEdge
          have hE₂ : E ≠ e₂ := by rw [← hPre]; exact hpreNe₂ edge
          rw [hRevOther E hE₁ hE₂]
          simp
      head_eq := by
        intro E
        rcases hCase E with hE | hE | ⟨edge, hEdge, hCast, hPre⟩
        · subst hE
          rw [hτe₂, hTgtHeadSecond]
          exact hSecondPair.2.symm
        · subst hE
          rw [hτe₁, hTgtHeadFirst]
          exact hFirstPair.2.symm
        · rw [hCast, hTgtHeadOther edge hEdge, hPre]
          have hE₁ : E ≠ e₁ := by rw [← hPre]; exact hpreNe₁ edge hEdge
          have hE₂ : E ≠ e₂ := by rw [← hPre]; exact hpreNe₂ edge
          rw [hRevOther E hE₁ hE₂]
          simp }).trans
    (OneEdgeSplitRefinement.canonicalSplitLaplacianEquiv source split L₁ L₂
      hL₁pos hL₂pos hLengthSplit).symm⟩⟩

/-! ## Iterating the merge step -/

/-- A core is *reduced* when no vertex of it can be suppressed. -/
def Reduced {n p : ℕ} (core : Core n p) : Prop := IsEmpty (MergeData core)

/-- Every subdivision specification presents its graph over a reduced core. -/
theorem exists_reduced : ∀ n : ℕ, ∀ (p : ℕ) (spec : Spec n p),
    ∃ (n' p' : ℕ) (spec' : Spec n' p'),
      Nonempty (LaplacianEquiv spec.graph spec'.graph) ∧ Reduced spec'.core := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro p spec
    by_cases hEmpty : Reduced spec.core
    · exact ⟨n, p, spec, ⟨⟨Equiv.refl _, fun _ _ => rfl⟩⟩, hEmpty⟩
    · rw [Reduced, not_isEmpty_iff] at hEmpty
      obtain ⟨data⟩ := hEmpty
      have hVertexBound : 2 ≤ n := by
        have hNe : (farEnd spec.core data.first).val
            ≠ (farEnd spec.core data.second).val := fun h => data.far_ne (Fin.ext h)
        have h1 := (farEnd spec.core data.first).isLt
        have h2 := (farEnd spec.core data.second).isLt
        omega
      have hSlotBound : 2 ≤ p := by
        have hNe : (data.first.1).val ≠ (data.second.1).val :=
          fun h => data.slots_ne (Fin.ext h)
        have h1 := (data.first.1).isLt
        have h2 := (data.second.1).isLt
        omega
      obtain ⟨n₀, rfl⟩ : ∃ n₀, n = n₀ + 1 := ⟨n - 1, by omega⟩
      obtain ⟨p₀, rfl⟩ : ∃ p₀, p = p₀ + 1 := ⟨p - 1, by omega⟩
      obtain ⟨middle, hMiddle⟩ :=
        exists_merge spec (by omega) (by omega) data
      obtain ⟨n', p', final, hFinal, hReduced⟩ :=
        ih n₀ (by omega) p₀ middle
      obtain ⟨first⟩ := hMiddle
      obtain ⟨second⟩ := hFinal
      exact ⟨n', p', final, ⟨first.trans second⟩, hReduced⟩

end Merge

/-! ## Valence of a core vertex inside the subdivided graph -/

theorem slotValence_eq_natSum {n p : ℕ} (core : Core n p) (v : Fin n) :
    slotValence core v = ∑ edge : Fin p,
      ((if core.tail edge = v then 1 else 0) +
        if core.head edge = v then 1 else 0) := by
  classical
  have hCard : slotValence core v
      = ∑ x : Fin p × Bool,
          if (if x.2 then core.head x.1 = v else core.tail x.1 = v) then 1 else 0 := by
    rw [slotValence, slotEnds, Finset.card_filter]
  rw [hCard, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl ?_
  intro edge _hEdge
  rw [Fintype.sum_bool]
  simp only [Bool.false_eq_true, if_false, if_true]
  ring

theorem slotValence_eq_sum {n p : ℕ} (core : Core n p) (v : Fin n) :
    ((slotValence core v : ℕ) : ℤ) = ∑ edge : Fin p,
      ((if core.tail edge = v then (1 : ℤ) else 0) +
        if core.head edge = v then (1 : ℤ) else 0) := by
  rw [slotValence_eq_natSum, Nat.cast_sum]
  refine Finset.sum_congr rfl ?_
  intro edge _hEdge
  push_cast
  split_ifs <;> simp

/-- Handshake at the core: every slot has two ends. -/
theorem sum_slotValence {n p : ℕ} (core : Core n p) :
    ∑ v : Fin n, slotValence core v = 2 * p := by
  classical
  simp_rw [slotValence_eq_natSum]
  rw [Finset.sum_comm]
  have hInner : ∀ edge : Fin p,
      (∑ v : Fin n, ((if core.tail edge = v then 1 else 0) +
        if core.head edge = v then 1 else 0)) = 2 := by
    intro edge
    rw [Finset.sum_add_distrib]
    simp
  rw [Finset.sum_congr rfl (fun edge _ => hInner edge)]
  simp [Finset.sum_const, mul_comm]

/-- Slots incident to a vertex, counted without their orientation. -/
theorem card_incidentSlots {n p : ℕ} (core : Core n p)
    (hLoopless : ∀ edge, core.tail edge ≠ core.head edge) (v : Fin n) :
    (Finset.univ.filter fun edge : Fin p =>
        core.tail edge = v ∨ core.head edge = v).card = slotValence core v := by
  classical
  have hImage : (slotEnds core v).image Prod.fst
      = Finset.univ.filter fun edge : Fin p =>
          core.tail edge = v ∨ core.head edge = v := by
    ext edge
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      mem_slotEnds]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hSide : x.2 with _ | _
      · rw [hSide] at hx
        simp only [Bool.false_eq_true, if_false] at hx
        exact Or.inl hx
      · rw [hSide] at hx
        simp only [if_true] at hx
        exact Or.inr hx
    · rintro (hTail | hHead)
      · exact ⟨(edge, false), by simpa using hTail, rfl⟩
      · exact ⟨(edge, true), by simpa using hHead, rfl⟩
  have hInj : ∀ x ∈ slotEnds core v, ∀ y ∈ slotEnds core v,
      x.1 = y.1 → x = y := by
    intro x hx y hy hEq
    have hx' := (mem_slotEnds core v x).mp hx
    have hy' := (mem_slotEnds core v y).mp hy
    rcases hxSide : x.2 with _ | _ <;> rcases hySide : y.2 with _ | _
    · exact Prod.ext hEq (hxSide.trans hySide.symm)
    · rw [hxSide] at hx'; rw [hySide] at hy'
      simp only [Bool.false_eq_true, if_false] at hx'
      simp only [if_true] at hy'
      rw [hEq] at hx'
      exact absurd (hx'.trans hy'.symm) (hLoopless y.1)
    · rw [hxSide] at hx'; rw [hySide] at hy'
      simp only [if_true] at hx'
      simp only [Bool.false_eq_true, if_false] at hy'
      rw [hEq] at hx'
      exact absurd (hy'.trans hx'.symm) (hLoopless y.1)
    · exact Prod.ext hEq (hxSide.trans hySide.symm)
  rw [← hImage, Finset.card_image_of_injOn hInj, slotValence]

theorem slotValence_eq_vertex_degree {n p : ℕ} (spec : Spec n p) (v : Fin n) :
    ((slotValence spec.core v : ℕ) : ℤ)
      = vertexDegree spec.graph (spec.coreVertex v) := by
  rw [slotValence_eq_sum, spec.vertex_degree_coreVertex_eq_incidentSlots v]

/-! ## Reading off the shape of a reduced core -/

/-- In a reduced loopless core, a vertex with exactly two slot ends carries
them on two distinct slots running to one common neighbour. -/
theorem exists_marker_pair {n p : ℕ} {core : Core n p}
    (hLoopless : ∀ edge, core.tail edge ≠ core.head edge)
    (hReduced : Reduced core) (v : Fin n) (hVal : slotValence core v = 2) :
    ∃ x y : Fin p × Bool, x ∈ slotEnds core v ∧ y ∈ slotEnds core v ∧
      x.1 ≠ y.1 ∧ (∀ z ∈ slotEnds core v, z = x ∨ z = y) ∧
      farEnd core x = farEnd core y := by
  classical
  obtain ⟨x, y, hxy, hSet⟩ := Finset.card_eq_two.mp hVal
  have hxMem : x ∈ slotEnds core v := by rw [hSet]; simp
  have hyMem : y ∈ slotEnds core v := by rw [hSet]; simp
  have hExhaust : ∀ z ∈ slotEnds core v, z = x ∨ z = y := by
    intro z hz
    rw [hSet] at hz
    simpa using hz
  have hSlots : x.1 ≠ y.1 := by
    intro hEq
    have hSide : x.2 ≠ y.2 := by
      intro hSide
      exact hxy (Prod.ext hEq hSide)
    have hx := (mem_slotEnds core v x).mp hxMem
    have hy := (mem_slotEnds core v y).mp hyMem
    rcases hCase : x.2 with _ | _
    · have hy2 : y.2 = true := by
        rcases hCase2 : y.2 with _ | _
        · exact absurd (hCase.trans hCase2.symm) hSide
        · rfl
      rw [hCase] at hx
      rw [hy2] at hy
      simp only [Bool.false_eq_true, if_false] at hx
      simp only [if_true] at hy
      rw [hEq] at hx
      exact hLoopless y.1 (hx.trans hy.symm)
    · have hy2 : y.2 = false := by
        rcases hCase2 : y.2 with _ | _
        · rfl
        · exact absurd (hCase.trans hCase2.symm) hSide
      rw [hCase] at hx
      rw [hy2] at hy
      simp only [if_true] at hx
      simp only [Bool.false_eq_true, if_false] at hy
      rw [hEq] at hx
      exact hLoopless y.1 (hy.trans hx.symm)
  refine ⟨x, y, hxMem, hyMem, hSlots, hExhaust, ?_⟩
  by_contra hFar
  exact hReduced.false ⟨v, x, y, hxMem, hyMem, hSlots, hExhaust, hFar⟩

/-! ## Core connectedness from graph connectedness -/

/-- The side of a vertex cut of the core that a subdivision vertex lies on:
core vertices by themselves, interior vertices by the tail of their slot. -/
def sideOf {n p : ℕ} (spec : Spec n p) (S : Finset (Fin n)) :
    spec.Vertex → Prop :=
  Sum.elim (fun v => v ∈ S) (fun z => spec.core.tail z.1 ∈ S)

theorem sideOf_stepLeft {n p : ℕ} (spec : Spec n p) (S : Finset (Fin n))
    (edge : Fin p) (offset : Fin (spec.length edge)) :
    sideOf spec S (spec.stepLeft edge offset) ↔ spec.core.tail edge ∈ S := by
  rw [Spec.stepLeft]
  split_ifs with _hZero
  · exact Iff.rfl
  · exact Iff.rfl

theorem sideOf_stepRight {n p : ℕ} (spec : Spec n p) (S : Finset (Fin n))
    (edge : Fin p) (offset : Fin (spec.length edge))
    (hNoCross : spec.core.tail edge ∈ S ↔ spec.core.head edge ∈ S) :
    sideOf spec S (spec.stepRight edge offset) ↔ spec.core.head edge ∈ S := by
  rw [Spec.stepRight]
  split_ifs with _hLast
  · exact Iff.rfl
  · exact hNoCross

/-- Cut connectedness of the subdivided graph implies cut connectedness of the
core.  This is the converse of `graph_connected_of_coreConnected`. -/
theorem core_connected_of_graph_connected {n p : ℕ} (spec : Spec n p)
    (hConnected : graphConnected spec.graph) : spec.core.Connected := by
  classical
  intro S hSplit
  by_contra hNone
  have hNoCross : ∀ edge : Fin p,
      (spec.core.tail edge ∈ S ↔ spec.core.head edge ∈ S) := by
    intro edge
    constructor
    · intro hTail
      by_contra hHead
      exact hNone ⟨edge, Or.inl ⟨hTail, hHead⟩⟩
    · intro hHead
      by_contra hTail
      exact hNone ⟨edge, Or.inr ⟨hHead, hTail⟩⟩
  obtain ⟨inside, outside, hInside, hOutside⟩ := hSplit
  set A : Finset spec.graph.V :=
    Finset.univ.filter (fun z => sideOf spec S z) with hA
  have hMemA : ∀ z : spec.graph.V, z ∈ A ↔ sideOf spec S z := by
    intro z; simp [hA]
  have hGraphSplit : ∃ x y : spec.graph.V, x ∈ A ∧ y ∉ A := by
    refine ⟨spec.coreVertex inside, spec.coreVertex outside, ?_, ?_⟩
    · exact (hMemA _).mpr hInside
    · intro hMem
      exact hOutside ((hMemA _).mp hMem)
  obtain ⟨x, hx, y, hy, hEdge⟩ := hConnected A hGraphSplit
  rw [spec.num_edges_eq_card_filter_steps] at hEdge
  obtain ⟨step, hStep⟩ := Finset.card_pos.mp hEdge
  rw [Finset.mem_filter] at hStep
  obtain ⟨edge, offset⟩ := step
  have hSame : sideOf spec S (spec.stepLeft edge offset)
      ↔ sideOf spec S (spec.stepRight edge offset) := by
    rw [sideOf_stepLeft, sideOf_stepRight spec S edge offset (hNoCross edge)]
    exact hNoCross edge
  have hxSide : sideOf spec S x := (hMemA x).mp hx
  have hySide : ¬ sideOf spec S y := fun h => hy ((hMemA y).mpr h)
  rcases hStep.2 with hPair | hPair
  · have hLeft : spec.stepLeft edge offset = x := congrArg Prod.fst hPair
    have hRight : spec.stepRight edge offset = y := congrArg Prod.snd hPair
    rw [hLeft, hRight] at hSame
    exact hySide (hSame.mp hxSide)
  · have hLeft : spec.stepLeft edge offset = y := congrArg Prod.fst hPair
    have hRight : spec.stepRight edge offset = x := congrArg Prod.snd hPair
    rw [hLeft, hRight] at hSame
    exact hySide (hSame.mpr hxSide)

/-! ## Unordered multiplicities of a core -/

theorem explicitCoreMultiplicity_symm {n p : ℕ} (core : Core n p) (x y : Fin n) :
    explicitCoreMultiplicity core x y = explicitCoreMultiplicity core y x := by
  classical
  unfold explicitCoreMultiplicity
  congr 1
  ext edge
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  tauto

theorem explicitCoreMultiplicity_self {n p : ℕ} (core : Core n p)
    (hLoopless : ∀ edge, core.tail edge ≠ core.head edge) (x : Fin n) :
    explicitCoreMultiplicity core x x = 0 := by
  classical
  unfold explicitCoreMultiplicity
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro edge _hEdge
  rintro (⟨hTail, hHead⟩ | ⟨hTail, hHead⟩)
  · exact hLoopless edge (hTail.trans hHead.symm)
  · exact hLoopless edge (hTail.trans hHead.symm)

/-- Total unordered multiplicity at a vertex is its slot valence. -/
theorem sum_explicitCoreMultiplicity {n p : ℕ} (core : Core n p)
    (hLoopless : ∀ edge, core.tail edge ≠ core.head edge) (v : Fin n) :
    ∑ w : Fin n, explicitCoreMultiplicity core v w = slotValence core v := by
  classical
  rw [slotValence_eq_natSum]
  have hExpand : ∀ w : Fin n, explicitCoreMultiplicity core v w
      = ∑ edge : Fin p, if (core.tail edge = v ∧ core.head edge = w) ∨
          (core.tail edge = w ∧ core.head edge = v) then 1 else 0 := by
    intro w
    unfold explicitCoreMultiplicity
    rw [Finset.card_filter]
  rw [Finset.sum_congr rfl (fun w _ => hExpand w), Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro edge _hEdge
  by_cases hTail : core.tail edge = v
  · have hHead : core.head edge ≠ v := fun hEq => hLoopless edge (hTail.trans hEq.symm)
    rw [if_pos hTail, if_neg hHead]
    have hCond : ∀ w : Fin n,
        (((core.tail edge = v ∧ core.head edge = w) ∨
          (core.tail edge = w ∧ core.head edge = v)) ↔ core.head edge = w) := by
      intro w
      constructor
      · rintro (⟨_, h⟩ | ⟨_, h⟩)
        · exact h
        · exact absurd h hHead
      · intro h; exact Or.inl ⟨hTail, h⟩
    rw [Finset.sum_congr rfl (fun w _ => if_congr (hCond w) rfl rfl)]
    simp
  · by_cases hHead : core.head edge = v
    · rw [if_neg hTail, if_pos hHead]
      have hCond : ∀ w : Fin n,
          (((core.tail edge = v ∧ core.head edge = w) ∨
            (core.tail edge = w ∧ core.head edge = v)) ↔ core.tail edge = w) := by
        intro w
        constructor
        · rintro (⟨h, _⟩ | ⟨h, _⟩)
          · exact absurd h hTail
          · exact h
        · intro h; exact Or.inr ⟨h, hHead⟩
      rw [Finset.sum_congr rfl (fun w _ => if_congr (hCond w) rfl rfl)]
      simp
    · rw [if_neg hTail, if_neg hHead]
      have hCond : ∀ w : Fin n,
          ¬(((core.tail edge = v ∧ core.head edge = w) ∨
            (core.tail edge = w ∧ core.head edge = v))) := by
        intro w
        rintro (⟨h, _⟩ | ⟨_, h⟩)
        · exact hTail h
        · exact hHead h
      rw [Finset.sum_congr rfl (fun w _ => if_neg (hCond w))]
      simp

theorem explicitCoreMultiplicity_reindex {n p n' p' : ℕ} (core : Core n p)
    (vertexEquiv : Fin n ≃ Fin n') (slotEquiv : Fin p ≃ Fin p') (x y : Fin n) :
    explicitCoreMultiplicity (coreReindex core vertexEquiv slotEquiv)
        (vertexEquiv x) (vertexEquiv y)
      = explicitCoreMultiplicity core x y := by
  classical
  unfold explicitCoreMultiplicity
  have hSet : (Finset.univ.filter fun edge : Fin p' =>
        ((coreReindex core vertexEquiv slotEquiv).tail edge = vertexEquiv x ∧
          (coreReindex core vertexEquiv slotEquiv).head edge = vertexEquiv y) ∨
        ((coreReindex core vertexEquiv slotEquiv).tail edge = vertexEquiv y ∧
          (coreReindex core vertexEquiv slotEquiv).head edge = vertexEquiv x))
      = (Finset.univ.filter fun edge : Fin p =>
          (core.tail edge = x ∧ core.head edge = y) ∨
          (core.tail edge = y ∧ core.head edge = x)).map
            slotEquiv.toEmbedding := by
    ext edge
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Equiv.toEmbedding_apply, coreReindex, EmbeddingLike.apply_eq_iff_eq]
    constructor
    · intro hEdge
      exact ⟨slotEquiv.symm edge, hEdge, by simp⟩
    · rintro ⟨e, he, rfl⟩
      simpa using he
  rw [hSet, Finset.card_map]

/-! ## The shape of a reduced core -/

/-- A core presented as the loopless split of a loop-aware pseudocore: every
vertex is either stable, or a marker carrying exactly two slots to a single
stable partner. -/
structure MarkedShape {N P : ℕ} (spec : Spec N P) where
  /-- The Boolean designation of loop markers, distinguishing them from stable base vertices. -/
  isMarker : Fin N → Bool
  /-- The stable base partner of each marker, joined to it by exactly two edge occurrences and
  its only neighbor. -/
  partner : Fin N → Fin N
  base_stable : ∀ v : Fin N, isMarker v = false → 3 ≤ slotValence spec.core v
  partner_base : ∀ v : Fin N, isMarker v = true → isMarker (partner v) = false
  marker_mult : ∀ v : Fin N, isMarker v = true →
    explicitCoreMultiplicity spec.core v (partner v) = 2
  marker_mult_zero : ∀ v w : Fin N, isMarker v = true → w ≠ partner v →
    explicitCoreMultiplicity spec.core v w = 0

namespace MarkedShape

variable {N P : ℕ} {spec : Spec N P} (shape : MarkedShape spec)

theorem partner_ne (v : Fin N) (hv : shape.isMarker v = true) :
    shape.partner v ≠ v := by
  intro hEq
  have hBase := shape.partner_base v hv
  rw [hEq, hv] at hBase
  exact Bool.noConfusion hBase

theorem marker_slotValence (v : Fin N) (hv : shape.isMarker v = true) :
    slotValence spec.core v = 2 := by
  classical
  rw [← sum_explicitCoreMultiplicity spec.core spec.core_loopless v]
  rw [Finset.sum_eq_single (shape.partner v)]
  · exact shape.marker_mult v hv
  · intro w _hw hNe
    exact shape.marker_mult_zero v w hv hNe
  · intro hMem
    exact absurd (Finset.mem_univ (shape.partner v)) hMem

end MarkedShape

/-! ## Building the marked shape of a reduced core -/

/-- In a reduced core, a vertex with exactly two slot ends has all of its
slots running to one common neighbour. -/
theorem marker_structure {N P : ℕ} {spec : Spec N P} (hReduced : Reduced spec.core)
    (v : Fin N) (hVal : slotValence spec.core v = 2) :
    ∃ w : Fin N, w ≠ v ∧
      (∀ edge : Fin P, spec.core.tail edge = v → spec.core.head edge = w) ∧
      (∀ edge : Fin P, spec.core.head edge = v → spec.core.tail edge = w) := by
  classical
  obtain ⟨x, y, hxMem, hyMem, hSlots, hExhaust, hFar⟩ :=
    exists_marker_pair spec.core_loopless hReduced v hVal
  have hx := (mem_slotEnds spec.core v x).mp hxMem
  have hy := (mem_slotEnds spec.core v y).mp hyMem
  refine ⟨farEnd spec.core x, ?_, ?_, ?_⟩
  · rcases hSide : x.2 with _ | _
    · rw [hSide] at hx
      simp only [Bool.false_eq_true, if_false] at hx
      simp only [farEnd, hSide, Bool.false_eq_true, if_false]
      rw [← hx]
      exact fun hEq => spec.core_loopless x.1 hEq.symm
    · rw [hSide] at hx
      simp only [if_true] at hx
      simp only [farEnd, hSide, if_true]
      rw [← hx]
      exact spec.core_loopless x.1
  · intro edge hEdge
    have hMem : (edge, false) ∈ slotEnds spec.core v := by
      simpa [mem_slotEnds] using hEdge
    rcases hExhaust _ hMem with hEq | hEq
    · have h1 : x.1 = edge := congrArg Prod.fst hEq.symm
      have h2 : x.2 = false := congrArg Prod.snd hEq.symm
      simp only [farEnd, h2, Bool.false_eq_true, if_false, h1]
    · have h1 : y.1 = edge := congrArg Prod.fst hEq.symm
      have h2 : y.2 = false := congrArg Prod.snd hEq.symm
      rw [hFar]
      simp only [farEnd, h2, Bool.false_eq_true, if_false, h1]
  · intro edge hEdge
    have hMem : (edge, true) ∈ slotEnds spec.core v := by
      simpa [mem_slotEnds] using hEdge
    rcases hExhaust _ hMem with hEq | hEq
    · have h1 : x.1 = edge := congrArg Prod.fst hEq.symm
      have h2 : x.2 = true := congrArg Prod.snd hEq.symm
      simp only [farEnd, h2, if_true, h1]
    · have h1 : y.1 = edge := congrArg Prod.fst hEq.symm
      have h2 : y.2 = true := congrArg Prod.snd hEq.symm
      rw [hFar]
      simp only [farEnd, h2, if_true, h1]

section Shape

variable {N P : ℕ} {spec : Spec N P}

theorem mult_eq_slotValence_of_structure {v w : Fin N}
    (hTail : ∀ edge : Fin P, spec.core.tail edge = v → spec.core.head edge = w)
    (hHead : ∀ edge : Fin P, spec.core.head edge = v → spec.core.tail edge = w) :
    explicitCoreMultiplicity spec.core v w = slotValence spec.core v := by
  classical
  rw [← card_incidentSlots spec.core spec.core_loopless v]
  unfold explicitCoreMultiplicity
  congr 1
  ext edge
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨h, _⟩ | ⟨_, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (h | h)
    · exact Or.inl ⟨h, hTail edge h⟩
    · exact Or.inr ⟨hHead edge h, h⟩

theorem mult_eq_zero_of_structure {v w u : Fin N} (hNe : u ≠ w)
    (hTail : ∀ edge : Fin P, spec.core.tail edge = v → spec.core.head edge = w)
    (hHead : ∀ edge : Fin P, spec.core.head edge = v → spec.core.tail edge = w) :
    explicitCoreMultiplicity spec.core v u = 0 := by
  classical
  unfold explicitCoreMultiplicity
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro edge _hEdge
  rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
  · exact hNe ((hTail edge h1) ▸ h2.symm)
  · exact hNe ((hHead edge h2) ▸ h1.symm)

/-- Two adjacent bivalent vertices would exhaust the graph, which has genus
one. -/
theorem partner_not_bivalent_of_genus_ne_one (hReduced : Reduced spec.core)
    (hConnected : graphConnected spec.graph) {g : ℕ}
    (hGenus : genus spec.graph = g) (hGenus_ne_one : g ≠ 1)
    {v w : Fin N} (hvw : w ≠ v)
    (hVal : slotValence spec.core v = 2)
    (hTail : ∀ edge : Fin P, spec.core.tail edge = v → spec.core.head edge = w)
    (hHead : ∀ edge : Fin P, spec.core.head edge = v → spec.core.tail edge = w) :
    slotValence spec.core w ≠ 2 := by
  classical
  intro hValW
  obtain ⟨u, huw, hTailW, hHeadW⟩ := marker_structure hReduced w hValW
  have hUV : u = v := by
    by_contra hNe
    have hZero : explicitCoreMultiplicity spec.core w v = 0 :=
      mult_eq_zero_of_structure (Ne.symm hNe) hTailW hHeadW
    have hTwo : explicitCoreMultiplicity spec.core v w = slotValence spec.core v :=
      mult_eq_slotValence_of_structure hTail hHead
    rw [hVal] at hTwo
    rw [explicitCoreMultiplicity_symm] at hZero
    omega
  rw [hUV] at hTailW hHeadW
  -- every slot has both endpoints in `{v, w}`
  have hInside : ∀ edge : Fin P,
      (spec.core.tail edge = v ∨ spec.core.tail edge = w) →
      (spec.core.head edge = v ∨ spec.core.head edge = w) := by
    intro edge hEdge
    rcases hEdge with h | h
    · exact Or.inr (hTail edge h)
    · exact Or.inl (hTailW edge h)
  have hInsideHead : ∀ edge : Fin P,
      (spec.core.head edge = v ∨ spec.core.head edge = w) →
      (spec.core.tail edge = v ∨ spec.core.tail edge = w) := by
    intro edge hEdge
    rcases hEdge with h | h
    · exact Or.inr (hHead edge h)
    · exact Or.inl (hHeadW edge h)
  by_cases hOther : ∃ z : Fin N, z ≠ v ∧ z ≠ w
  · obtain ⟨z, hzv, hzw⟩ := hOther
    have hCore := core_connected_of_graph_connected spec hConnected
    obtain ⟨edge, hEdge⟩ := hCore ({v, w} : Finset (Fin N)) ⟨v, z, by simp, by simp [hzv, hzw]⟩
    rcases hEdge with ⟨hIn, hOut⟩ | ⟨hIn, hOut⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hIn hOut
      exact hOut (hInside edge hIn)
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hIn hOut
      exact hOut (hInsideHead edge hIn)
  · push Not at hOther
    have hCardN : N = 2 := by
      have hUniv : (Finset.univ : Finset (Fin N)) = {v, w} := by
        ext z
        simp only [Finset.mem_univ, true_iff, Finset.mem_insert, Finset.mem_singleton]
        by_cases hz : z = v
        · exact Or.inl hz
        · exact Or.inr (hOther z hz)
      have := congrArg Finset.card hUniv
      rw [Finset.card_univ, Fintype.card_fin, Finset.card_insert_of_notMem (by simp [Ne.symm hvw]),
        Finset.card_singleton] at this
      omega
    have hCardP : P = 2 := by
      have hUniv : (Finset.univ.filter fun edge : Fin P =>
          spec.core.tail edge = v ∨ spec.core.head edge = v)
            = (Finset.univ : Finset (Fin P)) := by
        ext edge
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
        by_cases hT : spec.core.tail edge = v
        · exact Or.inl hT
        · have : spec.core.tail edge = w := by
            rcases hOther (spec.core.tail edge) hT with h
            exact h
          exact Or.inr (hTailW edge this)
      have hCard := card_incidentSlots spec.core spec.core_loopless v
      rw [hUniv, Finset.card_univ, Fintype.card_fin, hVal] at hCard
      exact hCard
    have hG := spec.genus_graph
    rw [hGenus, hCardN, hCardP] at hG
    apply hGenus_ne_one
    omega

end Shape

/-- **Shape of a reduced presentation.**  Every vertex of a reduced core is
either stable or a bivalent marker attached to a single stable base. -/
theorem exists_markedShapeAt {N P g : ℕ} (spec : Spec N P)
    (hReduced : Reduced spec.core) (hConnected : graphConnected spec.graph)
    (hGenus : genus spec.graph = g) (hGenus_ne_one : g ≠ 1)
    (hDegree : ∀ v : Fin N, 2 ≤ slotValence spec.core v) :
    Nonempty (MarkedShape spec) := by
  classical
  set isMarker : Fin N → Bool := fun v => decide (slotValence spec.core v = 2)
    with hIsMarker
  have hMarkerVal : ∀ v : Fin N, isMarker v = true → slotValence spec.core v = 2 := by
    intro v hv
    simpa [hIsMarker] using hv
  have hBaseVal : ∀ v : Fin N, isMarker v = false → 3 ≤ slotValence spec.core v := by
    intro v hv
    have hNe : slotValence spec.core v ≠ 2 := by simpa [hIsMarker] using hv
    have := hDegree v
    omega
  have hAll : ∀ v : Fin N, ∃ w : Fin N, isMarker v = true →
      (isMarker w = false ∧ explicitCoreMultiplicity spec.core v w = 2 ∧
        ∀ u : Fin N, u ≠ w → explicitCoreMultiplicity spec.core v u = 0) := by
    intro v
    by_cases hv : isMarker v = true
    · have hVal := hMarkerVal v hv
      obtain ⟨w, hwv, hTail, hHead⟩ := marker_structure hReduced v hVal
      refine ⟨w, fun _ => ⟨?_, ?_, ?_⟩⟩
      · have hNotTwo : slotValence spec.core w ≠ 2 :=
          partner_not_bivalent_of_genus_ne_one hReduced hConnected hGenus hGenus_ne_one
            hwv hVal hTail hHead
        simpa [hIsMarker] using hNotTwo
      · rw [mult_eq_slotValence_of_structure hTail hHead, hVal]
      · intro u hu
        exact mult_eq_zero_of_structure hu hTail hHead
    · exact ⟨v, fun h => absurd h hv⟩
  choose partner hPartner using hAll
  exact ⟨{ isMarker := isMarker
           partner := partner
           base_stable := hBaseVal
           partner_base := fun v hv => (hPartner v hv).1
           marker_mult := fun v hv => (hPartner v hv).2.1
           marker_mult_zero := fun v w hv hne => (hPartner v hv).2.2 w hne }⟩

/-- The genus-four specialization of `exists_markedShapeAt`. -/
theorem exists_markedShape {N P : ℕ} (spec : Spec N P)
    (hReduced : Reduced spec.core) (hConnected : graphConnected spec.graph)
    (hGenus : genus spec.graph = 4)
    (hDegree : ∀ v : Fin N, 2 ≤ slotValence spec.core v) :
    Nonempty (MarkedShape spec) :=
  exists_markedShapeAt spec hReduced hConnected hGenus (by norm_num) hDegree

/-! ## Encoding a marked shape as a pseudocore with split metadata -/

namespace MarkedShape

variable {N P : ℕ} {spec : Spec N P} (shape : MarkedShape spec)

theorem head_eq_partner (v : Fin N) (hv : shape.isMarker v = true)
    (edge : Fin P) (hEdge : spec.core.tail edge = v) :
    spec.core.head edge = shape.partner v := by
  classical
  by_contra hNe
  have hZero := shape.marker_mult_zero v (spec.core.head edge) hv hNe
  unfold explicitCoreMultiplicity at hZero
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hZero
  exact hZero (Finset.mem_univ edge) (Or.inl ⟨hEdge, rfl⟩)

theorem tail_eq_partner (v : Fin N) (hv : shape.isMarker v = true)
    (edge : Fin P) (hEdge : spec.core.head edge = v) :
    spec.core.tail edge = shape.partner v := by
  classical
  by_contra hNe
  have hZero := shape.marker_mult_zero v (spec.core.tail edge) hv hNe
  unfold explicitCoreMultiplicity at hZero
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hZero
  exact hZero (Finset.mem_univ edge) (Or.inr ⟨rfl, hEdge⟩)

end MarkedShape

private theorem exists_markedPartition {N P : ℕ} (spec : Spec N P)
    (shape : MarkedShape spec) :
    ∃ (k L : ℕ) (ρ : Fin N ≃ Fin k ⊕ Fin L)
      (baseOf : Fin k → Fin N) (markOf : Fin L → Fin N) (fmap : Fin L → Fin k),
      (∀ i : Fin k, ρ (baseOf i) = Sum.inl i) ∧
      (∀ j : Fin L, ρ (markOf j) = Sum.inr j) ∧
      (∀ i : Fin k, shape.isMarker (baseOf i) = false) ∧
      (∀ j : Fin L, shape.isMarker (markOf j) = true) ∧
      Function.Injective baseOf ∧
      (∀ v : Fin N, (∃ i, v = baseOf i) ∨ ∃ j, v = markOf j) ∧
      (∀ f : Fin N → ℕ, ∑ v : Fin N, f v =
        (∑ i : Fin k, f (baseOf i)) + ∑ j : Fin L, f (markOf j)) ∧
      N = k + L ∧
      (∀ j : Fin L, baseOf (fmap j) = shape.partner (markOf j)) ∧
      (∀ (j : Fin L) (i : Fin k), fmap j = i ↔
        shape.partner (markOf j) = baseOf i) := by
  classical
  -- split the core vertices into bases and markers
  set isBase : Fin N → Prop := fun v => shape.isMarker v = false with hIsBase
  have : DecidablePred isBase := fun v => by unfold isBase; infer_instance
  set Base := {v : Fin N // isBase v} with hBaseType
  set Mark := {v : Fin N // ¬ isBase v} with hMarkType
  set k : ℕ := Fintype.card Base with hk
  set L : ℕ := Fintype.card Mark with hL
  set eb : Base ≃ Fin k := Fintype.equivFin Base with heb
  set em : Mark ≃ Fin L := Fintype.equivFin Mark with hem
  set ρ : Fin N ≃ Fin k ⊕ Fin L :=
    (Equiv.sumCompl isBase).symm.trans (Equiv.sumCongr eb em) with hρ
  set baseOf : Fin k → Fin N := fun i => ((eb.symm i : Base) : Fin N) with hbaseOf
  set markOf : Fin L → Fin N := fun j => ((em.symm j : Mark) : Fin N) with hmarkOf
  have hRhoBase : ∀ i : Fin k, ρ (baseOf i) = Sum.inl i := by
    intro i
    have hInner : (Equiv.sumCompl isBase).symm (baseOf i) = Sum.inl (eb.symm i) :=
      (Equiv.symm_apply_eq _).mpr rfl
    simp [hρ, hInner]
  have hRhoMark : ∀ j : Fin L, ρ (markOf j) = Sum.inr j := by
    intro j
    have hInner : (Equiv.sumCompl isBase).symm (markOf j) = Sum.inr (em.symm j) :=
      (Equiv.symm_apply_eq _).mpr rfl
    simp [hρ, hInner]
  have hBaseMarker : ∀ i : Fin k, shape.isMarker (baseOf i) = false :=
    fun i => (eb.symm i).2
  have hMarkMarker : ∀ j : Fin L, shape.isMarker (markOf j) = true := by
    intro j
    have := (em.symm j).2
    simp only [hIsBase] at this
    simpa using this
  have hBaseInj : Function.Injective baseOf := by
    intro i i' hEq
    have := congrArg ρ hEq
    rw [hRhoBase, hRhoBase] at this
    exact Sum.inl.inj this
  have hCases : ∀ v : Fin N, (∃ i, v = baseOf i) ∨ ∃ j, v = markOf j := by
    intro v
    rcases hSum : ρ v with i | j
    · exact Or.inl ⟨i, by rw [← hRhoBase i] at hSum; exact ρ.injective hSum⟩
    · exact Or.inr ⟨j, by rw [← hRhoMark j] at hSum; exact ρ.injective hSum⟩
  have hSplitSum : ∀ g : Fin N → ℕ, ∑ w : Fin N, g w
      = (∑ i : Fin k, g (baseOf i)) + ∑ j : Fin L, g (markOf j) := by
    intro g
    rw [← Equiv.sum_comp ρ.symm g, Fintype.sum_sum_type]
    have h1 : ∀ i : Fin k, g (ρ.symm (Sum.inl i)) = g (baseOf i) := fun i => by
      rw [← hRhoBase i, Equiv.symm_apply_apply]
    have h2 : ∀ j : Fin L, g (ρ.symm (Sum.inr j)) = g (markOf j) := fun j => by
      rw [← hRhoMark j, Equiv.symm_apply_apply]
    rw [Finset.sum_congr rfl (fun i _ => h1 i), Finset.sum_congr rfl (fun j _ => h2 j)]
  have hCardN : N = k + L := by
    have h1 : Fintype.card (Fin N) = Fintype.card (Base ⊕ Mark) :=
      Fintype.card_congr (Equiv.sumCompl isBase).symm
    rw [Fintype.card_fin, Fintype.card_sum] at h1
    exact h1
  -- the fibre map from markers to their base
  set fmap : Fin L → Fin k := fun j =>
    eb ⟨shape.partner (markOf j), shape.partner_base _ (hMarkMarker j)⟩ with hfmap
  have hFmap : ∀ j : Fin L, baseOf (fmap j) = shape.partner (markOf j) := by
    intro j; simp [hbaseOf, hfmap]
  have hFmapIff : ∀ (j : Fin L) (i : Fin k),
      fmap j = i ↔ shape.partner (markOf j) = baseOf i := by
    intro j i
    constructor
    · intro h; rw [← hFmap j, h]
    · intro h; exact hBaseInj (by rw [hFmap j, h])
  exact ⟨k, L, ρ, baseOf, markOf, fmap, hRhoBase, hRhoMark, hBaseMarker,
    hMarkMarker, hBaseInj, hCases, hSplitSum, hCardN, hFmap, hFmapIff⟩

private theorem pseudocore_connected_of_markedPartition {N P k L : ℕ}
    (spec : Spec N P) (shape : MarkedShape spec)
    (hConnected : graphConnected spec.graph) (pc : Pseudocore k)
    (ρ : Fin N ≃ Fin k ⊕ Fin L) (baseOf : Fin k → Fin N)
    (markOf : Fin L → Fin N) (fmap : Fin L → Fin k)
    (hRhoBase : ∀ i : Fin k, ρ (baseOf i) = Sum.inl i)
    (hRhoMark : ∀ j : Fin L, ρ (markOf j) = Sum.inr j)
    (hMarkMarker : ∀ j : Fin L, shape.isMarker (markOf j) = true)
    (hBaseInj : Function.Injective baseOf)
    (hCases : ∀ v : Fin N, (∃ i, v = baseOf i) ∨ ∃ j, v = markOf j)
    (hFmap : ∀ j : Fin L, baseOf (fmap j) = shape.partner (markOf j))
    (hMarkMark : ∀ j j' : Fin L,
      explicitCoreMultiplicity spec.core (markOf j) (markOf j') = 0)
    (hMultiplicity : ∀ i i' : Fin k, pc.multiplicity i i' =
      explicitCoreMultiplicity spec.core (baseOf i) (baseOf i')) : pc.Connected := by
  classical
  have hCoreConnected := core_connected_of_graph_connected spec hConnected
  intro S hSplit
  obtain ⟨i₀, i₁, hi₀, hi₁⟩ := hSplit
  set T : Finset (Fin N) := Finset.univ.filter (fun v =>
    match ρ v with
    | Sum.inl i => i ∈ S
    | Sum.inr j => fmap j ∈ S) with hT
  have hMemBase : ∀ i : Fin k, (baseOf i ∈ T ↔ i ∈ S) := by
    intro i; simp [hT, hRhoBase i]
  have hMemMark : ∀ j : Fin L, (markOf j ∈ T ↔ fmap j ∈ S) := by
    intro j; simp [hT, hRhoMark j]
  obtain ⟨edge, hEdge⟩ := hCoreConnected T
    ⟨baseOf i₀, baseOf i₁, (hMemBase i₀).mpr hi₀,
      fun hMem => hi₁ ((hMemBase i₁).mp hMem)⟩
  -- both endpoints of a crossing slot must be bases
  have hBaseEnd : ∀ (v w : Fin N), spec.core.tail edge = v →
      spec.core.head edge = w → (v ∈ T ↔ w ∈ T) ∨
      ∃ i i' : Fin k, v = baseOf i ∧ w = baseOf i' := by
    intro v w hv hw
    rcases hCases v with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rcases hCases w with ⟨i', rfl⟩ | ⟨j', rfl⟩
      · exact Or.inr ⟨i, i', rfl, rfl⟩
      · left
        have hPartner := shape.tail_eq_partner (markOf j') (hMarkMarker j') edge hw
        rw [hv, ← hFmap j'] at hPartner
        have hEq : i = fmap j' := hBaseInj hPartner
        rw [hMemBase, hMemMark, hEq]
    · left
      have hPartner := shape.head_eq_partner (markOf j) (hMarkMarker j) edge hv
      rcases hCases w with ⟨i', rfl⟩ | ⟨j', rfl⟩
      · rw [hw, ← hFmap j] at hPartner
        have hEq : i' = fmap j := hBaseInj hPartner
        rw [hMemMark, hMemBase, hEq]
      · exfalso
        have hZero := hMarkMark j j'
        unfold explicitCoreMultiplicity at hZero
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hZero
        exact hZero (Finset.mem_univ edge) (Or.inl ⟨hv, hw⟩)
  rcases hEdge with ⟨hIn, hOut⟩ | ⟨hIn, hOut⟩
  · rcases hBaseEnd _ _ rfl rfl with hIff | ⟨i, i', hvi, hwi⟩
    · exact absurd (hIff.mp hIn) hOut
    · refine ⟨i, ?_, i', ?_, ?_⟩
      · rw [← hMemBase i, ← hvi]; exact hIn
      · rw [← hMemBase i', ← hwi]; exact hOut
      · change 0 < pc.multiplicity i i'
        rw [hMultiplicity]
        unfold explicitCoreMultiplicity
        refine Finset.card_pos.mpr ⟨edge, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inl ⟨hvi, hwi⟩
  · rcases hBaseEnd _ _ rfl rfl with hIff | ⟨i, i', hvi, hwi⟩
    · exact absurd (hIff.mpr hIn) hOut
    · refine ⟨i', ?_, i, ?_, ?_⟩
      · rw [← hMemBase i', ← hwi]; exact hIn
      · rw [← hMemBase i, ← hvi]; exact hOut
      · change 0 < pc.multiplicity i' i
        rw [hMultiplicity]
        unfold explicitCoreMultiplicity
        refine Finset.card_pos.mpr ⟨edge, ?_⟩
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact Or.inr ⟨hvi, hwi⟩

/-- **The pseudocore encoding.**  A marked-shape presentation of a connected
genus-`g` graph is the loopless split of a valid pseudocore on at most
`2 * (g - 1)` vertices. -/
theorem pseudocorePresentation_of_markedShapeAt {N P g : ℕ} (spec : Spec N P)
    (shape : MarkedShape spec) (hConnected : graphConnected spec.graph)
    (hGenus : genus spec.graph = g) {G : CFGraph.{0}}
    (hG : Nonempty (LaplacianEquiv G spec.graph)) :
    ∃ (k : ℕ) (core : Pseudocore k) (split : core.SplitMetadata),
      k ≤ 2 * (g - 1) ∧ core.ValidAt g ∧ PseudocoreSplitGlue.Compatible split ∧
      ∃ spec' : Spec (k + core.loopCount) core.splitEdgeCount,
        spec'.core = split.splitCore ∧ Nonempty (LaplacianEquiv G spec'.graph) := by
  classical
  obtain ⟨k, L, ρ, baseOf, markOf, fmap, hRhoBase, hRhoMark, hBaseMarker,
    hMarkMarker, hBaseInj, hCases, hSplitSum, hCardN, hFmap, hFmapIff⟩ :=
    exists_markedPartition spec shape
  -- the pseudocore
  set pc : Pseudocore k :=
    { loops := fun i => (Finset.univ.filter fun j : Fin L => fmap j = i).card
      multiplicity := fun i i' =>
        explicitCoreMultiplicity spec.core (baseOf i) (baseOf i') } with hpc
  have hLoops : ∀ i : Fin k, pc.loops i
      = (Finset.univ.filter fun j : Fin L => fmap j = i).card := fun _ => rfl
  have hLoopCount : pc.loopCount = L := by
    rw [Pseudocore.loopCount]
    have := Finset.card_eq_sum_card_fiberwise
      (f := fmap) (s := (Finset.univ : Finset (Fin L)))
      (t := (Finset.univ : Finset (Fin k))) (fun j _ => Finset.mem_univ _)
    rw [Finset.card_univ, Fintype.card_fin] at this
    exact this.symm
  have hWellFormed : pc.MatrixWellFormed := by
    constructor
    · intro i
      exact explicitCoreMultiplicity_self spec.core spec.core_loopless (baseOf i)
    · intro i i'
      exact explicitCoreMultiplicity_symm spec.core (baseOf i) (baseOf i')
  -- multiplicities involving markers
  have hBaseMark : ∀ (i : Fin k) (j : Fin L),
      explicitCoreMultiplicity spec.core (baseOf i) (markOf j)
        = if fmap j = i then 2 else 0 := by
    intro i j
    rw [explicitCoreMultiplicity_symm]
    by_cases hEq : fmap j = i
    · rw [if_pos hEq]
      have hPartner : shape.partner (markOf j) = baseOf i := (hFmapIff j i).mp hEq
      rw [← hPartner]
      exact shape.marker_mult (markOf j) (hMarkMarker j)
    · rw [if_neg hEq]
      refine shape.marker_mult_zero (markOf j) (baseOf i) (hMarkMarker j) ?_
      intro hContra
      exact hEq ((hFmapIff j i).mpr hContra.symm)
  have hMarkMark : ∀ j j' : Fin L,
      explicitCoreMultiplicity spec.core (markOf j) (markOf j') = 0 := by
    intro j j'
    refine shape.marker_mult_zero (markOf j) (markOf j') (hMarkMarker j) ?_
    intro hContra
    have hBase := shape.partner_base (markOf j) (hMarkMarker j)
    rw [← hContra, hMarkMarker j'] at hBase
    exact Bool.noConfusion hBase
  -- valences
  have hValenceBase : ∀ i : Fin k, pc.valence i = slotValence spec.core (baseOf i) := by
    intro i
    rw [← sum_explicitCoreMultiplicity spec.core spec.core_loopless (baseOf i),
      hSplitSum (fun w => explicitCoreMultiplicity spec.core (baseOf i) w)]
    have hSecond : (∑ j : Fin L,
        explicitCoreMultiplicity spec.core (baseOf i) (markOf j)) = 2 * pc.loops i := by
      rw [Finset.sum_congr rfl (fun j _ => hBaseMark i j)]
      rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, hLoops i,
        smul_eq_mul, mul_comm]
    rw [hSecond, Pseudocore.valence]
    ring
  have hValenceMark : ∀ j : Fin L, slotValence spec.core (markOf j) = 2 :=
    fun j => shape.marker_slotValence (markOf j) (hMarkMarker j)
  have hStable : pc.Stable := by
    intro i
    rw [hValenceBase i]
    exact shape.base_stable (baseOf i) (hBaseMarker i)
  -- the split edge count
  have hSplitEdgeCount : pc.splitEdgeCount = P := by
    have hHand : ∑ v : Fin N, slotValence spec.core v = 2 * P :=
      sum_slotValence spec.core
    rw [hSplitSum (fun v => slotValence spec.core v)] at hHand
    have hFirst : (∑ i : Fin k, slotValence spec.core (baseOf i))
        = 2 * pc.edgeCount := by
      rw [Finset.sum_congr rfl (fun i _ => (hValenceBase i).symm)]
      exact Pseudocore.sum_valence_eq pc hWellFormed
    have hSecond : (∑ j : Fin L, slotValence spec.core (markOf j)) = 2 * L := by
      rw [Finset.sum_congr rfl (fun j _ => hValenceMark j)]
      simp [mul_comm]
    rw [hFirst, hSecond] at hHand
    rw [Pseudocore.splitEdgeCount]
    have hEdge : pc.edgeCount = pc.loopCount + pc.nonloopEdgeCount := rfl
    rw [hEdge, hLoopCount] at hHand
    omega
  have hEdgeCountIdentity : pc.edgeCount + 1 = k + g := by
    have hG := spec.genus_graph
    rw [hGenus] at hG
    have hEdge : pc.edgeCount = pc.loopCount + pc.nonloopEdgeCount := rfl
    have hSplit : pc.splitEdgeCount = pc.nonloopEdgeCount + 2 * pc.loopCount := rfl
    rw [hSplitEdgeCount] at hSplit
    rw [hLoopCount] at hEdge hSplit
    omega
  have hSmall : k ≤ 2 * (g - 1) := by
    have hHand := Pseudocore.sum_valence_eq pc hWellFormed
    have hLower : 3 * k ≤ ∑ i : Fin k, pc.valence i := by
      calc 3 * k = ∑ _i : Fin k, 3 := by simp [mul_comm]
        _ ≤ ∑ i : Fin k, pc.valence i := Finset.sum_le_sum (fun i _ => hStable i)
    omega
  have hPcConnected : pc.Connected :=
    pseudocore_connected_of_markedPartition spec shape hConnected pc ρ baseOf markOf fmap
      hRhoBase hRhoMark hMarkMarker hBaseInj hCases hFmap hMarkMark (fun _ _ => rfl)
  have hValid : pc.ValidAt g :=
    ⟨hWellFormed, hPcConnected, hStable, hEdgeCountIdentity⟩
  -- the split metadata
  set vEquiv : Fin N ≃ Fin (k + pc.loopCount) :=
    ρ.trans ((Equiv.sumCongr (Equiv.refl (Fin k)) (finCongr hLoopCount.symm)).trans
      finSumFinEquiv) with hvEquiv
  set sEquiv : Fin P ≃ Fin pc.splitEdgeCount := finCongr hSplitEdgeCount.symm with hsEquiv
  set markIndex : Fin L ≃ Fin pc.loopCount := finCongr hLoopCount.symm with hmarkIndex
  have hVBase : ∀ i : Fin k,
      (@finSumFinEquiv k pc.loopCount).symm (vEquiv (baseOf i)) = Sum.inl i := by
    intro i; simp [hvEquiv, hRhoBase i]
  have hVMark : ∀ j : Fin L,
      (@finSumFinEquiv k pc.loopCount).symm (vEquiv (markOf j)) = Sum.inr (markIndex j) := by
    intro j; simp [hvEquiv, hRhoMark j, hmarkIndex]
  set splitData : pc.SplitMetadata :=
    { markerBase := fun m => fmap (markIndex.symm m)
      splitCore := coreReindex spec.core vEquiv sEquiv } with hsplitData
  have hNpos : 0 < k + pc.loopCount := by
    have := spec.core_nonempty
    omega
  set spec' : Spec (k + pc.loopCount) pc.splitEdgeCount :=
    specReindex spec vEquiv sEquiv hNpos with hspec'
  refine ⟨k, pc, splitData, hSmall, hValid, ⟨?_, ?_, ?_⟩, spec', rfl, ?_⟩
  · -- marker multiplicities
    intro i
    show (Finset.univ.filter fun m : Fin pc.loopCount =>
      fmap (markIndex.symm m) = i).card = pc.loops i
    rw [hLoops i]
    have hImage : (Finset.univ.filter fun m : Fin pc.loopCount =>
        fmap (markIndex.symm m) = i)
        = (Finset.univ.filter fun j : Fin L => fmap j = i).map
          markIndex.toEmbedding := by
      ext m
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
        Equiv.toEmbedding_apply]
      constructor
      · intro h; exact ⟨markIndex.symm m, h, by simp⟩
      · rintro ⟨j, hj, rfl⟩; simpa using hj
    rw [hImage, Finset.card_map]
  · -- looplessness
    intro edge
    show vEquiv (spec.core.tail (sEquiv.symm edge))
      ≠ vEquiv (spec.core.head (sEquiv.symm edge))
    simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]
    exact spec.core_loopless _
  · -- the split multiplicity table
    intro first second
    obtain ⟨v, rfl⟩ := vEquiv.surjective first
    obtain ⟨w, rfl⟩ := vEquiv.surjective second
    have hRe : explicitCoreMultiplicity splitData.splitCore (vEquiv v) (vEquiv w)
        = explicitCoreMultiplicity spec.core v w :=
      explicitCoreMultiplicity_reindex spec.core vEquiv sEquiv v w
    rw [hRe]
    rcases hCases v with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · rcases hCases w with ⟨i', rfl⟩ | ⟨j', rfl⟩
      · unfold Pseudocore.SplitMetadata.expectedMultiplicity
        rw [hVBase i, hVBase i']
      · unfold Pseudocore.SplitMetadata.expectedMultiplicity
        rw [hVBase i, hVMark j', hBaseMark i j']
        simp [hsplitData]
    · rcases hCases w with ⟨i', rfl⟩ | ⟨j', rfl⟩
      · unfold Pseudocore.SplitMetadata.expectedMultiplicity
        rw [hVMark j, hVBase i', explicitCoreMultiplicity_symm, hBaseMark i' j]
        simp [hsplitData]
      · unfold Pseudocore.SplitMetadata.expectedMultiplicity
        rw [hVMark j, hVMark j']
        exact hMarkMark j j'
  · obtain ⟨equivalence⟩ := hG
    obtain ⟨reindex⟩ := laplacianEquiv_specReindex spec vEquiv sEquiv hNpos
    exact ⟨equivalence.trans reindex⟩

/-- The genus-four specialization of
`pseudocorePresentation_of_markedShapeAt`. -/
theorem pseudocorePresentation_of_markedShape {N P : ℕ} (spec : Spec N P)
    (shape : MarkedShape spec) (hConnected : graphConnected spec.graph)
    (hGenus : genus spec.graph = 4) {G : CFGraph.{0}}
    (hG : Nonempty (LaplacianEquiv G spec.graph)) :
    ∃ (k : ℕ) (core : Pseudocore k) (split : core.SplitMetadata),
      k ≤ 6 ∧ core.Valid ∧ PseudocoreSplitGlue.Compatible split ∧
      ∃ spec' : Spec (k + core.loopCount) core.splitEdgeCount,
        spec'.core = split.splitCore ∧ Nonempty (LaplacianEquiv G spec'.graph) := by
  simpa only [Nat.reduceSub, Nat.mul_one, Pseudocore.Valid] using
    pseudocorePresentation_of_markedShapeAt spec shape hConnected hGenus hG

/-- Every connected leafless graph of genus at least two is
Laplacian-equivalent to a positive subdivision of the loopless split of a
valid pseudocore on at most `2(g-1)` base vertices. -/
theorem pseudocorePresentation_of_leafless {g : ℕ} (G : CFGraph.{0})
    (hConnected : graphConnected G) (hGenus : genus G = g)
    (hGenusLower : 2 ≤ g)
    (hLeafless : ∀ vertex : G.V, vertexDegree G vertex ≠ 1) :
    ∃ (k : ℕ) (core : Pseudocore k) (split : core.SplitMetadata),
      k ≤ 2 * (g - 1) ∧ core.ValidAt g ∧
      PseudocoreSplitGlue.Compatible split ∧
      ∃ spec : Spec (k + core.loopCount) core.splitEdgeCount,
        spec.core = split.splitCore ∧
        Nonempty (LaplacianEquiv G spec.graph) := by
  classical
  have hDeg : ∀ vertex : G.V, 2 ≤ vertexDegree G vertex := by
    intro vertex
    have hCard : (G.edges.card : ℤ) = (Fintype.card G.V : ℤ) + (g : ℤ) - 1 := by
      simp only [genus] at hGenus
      omega
    have hVerticesPositive : 0 < Fintype.card G.V := Fintype.card_pos
    have hEdgesPositive : 0 < G.edges.card := by omega
    rw [Multiset.card_pos_iff_exists_mem] at hEdgesPositive
    obtain ⟨edge, hEdge⟩ := hEdgesPositive
    rcases edge with ⟨left, right⟩
    have hDistinct : left ≠ right := by
      intro hEqual
      subst right
      exact G.loopless left hEdge
    obtain ⟨other, hOther⟩ : ∃ other : G.V, other ≠ vertex := by
      by_cases hLeft : left = vertex
      · exact ⟨right, fun hRight => hDistinct (hLeft.trans hRight.symm)⟩
      · exact ⟨left, hLeft⟩
    obtain ⟨inside, hInside, outside, _hOutside, hCrossing⟩ :=
      hConnected ({vertex} : Finset G.V)
        ⟨vertex, other, by simp, by simpa [Ne.symm hOther]⟩
    have hInsideEq : inside = vertex := by simpa using hInside
    subst inside
    have hPositive : 0 < vertexDegree G vertex := by
      unfold vertexDegree
      apply Finset.sum_pos'
      · intro neighbour _hNeighbour
        positivity
      · exact ⟨outside, Finset.mem_univ outside, by exact_mod_cast hCrossing⟩
    have hNotOne := hLeafless vertex
    omega
  obtain ⟨N, P, spec, hPresent, hReduced⟩ :=
    exists_reduced (Fintype.card G.V) G.edges.card
      (UnitSubdivisionPresentation.spec G)
  obtain ⟨reduction⟩ := hPresent
  have equivalence : LaplacianEquiv G spec.graph :=
    (UnitSubdivisionPresentation.laplacianEquiv G).trans reduction
  have hSpecConnected : graphConnected spec.graph :=
    equivalence.graphConnected hConnected
  have hSpecGenus : genus spec.graph = g := by
    rw [equivalence.genus_eq, hGenus]
  have hSpecDegree : ∀ v : Fin N, 2 ≤ slotValence spec.core v := by
    intro v
    have hCast := slotValence_eq_vertex_degree spec v
    have hBack := equivalence.vertexDegree_eq
      (equivalence.toEquiv.symm (spec.coreVertex v))
    rw [Equiv.apply_symm_apply] at hBack
    have hGe := hDeg (equivalence.toEquiv.symm (spec.coreVertex v))
    rw [← hBack, ← hCast] at hGe
    exact_mod_cast hGe
  obtain ⟨shape⟩ :=
    exists_markedShapeAt spec hReduced hSpecConnected hSpecGenus
      (by omega : g ≠ 1) hSpecDegree
  exact pseudocorePresentation_of_markedShapeAt spec shape hSpecConnected
    hSpecGenus ⟨equivalence⟩

/-- Every connected leafless genus-five graph is Laplacian-equivalent to a
positive subdivision of the loopless split of a valid genus-five pseudocore
on at most eight vertices. -/
theorem pseudocorePresentation_genusFive (G : CFGraph.{0})
    (hConnected : graphConnected G) (hGenus : genus G = 5)
    (hLeafless : ∀ vertex : G.V, vertexDegree G vertex ≠ 1) :
    ∃ (k : ℕ) (core : Pseudocore k) (split : core.SplitMetadata),
      k ≤ 8 ∧ core.ValidAt 5 ∧ PseudocoreSplitGlue.Compatible split ∧
      ∃ spec : Spec (k + core.loopCount) core.splitEdgeCount,
        spec.core = split.splitCore ∧ Nonempty (LaplacianEquiv G spec.graph) := by
  classical
  have hDeg : ∀ vertex : G.V, 2 ≤ vertexDegree G vertex := by
    intro vertex
    have hCard : (G.edges.card : ℤ) = (Fintype.card G.V : ℤ) + 4 := by
      simp only [genus] at hGenus
      omega
    have hEdgesPositive : 0 < G.edges.card := by omega
    rw [Multiset.card_pos_iff_exists_mem] at hEdgesPositive
    obtain ⟨edge, hEdge⟩ := hEdgesPositive
    rcases edge with ⟨left, right⟩
    have hDistinct : left ≠ right := by
      intro hEqual
      subst right
      exact G.loopless left hEdge
    obtain ⟨other, hOther⟩ : ∃ other : G.V, other ≠ vertex := by
      by_cases hLeft : left = vertex
      · exact ⟨right, fun hRight => hDistinct (hLeft.trans hRight.symm)⟩
      · exact ⟨left, hLeft⟩
    obtain ⟨inside, hInside, outside, _hOutside, hCrossing⟩ :=
      hConnected ({vertex} : Finset G.V)
        ⟨vertex, other, by simp, by simpa [Ne.symm hOther]⟩
    have hInsideEq : inside = vertex := by simpa using hInside
    subst inside
    have hPositive : 0 < vertexDegree G vertex := by
      unfold vertexDegree
      apply Finset.sum_pos'
      · intro neighbour _hNeighbour
        positivity
      · exact ⟨outside, Finset.mem_univ outside, by exact_mod_cast hCrossing⟩
    have hNotOne := hLeafless vertex
    omega
  obtain ⟨N, P, spec, hPresent, hReduced⟩ :=
    exists_reduced (Fintype.card G.V) G.edges.card
      (UnitSubdivisionPresentation.spec G)
  obtain ⟨reduction⟩ := hPresent
  have equivalence : LaplacianEquiv G spec.graph :=
    (UnitSubdivisionPresentation.laplacianEquiv G).trans reduction
  have hSpecConnected : graphConnected spec.graph :=
    equivalence.graphConnected hConnected
  have hSpecGenus : genus spec.graph = 5 := by
    rw [equivalence.genus_eq, hGenus]
  have hSpecDegree : ∀ v : Fin N, 2 ≤ slotValence spec.core v := by
    intro v
    have hCast := slotValence_eq_vertex_degree spec v
    have hBack := equivalence.vertexDegree_eq
      (equivalence.toEquiv.symm (spec.coreVertex v))
    rw [Equiv.apply_symm_apply] at hBack
    have hGe := hDeg (equivalence.toEquiv.symm (spec.coreVertex v))
    rw [← hBack, ← hCast] at hGe
    exact_mod_cast hGe
  obtain ⟨shape⟩ :=
    exists_markedShapeAt spec hReduced hSpecConnected hSpecGenus (by norm_num) hSpecDegree
  simpa only [Nat.reduceSub, Nat.mul_one] using
    pseudocorePresentation_of_markedShapeAt spec shape hSpecConnected
      hSpecGenus ⟨equivalence⟩

end Utilities.Certificate.PseudocorePresentation
