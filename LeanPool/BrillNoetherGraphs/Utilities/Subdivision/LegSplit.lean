/-
Copyright (c) 2026 Nathan Pflueger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathan Pflueger
-/
module


public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.CubicCore
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionConnectivity
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.SubdivisionTwoEdgeCut
public import LeanPool.BrillNoetherGraphs.Utilities.Subdivision.OneEdgeSplitRefinement

/-!
# Legged cores: marked points as legs

The marked-moduli organization (`PHILOSOPHY.md` §1): a marked point is a
**leg** attached at its own vertex of the core, contributing one incidence
to valence.  The leg construction on the ordered-slot core is a one-slot
split — the same combinatorial move as
`OneEdgeSplitRefinement.splitCore`, restated here at the `Core` level so it
can be iterated (the second leg of a two-marked row lands on the once-legged
core) and consumed by the closed-orthant machinery, which never sees a
`Spec`.

`MarkedCore` packages a core with distinguished marked vertices, and
`LegStable` is the maximal-cone condition of `M_{g,n}^trop`: marked vertices
are exactly bivalent in the edge graph (their leg supplies the third
incidence) and every other vertex is exactly trivalent.
-/

@[expose] public section

namespace Utilities.Certificate.ExplicitPotential

namespace Core

variable {n p : ℕ}

/-- The leg construction: split `slot` through a fresh last vertex.  The old
slot keeps the tail and is redirected into the fresh vertex; the fresh last
slot runs from the fresh vertex to the old head.  Definitionally the core of
`OneEdgeSplitRefinement.splitCore` (see `legSplit_eq_splitCore`). -/
def legSplit (core : Core n p) (slot : Fin p) : Core (n + 1) (p + 1) where
  tail := Fin.lastCases (Fin.last n) (fun edge => (core.tail edge).castSucc)
  head := Fin.lastCases ((core.head slot).castSucc)
    (fun edge => if edge = slot then Fin.last n
      else (core.head edge).castSucc)

/-- The fresh vertex carrying the leg. -/
def legVertexOf (_core : Core n p) : Fin (n + 1) := Fin.last n

@[simp] theorem legSplit_tail_old (core : Core n p) (slot edge : Fin p) :
    (core.legSplit slot).tail edge.castSucc = (core.tail edge).castSucc := by
  simp [legSplit]

@[simp] theorem legSplit_tail_last (core : Core n p) (slot : Fin p) :
    (core.legSplit slot).tail (Fin.last p) = Fin.last n := by
  simp [legSplit]

@[simp] theorem legSplit_head_old (core : Core n p) (slot edge : Fin p) :
    (core.legSplit slot).head edge.castSucc =
      if edge = slot then Fin.last n else (core.head edge).castSucc := by
  simp [legSplit]

@[simp] theorem legSplit_head_last (core : Core n p) (slot : Fin p) :
    (core.legSplit slot).head (Fin.last p) = (core.head slot).castSucc := by
  simp [legSplit]

/-- The leg construction agrees with the one-slot split refinement's core. -/
theorem legSplit_eq_splitCore {n p : ℕ}
    (source : SubdivisionGraph.Spec n p) (slot : Fin p) :
    OneEdgeSplitRefinement.splitCore source slot = source.core.legSplit slot :=
  rfl

/-- Splitting preserves looplessness. -/
theorem legSplit_loopless (core : Core n p) (slot : Fin p)
    (hLoopless : ∀ edge : Fin p, core.tail edge ≠ core.head edge) :
    ∀ edge : Fin (p + 1),
      (core.legSplit slot).tail edge ≠ (core.legSplit slot).head edge := by
  intro edge
  refine Fin.lastCases ?_ ?_ edge
  · simp only [legSplit_tail_last, legSplit_head_last]
    exact fun h => absurd h.symm (Fin.castSucc_lt_last (core.head slot)).ne
  · intro old
    simp only [legSplit_tail_old, legSplit_head_old]
    by_cases hslot : old = slot
    · subst hslot
      simp only [ite_eq_left]
      exact (Fin.castSucc_lt_last (core.tail old)).ne
    · simp only [ite_eq_right hslot]
      exact fun h => hLoopless old (Fin.castSucc_injective n h)

/-- Splitting preserves cut connectedness. -/
theorem legSplit_connected (core : Core n p) (slot : Fin p)
    (hConnected : core.Connected) : (core.legSplit slot).Connected := by
  intro S hSplitSet
  obtain ⟨v, w, hv, hw⟩ := hSplitSet
  by_cases hProper : ∃ a b : Fin n, a.castSucc ∈ S ∧ b.castSucc ∉ S
  · -- the old vertices already separate: use the base crossing edge
    obtain ⟨a, b, ha, hb⟩ := hProper
    obtain ⟨edge, hEdge⟩ := hConnected {v : Fin n | v.castSucc ∈ S}.toFinset
      ⟨a, b, by simpa using ha, by simpa using hb⟩
    simp only [Set.mem_toFinset, Set.mem_ofPred_eq] at hEdge
    by_cases hslot : edge = slot
    · subst hslot
      -- the split slot crosses; route through the leg vertex on the correct side
      by_cases hLeg : (Fin.last n : Fin (n + 1)) ∈ S
      · rcases hEdge with ⟨hT, hH⟩ | ⟨hH, hT⟩
        · exact ⟨Fin.last p, Or.inl (by simpa using ⟨hLeg, hH⟩)⟩
        · exact ⟨edge.castSucc, Or.inr (by simpa using ⟨hLeg, hT⟩)⟩
      · rcases hEdge with ⟨hT, hH⟩ | ⟨hH, hT⟩
        · exact ⟨edge.castSucc, Or.inl (by simpa using ⟨hT, hLeg⟩)⟩
        · exact ⟨Fin.last p, Or.inr (by simpa using ⟨hH, hLeg⟩)⟩
    · rcases hEdge with ⟨hT, hH⟩ | ⟨hH, hT⟩
      · exact ⟨edge.castSucc, Or.inl (by simpa [hslot] using ⟨hT, hH⟩)⟩
      · exact ⟨edge.castSucc, Or.inr (by simpa [hslot] using ⟨hH, hT⟩)⟩
  · -- all old vertices sit on one side; the leg vertex is the lone dissident
    by_cases hAll : ∀ a : Fin n, a.castSucc ∈ S
    · -- every old vertex inside, so the outside vertex is the leg vertex
      have hwLast : w = Fin.last n := by
        rcases Fin.eq_castSucc_or_eq_last w with ⟨b, rfl⟩ | rfl
        · exact absurd (hAll b) hw
        · rfl
      refine ⟨slot.castSucc, Or.inl ⟨?_, ?_⟩⟩
      · simpa using hAll (core.tail slot)
      · simpa using hwLast ▸ hw
    · -- some old vertex outside, hence every old vertex outside (else
      -- `hProper` would produce a mixed pair); the inside vertex is the leg
      have hNone : ∀ a : Fin n, a.castSucc ∉ S := by
        intro a ha
        rcases not_forall.mp hAll with ⟨b, hb⟩
        exact hProper ⟨a, b, ha, hb⟩
      have hvLast : v = Fin.last n := by
        rcases Fin.eq_castSucc_or_eq_last v with ⟨a, rfl⟩ | rfl
        · exact absurd hv (hNone a)
        · rfl
      refine ⟨slot.castSucc, Or.inr ⟨?_, ?_⟩⟩
      · simpa using hvLast ▸ hv
      · simpa using hNone (core.tail slot)

end Core

/-- A core with distinguished marked vertices — the combinatorial datum of a
marked tropical curve.  `k` is the number of marked points; each mark is a
leg attached at `marks i`. -/
structure MarkedCore (n p k : ℕ) where
  /-- The finite edge core to which the marked legs are attached. -/
  core : Core n p
  /-- The core vertex carrying each marked leg; injectivity and valence conditions are imposed
  by `LegStable`. -/
  marks : Fin k → Fin n

namespace MarkedCore

variable {n p k : ℕ}

/-- Maximal-cone stability: marks are pairwise distinct, marked vertices are
exactly bivalent in the edge graph (the leg is the third incidence), and
every unmarked vertex is exactly trivalent. -/
def LegStable (C : MarkedCore n p k) : Prop :=
  Function.Injective C.marks ∧
    (∀ i : Fin k, C.core.incidenceDegree (C.marks i) = 2) ∧
    (∀ v : Fin n, (∀ i : Fin k, C.marks i ≠ v) → C.core.incidenceDegree v = 3)

/-- Exact Boolean check for `LegStable`. -/
def legStableCheck (C : MarkedCore n p k) : Bool :=
  decide (Function.Injective C.marks) &&
    decide (∀ i : Fin k, C.core.incidenceDegree (C.marks i) = 2) &&
    decide (∀ v : Fin n, (∀ i : Fin k, C.marks i ≠ v) →
      C.core.incidenceDegree v = 3)

@[simp] theorem legStableCheck_eq_true_iff (C : MarkedCore n p k) :
    C.legStableCheck = true ↔ C.LegStable := by
  simp [legStableCheck, LegStable, and_assoc]

end MarkedCore

end Utilities.Certificate.ExplicitPotential
