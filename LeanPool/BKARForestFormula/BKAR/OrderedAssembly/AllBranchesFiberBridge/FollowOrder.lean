/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFibers

/-! # Following a prescribed order through the choice system

Defines `ChosenGrowth`, the ordered growth that follows exactly the active
extensions selected by a fixed `ActiveExtensionChoice`, and the partial
function `followOrder` attempting to realize a prescribed edge order as
such a growth.  Every chosen growth arises this way, giving the canonical
realization of a support/order fiber used by the fiber bridge.
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
An ordered growth that follows exactly the active extensions selected by a
fixed `ActiveExtensionChoice`.
-/
inductive ChosenGrowth (choices : ActiveExtensionChoice V) :
    Forest V → List (Edge V) → Forest V → Prop
  | nil (F : Forest V) : ChosenGrowth choices F [] F
  | cons {F G : Forest V} {e : Edge V} {order : List (Edge V)}
      (he : e ∈ F.activeEdges)
      (tail :
        ChosenGrowth choices (choices F ⟨e, he⟩).forest order G) :
      ChosenGrowth choices F (e :: order) G

namespace ChosenGrowth

variable {choices : ActiveExtensionChoice V}
variable {F G : Forest V} {order : List (Edge V)}

/-- Edge-set bookkeeping for a chosen growth path. -/
theorem edges_eq_toFinset_union
    (path : ChosenGrowth choices F order G) :
    G.edges = order.toFinset ∪ F.edges := by
  induction path with
  | nil F =>
      rw [List.toFinset_nil, Finset.empty_union]
  | cons he tail ih =>
      rw [ih, (choices _ ⟨_, he⟩).extension.edges_eq,
        List.toFinset_cons]
      ext x
      simp [or_comm]

/-- Root-start edge-set bookkeeping for a chosen growth path. -/
theorem support_edges_eq_toFinset_emptyStart
    (path : ChosenGrowth choices (Forest.empty V) order G) :
    G.support.edges = order.toFinset := by
  rw [Forest.support_edges, path.edges_eq_toFinset_union, Forest.empty_edges,
    Finset.union_empty]

end ChosenGrowth

/-- Follow an edge order through the active extensions selected by `choices`. -/
noncomputable def followOrder?
    (choices : ActiveExtensionChoice V) :
    Forest V → List (Edge V) → Option (Forest V)
  | F, [] => some F
  | F, e :: order =>
      if he : e ∈ F.activeEdges then
        followOrder? choices (choices F ⟨e, he⟩).forest order
      else
        none

theorem chosenGrowth_of_followOrder?_eq_some
    (choices : ActiveExtensionChoice V) :
    ∀ {F G : Forest V} {order : List (Edge V)},
      followOrder? choices F order = some G →
      ChosenGrowth choices F order G
  | F, G, [], h => by
      simp [followOrder?] at h
      rw [← h]
      exact ChosenGrowth.nil F
  | F, G, e :: order, h => by
      by_cases he : e ∈ F.activeEdges
      · simp [followOrder?, he] at h
        exact ChosenGrowth.cons he
          (chosenGrowth_of_followOrder?_eq_some choices h)
      · simp [followOrder?, he] at h

/--
Canonical orders of an acyclic target support can be followed through any
choice of active extensions. The invariant says that the current
`Forest` representative carries the already-consumed prefix, while `order` is the remaining
suffix and `S` is the final edge set.
-/
theorem exists_followOrder?_eq_some_of_acyclic_union
    (choices : ActiveExtensionChoice V) :
    ∀ {F : Forest V} {S : Finset (Edge V)} (order : List (Edge V)),
      IsAcyclicEdgeSet S →
      order.toFinset ∪ F.edges = S →
      order.Nodup →
      Disjoint order.toFinset F.edges →
      ∃ G : Forest V, followOrder? choices F order = some G ∧
        G.edges = S
  | F, S, [], _hS, hset, _hnodup, _hdisj => by
      refine ⟨F, ?_, ?_⟩
      · rfl
      · rw [List.toFinset_nil, Finset.empty_union] at hset
        exact hset
  | F, S, e :: tail, hS, hset, hnodup, hdisj => by
      have hnotMemTail : e ∉ tail := by
        exact (List.nodup_cons.mp hnodup).1
      have htailNodup : tail.Nodup := by
        exact (List.nodup_cons.mp hnodup).2
      have hnotMemF : e ∉ F.edges := by
        rw [List.toFinset_cons, Finset.disjoint_insert_left] at hdisj
        exact hdisj.1
      have htailDisjF : Disjoint tail.toFinset F.edges := by
        rw [List.toFinset_cons, Finset.disjoint_insert_left] at hdisj
        exact hdisj.2
      have hinsertSub : insert e F.edges ⊆ S := by
        intro x hx
        rw [← hset]
        rw [List.toFinset_cons]
        rw [Finset.mem_union]
        rw [Finset.mem_insert] at hx
        exact hx.elim
          (fun hx => Or.inl (by
            rw [hx]
            exact Finset.mem_insert_self e tail.toFinset))
          (fun hx => Or.inr hx)
      have hacyclicInsert : IsAcyclicEdgeSet (insert e F.edges) :=
        IsAcyclicEdgeSet.mono hS hinsertSub
      have he : e ∈ F.activeEdges :=
        F.mem_activeEdges_of_not_inSameComponent
          ((F.acyclic_insert_iff_edge hnotMemF).mp hacyclicInsert)
      let F' : Forest V := (choices F ⟨e, he⟩).forest
      have hchildSet : tail.toFinset ∪ F'.edges = S := by
        rw [show F'.edges = insert e F.edges by
          exact (choices F ⟨e, he⟩).extension.edges_eq]
        ext x
        rw [← hset]
        simp [List.toFinset_cons, or_comm]
      have hchildDisj : Disjoint tail.toFinset F'.edges := by
        rw [show F'.edges = insert e F.edges by
          exact (choices F ⟨e, he⟩).extension.edges_eq]
        rw [Finset.disjoint_left]
        intro x hxTail hxInsert
        rw [Finset.mem_insert] at hxInsert
        cases hxInsert with
        | inl hxe =>
            exact hnotMemTail (hxe ▸ List.mem_toFinset.mp hxTail)
        | inr hxF =>
            rw [Finset.disjoint_left] at htailDisjF
            exact htailDisjF hxTail hxF
      rcases exists_followOrder?_eq_some_of_acyclic_union choices tail
          hS hchildSet htailNodup hchildDisj with
        ⟨G, hfollow, hGedges⟩
      refine ⟨G, ?_, hGedges⟩
      simp [followOrder?, he]
      exact hfollow

/--
Every canonical order of a forest index follows to some `Forest` representative whose
support is exactly that index, independently of the extension choices.
-/
theorem exists_followOrder?_eq_some_support_of_mem_edgeSetOrders
    (choices : ActiveExtensionChoice V)
    {I : ForestIndex V} {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges) :
    ∃ G : Forest V,
      followOrder? choices (Forest.empty V) order = some G ∧
        G.support = I := by
  have hset : order.toFinset = I.edges :=
    toFinset_eq_of_mem_edgeSetOrders horder
  have hnodup : order.Nodup :=
    nodup_of_mem_edgeSetOrders horder
  have hunion :
      order.toFinset ∪ (Forest.empty V).edges = I.edges := by
    rw [Forest.empty_edges, Finset.union_empty, hset]
  have hdisj : Disjoint order.toFinset (Forest.empty V).edges := by
    rw [Forest.empty_edges]
    exact Finset.disjoint_empty_right order.toFinset
  rcases exists_followOrder?_eq_some_of_acyclic_union choices order
      I.acyclic hunion hnodup hdisj with
    ⟨G, hfollow, hGedges⟩
  refine ⟨G, hfollow, ?_⟩
  apply ForestIndex.ext
  rw [Forest.support_edges, hGedges]

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
