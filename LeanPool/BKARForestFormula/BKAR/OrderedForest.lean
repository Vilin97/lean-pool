/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedExpansion

/-! # Ordered forest growth certificates

Defines `OrderedGrowth F order G`, the certificate that the forest `G` is
obtained from `F` by adding the edges of the list `order` one at a time,
each step being a valid one-edge forest extension.  Provides accessors for
the first step and tail growth and the basic bookkeeping (edge sets,
cardinalities) used throughout the ordered expansion of the BKAR forest
interpolation formula (see `BKAR.Formula`).
-/

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
Certificate that `G` is obtained from `F` by adding the edges in `order`, one
at a time, with a valid one-edge forest extension at each step.
-/
inductive OrderedGrowth : Forest V → List (Edge V) → Forest V → Type _
  | nil (F : Forest V) : OrderedGrowth F [] F
  | cons {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
      (step : EdgeExtension F F' e)
      (tail : OrderedGrowth F' order G) :
      OrderedGrowth F (e :: order) G

namespace OrderedGrowth

variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

structure ConsData (F : Forest V) (e : Edge V) (order : List (Edge V))
    (G : Forest V) where
  forest : Forest V
  step : EdgeExtension F forest e
  tail : OrderedGrowth forest order G

/-- Decompose a nonempty ordered growth into its first step and tail growth. -/
def consData (h : OrderedGrowth F (e :: order) G) :
    ConsData F e order G := by
  cases h with
  | cons step tail =>
      exact ⟨_, step, tail⟩

/-- The intermediate forest after the first step of a nonempty ordered growth. -/
def tailForest (h : OrderedGrowth F (e :: order) G) : Forest V :=
  h.consData.forest

/-- The first one-edge extension in a nonempty ordered growth. -/
theorem firstStep (h : OrderedGrowth F (e :: order) G) :
    EdgeExtension F h.tailForest e :=
  h.consData.step

/-- The remaining ordered growth after the first step. -/
def tailGrowth (h : OrderedGrowth F (e :: order) G) :
    OrderedGrowth h.tailForest order G :=
  h.consData.tail

/-- The first edge of a nonempty ordered growth is active for the starting forest. -/
def firstActiveExtension (h : OrderedGrowth F (e :: order) G) :
    ActiveExtension F e :=
  ⟨h.tailForest, h.firstStep⟩

theorem first_mem_activeEdges (h : OrderedGrowth F (e :: order) G) :
    e ∈ F.activeEdges :=
  h.firstActiveExtension.mem_activeEdges

theorem first_not_mem_edges (h : OrderedGrowth F (e :: order) G) :
    e ∉ F.edges :=
  h.firstStep.new_not_mem

theorem tailForest_edges_eq (h : OrderedGrowth F (e :: order) G) :
    h.tailForest.edges = insert e F.edges :=
  h.firstStep.edges_eq

theorem tailForest_card_edges_eq (h : OrderedGrowth F (e :: order) G) :
    h.tailForest.edges.card = F.edges.card + 1 := by
  rw [h.tailForest_edges_eq]
  exact Finset.card_insert_of_notMem h.first_not_mem_edges

/-- Edge-set bookkeeping for an ordered growth certificate. -/
theorem edges_eq_toFinset_union (h : OrderedGrowth F order G) :
    G.edges = order.toFinset ∪ F.edges := by
  induction h with
  | nil F =>
      rw [List.toFinset_nil, Finset.empty_union]
  | cons step tail ih =>
      rw [ih, step.edges_eq, List.toFinset_cons]
      rw [Finset.union_insert, Finset.insert_union]

theorem tailGrowth_edges_eq_toFinset_union
    (h : OrderedGrowth F (e :: order) G) :
    G.edges = order.toFinset ∪ h.tailForest.edges :=
  h.tailGrowth.edges_eq_toFinset_union

/-- The finite forest index grown by an ordered growth. -/
def support (_h : OrderedGrowth F order G) : ForestIndex V :=
  G.support

theorem support_edges (h : OrderedGrowth F order G) :
    h.support.edges = G.edges :=
  rfl

theorem support_edges_eq_toFinset_union (h : OrderedGrowth F order G) :
    h.support.edges = order.toFinset ∪ F.edges :=
  h.edges_eq_toFinset_union

theorem order_toFinset_subset_edges (h : OrderedGrowth F order G) :
    order.toFinset ⊆ G.edges := by
  intro e he
  rw [h.edges_eq_toFinset_union]
  exact Finset.mem_union_left F.edges he

theorem initial_edges_subset_edges (h : OrderedGrowth F order G) :
    F.edges ⊆ G.edges := by
  intro e he
  rw [h.edges_eq_toFinset_union]
  exact Finset.mem_union_right order.toFinset he

theorem mem_edges_of_mem_order (h : OrderedGrowth F order G) {e : Edge V}
    (he : e ∈ order) :
    e ∈ G.edges :=
  h.order_toFinset_subset_edges (List.mem_toFinset.mpr he)

/-- The ordered-growth list is disjoint from the starting forest's edge set. -/
theorem order_toFinset_disjoint_initial_edges (h : OrderedGrowth F order G) :
    Disjoint order.toFinset F.edges := by
  induction h with
  | nil F =>
      rw [List.toFinset_nil]
      exact Finset.disjoint_empty_left F.edges
  | cons step tail ih =>
      rw [List.toFinset_cons, Finset.disjoint_insert_left]
      constructor
      · exact step.new_not_mem
      · rw [Finset.disjoint_left] at ih ⊢
        intro x hx hxF
        exact ih hx (by
          rw [step.edges_eq]
          exact Finset.mem_insert_of_mem hxF)

/-- An ordered-growth list never repeats an edge. -/
theorem order_nodup (h : OrderedGrowth F order G) :
    order.Nodup := by
  induction h with
  | nil F =>
      exact List.nodup_nil
  | cons step tail ih =>
      apply List.Nodup.cons
      · intro he
        have hdisj := tail.order_toFinset_disjoint_initial_edges
        rw [Finset.disjoint_left] at hdisj
        exact hdisj (List.mem_toFinset.mpr he) (by
          rw [step.edges_eq]
          exact Finset.mem_insert_self _ _)
      · exact ih

theorem order_toFinset_card_eq_length (h : OrderedGrowth F order G) :
    order.toFinset.card = order.length :=
  List.toFinset_card_of_nodup h.order_nodup

/-- The final forest has exactly `order.length` more edges than the start. -/
theorem card_edges_eq (h : OrderedGrowth F order G) :
    G.edges.card = F.edges.card + order.length := by
  induction h with
  | nil F =>
      rw [List.length_nil, Nat.add_zero]
  | cons step tail ih =>
      rw [ih, step.edges_eq, Finset.card_insert_of_notMem step.new_not_mem,
        List.length_cons]
      rw [Nat.add_assoc, Nat.add_comm 1]

theorem tailGrowth_card_edges_eq (h : OrderedGrowth F (e :: order) G) :
    G.edges.card = h.tailForest.edges.card + order.length :=
  h.tailGrowth.card_edges_eq

end OrderedGrowth

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
