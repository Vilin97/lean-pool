/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge

/-! # Canonical forests realizing a support

For each forest index and each enumeration of its edge set, defines the
forest grown by following that order through a fixed active-extension
choice system (`grownForestForSupportOrder`), and the canonical
representative `canonicalGrownForestForSupport` obtained from the
canonical order of the support.  Both carry the support as their edge set,
so every abstract forest index acquires a concrete forest realizing it.
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace ForestIndex

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The canonical list order of a forest index, obtained from the finite edge-set
enumeration. This is a definite support representative; later sector sums may
still range over all permutations of the same support.
-/
def canonicalOrder (I : ForestIndex V) :
    {order : List (Edge V) // order ∈ Forest.edgeSetOrders I.edges} :=
  ⟨I.edges.toList,
    (Forest.mem_edgeSetOrders_iff I.edges).mpr (List.Perm.refl _)⟩

@[simp]
theorem canonicalOrder_val (I : ForestIndex V) :
    I.canonicalOrder.val = I.edges.toList :=
  rfl

end ForestIndex

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The `Forest` representative grown by following a canonical order of a forest index from
the empty forest through the selected active-extension choices.
-/
def grownForestForSupportOrder
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    Forest V :=
  Classical.choose
    (exists_followOrderOption_eq_some_support_of_mem_edgeSetOrders
      choices order.property)

theorem followOrderOption_grownForestForSupportOrder
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    followOrderOption choices (Forest.empty V) order.val =
      some (grownForestForSupportOrder choices I order) :=
  (Classical.choose_spec
    (exists_followOrderOption_eq_some_support_of_mem_edgeSetOrders
      choices order.property)).1

theorem grownForestForSupportOrder_support
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    (grownForestForSupportOrder choices I order).support = I :=
  (Classical.choose_spec
    (exists_followOrderOption_eq_some_support_of_mem_edgeSetOrders
      choices order.property)).2

theorem grownForestForSupportOrder_edges
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    (grownForestForSupportOrder choices I order).edges = I.edges := by
  rw [← Forest.support_edges (grownForestForSupportOrder choices I order)]
  exact congr_arg ForestIndex.edges
    (grownForestForSupportOrder_support choices I order)

theorem grownForestForSupportOrder_order_mem_edgeOrders
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges}) :
    order.val ∈ (grownForestForSupportOrder choices I order).edgeOrders := by
  rw [mem_edgeOrders_iff_toFinset_eq_and_nodup]
  constructor
  · rw [toFinset_eq_of_mem_edgeSetOrders order.property,
      grownForestForSupportOrder_edges choices I order]
  · exact nodup_of_mem_edgeSetOrders order.property

/--
The `Forest` representative grown through the canonical order of the support. This is a
fixed representative for the support once an active-extension choice system is
fixed.
-/
def canonicalGrownForestForSupport
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    Forest V :=
  grownForestForSupportOrder choices I I.canonicalOrder

theorem canonicalGrownForestForSupport_support
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    (canonicalGrownForestForSupport choices I).support = I :=
  grownForestForSupportOrder_support choices I I.canonicalOrder

theorem canonicalGrownForestForSupport_edges
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    (canonicalGrownForestForSupport choices I).edges = I.edges :=
  grownForestForSupportOrder_edges choices I I.canonicalOrder

theorem canonicalGrownForestForSupport_order_mem_edgeOrders
    (choices : ActiveExtensionChoice V) (I : ForestIndex V)
    {order : List (Edge V)} (horder : order ∈ edgeSetOrders I.edges) :
    order ∈ (canonicalGrownForestForSupport choices I).edgeOrders := by
  rw [mem_edgeOrders_iff_toFinset_eq_and_nodup]
  constructor
  · rw [toFinset_eq_of_mem_edgeSetOrders horder,
      canonicalGrownForestForSupport_edges choices I]
  · exact nodup_of_mem_edgeSetOrders horder

theorem canonicalGrownForestForSupport_edgeOrders
    (choices : ActiveExtensionChoice V) (I : ForestIndex V) :
    (canonicalGrownForestForSupport choices I).edgeOrders =
      edgeSetOrders I.edges := by
  ext order
  rw [mem_edgeOrders_iff_toFinset_eq_and_nodup,
    mem_edgeSetOrders_iff_toFinset_eq_and_nodup,
    canonicalGrownForestForSupport_edges choices I]

/--
Canonical-representative bridge for one support/order sector: the root support fiber is
the ordered contribution of the `Forest` representative grown by following that order.
-/
theorem rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V)
    (order : {order : List (Edge V) // order ∈ edgeSetOrders I.edges})
    (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ I order.val =
      (grownForestForSupportOrder choices I order).orderedContribution
        order.val ρ := by
  cases horderList : order.val with
  | nil =>
      have hI : I.edges = ∅ := by
        have hset : ([] : List (Edge V)).toFinset = I.edges := by
          simpa [horderList] using
            toFinset_eq_of_mem_edgeSetOrders order.property
        simpa using hset.symm
      have hgrown :
          grownForestForSupportOrder choices I order = Forest.empty V := by
        have hfollow :=
          followOrderOption_grownForestForSupportOrder choices I order
        simp [followOrderOption, horderList] at hfollow
        exact hfollow.symm
      rw [hgrown]
      exact rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
        choices ρ I hI
  | cons e tail =>
      have hsupport :
          (grownForestForSupportOrder choices I order).support = I :=
        grownForestForSupportOrder_support choices I order
      have hroot :=
        rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
          choices
          (followOrderOption_grownForestForSupportOrder choices I order)
          ρ
          (by
            rw [horderList]
            simp)
      simpa [horderList, hsupport] using hroot

theorem rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder_of_mem
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ I order =
      (grownForestForSupportOrder choices I ⟨order, horder⟩).orderedContribution
        order ρ :=
  rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
    choices I ⟨order, horder⟩ ρ

theorem sum_rootBoundarySupportOrderContribution_eq_sum_grownForestForSupportOrder
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          rootBoundarySupportOrderContribution choices ρ I order) =
      Finset.sum (edgeSetOrders I.edges).attach
        (fun order =>
          (grownForestForSupportOrder choices I order).orderedContribution
            order.val ρ) := by
  rw [← (edgeSetOrders I.edges).sum_attach
    (fun order => rootBoundarySupportOrderContribution choices ρ I order)]
  apply Finset.sum_congr rfl
  intro order _
  exact
    rootBoundarySupportOrderContribution_eq_grownForestForSupportOrder
      choices I order ρ

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
