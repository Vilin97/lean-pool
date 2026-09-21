/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.Core

/-! # The fiber bridge: order sums and low-rank cases

Sums the fiber bridge over all orders of a fixed support: the summed root
fiber contribution equals the ordered contribution of the grown forest
when `followOrder` succeeds and vanishes otherwise, with the empty,
singleton, and pair supports worked out explicitly.
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The empty order contributes only to the empty support. -/
theorem rootBoundarySupportOrderContribution_nil_eq_zero_of_edges_ne_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V)
    (hI : I.edges ≠ ∅) :
    rootBoundarySupportOrderContribution choices ρ I [] = 0 := by
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
    choices ρ I [] hI]
  exact boundarySupportOrderTreeFiber_empty_order_eq_zero choices I ρ

/-- The empty support sector sums to the ordered contribution of the empty forest. -/
theorem sum_rootBoundarySupportOrderContribution_nil
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I []) =
      (Forest.empty V).orderedContribution [] ρ := by
  classical
  let I0 : ForestIndex V := (Forest.empty V).support
  have hI0edges : I0.edges = ∅ := rfl
  rw [Finset.sum_eq_single_of_mem I0 (Finset.mem_univ I0)]
  · exact
      rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
        choices ρ I0 hI0edges
  · intro I _ hne
    have hIedges : I.edges ≠ ∅ := by
      intro hempty
      apply hne
      apply ForestIndex.ext
      rw [hempty, hI0edges]
    exact
      rootBoundarySupportOrderContribution_nil_eq_zero_of_edges_ne_empty
        choices ρ I hIedges

/--
For any chosen root growth path, summing the fixed order over all support
indices leaves exactly the ordered contribution of the path's terminal forest.
-/
theorem sum_rootBoundarySupportOrderContribution_chosenGrowth
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (path : ChosenGrowth choices (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I order) =
      G.orderedContribution order ρ := by
  classical
  by_cases horder : order = []
  · subst order
    cases path with
    | nil F =>
        exact sum_rootBoundarySupportOrderContribution_nil choices ρ
  · have hsupport : order.toFinset = G.support.edges := by
      rw [ChosenGrowth.support_edges_eq_toFinset_emptyStart path]
    rw [Finset.sum_eq_single_of_mem G.support (Finset.mem_univ G.support)]
    · exact
        rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
          choices path ρ horder
    · intro I _ hne
      exact
        rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges
          choices ρ I order (by
            intro hI
            apply hne
            apply ForestIndex.ext
            rw [← hI, hsupport])

/--
Deterministic finite-order form of the chosen-growth bridge: if following an
order through the selected active extensions reaches `G`, the support-summed
root fiber is exactly the ordered sector of `G` with that order.
-/
theorem sum_rootContribution_eq_orderedContribution_of_followOrder_eq_some
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (hG : followOrderOption choices (Forest.empty V) order = some G)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I order) =
      G.orderedContribution order ρ :=
  sum_rootBoundarySupportOrderContribution_chosenGrowth choices
    (chosenGrowth_of_followOrderOption_eq_some choices hG) ρ

/--
Complementary deterministic finite-order form: if the selected extensions
cannot follow the requested root order, then that fixed order has zero total
root fiber after summing over supports.
-/
theorem sum_rootBoundarySupportOrderContribution_eq_zero_of_followOrder_eq_none
    (choices : ActiveExtensionChoice V)
    {order : List (Edge V)}
    (horder : followOrderOption choices (Forest.empty V) order = none)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I order) =
      0 := by
  classical
  cases order with
  | nil =>
      simp [followOrderOption] at horder
  | cons e tail =>
      apply Finset.sum_eq_zero
      intro I _
      rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
        choices ρ I (e :: tail) (by
          intro hmarker
          cases hmarker.2)]
      exact
        boundarySupportOrderTreeFiber_eq_zero_of_followOrder_eq_none
          choices (e :: tail) (Forest.empty V) [] [] 1 I ρ horder

/--
For a canonical support order, the root fiber is an ordered sector of the
`Forest` representative grown by following that order. This isolates the only remaining
choice dependence in the sector integrand: the grown `Forest` representative data.
-/
theorem exists_rootContribution_eq_orderedContribution_of_mem_edgeSetOrders
    (choices : ActiveExtensionChoice V)
    {I : ForestIndex V} {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    ∃ G : Forest V, G.support = I ∧
      rootBoundarySupportOrderContribution choices ρ I order =
        G.orderedContribution order ρ := by
  cases order with
  | nil =>
      have hI : I.edges = ∅ := by
        have hset : ([] : List (Edge V)).toFinset = I.edges :=
          toFinset_eq_of_mem_edgeSetOrders horder
        rw [List.toFinset_nil] at hset
        exact hset.symm
      refine ⟨Forest.empty V, ?_, ?_⟩
      · apply ForestIndex.ext
        rw [Forest.support_edges, Forest.empty_edges, hI]
      · exact
          rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
            choices ρ I hI
  | cons e tail =>
      rcases exists_followOrderOption_eq_some_support_of_mem_edgeSetOrders
          choices horder with
        ⟨G, hfollow, hsupport⟩
      refine ⟨G, hsupport, ?_⟩
      rw [← hsupport]
      exact
        rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
          choices hfollow ρ (by simp)

/--
After summing over all support indices, a canonical order leaves the ordered
sector of the `Forest` representative grown by following that order.
-/
theorem exists_sum_rootContribution_eq_orderedContribution_of_mem_edgeSetOrders
    (choices : ActiveExtensionChoice V)
    {I : ForestIndex V} {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    ∃ G : Forest V, G.support = I ∧
      Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun J => rootBoundarySupportOrderContribution choices ρ J order) =
        G.orderedContribution order ρ := by
  rcases exists_followOrderOption_eq_some_support_of_mem_edgeSetOrders
      choices horder with
    ⟨G, hfollow, hsupport⟩
  refine ⟨G, hsupport, ?_⟩
  exact
    sum_rootContribution_eq_orderedContribution_of_followOrder_eq_some
      choices hfollow ρ

/-- The empty support inner sum is the empty forest ordered contribution. -/
theorem sum_rootBoundarySupportOrderContribution_emptySupport
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (edgeSetOrders (Forest.empty V).support.edges)
        (fun order =>
          rootBoundarySupportOrderContribution choices ρ
            (Forest.empty V).support order) =
      (Forest.empty V).orderedContribution [] ρ := by
  rw [show (Forest.empty V).support.edges = (∅ : Finset (Edge V)) by rfl]
  rw [edgeSetOrders_empty, Finset.sum_singleton]
  exact
    rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
      choices ρ (Forest.empty V).support rfl

/-- A singleton order contributes only over the matching singleton support. -/
theorem rootBoundarySupportOrderContribution_singleton_eq_zero_of_edges_ne_singleton
    (choices : ActiveExtensionChoice V)
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V)
    (hI : I.edges ≠ ({a} : Finset (Edge V))) :
    rootBoundarySupportOrderContribution choices ρ I [a] = 0 := by
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
    choices ρ I [a] (by
      intro hmarker
      cases hmarker.2)]
  rw [boundarySupportOrderTreeFiber_empty_singleton_eq_localBoundary]
  rw [localBoundarySupportOrderContribution_def]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ he
    apply hI
    have horder : e.val = a := by
      have horder' := he.2
      simp only [List.nil_append] at horder'
      injection horder'
    rw [← he.1]
    rw [activeExtension_forest_support_eq_singleton_empty
      (choices (Forest.empty V) e)]
    rw [ForestIndex.singleton_edges, horder]

/--
Summing a fixed singleton order over all support indices leaves exactly the
matching one-edge ordered contribution.
-/
theorem sum_rootBoundarySupportOrderContribution_singleton
    (choices : ActiveExtensionChoice V)
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I [a]) =
      (choices (Forest.empty V) (emptyActiveEdge a)).forest.orderedContribution
        [a] ρ := by
  classical
  rw [Finset.sum_eq_single_of_mem (ForestIndex.singleton a)
    (Finset.mem_univ (ForestIndex.singleton a))]
  · exact rootBoundarySupportOrderContribution_singleton_eq_orderedContribution
      choices a ρ
  · intro I _ hne
    exact
      rootBoundarySupportOrderContribution_singleton_eq_zero_of_edges_ne_singleton
        choices a ρ I (by
          intro hIedges
          apply hne
          apply ForestIndex.ext
          rw [hIedges, ForestIndex.singleton_edges])

/--
The singleton support inner sum has already collapsed to the unique singleton
order and is the matching one-edge ordered contribution.
-/
theorem sum_rootBoundarySupportOrderContribution_singletonSupport
    (choices : ActiveExtensionChoice V)
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (edgeSetOrders (ForestIndex.singleton a : ForestIndex V).edges)
        (fun order =>
          rootBoundarySupportOrderContribution choices ρ
            (ForestIndex.singleton a) order) =
      (choices (Forest.empty V) (emptyActiveEdge a)).forest.orderedContribution
        [a] ρ := by
  rw [ForestIndex.singleton_edges, edgeSetOrders_singleton]
  rw [Finset.sum_singleton]
  exact rootBoundarySupportOrderContribution_singleton_eq_orderedContribution
    choices a ρ

/--
The length-two root fiber follows the chosen first edge, then the chosen
second edge, and is exactly the corresponding ordered contribution.
-/
theorem rootBoundarySupportOrderContribution_pair_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    (a b : Edge V) (ρ : (Edge V → ℝ) → ℝ)
    (hb :
      b ∈ (choices (Forest.empty V) (emptyActiveEdge a)).forest.activeEdges) :
    rootBoundarySupportOrderContribution choices ρ
        ((choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
          ⟨b, hb⟩).forest.support) [a, b] =
      (choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
        ⟨b, hb⟩).forest.orderedContribution [a, b] ρ := by
  let F₁ : Forest V :=
    (choices (Forest.empty V) (emptyActiveEdge a)).forest
  let e₂ : {e // e ∈ F₁.activeEdges} := ⟨b, hb⟩
  let F₂ : Forest V := (choices F₁ e₂).forest
  change
    rootBoundarySupportOrderContribution choices ρ F₂.support [a, b] =
      F₂.orderedContribution [a, b] ρ
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
    choices ρ F₂.support [a, b] (by
      intro hmarker
      cases hmarker.2)]
  have heqEmpty :
      (⟨a, (emptyActiveEdge a).property⟩ :
        {e // e ∈ (Forest.empty V).activeEdges}) =
        emptyActiveEdge a := by
    apply Subtype.ext
    rfl
  rw [show
      boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
          F₂.support [a, b] ρ =
        ∫ t in 0..(1 : ℝ),
          boundarySupportOrderTreeFiber choices
            (choices (Forest.empty V)
              ⟨a, (emptyActiveEdge a).property⟩).forest
            ([] ++ [a]) ([] ++ [t]) t F₂.support [a, b] ρ by
    exact
      boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
        choices (Forest.empty V) [] [] 1 F₂.support a [b] ρ
        (emptyActiveEdge a).property (by simp)]
  rw [heqEmpty]
  rw [orderedContribution, orderedSimplexIntegral]
  apply intervalIntegral.integral_congr
  intro t _ht
  change
    boundarySupportOrderTreeFiber choices
        (choices (Forest.empty V) (emptyActiveEdge a)).forest
        ([] ++ [a]) ([] ++ [t]) t F₂.support [a, b] ρ = _
  rw [show
      boundarySupportOrderTreeFiber choices
          (choices (Forest.empty V) (emptyActiveEdge a)).forest
          ([] ++ [a]) ([] ++ [t]) t F₂.support [a, b] ρ =
        localBoundarySupportOrderContribution choices F₁ [a] [t] t
          F₂.support [a, b] ρ by
    change boundarySupportOrderTreeFiber choices F₁ [a] [t] t F₂.support
        [a, b] ρ =
      localBoundarySupportOrderContribution choices F₁ [a] [t] t
        F₂.support [a, b] ρ
    exact
      boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
        choices F₁ [a] [t] t F₂.support [a, b] ρ (by simp)]
  rw [localBoundarySupportOrderContribution_def]
  have hfilter :
      F₁.activeEdges.attach.filter
          (fun e =>
            (choices F₁ e).forest.support = F₂.support ∧
              [a] ++ [e.val] = [a, b]) =
        {e₂} := by
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      exact Subtype.ext (by
        have horder := h.2.2
        have htail : [e.val] = [b] := (List.cons.inj horder).2
        exact (List.cons.inj htail).1)
    · intro h
      rw [h]
      constructor
      · exact Finset.mem_attach _ _
      · constructor
        · rfl
        · simp [e₂]
  rw [hfilter, Finset.sum_singleton]
  simp only [e₂, F₂, List.singleton_append]

/--
After summing over all support indices, a fixed active two-edge order leaves
only the support grown by the corresponding two chosen extensions.
-/
theorem sum_rootBoundarySupportOrderContribution_pair
    (choices : ActiveExtensionChoice V)
    (a b : Edge V) (ρ : (Edge V → ℝ) → ℝ)
    (hb :
      b ∈ (choices (Forest.empty V) (emptyActiveEdge a)).forest.activeEdges) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I [a, b]) =
      (choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
        ⟨b, hb⟩).forest.orderedContribution [a, b] ρ := by
  classical
  let F₁ : Forest V :=
    (choices (Forest.empty V) (emptyActiveEdge a)).forest
  let e₂ : {e // e ∈ F₁.activeEdges} := ⟨b, hb⟩
  let F₂ : Forest V := (choices F₁ e₂).forest
  have hF₁edges : F₁.edges = ({a} : Finset (Edge V)) := by
    change (choices (Forest.empty V) (emptyActiveEdge a)).forest.edges =
      ({a} : Finset (Edge V))
    rw [(choices (Forest.empty V) (emptyActiveEdge a)).extension.edges_eq,
      Forest.empty_edges]
    rfl
  have hF₂edges : [a, b].toFinset = F₂.support.edges := by
    change [a, b].toFinset = F₂.edges
    rw [show F₂.edges = insert b F₁.edges by
      exact (choices F₁ e₂).extension.edges_eq]
    rw [hF₁edges]
    ext x
    simp [or_comm]
  rw [Finset.sum_eq_single_of_mem F₂.support (Finset.mem_univ F₂.support)]
  · change
      rootBoundarySupportOrderContribution choices ρ
          ((choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
            ⟨b, hb⟩).forest.support) [a, b] =
        (choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
          ⟨b, hb⟩).forest.orderedContribution [a, b] ρ
    exact rootBoundarySupportOrderContribution_pair_eq_orderedContribution
      choices a b ρ hb
  · intro I _ hne
    exact
      rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges
        choices ρ I [a, b] (by
          intro hI
          apply hne
          apply ForestIndex.ext
          rw [← hI, hF₂edges])


end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
