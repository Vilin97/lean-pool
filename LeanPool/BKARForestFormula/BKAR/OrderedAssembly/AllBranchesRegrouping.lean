/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranches

/-! # Regrouping the all-branches expansion by support and order

Regroups one level of the all-branches expansion by the support grown and
the order followed: defines the local boundary support and support/order
contributions and proves the finite regrouping identities expressing the
expansion's boundary terms as sums over supports and their enumerating
orders.
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A one-edge active extension from the empty forest has singleton support. -/
theorem activeExtension_forest_support_eq_singleton_empty
    {e : Edge V} (h : ActiveExtension (Forest.empty V) e) :
    h.forest.support = ForestIndex.singleton e := by
  apply ForestIndex.ext
  rw [Forest.support_edges, ForestIndex.singleton_edges, h.extension.edges_eq,
    Forest.empty_edges]
  rfl

/--
The singleton order attached to an empty-start active extension is canonical in
any support fiber containing that extension.
-/
theorem activeExtension_singleton_order_mem_edgeSetOrders_of_support_eq_empty
    {e : Edge V} (h : ActiveExtension (Forest.empty V) e)
    {I : ForestIndex V} (hsupport : h.forest.support = I) :
    [e] ∈ edgeSetOrders I.edges := by
  rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
  constructor
  · rw [List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    rw [← ForestIndex.singleton_edges e]
    rw [← activeExtension_forest_support_eq_singleton_empty h, hsupport]
  · exact List.nodup_singleton e

/--
At an arbitrary recursion node, appending the chosen active edge to an existing
canonical prefix gives a canonical order of the child support.
-/
theorem activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
    {F : Forest V} {e : Edge V} (h : ActiveExtension F e)
    {pref : List (Edge V)} (hpref : pref.toFinset = F.edges)
    (hnodup : pref.Nodup)
    {I : ForestIndex V} (hsupport : h.forest.support = I) :
    pref ++ [e] ∈ edgeSetOrders I.edges := by
  rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
  constructor
  · have hset : (pref ++ [e]).toFinset = h.forest.edges := by
      rw [List.toFinset_append, h.extension.edges_eq, hpref]
      simp
    rw [hset, ← Forest.support_edges h.forest, hsupport]
  · rw [List.nodup_append]
    refine ⟨hnodup, List.nodup_singleton e, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst b
    subst a
    have he_mem : e ∈ F.edges := by
      rw [← hpref]
      exact List.mem_toFinset.mpr ha
    exact h.extension.new_not_mem he_mem

/--
Local active-boundary sectors from a recursion node whose child forest has a
fixed support.
-/
noncomputable def localBoundarySupportContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      (F.activeEdges.attach.filter
        (fun e => (choices F e).forest.support = I))
      (fun e =>
        orderedSimplexIntegralAux top [e.val]
          (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ ts)))))

theorem localBoundarySupportContribution_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportContribution choices F pref prefixTs top I ρ =
      Finset.sum
        (F.activeEdges.attach.filter
          (fun e => (choices F e).forest.support = I))
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ ts))))) := by
  rw [localBoundarySupportContribution]

/--
Local active-boundary sectors from a recursion node with fixed child support
and fixed canonical order.
-/
noncomputable def localBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      (F.activeEdges.attach.filter
        (fun e =>
          (choices F e).forest.support = I ∧
            pref ++ [e.val] = order))
      (fun e =>
        orderedSimplexIntegralAux top [e.val]
          (fun ts => mixedPartialList order.reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder order (prefixTs ++ ts)))))

theorem localBoundarySupportOrderContribution_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportOrderContribution choices F pref prefixTs top I order ρ =
      Finset.sum
        (F.activeEdges.attach.filter
          (fun e =>
            (choices F e).forest.support = I ∧
              pref ++ [e.val] = order))
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList order.reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder order
                  (prefixTs ++ ts))))) := by
  rw [localBoundarySupportOrderContribution]

/--
A local support/order boundary sector can contribute only when the requested
order is obtained by appending exactly one edge to the current prefix.
-/
theorem localBoundarySupportOrderContribution_eq_zero_of_length_ne
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hne : order.length ≠ pref.length + 1) :
    localBoundarySupportOrderContribution choices F pref prefixTs top
        I order ρ = 0 := by
  rw [localBoundarySupportOrderContribution_def]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ he
    apply hne
    rw [← he.2]
    simp

/-- Local active-boundary sectors regroup by child support. -/
theorem sum_localBoundarySupportContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum F.activeEdges.attach
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ ts))))) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I =>
          localBoundarySupportContribution choices F pref prefixTs top I ρ) := by
  classical
  have hmap :
      ∀ e ∈ F.activeEdges.attach,
        (choices F e).forest.support ∈
          (Finset.univ : Finset (ForestIndex V)) := by
    intro e _
    exact Finset.mem_univ _
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := F.activeEdges.attach)
      (t := (Finset.univ : Finset (ForestIndex V)))
      (g := fun e => (choices F e).forest.support)
      hmap
      (fun e =>
        orderedSimplexIntegralAux top [e.val]
          (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ ts)))))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro I _
  rw [localBoundarySupportContribution_def choices F pref prefixTs top I ρ]

/-- A local support fiber splits by canonical child order. -/
theorem localBoundarySupportContribution_eq_sum_supportOrderContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportContribution choices F pref prefixTs top I ρ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          localBoundarySupportOrderContribution choices F pref prefixTs top
            I order ρ) := by
  classical
  rw [localBoundarySupportContribution_def choices F pref prefixTs top I ρ]
  have hmap :
      ∀ e ∈ F.activeEdges.attach.filter
          (fun e => (choices F e).forest.support = I),
        pref ++ [e.val] ∈ edgeSetOrders I.edges := by
    intro e he
    exact
      activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
        (choices F e) hpref hnodup (Finset.mem_filter.mp he).2
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := F.activeEdges.attach.filter
        (fun e => (choices F e).forest.support = I))
      (t := edgeSetOrders I.edges)
      (g := fun e => pref ++ [e.val])
      hmap
      (fun e =>
        orderedSimplexIntegralAux top [e.val]
          (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ ts)))))
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro order _
  rw [localBoundarySupportOrderContribution_def choices F pref prefixTs top
    I order ρ]
  have hfilter :
      (F.activeEdges.attach.filter
          (fun e => (choices F e).forest.support = I)).filter
          (fun e => pref ++ [e.val] = order) =
        F.activeEdges.attach.filter
          (fun e =>
            (choices F e).forest.support = I ∧
              pref ++ [e.val] = order) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro e he
  rw [(Finset.mem_filter.mp he).2.2]

/-- Local active-boundary sectors regroup by child support and order. -/
theorem sum_localBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum F.activeEdges.attach
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ ts))))) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            localBoundarySupportOrderContribution choices F pref prefixTs top
              I order ρ)) := by
  rw [sum_localBoundarySupportContribution choices F pref prefixTs top ρ]
  apply Finset.sum_congr rfl
  intro I _
  rw [localBoundarySupportContribution_eq_sum_supportOrderContribution
    choices F pref prefixTs top hpref hnodup I ρ]

/--
Contribution of exposed one-edge boundary sectors whose child forest has a
fixed finite support.
-/
noncomputable def firstBoundarySupportContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      ((Forest.empty V).activeEdges.attach.filter
        (fun e => (choices (Forest.empty V) e).forest.support = I))
      (fun e =>
        (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ)

theorem firstBoundarySupportContribution_def
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportContribution choices I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (choices (Forest.empty V) e).forest.support = I))
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ) := by
  rw [firstBoundarySupportContribution]

/--
Contribution of exposed one-edge boundary sectors with fixed support and fixed
canonical edge order.
-/
noncomputable def firstBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      ((Forest.empty V).activeEdges.attach.filter
        (fun e =>
          (choices (Forest.empty V) e).forest.support = I ∧
            [e.val] = order))
      (fun e =>
        (choices (Forest.empty V) e).forest.orderedContribution order ρ)

theorem firstBoundarySupportOrderContribution_def
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportOrderContribution choices I order ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e =>
            (choices (Forest.empty V) e).forest.support = I ∧
              [e.val] = order))
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution order ρ) := by
  rw [firstBoundarySupportOrderContribution]

/-- The root support fiber is the empty-prefix instance of the local API. -/
theorem firstBoundarySupportContribution_eq_localBoundarySupportContribution_empty
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportContribution choices I ρ =
      localBoundarySupportContribution choices (Forest.empty V) [] [] 1 I ρ := by
  rw [firstBoundarySupportContribution_def,
    localBoundarySupportContribution_def]
  apply Finset.sum_congr rfl
  intro e _
  rw [← integral_standardInterp_empty_singleton_eq_orderedContribution]
  rfl

/-- The root support/order fiber is the empty-prefix instance of the local API. -/
theorem firstContribution_eq_boundaryContribution_empty
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportOrderContribution choices I order ρ =
      localBoundarySupportOrderContribution choices (Forest.empty V) [] [] 1
        I order ρ := by
  rw [firstBoundarySupportOrderContribution_def,
    localBoundarySupportOrderContribution_def]
  apply Finset.sum_congr rfl
  intro e he
  rw [← (Finset.mem_filter.mp he).2.2]
  rw [← integral_standardInterp_empty_singleton_eq_orderedContribution]
  rfl

/-- Exposed first boundary sectors regroup by finite support. -/
theorem sum_firstBoundarySupportContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Forest.empty V).activeEdges.attach
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => firstBoundarySupportContribution choices I ρ) := by
  classical
  have hmap :
      ∀ e ∈ (Forest.empty V).activeEdges.attach,
        (choices (Forest.empty V) e).forest.support ∈
          (Finset.univ : Finset (ForestIndex V)) := by
    intro e _
    exact Finset.mem_univ _
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Forest.empty V).activeEdges.attach)
      (t := (Finset.univ : Finset (ForestIndex V)))
      (g := fun e => (choices (Forest.empty V) e).forest.support)
      hmap
      (fun e =>
        (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro I _
  rw [firstBoundarySupportContribution_def choices I ρ]

/-- A support fiber of exposed first sectors splits by canonical edge order. -/
theorem firstBoundarySupportContribution_eq_sum_supportOrderContribution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportContribution choices I ρ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order =>
          firstBoundarySupportOrderContribution choices I order ρ) := by
  classical
  rw [firstBoundarySupportContribution_def choices I ρ]
  have hmap :
      ∀ e ∈ (Forest.empty V).activeEdges.attach.filter
          (fun e => (choices (Forest.empty V) e).forest.support = I),
        [e.val] ∈ edgeSetOrders I.edges := by
    intro e he
    exact
      activeExtension_singleton_order_mem_edgeSetOrders_of_support_eq_empty
        (choices (Forest.empty V) e) (Finset.mem_filter.mp he).2
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Forest.empty V).activeEdges.attach.filter
        (fun e => (choices (Forest.empty V) e).forest.support = I))
      (t := edgeSetOrders I.edges)
      (g := fun e => [e.val])
      hmap
      (fun e =>
        (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro order _
  rw [firstBoundarySupportOrderContribution_def choices I order ρ]
  have hfilter :
      ((Forest.empty V).activeEdges.attach.filter
          (fun e => (choices (Forest.empty V) e).forest.support = I)).filter
          (fun e => [e.val] = order) =
        (Forest.empty V).activeEdges.attach.filter
          (fun e =>
            (choices (Forest.empty V) e).forest.support = I ∧
              [e.val] = order) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro h
      exact ⟨h.1.1, h.1.2, h.2⟩
    · intro h
      exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩
  rw [hfilter]
  apply Finset.sum_congr rfl
  intro e he
  rw [(Finset.mem_filter.mp he).2.2]

/-- Exposed first boundary sectors regroup by support and canonical order. -/
theorem sum_firstBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Forest.empty V).activeEdges.attach
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            firstBoundarySupportOrderContribution choices I order ρ)) := by
  rw [sum_firstBoundarySupportContribution choices ρ]
  apply Finset.sum_congr rfl
  intro I _
  rw [firstBoundarySupportContribution_eq_sum_supportOrderContribution
    choices I ρ]

/--
The first recursive boundary remainder after exposing and regrouping all
one-edge sectors below the empty forest.
-/
noncomputable def firstRecursiveBoundaryRemainder
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum (Forest.empty V).activeEdges.attach
    (fun e => ∫ t in 0..(1 : ℝ),
      Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
        (fun e' => ∫ s in 0..t,
          allBranchesBoundaryExpansion choices
            (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
            (choices ((choices (Forest.empty V) e).forest) e').forest
            ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))

theorem firstRecursiveBoundaryRemainder_def
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    firstRecursiveBoundaryRemainder choices ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ)) :=
  rfl

/--
If every first child is already terminal, the recursive boundary remainder is
zero.
-/
theorem firstRecursiveBoundaryRemainder_eq_zero_of_forall_child_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    firstRecursiveBoundaryRemainder choices ρ = 0 := by
  rw [firstRecursiveBoundaryRemainder_def]
  apply Finset.sum_eq_zero
  intro e _
  have hattach :
      (choices (Forest.empty V) e).forest.activeEdges.attach = ∅ := by
    rw [hterm e]
    rfl
  simp [hattach]

/-- The child first-sector integrability contained in `allBranchesAnalytic`. -/
theorem allBranchesAnalytic.child_standard_intervalIntegrable
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    IntervalIntegrable
      (fun t : ℝ => mixedPartialList (pref ++ [e.val]).reverse ρ
        ((choices F e).forest.standardInterp
          ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
            (prefixTs ++ [t]))))
      MeasureTheory.volume 0 top := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨_hbound, _hρ, _hint, hstd, _hrec, _hchild⟩
  exact hstd e

/-- The recursive child-sum integrability contained in `allBranchesAnalytic`. -/
theorem allBranchesAnalytic.child_recursive_sum_intervalIntegrable
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    IntervalIntegrable
      (fun t : ℝ =>
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ))
      MeasureTheory.volume 0 top := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨_hbound, _hρ, _hint, _hstd, hrec, _hchild⟩
  exact hrec e

/--
Linearity bridge for one nonterminal child of the exact-depth boundary tree.

The theorem is intentionally local: it separates the boundary subtree into the
child's first ordered sector and the recursive exact-depth grandchildren once
those two functions are known to be interval-integrable.
-/
theorem integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hstd :
      IntervalIntegrable
        (fun t : ℝ =>
          mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ [t]))))
        MeasureTheory.volume 0 top)
    (hrec :
      IntervalIntegrable
        (fun t : ℝ =>
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ))
        MeasureTheory.volume 0 top) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ) =
      (∫ t in 0..top,
        mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ [t])))) +
        ∫ t in 0..top,
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ) := by
  rw [integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum]
  rw [intervalIntegral.integral_add hstd hrec]

/--
Prefixed ordered-simplex form of the nonterminal child split.
-/
theorem childIntegral_eq_prefixedSimplex_add_integralSum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hstd :
      IntervalIntegrable
        (fun t : ℝ =>
          mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ [t]))))
        MeasureTheory.volume 0 top)
    (hrec :
      IntervalIntegrable
        (fun t : ℝ =>
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ))
        MeasureTheory.volume 0 top) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ) =
      orderedSimplexIntegralAux top [e.val]
        (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ ts)))) +
        ∫ t in 0..top,
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ) := by
  rw [integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
    choices F e pref prefixTs top ρ hstd hrec]
  rw [integral_prefixed_standardInterp_singleton_eq_orderedSimplexIntegralAux]

/--
Nonterminal child split with the linearity hypotheses read from
`allBranchesAnalytic`.
-/
theorem childIntegral_eq_prefixedSimplex_add_integralSum_of_analytic
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ) =
      orderedSimplexIntegralAux top [e.val]
        (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ ts)))) +
        ∫ t in 0..top,
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ) := by
  exact
    childIntegral_eq_prefixedSimplex_add_integralSum
      choices F e pref prefixTs top ρ
      (allBranchesAnalytic.child_standard_intervalIntegrable
        choices F e pref prefixTs top ρ hanalytic)
      (allBranchesAnalytic.child_recursive_sum_intervalIntegrable
        choices F e pref prefixTs top ρ hanalytic)

/--
Arbitrary-node nonterminal regrouping step. After summing over all active
children, the first child sectors regroup by support and canonical order, and
the only remaining term is the exact recursive child-boundary sum.
-/
theorem childIntegralSum_eq_boundarySum_add_childIntegral_of_analytic
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          allBranchesBoundaryExpansion choices
            (choices F e).forest.activeEdges.card
            (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t ρ) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            localBoundarySupportOrderContribution choices F pref prefixTs top
              I order ρ)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            Finset.sum (choices F e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices (choices F e).forest e').forest.activeEdges.card
                  (choices (choices F e).forest e').forest
                  ((pref ++ [e.val]) ++ [e'.val])
                  ((prefixTs ++ [t]) ++ [s]) s ρ)) := by
  have hsplit :
      Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices
              (choices F e).forest.activeEdges.card
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) =
        Finset.sum F.activeEdges.attach
          (fun e =>
            orderedSimplexIntegralAux top [e.val]
              (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
                ((choices F e).forest.standardInterp
                  ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                    (prefixTs ++ ts)))) +
            ∫ t in 0..top,
              Finset.sum (choices F e).forest.activeEdges.attach
                (fun e' => ∫ s in 0..t,
                  allBranchesBoundaryExpansion choices
                    (choices (choices F e).forest e').forest.activeEdges.card
                    (choices (choices F e).forest e').forest
                    ((pref ++ [e.val]) ++ [e'.val])
                    ((prefixTs ++ [t]) ++ [s]) s ρ)) := by
    apply Finset.sum_congr rfl
    intro e _
    exact
      childIntegral_eq_prefixedSimplex_add_integralSum_of_analytic
        choices F e pref prefixTs top ρ hanalytic
  rw [hsplit]
  rw [Finset.sum_add_distrib]
  rw [sum_localBoundarySupportOrderContribution choices F pref prefixTs top
    hpref hnodup ρ]

/--
Root specialization of the arbitrary-node nonterminal regrouping step.
-/
theorem oneConfig_eq_initialSectorSum_add_boundarySum_add_childIntegral
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              localBoundarySupportOrderContribution choices
                (Forest.empty V) [] [] 1 I order ρ)) +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    choices ρ hanalytic]
  have hsplit :=
    childIntegralSum_eq_boundarySum_add_childIntegral_of_analytic
      choices (Forest.empty V) [] [] 1 ρ (by simp [Forest.empty_edges])
      List.nodup_nil hanalytic
  simpa using
    congrArg (fun r => (Forest.empty V).orderedSectorSum ρ + r) hsplit

/--
Empty-start form of the nonterminal child split: the first child sector is the
one-edge ordered contribution of the child forest.
-/
theorem integral_boundaryExpansion_empty_child_eq_orderedContribution_add_integral_sum
    (choices : ActiveExtensionChoice V)
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (ρ : (Edge V → ℝ) → ℝ)
    (hstd :
      IntervalIntegrable
        (fun t : ℝ =>
          mixedPartialList [e.val].reverse ρ
            ((choices (Forest.empty V) e).forest.standardInterp
              ((choices (Forest.empty V) e).forest.paramsOfOrder
                [e.val] [t])))
        MeasureTheory.volume 0 1)
    (hrec :
      IntervalIntegrable
        (fun t : ℝ =>
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))
        MeasureTheory.volume 0 1) :
    (∫ t in 0..(1 : ℝ),
        allBranchesBoundaryExpansion choices
          (choices (Forest.empty V) e).forest.activeEdges.card
          (choices (Forest.empty V) e).forest [e.val] [t] t ρ) =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ +
        ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ) := by
  calc
    (∫ t in 0..(1 : ℝ),
        allBranchesBoundaryExpansion choices
          (choices (Forest.empty V) e).forest.activeEdges.card
          (choices (Forest.empty V) e).forest [e.val] [t] t ρ) =
      (∫ t in 0..(1 : ℝ),
        mixedPartialList [e.val].reverse ρ
          ((choices (Forest.empty V) e).forest.standardInterp
            ((choices (Forest.empty V) e).forest.paramsOfOrder [e.val]
              [t]))) +
        ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ) := by
        simpa using
          integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
            choices (Forest.empty V) e [] [] 1 ρ hstd hrec
    _ =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ +
        ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ) := by
        rw [integral_standardInterp_empty_singleton_eq_orderedContribution]

/--
Root first-layer nonterminal regrouping bridge. Each first active edge now
contributes its one-edge ordered sector plus the exact recursive boundary
subtrees below the child.
-/
theorem oneConfig_eq_initialSectorSum_add_orderedContributionSum_add_childIntegralSum
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hstd :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            mixedPartialList [e.val].reverse ρ
              ((choices (Forest.empty V) e).forest.standardInterp
                ((choices (Forest.empty V) e).forest.paramsOfOrder
                  [e.val] [t])))
          MeasureTheory.volume 0 1)
    (hrec :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))
          MeasureTheory.volume 0 1) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e =>
            (choices (Forest.empty V) e).forest.orderedContribution
              [e.val] ρ +
            ∫ t in 0..(1 : ℝ),
              Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
                (fun e' => ∫ s in 0..t,
                  allBranchesBoundaryExpansion choices
                    (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                    (choices ((choices (Forest.empty V) e).forest) e').forest
                    ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ)) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    choices ρ hanalytic]
  apply congrArg
    (fun r => (Forest.empty V).orderedSectorSum ρ + r)
  apply Finset.sum_congr rfl
  intro e _
  exact
    integral_boundaryExpansion_empty_child_eq_orderedContribution_add_integral_sum
      choices e ρ (hstd e) (hrec e)

/--
Separated finite-sum form of the root nonterminal bridge: exposed one-edge
sectors and recursive child sums are now two distinct finite sums.
-/
theorem oneConfig_eq_initialSectorSum_add_orderedContributionSum_add_childIntegral
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hstd :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            mixedPartialList [e.val].reverse ρ
              ((choices (Forest.empty V) e).forest.standardInterp
                ((choices (Forest.empty V) e).forest.paramsOfOrder
                  [e.val] [t])))
          MeasureTheory.volume 0 1)
    (hrec :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))
          MeasureTheory.volume 0 1) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Forest.empty V).activeEdges.attach
          (fun e =>
            (choices (Forest.empty V) e).forest.orderedContribution
              [e.val] ρ) +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by
  rw [oneConfig_eq_initialSectorSum_add_orderedContributionSum_add_childIntegralSum
    choices ρ hanalytic hstd hrec]
  rw [Finset.sum_add_distrib]

/--
Root nonterminal regrouping with the first sectors split from the recursive
child sums, using only the strengthened all-branches analytic hypothesis.
-/
theorem oneConfig_eq_initialSectorSum_add_orderedContributionSum_add_childIntegral_of_analytic
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Forest.empty V).activeEdges.attach
          (fun e =>
            (choices (Forest.empty V) e).forest.orderedContribution
              [e.val] ρ) +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by
  exact
    oneConfig_eq_initialSectorSum_add_orderedContributionSum_add_childIntegral
      choices ρ hanalytic
      (fun e =>
        allBranchesAnalytic.child_standard_intervalIntegrable
          choices (Forest.empty V) e [] [] 1 ρ hanalytic)
      (fun e =>
        allBranchesAnalytic.child_recursive_sum_intervalIntegrable
          choices (Forest.empty V) e [] [] 1 ρ hanalytic)

/--
Root nonterminal regrouping with exposed one-edge sectors already fibered by
support and canonical order. The remaining summand is the exact recursive
child-boundary contribution.
-/
theorem oneConfig_eq_initialSectorSum_add_sum_firstContribution_add_childIntegral
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              firstBoundarySupportOrderContribution choices I order ρ)) +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by
  rw [oneConfig_eq_initialSectorSum_add_orderedContributionSum_add_childIntegral_of_analytic
    choices ρ hanalytic]
  rw [sum_firstBoundarySupportOrderContribution choices ρ]

/--
Root nonterminal regrouping with the recursive contribution packaged as the
first recursive boundary remainder.
-/
theorem oneConfig_eq_initialSectorSum_add_sum_firstContribution_add_recursiveRemainder
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              firstBoundarySupportOrderContribution choices I order ρ)) +
        firstRecursiveBoundaryRemainder choices ρ) := by
  rw [oneConfig_eq_initialSectorSum_add_sum_firstContribution_add_childIntegral
    choices ρ hanalytic]
  rw [firstRecursiveBoundaryRemainder_def]

/--
Terminal-child base case of the regrouped all-branches identity.
-/
theorem oneConfig_eq_initialSectorSum_add_sum_firstContribution_of_terminalChildren
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              firstBoundarySupportOrderContribution choices I order ρ)) := by
  rw [oneConfig_eq_initialSectorSum_add_sum_firstContribution_add_recursiveRemainder
    choices ρ hanalytic]
  rw [firstRecursiveBoundaryRemainder_eq_zero_of_forall_child_activeEdges_eq_empty
    choices ρ hterm]
  ring

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
