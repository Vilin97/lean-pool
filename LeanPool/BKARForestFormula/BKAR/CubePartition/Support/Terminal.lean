/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Contribution

/-! # Vanishing and base cases for support/order contributions

Support/order contributions vanish unless the order enumerates the support;
contributions with empty order or empty support degenerate as expected; and
one-edge supports are characterized.  Together with the unfolding of a
nonempty order into an integral of tail branch integrals, these are the
boundary cases closing the support/order recursion of the BKAR forest
interpolation formula (see `BKAR.Formula`).
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ActiveTerminalBranchData

variable {F : Forest V}

/--
An order outside `edgeSetOrders I.edges` has no selected branch in the support
`I` fiber.
-/
theorem supportOrderContribution_eq_zero_of_order_not_mem_edgeSetOrders
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) {order : List (Edge V)}
    (horder : order ∉ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I order ρ = 0 := by
  rw [data.supportOrderContribution_def I order ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ h
    apply horder
    rw [← h.2]
    exact data.growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart e h.1

/-- No selected empty-start terminal branch has empty terminal order. -/
theorem supportOrderContribution_nil_eq_zero
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I [] ρ = 0 := by
  rw [data.supportOrderContribution_def I [] ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ h
    have horder := h.2
    rw [data.growthOrder_eq e] at horder
    cases horder

/--
A fixed nonempty ordered sector can only be supplied by the branch whose first
edge is the head of that order.
-/
theorem supportOrderContribution_cons_eq_orderedContribution_of_support_eq_and_tail_eq
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (a : Edge V) (tail : List (Edge V))
    (hsupport : (data.growth (emptyActiveEdge a)).support = I)
    (htail : (data.tail (emptyActiveEdge a)).order = tail)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ =
      (data.growth (emptyActiveEdge a)).terminal.orderedContribution
        (a :: tail) ρ := by
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I ∧
            data.growthOrder e = a :: tail) =
        {emptyActiveEdge a} := by
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      apply Subtype.ext
      have horder := h.2.2
      rw [data.growthOrder_eq e] at horder
      injection horder with hfirst _
    · intro h
      rw [h]
      constructor
      · exact Finset.mem_attach _ _
      · constructor
        · exact hsupport
        · rw [data.growthOrder_eq (emptyActiveEdge a), htail,
            emptyActiveEdge_val]
  rw [data.supportOrderContribution_def I (a :: tail) ρ]
  rw [hfilter, Finset.sum_singleton]

/--
Recursive form of a fixed nonempty support/order fiber: once the selected
branch over the head edge has the requested support and tail order, the fiber
is exactly the tail branch integral after the first edge.
-/
theorem supportOrderContribution_cons_eq_integral_tail_branchIntegralAux_of_support_eq_and_tail_eq
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (a : Edge V) (tail : List (Edge V))
    (hsupport : (data.growth (emptyActiveEdge a)).support = I)
    (htail : (data.tail (emptyActiveEdge a)).order = tail)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ =
      ∫ t in 0..(1 : ℝ),
        (data.tail (emptyActiveEdge a)).branchIntegralAux t
          ((data.extension (emptyActiveEdge a)).extension.extendParam
            emptyParam t)
          (partialDeriv a ρ) := by
  rw [data.supportOrderContribution_cons_eq_orderedContribution_of_support_eq_and_tail_eq
    I a tail hsupport htail ρ]
  rw [← htail]
  simpa only [emptyActiveEdge_val] using!
    TerminalGrowth.cons_orderedContribution_eq_integral_tail_branchIntegralAux_emptyStart
      (data.extension (emptyActiveEdge a)) (data.tail (emptyActiveEdge a)) ρ

/--
If the branch over the head edge does not have support `I`, then no branch
can contribute to the ordered sector `a :: tail` over `I`.
-/
theorem supportOrderContribution_cons_eq_zero_of_support_ne
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (a : Edge V) (tail : List (Edge V))
    (hsupport : (data.growth (emptyActiveEdge a)).support ≠ I)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ = 0 := by
  rw [data.supportOrderContribution_def I (a :: tail) ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ h
    have heq : e = emptyActiveEdge a := by
      apply Subtype.ext
      have horder := h.2
      rw [data.growthOrder_eq e] at horder
      injection horder with hfirst _
    exact hsupport (by
      rw [← heq]
      exact h.1)

/--
If the branch over the head edge has a different tail order, then it does not
contribute to the ordered sector `a :: tail`.
-/
theorem supportOrderContribution_cons_eq_zero_of_tail_ne
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (a : Edge V) (tail : List (Edge V))
    (htail : (data.tail (emptyActiveEdge a)).order ≠ tail)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I (a :: tail) ρ = 0 := by
  rw [data.supportOrderContribution_def I (a :: tail) ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ h
    have heq : e = emptyActiveEdge a := by
      apply Subtype.ext
      have horder := h.2
      rw [data.growthOrder_eq e] at horder
      injection horder with hfirst _
    apply htail
    have horder := h.2
    rw [data.growthOrder_eq e] at horder
    injection horder with _ htail_eq
    rw [← heq]
    exact htail_eq

/--
No selected active-terminal branch from the empty forest has empty terminal
support.
-/
theorem supportContribution_eq_zero_of_edges_empty
    (data : ActiveTerminalBranchData (Forest.empty V))
    {I : ForestIndex V} (hI : I.edges = ∅)
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ = 0 := by
  rw [data.supportContribution_eq_sum_order_toFinset I ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ horder
    have hempty : e.val ∈ (∅ : Finset (Edge V)) := by
      rw [← hI, ← horder]
      exact List.mem_toFinset.mpr (by
        rw [List.mem_cons]
        exact Or.inl rfl)
    exact Finset.notMem_empty e.val hempty

/--
A selected terminal branch from the empty forest has singleton support exactly
when its first edge is that singleton and its tail order is empty.
-/
theorem growth_support_eq_singleton_iff_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (a : Edge V) :
    (data.growth e).support = ForestIndex.singleton a ↔
      e.val = a ∧ (data.tail e).order = [] := by
  constructor
  · intro hsupport
    have hset :
        (e.val :: (data.tail e).order).toFinset =
          ({a} : Finset (Edge V)) := by
      simpa only [ForestIndex.singleton_edges] using
        (data.growth_support_eq_iff_order_toFinset_eq_emptyStart e
          (ForestIndex.singleton a)).mp hsupport
    exact eq_and_tail_eq_nil_of_cons_toFinset_eq_singleton_of_nodup
      hset (data.growth_order_nodup e)
  · intro h
    apply
      (data.growth_support_eq_iff_order_toFinset_eq_emptyStart e
        (ForestIndex.singleton a)).mpr
    rw [ForestIndex.singleton_edges, List.toFinset_cons, h.2,
      List.toFinset_nil, h.1, Finset.insert_empty]

/--
The tail order is empty exactly when the selected terminal support is the
singleton generated by the first edge.
-/
theorem tail_order_eq_nil_iff_growth_support_eq_singleton_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.tail e).order = [] ↔
      (data.growth e).support = ForestIndex.singleton e.val := by
  constructor
  · intro htail
    exact (data.growth_support_eq_singleton_iff_emptyStart e e.val).mpr
      ⟨rfl, htail⟩
  · intro hsupport
    exact
      ((data.growth_support_eq_singleton_iff_emptyStart e e.val).mp
        hsupport).2

/--
If the selected terminal support is not the singleton of its first edge, then
the branch has a nonempty tail order.
-/
theorem tail_order_ne_nil_of_growth_support_ne_singleton_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (hsupport :
      (data.growth e).support ≠ ForestIndex.singleton e.val) :
    (data.tail e).order ≠ [] := by
  intro htail
  exact hsupport
    ((data.tail_order_eq_nil_iff_growth_support_eq_singleton_emptyStart e).mp
      htail)

/--
Branches over a support with more than one edge have a genuinely nonempty
tail after the first selected edge.
-/
theorem tail_order_ne_nil_of_one_lt_support_edges_card_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I)
    (hcard : 1 < I.edges.card) :
    (data.tail e).order ≠ [] := by
  apply data.tail_order_ne_nil_of_growth_support_ne_singleton_emptyStart e
  intro hsingleton
  have hI : I = ForestIndex.singleton e.val := by
    rw [← hsupport, hsingleton]
  have hcardI : I.edges.card = 1 := by
    rw [hI, ForestIndex.singleton_edges, Finset.card_singleton]
  rw [hcardI] at hcard
  exact Nat.lt_irrefl 1 hcard

/--
Conversely, if the selected empty-start branch has a nonempty tail, its
terminal support has at least two edges.
-/
theorem one_lt_growth_support_edges_card_of_tail_order_ne_nil_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (htail : (data.tail e).order ≠ []) :
    1 < (data.growth e).support.edges.card := by
  have hlen :
      (e.val :: (data.tail e).order).length =
        (data.growth e).support.edges.card :=
    data.growth_order_length_eq_card_support_edges_emptyStart e rfl
  cases horder : (data.tail e).order with
  | nil =>
      exact False.elim (htail horder)
  | cons a tail =>
      rw [horder, List.length_cons, List.length_cons] at hlen
      rw [← hlen]
      exact Nat.succ_lt_succ (Nat.zero_lt_succ tail.length)

/--
For selected empty-start terminal branches, higher-support fibers are exactly
the branches whose selected tail order is nonempty.
-/
theorem one_lt_growth_support_edges_card_iff_tail_order_ne_nil_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    1 < (data.growth e).support.edges.card ↔
      (data.tail e).order ≠ [] := by
  constructor
  · intro hcard
    exact data.tail_order_ne_nil_of_one_lt_support_edges_card_emptyStart
      e rfl hcard
  · intro htail
    exact
      data.one_lt_growth_support_edges_card_of_tail_order_ne_nil_emptyStart
        e htail

/--
Singleton-support terminal branch fibers can be read as the branches with the
specified first edge and empty tail order.
-/
theorem supportContribution_singleton_eq_sum_first_eq_and_tail_nil
    (data : ActiveTerminalBranchData (Forest.empty V))
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution (ForestIndex.singleton a) ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => e.val = a ∧ (data.tail e).order = []))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = ForestIndex.singleton a) =
        (Forest.empty V).activeEdges.attach.filter
          (fun e => e.val = a ∧ (data.tail e).order = []) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter]
    exact and_congr_right
      (fun _ => data.growth_support_eq_singleton_iff_emptyStart e a)
  rw [data.supportContribution_def (ForestIndex.singleton a) ρ, hfilter]

/--
If the selected branch over `a` stops after its first edge, the singleton
support fiber is exactly its one-edge ordered contribution.
-/
theorem supportContribution_singleton_eq_orderedContribution_of_tail_eq_nil
    (data : ActiveTerminalBranchData (Forest.empty V))
    (a : Edge V) (htail : (data.tail (emptyActiveEdge a)).order = [])
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution (ForestIndex.singleton a) ρ =
      (data.growth (emptyActiveEdge a)).terminal.orderedContribution [a] ρ := by
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e => e.val = a ∧ (data.tail e).order = []) =
        {emptyActiveEdge a} := by
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      apply Subtype.ext
      rw [emptyActiveEdge_val]
      exact h.2.1
    · intro h
      rw [h]
      exact ⟨Finset.mem_attach _ _, rfl, htail⟩
  rw [data.supportContribution_singleton_eq_sum_first_eq_and_tail_nil a ρ]
  rw [hfilter, Finset.sum_singleton]
  rw [data.growthOrder_eq (emptyActiveEdge a), htail, emptyActiveEdge_val]

/--
If the selected branch over `a` has a nonempty tail, then it contributes
nothing to the singleton support fiber over `{a}`.
-/
theorem supportContribution_singleton_eq_zero_of_tail_ne_nil
    (data : ActiveTerminalBranchData (Forest.empty V))
    (a : Edge V) (htail : (data.tail (emptyActiveEdge a)).order ≠ [])
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution (ForestIndex.singleton a) ρ = 0 := by
  rw [data.supportContribution_singleton_eq_sum_first_eq_and_tail_nil a ρ]
  rw [Finset.filter_eq_empty_iff.mpr]
  · exact Finset.sum_empty
  · intro e _ h
    have heq : e = emptyActiveEdge a := by
      apply Subtype.ext
      rw [emptyActiveEdge_val]
      exact h.1
    exact htail (by
      rw [← h.2]
      rw [heq])

/--
For singleton terminal branches from the empty forest, the active-terminal
branch sum is a finite sum of canonical one-edge ordered-sector contributions.
-/
theorem singleton_branchIntegral_empty_eq_sum_orderedContribution
    (extensions :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        ActiveExtension (Forest.empty V) e.val)
    (hterm :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        (extensions e).forest.activeEdges = ∅)
    (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegral emptyParam ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => (extensions e).forest.orderedContribution [e.val] ρ) := by
  rw [branchIntegral_eq_branchIntegralAux_one]
  rw [branchIntegralAux_eq_sum_growth_branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  change ((extensions e).singletonGrowth.branchIntegral emptyParam ρ) =
    (extensions e).forest.orderedContribution [e.val] ρ
  exact (extensions e).singletonGrowth_branchIntegral_empty_eq_orderedContribution ρ

end ActiveTerminalBranchData

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
