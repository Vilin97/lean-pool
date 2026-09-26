/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.Support.Growth

/-! # Contributions grouped by support and order

Defines `supportContribution` and `supportOrderContribution`, the sums of
terminal branch integrals whose growth reaches a prescribed support edge
set (and, in the refined version, follows a prescribed order), and proves
the regrouping identities expressing the total branch integral from the
empty forest as a sum over supports, then over first edge and tail order.
This is the combinatorial regrouping behind the sum-over-forests form of
the BKAR forest interpolation formula (see `BKAR.Formula`).
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ActiveTerminalBranchData

variable {F : Forest V}

/--
Contribution of the selected empty-start terminal branches whose terminal
forest has a fixed finite support index.
-/
noncomputable def supportContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      ((Forest.empty V).activeEdges.attach.filter
        (fun e => (data.growth e).support = I))
      (fun e => (data.growth e).terminal.orderedContribution
        (data.growthOrder e) ρ)

theorem supportContribution_def
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by
  rw [supportContribution]

/--
Contribution of selected empty-start terminal branches with both fixed support
and fixed terminal edge order.
-/
noncomputable def supportOrderContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ := by
  classical
  exact
    Finset.sum
      ((Forest.empty V).activeEdges.attach.filter
        (fun e => (data.growth e).support = I ∧
          data.growthOrder e = order))
      (fun e => (data.growth e).terminal.orderedContribution order ρ)

theorem supportOrderContribution_def
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.supportOrderContribution I order ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I ∧
            data.growthOrder e = order))
        (fun e => (data.growth e).terminal.orderedContribution order ρ) := by
  rw [supportOrderContribution]

/--
The selected active-terminal branches from the empty forest can be regrouped by
their finite terminal forest support.
-/
theorem branchIntegral_empty_eq_sum_supportContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => data.supportContribution I ρ) := by
  classical
  rw [data.branchIntegral_empty_eq_sum_growthOrderContribution ρ]
  have hmap :
      ∀ e ∈ (Forest.empty V).activeEdges.attach,
        (data.growth e).support ∈
          (Finset.univ : Finset (ForestIndex V)) := by
    intro e _
    exact Finset.mem_univ (data.growth e).support
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Forest.empty V).activeEdges.attach)
      (t := (Finset.univ : Finset (ForestIndex V)))
      (g := fun e => (data.growth e).support)
      hmap
      (fun e => (data.growth e).terminal.orderedContribution
        (data.growthOrder e) ρ)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro I _
  rw [data.supportContribution_def I ρ]

/--
For selected terminal branches from the empty forest, equality of finite
supports is exactly equality of the selected order's edge set.
-/
theorem growth_support_eq_iff_order_toFinset_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (I : ForestIndex V) :
    (data.growth e).support = I ↔
      (e.val :: (data.tail e).order).toFinset = I.edges := by
  constructor
  · intro h
    rw [← data.growth_support_edges_eq_toFinset_emptyStart e]
    rw [h]
  · intro h
    apply ForestIndex.ext
    rw [data.growth_support_edges_eq_toFinset_emptyStart e, h]

/--
Edge-set form of `ActiveTerminalBranchData.supportContribution`. This removes
the proof-carrying support index from the fiber predicate.
-/
theorem supportContribution_eq_sum_order_toFinset
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (e.val :: (data.tail e).order).toFinset = I.edges))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I) =
        (Forest.empty V).activeEdges.attach.filter
          (fun e => (e.val :: (data.tail e).order).toFinset = I.edges) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter]
    exact and_congr_right
      (fun _ => data.growth_support_eq_iff_order_toFinset_eq_emptyStart e I)
  rw [data.supportContribution_def I ρ, hfilter]

/--
Support equality for a selected terminal branch from the empty forest is
equivalent to choosing the first edge in the support and a canonical ordering
of the support with that edge erased.
-/
theorem growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (I : ForestIndex V) :
    (data.growth e).support = I ↔
      e.val ∈ I.edges ∧
        (data.tail e).order ∈ edgeSetOrders (I.edges.erase e.val) := by
  constructor
  · intro hsupport
    have horder :
        e.val :: (data.tail e).order ∈ edgeSetOrders I.edges := by
      rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
      exact ⟨
        (data.growth_support_eq_iff_order_toFinset_eq_emptyStart e I).mp
          hsupport,
        data.growth_order_nodup e⟩
    exact
      (cons_mem_edgeSetOrders_iff I.edges).mp
        horder
  · intro h
    apply
      (data.growth_support_eq_iff_order_toFinset_eq_emptyStart e I).mpr
    have htail :
        (data.tail e).order.toFinset = I.edges.erase e.val :=
      toFinset_eq_of_mem_edgeSetOrders h.2
    rw [List.toFinset_cons, htail, Finset.insert_erase h.1]

/--
First-edge/tail-order form of `ActiveTerminalBranchData.supportContribution`.
This is the support-fiber shape used by the recursive BKAR sector enumeration.
-/
theorem supportContribution_eq_sum_first_mem_and_tail_order
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => e.val ∈ I.edges ∧
            (data.tail e).order ∈ edgeSetOrders (I.edges.erase e.val)))
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I) =
        (Forest.empty V).activeEdges.attach.filter
          (fun e => e.val ∈ I.edges ∧
            (data.tail e).order ∈ edgeSetOrders (I.edges.erase e.val)) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter]
    exact and_congr_right
      (fun _ =>
        data.growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart
          e I)
  rw [data.supportContribution_def I ρ, hfilter]

/--
Support-fiber form indexed directly by first edges in `I.edges`.  Since every
edge is active over the empty forest, the ambient active-edge filter can be
collapsed to the actual support edge set, with the tail order carrying the
remaining fiber predicate.
-/
theorem supportContribution_eq_sum_support_edges_filter_tail_order
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        (I.edges.attach.filter
          (fun e =>
            (data.tail (emptyActiveEdge e.val)).order ∈
              edgeSetOrders (I.edges.erase e.val)))
        (fun e => (data.growth (emptyActiveEdge e.val)).terminal.orderedContribution
          (data.growthOrder (emptyActiveEdge e.val)) ρ) := by
  rw [data.supportContribution_eq_sum_first_mem_and_tail_order I ρ]
  refine Finset.sum_bij
    (fun e he =>
      ⟨e.val, (Finset.mem_filter.mp he).2.1⟩)
    ?hmem ?hinj ?hsurj ?hterm
  · intro e he
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_attach _ _, by
      have htail := (Finset.mem_filter.mp he).2.2
      simpa only [emptyActiveEdge_val] using! htail⟩
  · intro e₁ _ e₂ _ heq
    apply Subtype.ext
    exact congrArg
      (fun x : {x : Edge V // x ∈ I.edges} => (x : Edge V)) heq
  · intro e he
    rw [Finset.mem_filter] at he
    refine ⟨emptyActiveEdge e.val, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨Finset.mem_attach _ _, by
        constructor
        · simpa only [emptyActiveEdge_val] using e.property
        · simpa only [emptyActiveEdge_val] using he.2⟩
    · apply Subtype.ext
      rw [emptyActiveEdge_val]
  · intro e _
    have heq : e = emptyActiveEdge e.val := by
      apply Subtype.ext
      rw [emptyActiveEdge_val]
    cases heq
    rfl

/--
Recursive support-fiber form: over a fixed support `I`, each admissible first
edge contributes the tail branch integral after that first edge.
-/
theorem supportContribution_eq_sum_support_edges_filter_tail_branchIntegralAux
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum
        (I.edges.attach.filter
          (fun e =>
            (data.tail (emptyActiveEdge e.val)).order ∈
              edgeSetOrders (I.edges.erase e.val)))
        (fun e => ∫ t in 0..(1 : ℝ),
          (data.tail (emptyActiveEdge e.val)).branchIntegralAux t
            ((data.extension (emptyActiveEdge e.val)).extension.extendParam
              emptyParam t)
            (partialDeriv e.val ρ)) := by
  rw [data.supportContribution_eq_sum_support_edges_filter_tail_order I ρ]
  apply Finset.sum_congr rfl
  intro e _
  rw [data.growthOrder_eq (emptyActiveEdge e.val)]
  simpa only [emptyActiveEdge_val] using!
    TerminalGrowth.cons_orderedContribution_eq_integral_tail_branchIntegralAux_emptyStart
      (data.extension (emptyActiveEdge e.val))
      (data.tail (emptyActiveEdge e.val)) ρ

/--
Full empty-start recursive form after regrouping by terminal support: the
selected terminal branch sum is a support-indexed sum of tail branch integrals.
-/
theorem branchIntegral_empty_eq_sum_support_edges_filter_tail_branchIntegralAux
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I =>
          Finset.sum
            (I.edges.attach.filter
              (fun e =>
                (data.tail (emptyActiveEdge e.val)).order ∈
                  edgeSetOrders (I.edges.erase e.val)))
            (fun e => ∫ t in 0..(1 : ℝ),
              (data.tail (emptyActiveEdge e.val)).branchIntegralAux t
                ((data.extension (emptyActiveEdge e.val)).extension.extendParam
                  emptyParam t)
                (partialDeriv e.val ρ))) := by
  rw [data.branchIntegral_empty_eq_sum_supportContribution ρ]
  apply Finset.sum_congr rfl
  intro I _
  rw [data.supportContribution_eq_sum_support_edges_filter_tail_branchIntegralAux
    I ρ]

/-- The first edge of a selected terminal branch lies in its support fiber. -/
theorem growth_first_mem_support_edges_of_support_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    e.val ∈ I.edges :=
  ((data.growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart e I).mp
    hsupport).1

/--
The tail of a selected terminal branch over support `I` is a canonical ordering
of `I.edges` with the first edge erased.
-/
theorem growth_tail_order_mem_edgeSetOrders_support_erase_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (data.tail e).order ∈ edgeSetOrders (I.edges.erase e.val) :=
  ((data.growth_support_eq_iff_first_mem_and_tail_order_mem_emptyStart e I).mp
    hsupport).2

/--
Over a fixed support fiber, the tail branch has exactly the number of edges
left after erasing the selected first edge.
-/
theorem growth_tail_order_length_eq_card_support_erase_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (data.tail e).order.length = (I.edges.erase e.val).card :=
  length_eq_card_of_mem_edgeSetOrders
    (data.growth_tail_order_mem_edgeSetOrders_support_erase_emptyStart e
      hsupport)

/--
A selected terminal branch lying over support `I` carries a canonical ordering
of the edge set `I.edges`.
-/
theorem growth_order_mem_edgeSetOrders_of_support_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (e.val :: (data.tail e).order) ∈ edgeSetOrders I.edges := by
  rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
  exact ⟨
    (data.growth_support_eq_iff_order_toFinset_eq_emptyStart e I).mp
      hsupport,
    data.growth_order_nodup e⟩

/--
The selected first-edge/tail order has length equal to the cardinality of its
support edge set.
-/
theorem growth_order_length_eq_card_support_edges_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    (e.val :: (data.tail e).order).length = I.edges.card :=
  length_eq_card_of_mem_edgeSetOrders
    (data.growth_order_mem_edgeSetOrders_of_support_eq_emptyStart e
      hsupport)

/--
The packaged first-edge/tail sector of a selected terminal branch over `I` is
one of the canonical orderings of `I.edges`.
-/
theorem growthOrderTail_order_mem_edgeSetOrders_of_support_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    ((data.growthOrderTail e).1.val :: (data.growthOrderTail e).2) ∈
      edgeSetOrders I.edges := by
  rw [data.growthOrderTail_order e]
  exact data.growth_order_mem_edgeSetOrders_of_support_eq_emptyStart e
    hsupport

/--
The selected terminal order of a branch over support `I` is one of the
canonical orderings of `I.edges`.
-/
theorem growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    {I : ForestIndex V} (hsupport : (data.growth e).support = I) :
    data.growthOrder e ∈ edgeSetOrders I.edges :=
  data.growthOrderTail_order_mem_edgeSetOrders_of_support_eq_emptyStart e
    hsupport

/--
A support contribution splits further into fixed ordered-sector fibers.
-/
theorem supportContribution_eq_sum_supportOrderContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    data.supportContribution I ρ =
      Finset.sum (edgeSetOrders I.edges)
        (fun order => data.supportOrderContribution I order ρ) := by
  classical
  rw [data.supportContribution_def I ρ]
  have hmap :
      ∀ e ∈ (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I),
        data.growthOrder e ∈ edgeSetOrders I.edges := by
    intro e he
    exact data.growthOrder_mem_edgeSetOrders_of_support_eq_emptyStart e
      (Finset.mem_filter.mp he).2
  have hfiber :=
    Finset.sum_fiberwise_of_maps_to
      (s := (Forest.empty V).activeEdges.attach.filter
        (fun e => (data.growth e).support = I))
      (t := edgeSetOrders I.edges)
      (g := fun e => data.growthOrder e)
      hmap
      (fun e => (data.growth e).terminal.orderedContribution
        (data.growthOrder e) ρ)
  rw [← hfiber]
  apply Finset.sum_congr rfl
  intro order _
  rw [data.supportOrderContribution_def I order ρ]
  have hfilter :
      ((Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I)).filter
          (fun e => data.growthOrder e = order) =
        (Forest.empty V).activeEdges.attach.filter
          (fun e => (data.growth e).support = I ∧
            data.growthOrder e = order) := by
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

/--
The full empty-start terminal branch sum is indexed by support and then by one
of the canonical ordered sectors of that support.
-/
theorem branchIntegral_empty_eq_sum_supportOrderContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order => data.supportOrderContribution I order ρ)) := by
  rw [data.branchIntegral_empty_eq_sum_supportContribution ρ]
  apply Finset.sum_congr rfl
  intro I _
  rw [data.supportContribution_eq_sum_supportOrderContribution I ρ]

end ActiveTerminalBranchData

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
