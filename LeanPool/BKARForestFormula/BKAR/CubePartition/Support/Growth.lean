/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.Branches

/-! # Growth-order bookkeeping for terminal branches

For the terminal branch data of the recursion started at the empty forest,
records how the growth order relates to the final support: the order
enumerates the support edge set, its tail enumerates the support minus the
first edge, and `growthOrderTail` packages this decomposition.  These facts
index the regrouping of branch contributions by support and order in the
BKAR forest interpolation formula (see `BKAR.Formula`).
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ActiveTerminalBranchData

variable {F : Forest V}

/--
Every full branch selected by active-terminal branch data from an initially
empty edge set carries a canonical ordering of its terminal forest.
-/
theorem growth_order_mem_edgeOrders_of_initial_edges_eq_empty
    (data : ActiveTerminalBranchData F) (hF : F.edges = ∅)
    (e : {e // e ∈ F.activeEdges}) :
    (e.val :: (data.tail e).order) ∈ (data.growth e).terminal.edgeOrders :=
  (data.growth e).order_mem_edgeOrders_of_initial_edges_eq_empty hF

theorem growth_order_mem_edgeOrders_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (e.val :: (data.tail e).order) ∈ (data.growth e).terminal.edgeOrders :=
  data.growth_order_mem_edgeOrders_of_initial_edges_eq_empty
    (Forest.empty_edges V) e

/--
For an active-terminal branch from the empty forest, the terminal edge set is
exactly the edge set represented by the selected first edge and tail order.
-/
theorem growth_terminal_edges_eq_toFinset_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growth e).terminal.edges =
      (e.val :: (data.tail e).order).toFinset :=
  (data.growth e).terminal_edges_eq_toFinset_emptyStart

/--
The support index of an active-terminal branch from the empty forest carries
the same edge set as its selected first-edge/tail order.
-/
theorem growth_support_edges_eq_toFinset_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growth e).support.edges =
      (e.val :: (data.tail e).order).toFinset :=
  (data.growth e).support_edges_eq_toFinset_emptyStart

theorem growth_order_toFinset_eq_terminal_edges_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (e.val :: (data.tail e).order).toFinset =
      (data.growth e).terminal.edges :=
  (data.growth_terminal_edges_eq_toFinset_emptyStart e).symm

/--
Every active-terminal branch selected from the empty forest has a nonempty
terminal edge set: it contains the first active edge of the branch.
-/
theorem growth_terminal_edges_nonempty_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growth e).terminal.edges.Nonempty := by
  have hsplit :=
    (cons_mem_edgeOrders_iff (data.growth e).terminal).mp
      (data.growth_order_mem_edgeOrders_emptyStart e)
  exact ⟨e.val, hsplit.1⟩

/--
The tail order selected after the first active edge of an empty-start
active-terminal branch is a canonical ordering of the terminal edge set with
that first edge erased.
-/
theorem tail_order_mem_edgeSetOrders_terminal_erase_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.tail e).order ∈
      edgeSetOrders ((data.growth e).terminal.edges.erase e.val) :=
  ((cons_mem_edgeOrders_iff (data.growth e).terminal).mp
    (data.growth_order_mem_edgeOrders_emptyStart e)).2

/--
Each selected active-terminal branch from the empty forest determines a member
of the terminal first-edge/tail-order indexing set.
-/
theorem growth_orderTail_mem_edgeSetOrderTails_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    ∃ he : e.val ∈ (data.growth e).terminal.edges,
      (⟨⟨e.val, he⟩, (data.tail e).order⟩ :
        Σ _ : {x : Edge V // x ∈ (data.growth e).terminal.edges},
          List (Edge V)) ∈
        edgeSetOrderTails (data.growth e).terminal.edges := by
  have hsplit :=
    (cons_mem_edgeOrders_iff (data.growth e).terminal).mp
      (data.growth_order_mem_edgeOrders_emptyStart e)
  refine ⟨hsplit.1, ?_⟩
  rw [mem_edgeSetOrderTails_iff]
  exact hsplit.2

/--
The terminal first-edge/tail sector selected by one active-terminal branch
from the empty forest.
-/
def growthOrderTail
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    Σ _ : {x : Edge V // x ∈ (data.growth e).terminal.edges},
      List (Edge V) :=
  ⟨⟨e.val,
    ((cons_mem_edgeOrders_iff (data.growth e).terminal).mp
      (data.growth_order_mem_edgeOrders_emptyStart e)).1⟩,
    (data.tail e).order⟩

theorem growthOrderTail_first
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growthOrderTail e).1.val = e.val :=
  rfl

theorem growthOrderTail_tail
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growthOrderTail e).2 = (data.tail e).order :=
  rfl

theorem growthOrderTail_order
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    (data.growthOrderTail e).1.val :: (data.growthOrderTail e).2 =
      e.val :: (data.tail e).order :=
  rfl

/-- The selected terminal edge order of one active-terminal branch. -/
def growthOrder
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) : List (Edge V) :=
  (data.growthOrderTail e).1.val :: (data.growthOrderTail e).2

theorem growthOrder_eq
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    data.growthOrder e = e.val :: (data.tail e).order :=
  rfl

theorem growthOrderTail_mem_edgeSetOrderTails_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges}) :
    data.growthOrderTail e ∈
      edgeSetOrderTails (data.growth e).terminal.edges := by
  rw [growthOrderTail, mem_edgeSetOrderTails_iff]
  exact ((cons_mem_edgeOrders_iff (data.growth e).terminal).mp
    (data.growth_order_mem_edgeOrders_emptyStart e)).2

/--
Each selected terminal forest admits the same first-edge/tail ordered-sector
decomposition as any nonempty forest.
-/
theorem growth_terminal_orderedSectorSum_eq_sum_orderTails_emptyStart
    (data : ActiveTerminalBranchData (Forest.empty V))
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (ρ : (Edge V → ℝ) → ℝ) :
    (data.growth e).terminal.orderedSectorSum ρ =
      Finset.sum (edgeSetOrderTails (data.growth e).terminal.edges)
        (fun x => (data.growth e).terminal.orderedContribution
          (x.1.val :: x.2) ρ) :=
  (data.growth e).terminal.orderedSectorSum_eq_sum_orderTails_of_edges_nonempty
    (data.growth_terminal_edges_nonempty_emptyStart e) ρ

/--
The active-terminal branch sum from the empty forest is a finite sum of
canonical ordered-sector contributions, one for each selected terminal branch.
-/
theorem branchIntegral_empty_eq_sum_orderedContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => (data.growth e).terminal.orderedContribution
          (e.val :: (data.tail e).order) ρ) := by
  rw [branchIntegral_eq_branchIntegralAux_one]
  rw [branchIntegralAux_eq_sum_growth_branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  exact (data.growth e).branchIntegral_emptyStart_eq_orderedContribution ρ

/--
Version of `ActiveTerminalBranchData.branchIntegral_empty_eq_sum_orderedContribution`
using the packaged terminal edge order.
-/
theorem branchIntegral_empty_eq_sum_growthOrderContribution
    (data : ActiveTerminalBranchData (Forest.empty V))
    (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => (data.growth e).terminal.orderedContribution
          (data.growthOrder e) ρ) := by
  rw [data.branchIntegral_empty_eq_sum_orderedContribution ρ]
  apply Finset.sum_congr rfl
  intro e _
  rw [data.growthOrder_eq e]

end ActiveTerminalBranchData

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
