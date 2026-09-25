/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.Orders

/-! # Branch integrals and ordered contributions from the empty forest

For ordered growths starting at the empty forest, identifies the
recursion's branch integrals with the intrinsic ordered contributions of
the grown forest, and records how the growth order and its tail sit inside
the enumerations of the final edge set.  This links the recursion's
bookkeeping to the per-order sector integrals of the BKAR forest
interpolation formula (see `BKAR.Formula`).
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace OrderedGrowth

variable {F G : Forest V} {order : List (Edge V)}

/--
An ordered growth from an initially empty edge set carries one of the canonical
edge orderings of its terminal forest.
-/
theorem order_mem_edgeOrders_of_initial_edges_eq_empty
    (h : OrderedGrowth F order G) (hF : F.edges = ∅) :
    order ∈ G.edgeOrders := by
  rw [G.mem_edgeOrders_iff_toFinset_eq_and_nodup]
  constructor
  · rw [h.edges_eq_toFinset_union, hF]
    rw [Finset.union_empty]
  · exact h.order_nodup

theorem order_mem_edgeOrders_emptyStart
    (h : OrderedGrowth (Forest.empty V) order G) :
    order ∈ G.edgeOrders :=
  h.order_mem_edgeOrders_of_initial_edges_eq_empty (Forest.empty_edges V)

/--
If an ordered growth starts from an empty edge set and has a first edge, then
the remaining growth order is a canonical ordering of the terminal edge set
with that first edge erased.
-/
theorem tail_order_mem_edgeSetOrders_erase_of_initial_edges_eq_empty
    {e : Edge V} (h : OrderedGrowth F (e :: order) G) (hF : F.edges = ∅) :
    order ∈ edgeSetOrders (G.edges.erase e) :=
  ((cons_mem_edgeOrders_iff G).mp
    (h.order_mem_edgeOrders_of_initial_edges_eq_empty hF)).2

theorem tail_order_mem_edgeSetOrders_erase_emptyStart
    {e : Edge V} (h : OrderedGrowth (Forest.empty V) (e :: order) G) :
    order ∈ edgeSetOrders (G.edges.erase e) :=
  h.tail_order_mem_edgeSetOrders_erase_of_initial_edges_eq_empty
    (Forest.empty_edges V)

end OrderedGrowth

namespace TerminalGrowth

variable {F : Forest V}

/--
A terminal branch grown from an initially empty edge set carries one of the
canonical edge orderings of its terminal forest.
-/
theorem order_mem_edgeOrders_of_initial_edges_eq_empty
    (data : TerminalGrowth F) (hF : F.edges = ∅) :
    data.order ∈ data.terminal.edgeOrders := by
  rw [data.terminal.mem_edgeOrders_iff_toFinset_eq_and_nodup]
  exact ⟨(data.edges_eq_toFinset_of_initial_edges_eq_empty hF).symm,
    data.order_nodup⟩

theorem order_mem_edgeOrders_emptyStart
    (data : TerminalGrowth (Forest.empty V)) :
    data.order ∈ data.terminal.edgeOrders :=
  data.order_mem_edgeOrders_of_initial_edges_eq_empty (Forest.empty_edges V)

/--
If an empty-start terminal branch order is nonempty, its tail is one of the
canonical orders of the terminal edge set with the first edge erased.
-/
theorem tail_order_mem_edgeSetOrders_erase_of_order_eq_cons
    (data : TerminalGrowth (Forest.empty V))
    {e : Edge V} {order : List (Edge V)}
    (horder : data.order = e :: order) :
    order ∈ edgeSetOrders (data.terminal.edges.erase e) := by
  have hmem : e :: order ∈ data.terminal.edgeOrders := by
    rw [← horder]
    exact data.order_mem_edgeOrders_emptyStart
  exact ((cons_mem_edgeOrders_iff data.terminal).mp hmem).2

/--
A nonempty empty-start terminal branch gives a member of the terminal
first-edge/tail-order indexing set.
-/
theorem orderTail_mem_edgeSetOrderTails_of_order_eq_cons
    (data : TerminalGrowth (Forest.empty V))
    {e : Edge V} {order : List (Edge V)}
    (horder : data.order = e :: order) :
    ∃ he : e ∈ data.terminal.edges,
      (⟨⟨e, he⟩, order⟩ :
        Σ _ : {x : Edge V // x ∈ data.terminal.edges},
          List (Edge V)) ∈
          edgeSetOrderTails data.terminal.edges := by
  have hmem : e :: order ∈ data.terminal.edgeOrders := by
    rw [← horder]
    exact data.order_mem_edgeOrders_emptyStart
  have hsplit := (cons_mem_edgeOrders_iff data.terminal).mp hmem
  refine ⟨hsplit.1, ?_⟩
  rw [mem_edgeSetOrderTails_iff]
  exact hsplit.2

/--
An empty-start terminal branch integral is the canonical ordered-sector
contribution of its terminal forest and terminal edge order.
-/
theorem branchIntegral_emptyStart_eq_orderedContribution
    (data : TerminalGrowth (Forest.empty V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      data.terminal.orderedContribution data.order ρ := by
  rw [branchIntegral_emptyStart_eq_orderedSimplexIntegral_mixedPartialList_standardInterp]
  rw [orderedContribution]
  exact orderedSimplexIntegral_congr_of_length (fun ts hlen => by
    rw [data.growth.params_emptyStart_eq_paramsOfOrder_of_length hlen])

/--
A terminal tail integral at a nonempty recursion node can be read as the
ordered simplex for the accumulated prefix followed by the tail order.
-/
theorem branchIntegralAux_mixedPartial_eq_simplexIntegralAux_paramsOfOrder_append
    (data : TerminalGrowth F) (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top (F.paramsOfOrder pref prefixTs)
        (mixedPartialList pref.reverse ρ) =
      orderedSimplexIntegralAux top data.order
        (fun ts => mixedPartialList (pref ++ data.order).reverse ρ
          (data.terminal.standardInterp
            (data.terminal.paramsOfOrder (pref ++ data.order)
              (prefixTs ++ ts)))) := by
  rw [data.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp]
  exact orderedSimplexIntegralAux_congr_of_length top data.order
    (fun ts hlen => by
      rw [data.growth.params_eq_paramsOfOrder_append_of_length
        pref prefixTs hpref hprefixTs hlen]
      rw [List.reverse_append, mixedPartialList_append])

/--
For a terminal branch obtained by first adding `e` from the empty forest, the
corresponding ordered-sector contribution is exactly the recursive tail
integral after that first edge.
-/
theorem cons_orderedContribution_eq_integral_tail_branchIntegralAux_emptyStart
    {e : Edge V} (h : ActiveExtension (Forest.empty V) e)
    (tail : TerminalGrowth h.forest) (ρ : (Edge V → ℝ) → ℝ) :
    tail.terminal.orderedContribution (e :: tail.order) ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam emptyParam t)
          (partialDeriv e ρ) := by
  change
    (TerminalGrowth.cons h tail).terminal.orderedContribution
        (TerminalGrowth.cons h tail).order ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam emptyParam t)
          (partialDeriv e ρ)
  rw [← (TerminalGrowth.cons h tail).branchIntegral_emptyStart_eq_orderedContribution ρ]
  rw [TerminalGrowth.cons_branchIntegral_eq_integral_tail_partialDeriv
    h tail emptyParam ρ]

end TerminalGrowth

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
