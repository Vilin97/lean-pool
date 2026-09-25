/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.OrderedRemainder

/-! # Terminal growths

Packages a terminal ordered growth (`TerminalGrowth`): an ordered branch
starting from a given forest together with the certificate that its final
forest has no active edges left.  Defines its branch integrals and the
constructors (`ofActiveEdgesEqEmpty`, `cons`) and unfolding lemmas used to
run the recursion behind the BKAR forest interpolation formula (see
`BKAR.Formula`) to completion.
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
A terminal ordered growth from a starting forest.

This packages one ordered branch together with the certificate that its final
forest has no active edges left.
-/
structure TerminalGrowth (F : Forest V) where
  /-- The list of edges adjoined along the terminal branch. -/
  order : List (Edge V)
  /-- The final forest, which has no active edges. -/
  terminal : Forest V
  /-- The ordered sequence of extensions reaching the terminal forest. -/
  growth : OrderedGrowth F order terminal
  terminal_activeEdges_eq_empty : terminal.activeEdges = ∅

namespace TerminalGrowth

variable {F : Forest V}

/-- The ordered branch integral with an explicit outer bound. -/
def branchIntegralAux (data : TerminalGrowth F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.growth.branchIntegralAux top u ρ

/-- The ordered branch integral over the unit simplex. -/
def branchIntegral (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.branchIntegralAux 1 u ρ

/-- The empty terminal branch attached to a forest with no active edges. -/
def ofActiveEdgesEqEmpty (F : Forest V) (hF : F.activeEdges = ∅) :
    TerminalGrowth F where
  order := []
  terminal := F
  growth := OrderedGrowth.nil F
  terminal_activeEdges_eq_empty := hF

/-- Prepend a chosen active extension to a terminal branch from the extended forest. -/
def cons {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) : TerminalGrowth F where
  order := e :: tail.order
  terminal := tail.terminal
  growth := h.consGrowth tail.growth
  terminal_activeEdges_eq_empty := tail.terminal_activeEdges_eq_empty

theorem branchIntegral_eq_branchIntegralAux_one (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = data.branchIntegralAux 1 u ρ :=
  rfl

theorem ofActiveEdgesEqEmpty_branchIntegralAux
    (F : Forest V) (hF : F.activeEdges = ∅)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (ofActiveEdgesEqEmpty F hF).branchIntegralAux top u ρ =
      ρ (F.standardInterp u) :=
  OrderedGrowth.branchIntegralAux_nil top F u ρ

theorem ofActiveEdgesEqEmpty_branchIntegral
    (F : Forest V) (hF : F.activeEdges = ∅)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (ofActiveEdgesEqEmpty F hF).branchIntegral u ρ =
      ρ (F.standardInterp u) :=
  ofActiveEdgesEqEmpty_branchIntegralAux F hF 1 u ρ

theorem cons_order {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) :
    (cons h tail).order = e :: tail.order :=
  rfl

theorem cons_terminal {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) :
    (cons h tail).terminal = tail.terminal :=
  rfl

theorem cons_growth {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) :
    (cons h tail).growth = h.consGrowth tail.growth :=
  rfl

theorem growth_derivativeOrder (data : TerminalGrowth F) :
    data.growth.derivativeOrder = data.order.reverse :=
  rfl

theorem edges_eq_toFinset_union (data : TerminalGrowth F) :
    data.terminal.edges = data.order.toFinset ∪ F.edges :=
  data.growth.edges_eq_toFinset_union

/-- The finite forest index grown by a terminal branch. -/
def support (data : TerminalGrowth F) : ForestIndex V :=
  data.terminal.support

theorem support_edges (data : TerminalGrowth F) :
    data.support.edges = data.terminal.edges :=
  rfl

theorem support_edges_eq_toFinset_union (data : TerminalGrowth F) :
    data.support.edges = data.order.toFinset ∪ F.edges :=
  data.edges_eq_toFinset_union

/--
If a terminal branch carries no growth order, its terminal forest is the
initial forest.
-/
theorem terminal_eq_initial_of_order_eq_nil
    (data : TerminalGrowth F) (horder : data.order = []) :
    data.terminal = F := by
  cases data with
  | mk order terminal growth hterm =>
      dsimp at horder
      cases horder
      cases growth
      rfl

/--
If a terminal branch carries no growth order, its support is the support of
the initial forest.
-/
theorem support_eq_initial_support_of_order_eq_nil
    (data : TerminalGrowth F) (horder : data.order = []) :
    data.support = F.support := by
  rw [support]
  rw [data.terminal_eq_initial_of_order_eq_nil horder]

/--
The branch integral of a terminal growth with empty order is just evaluation at
the initial standard interpolation point.
-/
theorem branchIntegralAux_eq_standardInterp_of_order_eq_nil
    (data : TerminalGrowth F) (horder : data.order = [])
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ = ρ (F.standardInterp u) := by
  cases data with
  | mk order terminal growth hterm =>
      dsimp at horder
      cases horder
      cases growth
      rw [branchIntegralAux, OrderedGrowth.branchIntegralAux_nil]

theorem branchIntegral_eq_standardInterp_of_order_eq_nil
    (data : TerminalGrowth F) (horder : data.order = [])
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = ρ (F.standardInterp u) :=
  data.branchIntegralAux_eq_standardInterp_of_order_eq_nil horder 1 u ρ

theorem edges_eq_toFinset_of_initial_edges_eq_empty
    (data : TerminalGrowth F) (hF : F.edges = ∅) :
    data.terminal.edges = data.order.toFinset := by
  rw [data.edges_eq_toFinset_union, hF]
  rw [Finset.union_empty]

theorem support_edges_eq_toFinset_of_initial_edges_eq_empty
    (data : TerminalGrowth F) (hF : F.edges = ∅) :
    data.support.edges = data.order.toFinset := by
  rw [data.support_edges, data.edges_eq_toFinset_of_initial_edges_eq_empty hF]

theorem terminal_edges_eq_toFinset_emptyStart
    (data : TerminalGrowth (Forest.empty V)) :
    data.terminal.edges = data.order.toFinset :=
  data.edges_eq_toFinset_of_initial_edges_eq_empty (Forest.empty_edges V)

theorem support_edges_eq_toFinset_emptyStart
    (data : TerminalGrowth (Forest.empty V)) :
    data.support.edges = data.order.toFinset :=
  data.support_edges_eq_toFinset_of_initial_edges_eq_empty
    (Forest.empty_edges V)

theorem order_toFinset_subset_edges (data : TerminalGrowth F) :
    data.order.toFinset ⊆ data.terminal.edges :=
  data.growth.order_toFinset_subset_edges

theorem initial_edges_subset_edges (data : TerminalGrowth F) :
    F.edges ⊆ data.terminal.edges :=
  data.growth.initial_edges_subset_edges

theorem mem_edges_of_mem_order (data : TerminalGrowth F) {e : Edge V}
    (he : e ∈ data.order) :
    e ∈ data.terminal.edges :=
  data.growth.mem_edges_of_mem_order he

theorem order_toFinset_disjoint_initial_edges (data : TerminalGrowth F) :
    Disjoint data.order.toFinset F.edges :=
  data.growth.order_toFinset_disjoint_initial_edges

theorem order_nodup (data : TerminalGrowth F) :
    data.order.Nodup :=
  data.growth.order_nodup

theorem order_toFinset_card_eq_length (data : TerminalGrowth F) :
    data.order.toFinset.card = data.order.length :=
  data.growth.order_toFinset_card_eq_length

theorem card_edges_eq (data : TerminalGrowth F) :
    data.terminal.edges.card = F.edges.card + data.order.length :=
  data.growth.card_edges_eq

/--
The recursive form of a terminal branch obtained by prepending one active
extension.
-/
theorem cons_branchIntegralAux_eq_integral_tail_partialDeriv
    {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (cons h tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) :=
  h.consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
    tail.growth top u ρ

/--
Unit-simplex recursive form of
`TerminalGrowth.cons_branchIntegralAux_eq_integral_tail_partialDeriv`.
-/
theorem cons_branchIntegral_eq_integral_tail_partialDeriv
    {e : Edge V} (h : ActiveExtension F e)
    (tail : TerminalGrowth h.forest)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (cons h tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (h.extension.extendParam u t)
          (partialDeriv e ρ) :=
  cons_branchIntegralAux_eq_integral_tail_partialDeriv h tail 1 u ρ

/--
A terminal branch integral in the standard interpolation form used by BKAR
main terms.
-/
theorem branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    (data : TerminalGrowth F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      orderedSimplexIntegralAux top data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.standardInterp (data.growth.params u ts))) := by
  rw [branchIntegralAux, OrderedGrowth.branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top data.order
    (fun ts => data.growth.branchIntegrand_def_standardInterp u ρ ts)

/--
Unit-simplex version of
`TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp`.
-/
theorem branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
    (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ =
      orderedSimplexIntegral data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.standardInterp (data.growth.params u ts))) :=
  data.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    1 u ρ

theorem branchIntegral_emptyStart_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
    (data : TerminalGrowth (Forest.empty V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      orderedSimplexIntegral data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.standardInterp (data.growth.params emptyParam ts))) :=
  data.branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
    emptyParam ρ

/--
The same terminal branch integral, with the final standard interpolation
expressed as the terminal fill-parameter interpolation.
-/
theorem branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
    (data : TerminalGrowth F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegralAux top u ρ =
      orderedSimplexIntegralAux top data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.interpWithFill (data.growth.params u ts) b)) := by
  rw [branchIntegralAux, OrderedGrowth.branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top data.order
    (fun ts =>
      data.growth.branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
        u ρ ts b data.terminal_activeEdges_eq_empty)

/--
Unit-simplex version of
`TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill`.
-/
theorem branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_interpWithFill
    (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegral u ρ =
      orderedSimplexIntegral data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.interpWithFill (data.growth.params u ts) b)) :=
  data.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
    1 u ρ b

end TerminalGrowth

/--
Terminal branch data chosen independently for each active edge of a forest.

For each active edge, this chooses a one-edge active extension and a terminal
ordered tail branch from the extended forest.
-/
structure ActiveTerminalBranchData (F : Forest V) where
  /-- The first extension chosen for each active edge. -/
  extension : ∀ e : {e // e ∈ F.activeEdges}, ActiveExtension F e.val
  /-- The terminal ordered branch following each chosen first extension. -/
  tail :
    ∀ e : {e // e ∈ F.activeEdges},
      TerminalGrowth (extension e).forest

namespace ActiveTerminalBranchData

variable {F : Forest V}

/-- Forget terminality, retaining the active-branch data underneath. -/
def branchData (data : ActiveTerminalBranchData F) : ActiveBranchData F where
  extension := data.extension
  order := fun e => (data.tail e).order
  terminal := fun e => (data.tail e).terminal
  tail := fun e => (data.tail e).growth

/-- The full terminal branch selected over one active edge. -/
def growth (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) : TerminalGrowth F :=
  TerminalGrowth.cons (data.extension e) (data.tail e)

/-- The finite active-edge sum of terminal branch integrals with an explicit bound. -/
def branchIntegralAux (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.branchData.branchIntegralAux top u ρ

/-- The finite active-edge sum of terminal branch integrals over the unit simplex. -/
def branchIntegral (data : ActiveTerminalBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.branchIntegralAux 1 u ρ

/--
The active-terminal branch data whose selected branch over each active edge
stops after the first extension.
-/
def singleton
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    ActiveTerminalBranchData F where
  extension := extensions
  tail := fun e => TerminalGrowth.ofActiveEdgesEqEmpty
    (extensions e).forest (hterm e)

theorem branchData_terminal_activeEdges_eq_empty
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.branchData.terminal e).activeEdges = ∅ :=
  (data.tail e).terminal_activeEdges_eq_empty

theorem singleton_branchData
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions hterm).branchData =
      ActiveBranchData.singleton extensions :=
  rfl

theorem branchData_growth (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    data.branchData.growth e = (data.growth e).growth :=
  rfl

theorem growth_order (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).order = e.val :: (data.tail e).order :=
  rfl

theorem growth_terminal (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).terminal = (data.tail e).terminal :=
  rfl

/--
If the selected tail after an active edge has empty order, then the full
branch support is just the support of the one-edge extension.
-/
theorem growth_support_eq_extension_support_of_tail_order_eq_nil
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (htail : (data.tail e).order = []) :
    (data.growth e).support = (data.extension e).forest.support := by
  change (data.tail e).support = (data.extension e).forest.support
  exact (data.tail e).support_eq_initial_support_of_order_eq_nil htail

/--
If the selected tail after an active edge has empty order, terminality of the
tail says that the one-edge extension is already terminal.
-/
theorem extension_activeEdges_eq_empty_of_tail_order_eq_nil
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (htail : (data.tail e).order = []) :
    (data.extension e).forest.activeEdges = ∅ := by
  rw [← (data.tail e).terminal_eq_initial_of_order_eq_nil htail]
  exact (data.tail e).terminal_activeEdges_eq_empty

theorem growth_growth (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).growth =
      (data.extension e).consGrowth (data.tail e).growth :=
  rfl

theorem growth_derivativeOrder (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    ((data.growth e).growth).derivativeOrder =
      (e.val :: (data.tail e).order).reverse :=
  rfl

theorem growth_edges_eq_toFinset_union (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).terminal.edges =
      (e.val :: (data.tail e).order).toFinset ∪ F.edges :=
  (data.growth e).edges_eq_toFinset_union

theorem growth_support_edges_eq_toFinset_union
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).support.edges =
      (e.val :: (data.tail e).order).toFinset ∪ F.edges :=
  (data.growth e).support_edges_eq_toFinset_union

theorem growth_order_nodup (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (e.val :: (data.tail e).order).Nodup :=
  (data.growth e).order_nodup

theorem growth_card_edges_eq (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).terminal.edges.card =
      F.edges.card + (e.val :: (data.tail e).order).length :=
  (data.growth e).card_edges_eq

theorem singleton_growth_growth_eq_singletonGrowth
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (e : {e // e ∈ F.activeEdges}) :
    ((singleton extensions hterm).growth e).growth =
      (extensions e).singletonGrowth :=
  rfl

theorem branchIntegral_eq_branchIntegralAux_one
    (data : ActiveTerminalBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = data.branchIntegralAux 1 u ρ :=
  rfl

theorem singleton_branchIntegralAux_eq_activeBranchData_singleton
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegralAux top u ρ =
      (ActiveBranchData.singleton extensions).branchIntegralAux top u ρ :=
  rfl

theorem singleton_branchIntegral_eq_activeBranchData_singleton
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegral u ρ =
      (ActiveBranchData.singleton extensions).branchIntegral u ρ :=
  rfl

/--
The active-terminal branch sum is the sum of the selected full terminal branch
integrals.
-/
theorem branchIntegralAux_eq_sum_growth_branchIntegralAux
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => (data.growth e).branchIntegralAux top u ρ) :=
  rfl

/--
Recursive form of the active-terminal branch sum after the first active edge.
-/
theorem branchIntegralAux_eq_sum_integrals_tail_partialDeriv
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val ρ)) :=
  data.branchData.branchIntegralAux_eq_sum_integrals_tail_partialDeriv
    top u ρ

/--
The active-terminal branch sum in the standard interpolation form used by the
ordered BKAR main terms.
-/
theorem branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: (data.tail e).order)
          (fun ts => mixedPartialList (e.val :: (data.tail e).order).reverse ρ
            ((data.tail e).terminal.standardInterp
              ((data.growth e).growth.params u ts)))) :=
  data.branchData.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    top u ρ

/--
Terminal fill-parameter form of the active-terminal branch sum.
-/
theorem branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
    (data : ActiveTerminalBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: (data.tail e).order)
          (fun ts => mixedPartialList (e.val :: (data.tail e).order).reverse ρ
            ((data.tail e).terminal.interpWithFill
              ((data.growth e).growth.params u ts) b))) :=
  data.branchData.branchIntegralAux_eq_simplexSum_of_emptyActiveEdges
    data.branchData_terminal_activeEdges_eq_empty top u ρ b

/--
Terminal singleton active-terminal branches in the standard
terminal-interpolation form.
-/
theorem singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (es : List (Edge V)) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegralAux top u
        (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) :=
  ActiveBranchData.singleton_branchIntegralAux_eq_standardIntegralSum_of_emptyActiveEdges
    extensions es top u ρ hterm

/--
Terminal singleton active-terminal branches in the terminal fill-parameter form.
-/
theorem singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_interpWithFill
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (es : List (Edge V)) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegralAux top u
        (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) :=
  ActiveBranchData.singleton_branchIntegralAux_eq_integralSum_mixedPartial_of_emptyActiveEdges
    extensions es top u ρ hterm

/--
Unit-simplex standard-interpolation version of
The standard-interpolation identity for `ActiveTerminalBranchData.singleton_branchIntegralAux`.
-/
theorem singleton_branchIntegral_eq_sum_integrals_mixedPartialList_standardInterp
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (es : List (Edge V))
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegral u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) :=
  singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp
    extensions hterm es 1 u ρ

end ActiveTerminalBranchData

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
