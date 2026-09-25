/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.OrderedParams

/-! # Branch integrals along ordered growths

For an ordered growth of forests, defines the accumulated derivative order
(`derivativeOrder`), the interpolation point of a branch (`branchPoint`),
the branch integrand obtained by applying the corresponding mixed partials,
and the nested branch integrals `branchIntegralAux` and `branchIntegral`
over the ordered simplex.  These are the basic objects manipulated by the
recursion proving the BKAR forest interpolation formula (see
`BKAR.Formula`).
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace OrderedGrowth

variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

/--
Derivative order accumulated by following a growth list from left to right.

The one-step recursion conses each new derivative onto the front, so the final
mixed-partial list is the reverse of the growth order.
-/
def derivativeOrder (_h : OrderedGrowth F order G) : List (Edge V) :=
  order.reverse

/--
The terminal BKAR interpolation point attached to one ordered branch and a
list of simplex parameters.
-/
def branchPoint (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) : Edge V → ℝ :=
  G.standardInterp (h.params u ts)

/--
The terminal integrand attached to one ordered forest-growth branch.
-/
def branchIntegrand (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    List ℝ → ℝ :=
  fun ts => mixedPartialList h.derivativeOrder ρ (h.branchPoint u ts)

/--
The ordered-simplex integral with an explicit outer bound attached to one
ordered forest-growth branch.
-/
def branchIntegralAux (top : ℝ) (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  orderedSimplexIntegralAux top order (h.branchIntegrand u ρ)

/--
The ordered-simplex integral attached to one ordered forest-growth branch.
-/
def branchIntegral (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  h.branchIntegralAux 1 u ρ

theorem derivativeOrder_def (h : OrderedGrowth F order G) :
    h.derivativeOrder = order.reverse :=
  rfl

theorem branchPoint_def (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) :
    h.branchPoint u ts = G.standardInterp (h.params u ts) :=
  rfl

/-- A branch point agrees with the starting parameter on every starting edge. -/
theorem branchPoint_initial (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) (e : F.EdgeParam) :
    h.branchPoint u ts e.val = u e := by
  rw [branchPoint_def]
  rw [G.standardInterp_of_mem (h.params u ts)
    (h.initial_edges_subset_edges e.property)]
  exact h.params_initial u ts e

theorem branchPoint_of_initial_mem (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) {e : Edge V} (he : e ∈ F.edges) :
    h.branchPoint u ts e = u ⟨e, he⟩ :=
  h.branchPoint_initial u ts ⟨e, he⟩

/-- The first edge of a nonempty branch receives the first simplex parameter. -/
theorem branchPoint_first (h : OrderedGrowth F (e :: order) G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    h.branchPoint u (t :: ts) e = t := by
  rw [branchPoint_def]
  rw [G.standardInterp_of_mem (h.params u (t :: ts))
    (h.mem_edges_of_mem_order (by rw [List.mem_cons]; exact Or.inl rfl))]
  exact h.params_first u t ts

theorem branchPoint_cons_nil {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ) :
    (OrderedGrowth.cons step tail).branchPoint u [] =
      tail.branchPoint (step.extendParam u 0) [] :=
  rfl

theorem branchPoint_cons_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).branchPoint u (t :: ts) =
      tail.branchPoint (step.extendParam u t) ts :=
  rfl

theorem branchPoint_mem_Icc (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) {top : ℝ} {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (htop : top ≤ 1) (hts : OrderedSimplexParams top ts)
    (e : Edge V) :
    0 ≤ h.branchPoint u ts e ∧ h.branchPoint u ts e ≤ 1 :=
  G.standardInterp_mem_Icc (h.params u ts)
    (h.params_mem_Icc_of_orderedSimplexParams u hu htop hts) e

theorem branchPoint_mem_Icc_one (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hts : OrderedSimplexParams 1 ts) (e : Edge V) :
    0 ≤ h.branchPoint u ts e ∧ h.branchPoint u ts e ≤ 1 :=
  h.branchPoint_mem_Icc u hu le_rfl hts e

theorem branchPoint_eq_interpWithFill_of_activeEdges_eq_empty
    (h : OrderedGrowth F order G) (u : F.EdgeParam → ℝ)
    (ts : List ℝ) (b : ℝ) (hG : G.activeEdges = ∅) :
    h.branchPoint u ts = G.interpWithFill (h.params u ts) b := by
  rw [branchPoint_def, G.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
    (h.params u ts) b hG]

theorem branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    (h : OrderedGrowth F order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) (b : ℝ)
    (hG : G.activeEdges = ∅) :
    h.branchIntegrand u ρ ts =
      mixedPartialList h.derivativeOrder ρ
        (G.interpWithFill (h.params u ts) b) := by
  change mixedPartialList h.derivativeOrder ρ (h.branchPoint u ts) =
    mixedPartialList h.derivativeOrder ρ
      (G.interpWithFill (h.params u ts) b)
  rw [h.branchPoint_eq_interpWithFill_of_activeEdges_eq_empty u ts b hG]

theorem derivativeOrder_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) :
    (OrderedGrowth.cons step tail).derivativeOrder =
      tail.derivativeOrder ++ [e] := by
  rw [derivativeOrder, derivativeOrder, List.reverse_cons]

@[simp]
theorem derivativeOrder_nil (F : Forest V) :
    (OrderedGrowth.nil F).derivativeOrder = [] :=
  rfl

theorem branchIntegrand_def (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) :
    h.branchIntegrand u ρ ts =
      mixedPartialList order.reverse ρ (h.branchPoint u ts) :=
  rfl

theorem branchIntegrand_def_standardInterp (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) :
    h.branchIntegrand u ρ ts =
      mixedPartialList order.reverse ρ (G.standardInterp (h.params u ts)) :=
  rfl

theorem branchIntegrand_congr_branchPoint (h : OrderedGrowth F order G)
    (u v : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpoint : ∀ ts, h.branchPoint u ts = h.branchPoint v ts) :
    h.branchIntegrand u ρ = h.branchIntegrand v ρ := by
  funext ts
  rw [branchIntegrand_def, branchIntegrand_def, hpoint ts]

theorem branchIntegrand_congr (h : OrderedGrowth F order G)
    {u v : F.EdgeParam → ℝ} {ρ σ : (Edge V → ℝ) → ℝ}
    (hfg : ∀ ts, h.branchIntegrand u ρ ts = h.branchIntegrand v σ ts) :
    h.branchIntegrand u ρ = h.branchIntegrand v σ := by
  funext ts
  exact hfg ts

@[simp]
theorem branchIntegrand_nil (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (ts : List ℝ) :
    (OrderedGrowth.nil F).branchIntegrand u ρ ts = ρ (F.standardInterp u) :=
  rfl

@[simp]
theorem branchIntegral_nil (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.nil F).branchIntegral u ρ = ρ (F.standardInterp u) :=
  rfl

theorem branchIntegrand_cons_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts) =
      mixedPartialList (e :: order).reverse ρ
        (G.standardInterp (tail.params (step.extendParam u t) ts)) :=
  rfl

theorem branchIntegrand_cons_cons_eq_tail_partialDeriv
    {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
    (step : EdgeExtension F F' e) (tail : OrderedGrowth F' order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts) =
      tail.branchIntegrand (step.extendParam u t) (partialDeriv e ρ) ts := by
  rw [branchIntegrand_cons_cons, branchIntegrand_def]
  rw [List.reverse_cons, mixedPartialList_append]
  rfl

theorem branchIntegrand_cons_nil_singleton {F F' : Forest V} {e : Edge V}
    (step : EdgeExtension F F' e) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) :
    (OrderedGrowth.cons step (OrderedGrowth.nil F')).branchIntegrand u ρ [t] =
      partialDeriv e ρ (F'.standardInterp (step.extendParam u t)) := by
  rw [branchIntegrand_cons_cons_eq_tail_partialDeriv]
  rfl

@[simp]
theorem branchIntegralAux_nil (top : ℝ) (F : Forest V)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.nil F).branchIntegralAux top u ρ = ρ (F.standardInterp u) :=
  rfl

theorem branchIntegral_eq_branchIntegralAux_one (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    h.branchIntegral u ρ = h.branchIntegralAux 1 u ρ :=
  rfl

theorem branchIntegralAux_congr (top : ℝ) (h : OrderedGrowth F order G)
    {u v : F.EdgeParam → ℝ} {ρ σ : (Edge V → ℝ) → ℝ}
    (hfg : ∀ ts, h.branchIntegrand u ρ ts = h.branchIntegrand v σ ts) :
    h.branchIntegralAux top u ρ = h.branchIntegralAux top v σ := by
  rw [branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top order hfg

theorem branchIntegral_congr (h : OrderedGrowth F order G)
    {u v : F.EdgeParam → ℝ} {ρ σ : (Edge V → ℝ) → ℝ}
    (hfg : ∀ ts, h.branchIntegrand u ρ ts = h.branchIntegrand v σ ts) :
    h.branchIntegral u ρ = h.branchIntegral v σ :=
  h.branchIntegralAux_congr 1 hfg

theorem branchIntegralAux_congr_branchPoint (top : ℝ)
    (h : OrderedGrowth F order G) (u v : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ)
    (hpoint : ∀ ts, h.branchPoint u ts = h.branchPoint v ts) :
    h.branchIntegralAux top u ρ = h.branchIntegralAux top v ρ :=
  h.branchIntegralAux_congr top
    (fun ts => by rw [branchIntegrand_def, branchIntegrand_def, hpoint ts])

theorem branchIntegral_congr_branchPoint (h : OrderedGrowth F order G)
    (u v : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpoint : ∀ ts, h.branchPoint u ts = h.branchPoint v ts) :
    h.branchIntegral u ρ = h.branchIntegral v ρ :=
  h.branchIntegral_congr
    (fun ts => by rw [branchIntegrand_def, branchIntegrand_def, hpoint ts])

theorem branchIntegralAux_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        orderedSimplexIntegralAux t order
          (fun ts =>
            (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts)) :=
  rfl

theorem branchIntegralAux_cons_eq_integral_tail_partialDeriv
    {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
    (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        tail.branchIntegralAux t (step.extendParam u t)
          (partialDeriv e ρ) := by
  rw [branchIntegralAux_cons]
  apply intervalIntegral.integral_congr
  intro t _
  exact orderedSimplexIntegralAux_congr t order
    (fun ts =>
      branchIntegrand_cons_cons_eq_tail_partialDeriv step tail u ρ t ts)

theorem branchIntegralAux_cons_nil_eq_integral_partialDeriv_standardInterp
    {F F' : Forest V} {e : Edge V} (step : EdgeExtension F F' e)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step (OrderedGrowth.nil F')).branchIntegralAux top u ρ =
      ∫ t in 0..top, partialDeriv e ρ
        (F'.standardInterp (step.extendParam u t)) := by
  rw [branchIntegralAux_cons_eq_integral_tail_partialDeriv]
  apply intervalIntegral.integral_congr
  intro t _
  rfl

theorem branchIntegral_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        orderedSimplexIntegralAux t order
          (fun ts =>
            (OrderedGrowth.cons step tail).branchIntegrand u ρ (t :: ts)) :=
  rfl

theorem branchIntegral_cons_eq_integral_tail_partialDeriv
    {F F' G : Forest V} {e : Edge V} {order : List (Edge V)}
    (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step tail).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ),
        tail.branchIntegralAux t (step.extendParam u t)
          (partialDeriv e ρ) :=
  (OrderedGrowth.branchIntegralAux_cons_eq_integral_tail_partialDeriv
    step tail 1 u ρ)

theorem branchIntegral_cons_nil_eq_integral_partialDeriv_standardInterp
    {F F' : Forest V} {e : Edge V} (step : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (OrderedGrowth.cons step (OrderedGrowth.nil F')).branchIntegral u ρ =
      ∫ t in 0..(1 : ℝ), partialDeriv e ρ
        (F'.standardInterp (step.extendParam u t)) :=
  branchIntegralAux_cons_nil_eq_integral_partialDeriv_standardInterp
    step 1 u ρ

end OrderedGrowth

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
