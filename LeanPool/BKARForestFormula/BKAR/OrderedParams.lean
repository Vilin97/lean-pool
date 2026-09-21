/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedSimplex

/-! # Parameter transport along ordered growths

Transports simplex parameter lists along an ordered forest growth: `params`
assembles the edge parameters of the grown forest from a list of
interpolation times, and the lemmas locate the resulting values in `[0, 1]`
and compare them under the ordered-simplex constraints.  This is the
parameter bookkeeping for the nested integrals in the ordered expansion of
the BKAR forest interpolation formula (see `BKAR.Formula`).
-/

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace EdgeExtension

variable {F F' : Forest V} {e : Edge V}

theorem extendParam_mem_Icc (h : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hs : 0 ≤ s ∧ s ≤ 1) (e' : F'.EdgeParam) :
    0 ≤ h.extendParam u s e' ∧ h.extendParam u s e' ≤ 1 := by
  by_cases he' : e'.val = e
  · rw [extendParam, dite_eq_left he']
    exact hs
  · rw [extendParam, dite_eq_right he']
    exact hu ⟨e'.val, h.mem_old_of_mem_of_ne e'.property he'⟩

theorem le_extendParam_of_le (h : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) {s top : ℝ}
    (hst : s ≤ top) (hu : ∀ e : F.EdgeParam, top ≤ u e)
    (e' : F'.EdgeParam) :
    s ≤ h.extendParam u s e' :=
  h.le_extendParam u (fun e => hst.trans (hu e)) e'

end EdgeExtension

namespace OrderedGrowth

variable {F G : Forest V} {e : Edge V} {order : List (Edge V)}

/--
Extend a starting forest parameter through an ordered growth certificate,
reading newly added edge parameters from a list in growth order.

If the list is shorter than the order, the missing new parameters are filled
with `0`; extra parameters are ignored once the growth terminates.
-/
def params {F G : Forest V} {order : List (Edge V)}
    (h : OrderedGrowth F order G) :
    (F.EdgeParam → ℝ) → List ℝ → G.EdgeParam → ℝ :=
  match h with
  | nil _ => fun u _ => u
  | cons step tail => fun u ts =>
      match ts with
      | [] => tail.params (step.extendParam u 0) []
      | t :: ts => tail.params (step.extendParam u t) ts

@[simp]
theorem params_nil (F : Forest V) (u : F.EdgeParam → ℝ) (ts : List ℝ) :
    (OrderedGrowth.nil F).params u ts = u :=
  rfl

@[simp]
theorem params_cons_nil {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ) :
    (OrderedGrowth.cons step tail).params u [] =
      tail.params (step.extendParam u 0) [] :=
  rfl

@[simp]
theorem params_cons_cons {F F' G : Forest V} {e : Edge V}
    {order : List (Edge V)} (step : EdgeExtension F F' e)
    (tail : OrderedGrowth F' order G) (u : F.EdgeParam → ℝ)
    (t : ℝ) (ts : List ℝ) :
    (OrderedGrowth.cons step tail).params u (t :: ts) =
      tail.params (step.extendParam u t) ts :=
  rfl

theorem params_mem_Icc (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ)
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hts : ∀ t ∈ ts, 0 ≤ t ∧ t ≤ 1) :
    ∀ e : G.EdgeParam, 0 ≤ h.params u ts e ∧ h.params u ts e ≤ 1 := by
  induction h generalizing ts with
  | nil F =>
      intro e
      exact hu e
  | cons step tail ih =>
      cases ts with
      | nil =>
          exact ih (step.extendParam u 0) []
            (fun e => step.extendParam_mem_Icc u hu ⟨le_rfl, zero_le_one⟩ e)
            (fun _ ht => by
              cases ht)
      | cons t ts =>
          exact ih (step.extendParam u t) ts
            (fun e => step.extendParam_mem_Icc u hu
              (hts t (by rw [List.mem_cons]; exact Or.inl rfl)) e)
            (fun s hs => hts s (by rw [List.mem_cons]; exact Or.inr hs))

theorem params_mem_Icc_of_orderedSimplexParams (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) {top : ℝ} {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (htop : top ≤ 1) (hts : OrderedSimplexParams top ts) :
    ∀ e : G.EdgeParam, 0 ≤ h.params u ts e ∧ h.params u ts e ≤ 1 :=
  h.params_mem_Icc u ts hu (fun _ ht =>
    ⟨OrderedSimplexParams.nonneg_of_mem hts ht,
      (OrderedSimplexParams.le_top_of_mem hts ht).trans htop⟩)

theorem params_mem_Icc_of_orderedSimplexParams_one
    (h : OrderedGrowth F order G) (u : F.EdgeParam → ℝ)
    {ts : List ℝ}
    (hu : ∀ e : F.EdgeParam, 0 ≤ u e ∧ u e ≤ 1)
    (hts : OrderedSimplexParams 1 ts) :
    ∀ e : G.EdgeParam, 0 ≤ h.params u ts e ∧ h.params u ts e ≤ 1 :=
  h.params_mem_Icc_of_orderedSimplexParams u hu le_rfl hts

theorem firstStep_le_extendParam_of_orderedSimplexParams
    (h : OrderedGrowth F (e :: order) G) (u : F.EdgeParam → ℝ)
    {top t : ℝ} {ts : List ℝ}
    (hts : OrderedSimplexParams top (t :: ts))
    (hu : ∀ e : F.EdgeParam, top ≤ u e) :
    ∀ e' : h.tailForest.EdgeParam, t ≤ h.firstStep.extendParam u t e' :=
  h.firstStep.le_extendParam_of_le u hts.head_le_top hu

/-- Ordered-growth parameters preserve every edge parameter already present at the start. -/
theorem params_initial (h : OrderedGrowth F order G)
    (u : F.EdgeParam → ℝ) (ts : List ℝ) (e : F.EdgeParam) :
    h.params u ts ⟨e.val, h.initial_edges_subset_edges e.property⟩ = u e := by
  induction h generalizing ts with
  | nil F =>
      rw [show (⟨e.val, (OrderedGrowth.nil F).initial_edges_subset_edges
          e.property⟩ : F.EdgeParam) = e from Subtype.ext rfl]
      rfl
  | cons step tail ih =>
      cases ts with
      | nil =>
          rw [params_cons_nil]
          rw [show ⟨e.val, (OrderedGrowth.cons step tail).initial_edges_subset_edges
              e.property⟩ =
              ⟨e.val, tail.initial_edges_subset_edges (step.old_mem e.property)⟩
              from Subtype.ext rfl]
          rw [ih (step.extendParam u 0) []
            ⟨e.val, step.old_mem e.property⟩]
          rw [step.extendParam_old u 0 e.property]
      | cons t ts =>
          rw [params_cons_cons]
          rw [show ⟨e.val, (OrderedGrowth.cons step tail).initial_edges_subset_edges
              e.property⟩ =
              ⟨e.val, tail.initial_edges_subset_edges (step.old_mem e.property)⟩
              from Subtype.ext rfl]
          rw [ih (step.extendParam u t) ts
            ⟨e.val, step.old_mem e.property⟩]
          rw [step.extendParam_old u t e.property]

/-- The first simplex parameter is assigned to the first edge of a nonempty growth. -/
theorem params_first (h : OrderedGrowth F (e :: order) G)
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    h.params u (t :: ts) ⟨e, h.mem_edges_of_mem_order
      (by rw [List.mem_cons]; exact Or.inl rfl)⟩ = t := by
  cases h with
  | cons step tail =>
      rw [params_cons_cons]
      rw [show ⟨e, (OrderedGrowth.cons step tail).mem_edges_of_mem_order
          (by rw [List.mem_cons]; exact Or.inl rfl)⟩ =
          ⟨e, tail.initial_edges_subset_edges step.new_mem⟩
          from Subtype.ext rfl]
      rw [tail.params_initial (step.extendParam u t) ts ⟨e, step.new_mem⟩]
      rw [step.extendParam_new u t]

end OrderedGrowth

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
