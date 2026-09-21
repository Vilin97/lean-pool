/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedRecursion

/-! # Branch data over the active edges

Defines `ActiveBranchData`: for each active edge of a forest, a chosen
one-edge active extension together with an ordered tail growth from the
extended forest.  Its branch integrals aggregate the per-edge remainder
terms produced by one round of the expansion step, in the form consumed by
the telescoping argument behind the BKAR forest interpolation formula (see
`BKAR.Formula`).
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
Branch data chosen independently for each active edge of a forest.

For each active edge, the data consists of a one-edge active extension and an
ordered tail growth starting from the extended forest.
-/
structure ActiveBranchData (F : Forest V) where
  /-- The chosen one-edge extension for each active edge. -/
  extension : ∀ e : {e // e ∈ F.activeEdges}, ActiveExtension F e.val
  /-- The order of the remaining edges along each chosen branch. -/
  order : ∀ _ : {e // e ∈ F.activeEdges}, List (Edge V)
  /-- The final forest of each chosen branch. -/
  terminal : ∀ _ : {e // e ∈ F.activeEdges}, Forest V
  /-- The ordered growth following the chosen first extension of each branch. -/
  tail :
    ∀ e : {e // e ∈ F.activeEdges},
      OrderedGrowth (extension e).forest (order e) (terminal e)

namespace ActiveBranchData

variable {F : Forest V}

/-- The full ordered branch obtained by prepending the selected active edge. -/
def growth (data : ActiveBranchData F) (e : {e // e ∈ F.activeEdges}) :
    OrderedGrowth F (e.val :: data.order e) (data.terminal e) :=
  (data.extension e).consGrowth (data.tail e)

/-- The finite active-edge sum of branch integrals with an explicit top bound. -/
def branchIntegralAux (data : ActiveBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum F.activeEdges.attach
    fun e => (data.growth e).branchIntegralAux top u ρ

/-- The finite active-edge sum of branch integrals over the unit simplex. -/
def branchIntegral (data : ActiveBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  data.branchIntegralAux 1 u ρ

/--
The active-branch data whose selected branch over each active edge stops after
the first extension.
-/
def singleton
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val) :
    ActiveBranchData F where
  extension := extensions
  order := fun _ => []
  terminal := fun e => (extensions e).forest
  tail := fun e => OrderedGrowth.nil (extensions e).forest

theorem growth_eq_consGrowth (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    data.growth e = (data.extension e).consGrowth (data.tail e) :=
  rfl

theorem growth_firstStep (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).firstStep = (data.extension e).extension :=
  rfl

theorem growth_tailForest (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).tailForest = (data.extension e).forest :=
  rfl

theorem growth_tailGrowth (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).tailGrowth = data.tail e :=
  rfl

theorem growth_firstActiveExtension (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).firstActiveExtension = data.extension e :=
  rfl

theorem growth_derivativeOrder (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges}) :
    (data.growth e).derivativeOrder = (data.order e).reverse ++ [e.val] :=
  OrderedGrowth.derivativeOrder_cons (data.extension e).extension (data.tail e)

theorem growth_branchPoint_first (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (t : ℝ) (ts : List ℝ) :
    (data.growth e).branchPoint u (t :: ts) e.val = t :=
  (data.extension e).consGrowth_branchPoint_first (data.tail e) u t ts

theorem growth_branchPoint_of_initial_mem (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (ts : List ℝ) {e' : Edge V}
    (he' : e' ∈ F.edges) :
    (data.growth e).branchPoint u ts e' = u ⟨e', he'⟩ :=
  (data.extension e).consGrowth_branchPoint_of_initial_mem
    (data.tail e) u ts he'

theorem growth_branchIntegralAux_eq_integral_tail_partialDeriv
    (data : ActiveBranchData F) (e : {e // e ∈ F.activeEdges})
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (data.growth e).branchIntegralAux top u ρ =
      ∫ t in 0..top,
        (data.tail e).branchIntegralAux t
          ((data.extension e).extension.extendParam u t)
          (partialDeriv e.val ρ) :=
  (data.extension e).consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
    (data.tail e) top u ρ

theorem singleton_growth_eq_singletonGrowth
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (e : {e // e ∈ F.activeEdges}) :
    (singleton extensions).growth e = (extensions e).singletonGrowth :=
  rfl

theorem branchIntegral_eq_branchIntegralAux_one (data : ActiveBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = data.branchIntegralAux 1 u ρ :=
  rfl

/--
The finite active-edge branch sum is exactly the sum of the recursive tail
integrals obtained after the chosen first active extension.
-/
theorem branchIntegralAux_eq_sum_integrals_tail_partialDeriv
    (data : ActiveBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val ρ)) := by
  rw [branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  exact (data.extension e).consGrowth_branchIntegralAux_eq_integral_tail_partialDeriv
    (data.tail e) top u ρ

/--
Unit-simplex version of
`ActiveBranchData.branchIntegralAux_eq_sum_integrals_tail_partialDeriv`.
-/
theorem branchIntegral_eq_sum_integrals_tail_partialDeriv
    (data : ActiveBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val ρ)) :=
  data.branchIntegralAux_eq_sum_integrals_tail_partialDeriv 1 u ρ

/--
Terminal singleton branches turn the active-edge branch sum into the sum of
one-edge partial-derivative integrals on the terminal fill-parameter
interpolations.
-/
theorem singleton_branchIntegralAux_eq_integralSum_partialDeriv_of_emptyActiveEdges
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          partialDeriv e.val ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) := by
  rw [branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  exact (extensions e).singleton_branchIntegralAux_eq_integral_partialDeriv_of_emptyActiveEdges
    top u ρ (hterm e)

/--
For a terminal selected branch, its integrand may be read on the terminal
fill-parameter interpolation point.
-/
theorem growth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    (data : ActiveBranchData F)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (data.terminal e).activeEdges = ∅)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) (b : ℝ) :
    (data.growth e).branchIntegrand u ρ ts =
      mixedPartialList (e.val :: data.order e).reverse ρ
        ((data.terminal e).interpWithFill
          ((data.growth e).params u ts) b) :=
  (data.growth e).branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    u ρ ts b (hterm e)

/--
The selected branch integrand in its standard terminal-interpolation form.
-/
theorem growth_branchIntegrand_eq_mixedPartialList_standardInterp
    (data : ActiveBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (ts : List ℝ) :
    (data.growth e).branchIntegrand u ρ ts =
      mixedPartialList (e.val :: data.order e).reverse ρ
        ((data.terminal e).standardInterp ((data.growth e).params u ts)) :=
  (data.growth e).branchIntegrand_def_standardInterp u ρ ts

/--
The active-branch sum in the standard terminal-interpolation form used by the
ordered BKAR main terms.
-/
theorem branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    (data : ActiveBranchData F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: data.order e)
          (fun ts => mixedPartialList (e.val :: data.order e).reverse ρ
            ((data.terminal e).standardInterp
              ((data.growth e).params u ts)))) := by
  rw [branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  rw [OrderedGrowth.branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top (e.val :: data.order e)
    (fun ts =>
      data.growth_branchIntegrand_eq_mixedPartialList_standardInterp e u ρ ts)

/--
Unit-simplex version of
The standard-interpolation identity for `ActiveBranchData.branchIntegralAux`.
-/
theorem branchIntegral_eq_sum_orderedSimplexIntegral_mixedPartialList_standardInterp
    (data : ActiveBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegral (e.val :: data.order e)
          (fun ts => mixedPartialList (e.val :: data.order e).reverse ρ
            ((data.terminal e).standardInterp
              ((data.growth e).params u ts)))) :=
  data.branchIntegralAux_eq_sum_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    1 u ρ

/--
Terminal selected branches rewrite the active-branch sum as a sum of ordered
simplex integrals over terminal fill-parameter interpolation points.
-/
theorem branchIntegralAux_eq_simplexSum_of_emptyActiveEdges
    (data : ActiveBranchData F)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (data.terminal e).activeEdges = ∅)
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (e.val :: data.order e)
          (fun ts => mixedPartialList (e.val :: data.order e).reverse ρ
            ((data.terminal e).interpWithFill
              ((data.growth e).params u ts) b))) := by
  rw [branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  rw [OrderedGrowth.branchIntegralAux]
  exact orderedSimplexIntegralAux_congr top (e.val :: data.order e)
    (fun ts =>
      data.growth_branchIntegrand_eq_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
        hterm e u ρ ts b)

/--
Accumulated-derivative version of the terminal singleton branch-sum identity.
-/
theorem singleton_branchIntegralAux_eq_integralSum_mixedPartial_of_emptyActiveEdges
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (es : List (Edge V)) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) := by
  rw [singleton_branchIntegralAux_eq_integralSum_partialDeriv_of_emptyActiveEdges
    extensions top u (mixedPartialList es ρ) hterm]
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr
  intro t _
  rfl

/--
Terminal singleton branches in the standard terminal-interpolation form.
-/
theorem singleton_branchIntegralAux_eq_standardIntegralSum_of_emptyActiveEdges
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (es : List (Edge V)) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) := by
  rw [singleton_branchIntegralAux_eq_integralSum_mixedPartial_of_emptyActiveEdges
    extensions es top u ρ hterm]
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr
  intro t _
  change mixedPartialList (e.val :: es) ρ
      ((extensions e).forest.interpWithFill
        ((extensions e).extension.extendParam u t) t) =
    mixedPartialList (e.val :: es) ρ
      ((extensions e).forest.standardInterp
        ((extensions e).extension.extendParam u t))
  rw [(extensions e).forest.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
    ((extensions e).extension.extendParam u t) t (hterm e)]

/--
Unit-simplex version of
`ActiveBranchData.singleton_branchIntegralAux_eq_integralSum_mixedPartial_of_emptyActiveEdges`.
-/
theorem singleton_branchIntegral_eq_integralSum_mixedPartial_of_emptyActiveEdges
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (es : List (Edge V))
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegral u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) :=
  singleton_branchIntegralAux_eq_integralSum_mixedPartial_of_emptyActiveEdges
    extensions es 1 u ρ hterm

/--
Unit-simplex version of
`ActiveBranchData.singleton_branchIntegralAux_eq_standardIntegralSum_of_emptyActiveEdges`.
-/
theorem singleton_branchIntegral_eq_integralSum_standardMixedPartial_of_emptyActiveEdges
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (es : List (Edge V))
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegral u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) :=
  singleton_branchIntegralAux_eq_standardIntegralSum_of_emptyActiveEdges
    extensions es 1 u ρ hterm

end ActiveBranchData

/--
Terminal active-extension expansion rewritten as a singleton active-branch
remainder.
-/
theorem mixedPartial_eq_standard_add_singletonBranchIntegralAux_of_emptyActiveEdges
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        (ActiveBranchData.singleton extensions).branchIntegralAux b u
          (mixedPartialList es ρ) := by
  rw [F.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
    es u ρ b hbound hρ hint extensions]
  rw [ActiveBranchData.singleton_branchIntegralAux_eq_integralSum_mixedPartial_of_emptyActiveEdges
    extensions es b u ρ hterm]

/--
Terminal active-extension expansion rewritten directly as standard
singleton-branch integrals.
-/
theorem mixedPartial_eq_standard_add_singletonIntegralSum_of_emptyActiveEdges
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..b,
            mixedPartialList (e.val :: es) ρ
              ((extensions e).forest.standardInterp
                ((extensions e).extension.extendParam u t))) := by
  rw [F.mixedPartial_eq_standard_add_singletonBranchIntegralAux_of_emptyActiveEdges
    es u ρ b hbound hρ hint extensions hterm]
  rw [ActiveBranchData.singleton_branchIntegralAux_eq_standardIntegralSum_of_emptyActiveEdges
    extensions es b u ρ hterm]

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
