/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.CubePartition.Prefixed

/-! # The local recursion step

One step of the recursion at a fixed node: the branch integral unfolds into
a sum over active one-edge extensions plus local first-tail remainders
(`localFirstTailRemainder`), and the mixed-partial value at the current
interpolation point splits accordingly.  Iterating this step generates the
all-branches expansion behind the BKAR forest interpolation formula (see
`BKAR.Formula`).
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ActiveTerminalBranchData

variable {F : Forest V}

/--
Local tail error for one selected terminal branch.

At a general recursion node, the selected terminal tail integral can be
compared to the one-step active-extension integral. The difference is the
piece that remains to be expanded by the all-branches induction.
-/
noncomputable def localFirstTailRemainder
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  (∫ t in 0..top,
      (data.tail e).branchIntegralAux t
        ((data.extension e).extension.extendParam u t)
        (partialDeriv e.val (mixedPartialList es ρ))) -
    ∫ t in 0..top,
      mixedPartialList (e.val :: es) ρ
        ((data.extension e).forest.interpWithFill
          ((data.extension e).extension.extendParam u t) t)

theorem localFirstTailRemainder_def
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.localFirstTailRemainder e top u es ρ =
      (∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val (mixedPartialList es ρ))) -
        ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t) :=
  rfl

/--
The selected terminal branch sum at a local recursion node is the one-step
active-extension remainder plus the sum of the local first-tail errors.
-/
theorem branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
    (data : ActiveTerminalBranchData F)
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t)) +
        Finset.sum F.activeEdges.attach
          (fun e => data.localFirstTailRemainder e top u es ρ) := by
  rw [data.branchIntegralAux_eq_sum_integrals_tail_partialDeriv]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro e _
  rw [localFirstTailRemainder_def]
  rw [mixedPartialList_cons]
  ring

/--
Local selected-terminal recursion.  Starting from any forest and accumulated
derivative list, one FTC layer contributes the selected terminal branch sum
and leaves exactly the local first-tail errors.
-/
theorem mixedPartialList_interpWithFill_eq_standardInterp_add_branchIntegralAux_sub_sum_localFirstTailRemainder
    (data : ActiveTerminalBranchData F)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        data.branchIntegralAux b u (mixedPartialList es ρ) -
          Finset.sum F.activeEdges.attach
            (fun e => data.localFirstTailRemainder e b u es ρ) := by
  have hstep :=
    F.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
      es u ρ b hbound hρ hint data.extension
  have hbranch :=
    data.branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
      b u es ρ
  linarith

/--
Prefixed sector form of the local selected-terminal recursion.  This is the
shape needed by the finishing induction: selected terminal branches are already
expressed using the accumulated edge order `pref`.
-/
theorem mixedPartialList_interpWithFill_eq_standardInterp_add_sum_prefixed_orderedSimplexIntegralAux_sub_sum_localFirstTailRemainder
    (data : ActiveTerminalBranchData F)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam,
      t ≤ F.paramsOfOrder pref prefixTs e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList pref.reverse ρ)
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: pref.reverse) ρ
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
        MeasureTheory.volume 0 b) :
    mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) b) =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => orderedSimplexIntegralAux b (data.growth e).order
            (fun ts =>
              mixedPartialList (pref ++ (data.growth e).order).reverse ρ
                ((data.growth e).terminal.standardInterp
                  ((data.growth e).terminal.paramsOfOrder
                    (pref ++ (data.growth e).order) (prefixTs ++ ts))))) -
          Finset.sum F.activeEdges.attach
            (fun e => data.localFirstTailRemainder e b
              (F.paramsOfOrder pref prefixTs) pref.reverse ρ) := by
  rw [data.mixedPartialList_interpWithFill_eq_standardInterp_add_branchIntegralAux_sub_sum_localFirstTailRemainder
    pref.reverse (F.paramsOfOrder pref prefixTs) ρ b hbound hρ hint]
  rw [data.branchIntegralAux_mixedPartialList_eq_sum_prefixed_orderedSimplexIntegralAux
    pref prefixTs hpref hprefixTs b ρ]

/--
A local first-tail error vanishes when the selected tail stops immediately.
-/
theorem localFirstTailRemainder_eq_zero_of_tail_order_eq_nil
    (data : ActiveTerminalBranchData F)
    (e : {e // e ∈ F.activeEdges})
    (htail : (data.tail e).order = [])
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.localFirstTailRemainder e top u es ρ = 0 := by
  rw [localFirstTailRemainder_def]
  have htailIntegral :
      (∫ t in 0..top,
          (data.tail e).branchIntegralAux t
            ((data.extension e).extension.extendParam u t)
            (partialDeriv e.val (mixedPartialList es ρ))) =
        ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t) := by
    apply intervalIntegral.integral_congr
    intro t _
    change (data.tail e).branchIntegralAux t
        ((data.extension e).extension.extendParam u t)
        (partialDeriv e.val (mixedPartialList es ρ)) =
      mixedPartialList (e.val :: es) ρ
        ((data.extension e).forest.interpWithFill
          ((data.extension e).extension.extendParam u t) t)
    rw [(data.tail e).branchIntegralAux_eq_standardInterp_of_order_eq_nil
      htail t
      ((data.extension e).extension.extendParam u t)
      (partialDeriv e.val (mixedPartialList es ρ))]
    rw [mixedPartialList_cons]
    rw [← (data.extension e).forest.interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
      ((data.extension e).extension.extendParam u t) t
      (data.extension_activeEdges_eq_empty_of_tail_order_eq_nil e htail)]
  rw [htailIntegral, sub_self]

/--
If every selected tail stops immediately, the local selected-terminal branch
sum is exactly the one-step active-extension remainder.
-/
theorem branchIntegralAux_eq_sum_activeExtension_integrals_of_forall_tail_order_eq_nil
    (data : ActiveTerminalBranchData F)
    (htail : ∀ e : {e // e ∈ F.activeEdges}, (data.tail e).order = [])
    (top : ℝ) (u : F.EdgeParam → ℝ)
    (es : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((data.extension e).forest.interpWithFill
              ((data.extension e).extension.extendParam u t) t)) := by
  rw [data.branchIntegralAux_eq_sum_activeExtension_integrals_add_sum_localFirstTailRemainder
    top u es ρ]
  have hzero :
      Finset.sum F.activeEdges.attach
          (fun e => data.localFirstTailRemainder e top u es ρ) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    exact data.localFirstTailRemainder_eq_zero_of_tail_order_eq_nil
      e (htail e) top u es ρ
  rw [hzero, add_zero]

end ActiveTerminalBranchData

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
