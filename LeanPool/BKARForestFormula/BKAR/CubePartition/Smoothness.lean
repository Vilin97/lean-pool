/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.CubePartition.Orders
import LeanPool.BKARForestFormula.BKAR.Smoothness

/-! # Continuity of sector parametrizations

Continuity and integrability facts for the cube-coordinate parametrization
`paramsOfOrder` of ordered sectors: continuity in the simplex parameters,
continuity after appending one edge, and interval-integrability of the
mixed-partial integrand along the appended coordinate.  Analytic input for
converting nested simplex integrals into sector set integrals.
-/

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem paramsOfOrder_continuous_of_listPathContinuous
    (F : Forest V) (order : List (Edge V))
    {X : Type*} [TopologicalSpace X] {n : Nat} {tsPath : X → List ℝ}
    (hts : BKAR.ListPathContinuous n tsPath) :
    Continuous (fun x : X => F.paramsOfOrder order (tsPath x)) := by
  apply continuous_pi
  intro e
  exact hts.2 (order.idxOf e.val)

namespace EdgeExtension

variable {F F' : Forest V} {e : Edge V}

theorem paramsOfOrder_append_singleton_continuous
    (h : EdgeExtension F F' e) (pref : List (Edge V))
    (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) :
    Continuous
      (fun t : ℝ =>
        F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t])) := by
  have hfun :
      (fun t : ℝ =>
        F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t])) =
        fun t : ℝ => h.extendParam (F.paramsOfOrder pref prefixTs) t := by
    funext t
    rw [← h.extendParam_eq_paramsOfOrder_append_singleton
      pref prefixTs t hpref hprefixTs]
  rw [hfun]
  exact h.extendParam_continuous (F.paramsOfOrder pref prefixTs)

end EdgeExtension

end Forest

namespace BKARContDiff

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
variable {F F' : Forest V} {e : Edge V}

theorem mixedPartialList_standardInterp_paramsOfOrder_append_singleton_intervalIntegrable
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (h : Forest.EdgeExtension F F' e) (pref : List (Edge V))
    (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        BKAR.mixedPartialList es ρ
          (F'.standardInterp
            (F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t]))))
      MeasureTheory.volume a b :=
  hρ.mixedPartialList_standardInterp_intervalIntegrable es F'
    (h.paramsOfOrder_append_singleton_continuous
      pref prefixTs hpref hprefixTs)
    a b

end BKARContDiff

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
