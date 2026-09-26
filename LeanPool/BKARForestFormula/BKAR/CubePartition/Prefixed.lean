/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.CubePartition.Branches

/-! # Prefix decomposition of branch integrals

A single unfolding identity: the auxiliary branch integral of an ordered
growth, with its mixed-partial integrand, is the sum over admissible next
edges of prefixed ordered-simplex integrals.  This is the shape in which
the local recursion step behind the BKAR forest interpolation formula (see
`BKAR.Formula`) consumes the branch integral.
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace ActiveTerminalBranchData

variable {F : Forest V}

/--
At a general recursion node, the selected terminal branch sum is a finite sum
of ordered simplices whose edge order is the accumulated prefix followed by
the selected terminal growth order.
-/
theorem branchIntegralAux_mixedPartialList_eq_sum_prefixed_orderedSimplexIntegralAux
    (data : ActiveTerminalBranchData F)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top (F.paramsOfOrder pref prefixTs)
        (mixedPartialList pref.reverse ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (data.growth e).order
          (fun ts => mixedPartialList (pref ++ (data.growth e).order).reverse ρ
            ((data.growth e).terminal.standardInterp
              ((data.growth e).terminal.paramsOfOrder
                (pref ++ (data.growth e).order) (prefixTs ++ ts))))) := by
  rw [data.branchIntegralAux_eq_sum_growth_branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  exact (data.growth e).branchIntegralAux_mixedPartial_eq_simplexIntegralAux_paramsOfOrder_append
    pref prefixTs hpref hprefixTs top ρ

end ActiveTerminalBranchData

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
