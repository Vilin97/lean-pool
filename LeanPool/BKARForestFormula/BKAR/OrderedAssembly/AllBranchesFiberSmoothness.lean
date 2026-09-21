/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.CubePartition.Smoothness
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFibers

/-! # Integrability of the boundary fibers

Under the global smoothness hypothesis, the local boundary support/order
contributions are continuous and interval-integrable, and the boundary tree
fibers satisfy the integrability certificates required to exchange
integrals and finite sums in the telescoping argument.  Produces the split
form of the identity: `ρ` at the all-ones configuration equals `ρ` at zero
plus the sum of the nonempty-support fibers.
-/

noncomputable section

namespace BKAR

namespace BKARContDiff

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

/--
The local support/order first-boundary fiber is continuous as a function of
its outer upper bound.
-/
theorem localBoundarySupportOrderContribution_continuous
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (I : ForestIndex V) (order : List (Edge V)) :
    Continuous
      (fun top : ℝ =>
        Forest.localBoundarySupportOrderContribution choices F pref prefixTs
          top I order ρ) := by
  classical
  change
    Continuous
      (fun top : ℝ =>
        Finset.sum
          (F.activeEdges.attach.filter
            (fun e =>
              (choices F e).forest.support = I ∧
                pref ++ [e.val] = order))
          (fun e =>
            orderedSimplexIntegralAux top [e.val]
              (fun ts =>
                BKAR.mixedPartialList order.reverse ρ
                  ((choices F e).forest.standardInterp
                    ((choices F e).forest.paramsOfOrder order
                      (prefixTs ++ ts))))))
  apply continuous_finsetSum
  intro e he
  have horder : pref ++ [e.val] = order :=
    (Finset.mem_filter.mp he).2.2
  have hparam :
      Continuous
        (fun t : ℝ =>
          (choices F e).forest.paramsOfOrder order (prefixTs ++ [t])) := by
    rw [← horder]
    exact
      (choices F e).extension.paramsOfOrder_append_singleton_continuous
        pref prefixTs hpref hprefixTs
  have hpath :
      Continuous
        (fun t : ℝ =>
          (choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder order (prefixTs ++ [t]))) :=
    (choices F e).forest.standardInterp_continuous_comp hparam
  have hintegrand :
      Continuous
        (fun t : ℝ =>
          BKAR.mixedPartialList order.reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder order
                (prefixTs ++ [t])))) :=
    hρ.mixedPartialList_continuous_comp order.reverse hpath
  simpa using
    BKAR.intervalIntegral_continuous_primitive_of_continuous
      hintegrand 0

/--
The local support/order first-boundary fiber is interval-integrable in its
outer upper bound.
-/
theorem localBoundarySupportOrderContribution_intervalIntegrable
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (I : ForestIndex V) (order : List (Edge V)) (a b : ℝ) :
    IntervalIntegrable
      (fun top : ℝ =>
        Forest.localBoundarySupportOrderContribution choices F pref prefixTs
          top I order ρ)
      MeasureTheory.volume a b :=
  (hρ.localBoundarySupportOrderContribution_continuous choices F pref prefixTs
    hpref hprefixTs I order).intervalIntegrable a b

/--
The local support/order first-boundary fiber is continuous along any
fixed-length coordinatewise-continuous parameter-list path.
-/
theorem localBoundarySupportOrderContribution_continuous_comp
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V))
    {X : Type*} [TopologicalSpace X]
    {tsPath : X → List ℝ} {topPath : X → ℝ}
    (hts : BKAR.ListPathContinuous pref.length tsPath)
    (htop : Continuous topPath)
    (I : ForestIndex V) (order : List (Edge V)) :
    Continuous
      (fun x : X =>
        Forest.localBoundarySupportOrderContribution choices F pref
          (tsPath x) (topPath x) I order ρ) := by
  classical
  change
    Continuous
      (fun x : X =>
        Finset.sum
          (F.activeEdges.attach.filter
            (fun e =>
              (choices F e).forest.support = I ∧
                pref ++ [e.val] = order))
          (fun e =>
            orderedSimplexIntegralAux (topPath x) [e.val]
              (fun ts =>
                BKAR.mixedPartialList order.reverse ρ
                  ((choices F e).forest.standardInterp
                    ((choices F e).forest.paramsOfOrder order
                      (tsPath x ++ ts))))))
  apply continuous_finsetSum
  intro e _he
  have htsProd :
      BKAR.ListPathContinuous (pref.length + 1)
        (fun p : X × ℝ => tsPath p.1 ++ [p.2]) :=
    BKAR.ListPathContinuous.append_singleton
      (BKAR.ListPathContinuous.comp hts continuous_fst)
      continuous_snd
  have hparam :
      Continuous
        (fun p : X × ℝ =>
          (choices F e).forest.paramsOfOrder order (tsPath p.1 ++ [p.2])) :=
    Forest.paramsOfOrder_continuous_of_listPathContinuous
      (choices F e).forest order htsProd
  have hpath :
      Continuous
        (fun p : X × ℝ =>
          (choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder order
              (tsPath p.1 ++ [p.2]))) :=
    (choices F e).forest.standardInterp_continuous_comp hparam
  have hintegrand :
      Continuous
        (Function.uncurry
          (fun x : X => fun t : ℝ =>
            BKAR.mixedPartialList order.reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder order
                  (tsPath x ++ [t]))))) := by
    change
      Continuous
        (fun p : X × ℝ =>
          BKAR.mixedPartialList order.reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder order
                (tsPath p.1 ++ [p.2]))))
    exact (hρ.mixedPartialList order.reverse).continuous.comp hpath
  simpa using
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := 0)
      (f :=
        fun x : X => fun t : ℝ =>
          BKAR.mixedPartialList order.reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder order
                (tsPath x ++ [t]))))
      hintegrand htop

/--
Finite-depth continuity of folded support/order fibers along any recursively
generated diagonal parameter-list path.
-/
theorem boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (k : Nat) (F : Forest V) (pref : List (Edge V))
      {X : Type*} [TopologicalSpace X]
      {tsPath : X → List ℝ} {topPath : X → ℝ},
      BKAR.ListPathContinuous pref.length tsPath →
      Continuous topPath →
      (I : ForestIndex V) → (order : List (Edge V)) →
      order.length = pref.length + k →
      Continuous
        (fun x : X =>
          Forest.boundarySupportOrderTreeFiber choices F pref (tsPath x)
            (topPath x) I order ρ)
  | 0, F, pref, X, _inst, tsPath, topPath, hts, _htop, I, order, hlen => by
      have hfiber_zero :
          (fun x : X =>
            Forest.boundarySupportOrderTreeFiber choices F pref (tsPath x)
              (topPath x) I order ρ) = fun _ : X => 0 := by
        funext x
        exact
          Forest.boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
            choices F.activeEdges.card F pref (tsPath x) (topPath x)
            I order ρ le_rfl (by
              rw [hlen]
              simp)
      rw [hfiber_zero]
      exact continuous_const
  | k + 1, F, pref, X, _inst, tsPath, topPath, hts, htop, I, order, hlen => by
      have hfiber_def :
          (fun x : X =>
            Forest.boundarySupportOrderTreeFiber choices F pref (tsPath x)
              (topPath x) I order ρ) =
          fun x : X =>
            Forest.localBoundarySupportOrderContribution choices F pref
                (tsPath x) (topPath x) I order ρ +
              Finset.sum F.activeEdges.attach
                (fun e => ∫ t in 0..topPath x,
                  Forest.boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (tsPath x ++ [t]) t I order ρ) := by
        funext x
        rw [Forest.boundarySupportOrderTreeFiber_def]
      rw [hfiber_def]
      apply Continuous.add
      · exact
          hρ.localBoundarySupportOrderContribution_continuous_comp
            choices F pref hts htop I order
      · apply continuous_finsetSum
        intro e _he
        have htsChild :
            BKAR.ListPathContinuous (pref ++ [e.val]).length
              (fun p : X × ℝ => tsPath p.1 ++ [p.2]) := by
          simpa using
            BKAR.ListPathContinuous.append_singleton
              (BKAR.ListPathContinuous.comp hts continuous_fst)
              continuous_snd
        have hlenChild :
            order.length = (pref ++ [e.val]).length + k := by
          rw [hlen]
          simp [Nat.add_assoc, Nat.add_comm]
        have hchild :
            Continuous
              (fun p : X × ℝ =>
                Forest.boundarySupportOrderTreeFiber choices
                  (choices F e).forest (pref ++ [e.val])
                  (tsPath p.1 ++ [p.2]) p.2 I order ρ) :=
          boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
            hρ choices k (choices F e).forest (pref ++ [e.val])
            htsChild continuous_snd I order hlenChild
        have huncurry :
            Continuous
              (Function.uncurry
                (fun x : X => fun t : ℝ =>
                  Forest.boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (tsPath x ++ [t]) t I order ρ)) := by
          simpa [Function.uncurry] using! hchild
        exact
          intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
            (μ := MeasureTheory.volume) (a₀ := 0)
            (f :=
              fun x : X => fun t : ℝ =>
                Forest.boundarySupportOrderTreeFiber choices
                  (choices F e).forest (pref ++ [e.val])
                  (tsPath x ++ [t]) t I order ρ)
            huncurry htop

/-- Finite-depth interval-integrability of folded support/order fibers. -/
theorem boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_eq_pref_length_add
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (k : Nat) (F : Forest V) (pref : List (Edge V))
    (prefixTs : List ℝ) (I : ForestIndex V) (order : List (Edge V))
    (top : ℝ)
    (hprefixTs : prefixTs.length = pref.length)
    (hlen : order.length = pref.length + k) :
    IntervalIntegrable
      (fun t : ℝ =>
        Forest.boundarySupportOrderTreeFiber choices F pref prefixTs t
          I order ρ)
      MeasureTheory.volume 0 top := by
  have hts :
      BKAR.ListPathContinuous pref.length
        (fun _ : ℝ => prefixTs) := by
    rw [← hprefixTs]
    exact BKAR.ListPathContinuous.const prefixTs
  exact
    (boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
      hρ choices k F pref hts continuous_id I order hlen).intervalIntegrable 0 top

/--
The narrowed nontrivial support/order fiber-integrability predicate follows
from global `C^∞` smoothness.
-/
theorem boundarySupportOrderTreeFiberNontrivialIntegrable_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ),
      prefixTs.length = pref.length →
      Forest.boundarySupportOrderTreeFiberNontrivialIntegrable choices n
        F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, _hprefixTs => by
      exact
        Forest.boundarySupportOrderTreeFiberNontrivialIntegrable_zero
          choices F pref prefixTs top ρ
  | n + 1, F, pref, prefixTs, top, hprefixTs => by
      constructor
      · intro e x _hx hlen_gt _hI
        let childPref := pref ++ [e.val]
        let k := x.2.length - childPref.length
        have htsBase :
            BKAR.ListPathContinuous pref.length
              (fun _ : ℝ => prefixTs) := by
          rw [← hprefixTs]
          exact BKAR.ListPathContinuous.const prefixTs
        have htsChild :
            BKAR.ListPathContinuous childPref.length
              (fun t : ℝ => prefixTs ++ [t]) := by
          simpa [childPref] using
            BKAR.ListPathContinuous.append_singleton
              htsBase continuous_id
        have hlen :
            x.2.length = childPref.length + k := by
          dsimp [k, childPref]
          omega
        exact
          (boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
            hρ choices k (choices F e).forest childPref htsChild
            continuous_id x.1 x.2 hlen).intervalIntegrable 0 top
      · intro e t _ht
        exact
          boundarySupportOrderTreeFiberNontrivialIntegrable_of_contDiff
            hρ choices n (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
            t (by simp [hprefixTs])

/--
Final flattened root identity with the fiber-integrability obligation
discharged by `BKARContDiff`. The remaining analytic input is the
all-branches induction hypothesis.
-/
theorem oneConfig_eq_zeroConfig_add_nonemptyTreeSum_of_contDiff_of_analytic
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (hanalytic :
      Forest.allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                [] [] 1 I order ρ)) :=
  Forest.oneConfig_eq_zeroConfig_add_nonemptyTreeSum_of_nontrivialIntegrable
    choices ρ hanalytic
    (hρ.boundarySupportOrderTreeFiberNontrivialIntegrable_of_contDiff
      choices (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 rfl)


end BKARContDiff

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
