/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberSmoothness

/-! # Discharging the analytic side conditions

Shows that the global smoothness hypothesis `BKARContDiff` implies the
analytic side conditions `allBranchesAnalytic` at every node and depth, and
concludes the two root identities of the ordered assembly: `ρ` at the
all-ones configuration equals the sum of all root boundary support/order
contributions, with or without the empty sector split off as `ρ` at the
zero configuration.
-/

noncomputable section

namespace BKAR

namespace BKARContDiff

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

/--
The ordered-parameter bound in `allBranchesAnalytic` propagates to a child
node after appending the active edge parameter.
-/
theorem allBranchesAnalytic_parameterBound_child
    (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (htop : 0 ≤ top)
    (hbound :
      ∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e)
    (e : {e // e ∈ F.activeEdges}) {t : ℝ}
    (ht : t ∈ Set.uIcc 0 top) :
    ∀ s ∈ Set.uIcc 0 t,
      ∀ e' : (choices F e).forest.EdgeParam,
        s ≤ (choices F e).forest.paramsOfOrder (pref ++ [e.val])
          (prefixTs ++ [t]) e' := by
  have htIcc : t ∈ Set.Icc 0 top := by
    simpa [Set.uIcc_of_le htop] using ht
  intro s hs e'
  have hsIcc : s ∈ Set.Icc 0 t := by
    simpa [Set.uIcc_of_le htIcc.1] using hs
  rw [← (choices F e).extension.extendParam_eq_paramsOfOrder_append_singleton
    pref prefixTs t hpref hprefixTs]
  exact hsIcc.2.trans
    ((choices F e).extension.le_extendParam
      (F.paramsOfOrder pref prefixTs) (hbound t ht) e')

/--
The non-recursive smoothness/integrability side conditions in
`allBranchesAnalytic` follow from global `C^∞` smoothness of `ρ`.
-/
theorem allBranchesAnalytic_smooth_obligations
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) :
    (∀ t ∈ Set.uIcc 0 top,
      DifferentiableAt ℝ (BKAR.mixedPartialList pref.reverse ρ)
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)) ∧
    (∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ =>
          BKAR.mixedPartialList (e :: pref.reverse) ρ
            (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
        MeasureTheory.volume 0 top) ∧
    (∀ e : {e // e ∈ F.activeEdges},
      IntervalIntegrable
        (fun t : ℝ =>
          BKAR.mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ [t]))))
        MeasureTheory.volume 0 top) := by
  constructor
  · intro t _ht
    exact hρ.mixedPartialList_differentiableAt pref.reverse
      (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)
  constructor
  · intro e _he
    exact hρ.mixedPartialList_interpWithFill_intervalIntegrable
      (e :: pref.reverse) F (F.paramsOfOrder pref prefixTs) 0 top
  · intro e
    exact
      hρ.mixedPartialList_standardInterp_paramsOfOrder_append_singleton_intervalIntegrable
        (pref ++ [e.val]).reverse (choices F e).extension
        pref prefixTs hpref hprefixTs 0 top

/--
Terminal recursion nodes satisfy `allBranchesAnalytic` at every remaining
fuel level once the order bound and global smoothness are available.
-/
theorem allBranchesAnalytic_of_activeEdges_eq_empty
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ),
      F.activeEdges = ∅ →
      (∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e) →
      Forest.allBranchesAnalytic choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, _hF, _hbound => by
      exact Forest.allBranchesAnalytic_zero choices F pref prefixTs top ρ
  | n + 1, F, pref, prefixTs, top, hF, hbound => by
      rw [Forest.allBranchesAnalytic]
      refine ⟨hbound, ?_, ?_, ?_, ?_, ?_⟩
      · intro t _ht
        exact hρ.mixedPartialList_differentiableAt pref.reverse
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)
      · intro e he
        have he_empty : e ∈ (∅ : Finset (Edge V)) := by
          rw [← hF]
          exact he
        exact False.elim (Finset.notMem_empty e he_empty)
      · intro e
        have he_empty : e.val ∈ (∅ : Finset (Edge V)) := by
          rw [← hF]
          exact e.property
        exact False.elim (Finset.notMem_empty e.val he_empty)
      · intro e
        have he_empty : e.val ∈ (∅ : Finset (Edge V)) := by
          rw [← hF]
          exact e.property
        exact False.elim (Finset.notMem_empty e.val he_empty)
      · intro e
        have he_empty : e.val ∈ (∅ : Finset (Edge V)) := by
          rw [← hF]
          exact e.property
        exact False.elim (Finset.notMem_empty e.val he_empty)

/--
The recursive child-sum integrability clause is automatic when the selected
child is already terminal.
-/
theorem allBranchesAnalytic_child_recursive_sum_intervalIntegrable_of_terminalChild
    (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hchild :
      (choices F e).forest.activeEdges = ∅) :
    IntervalIntegrable
      (fun t : ℝ =>
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            Forest.allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ))
      MeasureTheory.volume 0 top := by
  have hattach :
      (choices F e).forest.activeEdges.attach = ∅ := by
    rw [hchild]
    rfl
  simp [hattach]

/--
The boundary-only all-branches expansion is continuous along any fixed-length
coordinatewise-continuous parameter-list path.
-/
theorem allBranchesBoundaryExpansion_continuous_comp
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      {X : Type*} [TopologicalSpace X]
      {tsPath : X → List ℝ} {topPath : X → ℝ},
      BKAR.ListPathContinuous pref.length tsPath →
      Continuous topPath →
      Continuous
        (fun x : X =>
          Forest.allBranchesBoundaryExpansion choices n F pref
            (tsPath x) (topPath x) ρ)
  | 0, F, pref, X, _inst, tsPath, _topPath, hts, _htop => by
      have hparam :
          Continuous (fun x : X => F.paramsOfOrder pref (tsPath x)) :=
        Forest.paramsOfOrder_continuous_of_listPathContinuous F pref hts
      have hpath :
          Continuous
            (fun x : X =>
              F.standardInterp (F.paramsOfOrder pref (tsPath x))) :=
        F.standardInterp_continuous_comp hparam
      exact (hρ.mixedPartialList pref.reverse).continuous.comp hpath
  | n + 1, F, pref, X, _inst, tsPath, topPath, hts, htop => by
      rw [show
          (fun x : X =>
            Forest.allBranchesBoundaryExpansion choices (n + 1) F pref
              (tsPath x) (topPath x) ρ) =
          fun x : X =>
            BKAR.mixedPartialList pref.reverse ρ
              (F.standardInterp (F.paramsOfOrder pref (tsPath x))) +
              Finset.sum F.activeEdges.attach
                (fun e => ∫ t in 0..topPath x,
                  Forest.allBranchesBoundaryExpansion choices n
                    (choices F e).forest (pref ++ [e.val])
                    (tsPath x ++ [t]) t ρ) by
        funext x
        rw [Forest.allBranchesBoundaryExpansion_succ]]
      apply Continuous.add
      · have hparam :
            Continuous (fun x : X => F.paramsOfOrder pref (tsPath x)) :=
          Forest.paramsOfOrder_continuous_of_listPathContinuous F pref hts
        have hpath :
            Continuous
              (fun x : X =>
                F.standardInterp (F.paramsOfOrder pref (tsPath x))) :=
          F.standardInterp_continuous_comp hparam
        exact (hρ.mixedPartialList pref.reverse).continuous.comp hpath
      · apply continuous_finsetSum
        intro e _he
        have htsChild :
            BKAR.ListPathContinuous (pref ++ [e.val]).length
              (fun p : X × ℝ => tsPath p.1 ++ [p.2]) := by
          simpa using
            BKAR.ListPathContinuous.append_singleton
              (BKAR.ListPathContinuous.comp hts continuous_fst)
              continuous_snd
        have hchild :
            Continuous
              (fun p : X × ℝ =>
                Forest.allBranchesBoundaryExpansion choices n
                  (choices F e).forest (pref ++ [e.val])
                  (tsPath p.1 ++ [p.2]) p.2 ρ) :=
          allBranchesBoundaryExpansion_continuous_comp hρ choices n
            (choices F e).forest (pref ++ [e.val])
            htsChild continuous_snd
        have huncurry :
            Continuous
              (Function.uncurry
                (fun x : X => fun t : ℝ =>
                  Forest.allBranchesBoundaryExpansion choices n
                    (choices F e).forest (pref ++ [e.val])
                    (tsPath x ++ [t]) t ρ)) := by
          simpa [Function.uncurry] using! hchild
        exact
          intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
            (μ := MeasureTheory.volume) (a₀ := 0)
            (f :=
              fun x : X => fun t : ℝ =>
                Forest.allBranchesBoundaryExpansion choices n
                  (choices F e).forest (pref ++ [e.val])
                  (tsPath x ++ [t]) t ρ)
            huncurry htop

/--
The recursive child-sum integrability clause in `allBranchesAnalytic` follows
from global smoothness of `ρ`.
-/
theorem allBranchesAnalytic_child_recursive_sum_intervalIntegrable
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ) (top : ℝ)
    (hprefixTs : prefixTs.length = pref.length) :
    IntervalIntegrable
      (fun t : ℝ =>
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            Forest.allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ))
      MeasureTheory.volume 0 top := by
  apply Continuous.intervalIntegrable
  apply continuous_finsetSum
  intro e' _he'
  have htsBase :
      BKAR.ListPathContinuous pref.length
        (fun _ : ℝ × ℝ => prefixTs) := by
    rw [← hprefixTs]
    exact BKAR.ListPathContinuous.const prefixTs
  have htsChild :
      BKAR.ListPathContinuous (pref ++ [e.val]).length
        (fun p : ℝ × ℝ => prefixTs ++ [p.1]) := by
    simpa using
      BKAR.ListPathContinuous.append_singleton
        htsBase continuous_fst
  have htsGrandchild :
      BKAR.ListPathContinuous
        (((pref ++ [e.val]) ++ [e'.val]).length)
        (fun p : ℝ × ℝ => (prefixTs ++ [p.1]) ++ [p.2]) := by
    simpa using
      BKAR.ListPathContinuous.append_singleton
        htsChild continuous_snd
  have hchild :
      Continuous
        (fun p : ℝ × ℝ =>
          Forest.allBranchesBoundaryExpansion choices
            (choices (choices F e).forest e').forest.activeEdges.card
            (choices (choices F e).forest e').forest
            ((pref ++ [e.val]) ++ [e'.val])
            ((prefixTs ++ [p.1]) ++ [p.2]) p.2 ρ) :=
    hρ.allBranchesBoundaryExpansion_continuous_comp choices
      (choices (choices F e).forest e').forest.activeEdges.card
      (choices (choices F e).forest e').forest
      ((pref ++ [e.val]) ++ [e'.val])
      htsGrandchild continuous_snd
  have huncurry :
      Continuous
        (Function.uncurry
          (fun t s : ℝ =>
            Forest.allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ)) := by
    simpa [Function.uncurry] using! hchild
  exact
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous
      (μ := MeasureTheory.volume) (a₀ := 0)
      (f :=
        fun t s : ℝ =>
          Forest.allBranchesBoundaryExpansion choices
            (choices (choices F e).forest e').forest.activeEdges.card
            (choices (choices F e).forest e').forest
            ((pref ++ [e.val]) ++ [e'.val])
            ((prefixTs ++ [t]) ++ [s]) s ρ)
      huncurry continuous_id

/--
Global recursive discharge of the `allBranchesAnalytic` predicate from
`C^∞` smoothness of `ρ` and the ordered-parameter bound carried by the
recursion node.
-/
theorem allBranchesAnalytic_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ),
      pref.toFinset = F.edges →
      prefixTs.length = pref.length →
      0 ≤ top →
      (∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e) →
      Forest.allBranchesAnalytic choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, _hpref, _hprefixTs, _htop, _hbound => by
      exact Forest.allBranchesAnalytic_zero choices F pref prefixTs top ρ
  | n + 1, F, pref, prefixTs, top, hpref, hprefixTs, htop, hbound => by
      rw [Forest.allBranchesAnalytic]
      have hsmooth :=
        hρ.allBranchesAnalytic_smooth_obligations choices F pref prefixTs
          top hpref hprefixTs
      refine ⟨hbound, hsmooth.1, hsmooth.2.1, hsmooth.2.2, ?_, ?_⟩
      · intro e
        exact
          hρ.allBranchesAnalytic_child_recursive_sum_intervalIntegrable
            choices F e pref prefixTs top hprefixTs
      · intro e t ht
        let child := (choices F e).forest
        have hprefChild : (pref ++ [e.val]).toFinset = child.edges := by
          rw [List.toFinset_append, (choices F e).extension.edges_eq, hpref]
          simp
        have hprefixTsChild :
            (prefixTs ++ [t]).length = (pref ++ [e.val]).length := by
          simp [hprefixTs]
        have htIcc : t ∈ Set.Icc 0 top := by
          simpa [Set.uIcc_of_le htop] using ht
        have hboundChild :
            ∀ s ∈ Set.uIcc 0 t,
              ∀ e' : child.EdgeParam,
                s ≤ child.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ [t]) e' :=
          allBranchesAnalytic_parameterBound_child choices F pref prefixTs
            top hpref hprefixTs htop hbound e ht
        exact
          allBranchesAnalytic_of_contDiff hρ choices n child
            (pref ++ [e.val]) (prefixTs ++ [t]) t
            hprefChild hprefixTsChild htIcc.1 hboundChild

/-- Root all-branches analytic hypothesis, discharged from `BKARContDiff`. -/
theorem allBranchesAnalytic_empty_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    Forest.allBranchesAnalytic choices (Forest.empty V).activeEdges.card
      (Forest.empty V) [] [] 1 ρ := by
  exact
    hρ.allBranchesAnalytic_of_contDiff choices
      (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1
      (by simp [Forest.empty_edges]) rfl (by norm_num)
      (by
        intro _t _ht e
        have hempty : e.val ∈ (∅ : Finset (Edge V)) := by
          rw [← Forest.empty_edges V]
          exact e.property
        exact False.elim (Finset.notMem_empty e.val hempty))

/--
Final flattened root identity with both the analytic recursion predicate and
the nontrivial fiber-integrability predicate discharged by `BKARContDiff`.
-/
theorem oneConfig_eq_zeroConfig_add_nonemptyTreeSum_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
            (fun order =>
              Forest.boundarySupportOrderTreeFiber choices (Forest.empty V)
                [] [] 1 I order ρ)) :=
  hρ.oneConfig_eq_zeroConfig_add_nonemptyTreeSum_of_contDiff_of_analytic
    choices (hρ.allBranchesAnalytic_empty_of_contDiff choices)

/--
Final-shaped root BKAR identity with the empty support/order sector packaged
inside `rootBoundarySupportOrderContribution`.
-/
theorem rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (Forest.edgeSetOrders I.edges)
          (fun order =>
            Forest.rootBoundarySupportOrderContribution choices ρ I order)) := by
  rw [Forest.sum_rootContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty]
  exact
    hρ.oneConfig_eq_zeroConfig_add_nonemptyTreeSum_of_contDiff
      choices

end BKARContDiff

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
