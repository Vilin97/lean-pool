/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.CubePartition.Support
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.LocalRecursion

/-! # The all-branches expansion

Defines `ActiveExtensionChoice`, a global choice of one-edge forest
extension at every recursion node (nonempty by construction), and the
depth-indexed all-branches expansion `allBranchesExpansion` with its
boundary part and the analytic side conditions `allBranchesAnalytic`
needed to push it one level deeper.  The mixed partial of the interpolation
family equals the expansion at every depth — the engine driving the proof
of the BKAR forest interpolation formula (see `BKAR.Formula`).
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
A global choice of one-edge forest extension at every recursion node.

The all-branches induction expands every active edge of every forest it reaches;
this is the one piece of structural data needed to name the next forest.
-/
abbrev ActiveExtensionChoice (V : Type*) [Fintype V] [DecidableEq V] :=
  ∀ F : Forest V, ∀ e : {e // e ∈ F.activeEdges}, ActiveExtension F e.val

/-- A global active-extension choice exists by noncomputably choosing the `Forest`
representative obtained by inserting each active edge. -/
theorem nonempty_activeExtensionChoice (V : Type*) [Fintype V] [DecidableEq V] :
    Nonempty (ActiveExtensionChoice V) := by
  classical
  refine ⟨fun F e =>
    Classical.choice (F.nonempty_activeExtension_of_mem_activeEdges e.property)⟩

/--
The level-`n` all-branches expansion from a recursion node.

At level zero it is the current fill-parameter remainder.  At level `n + 1` it
exposes the current ordered-sector boundary term and recursively expands every
active-edge remainder one level deeper.
-/
noncomputable def allBranchesExpansion
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → ℝ
  | 0, F, pref, prefixTs, top, ρ =>
      mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top)
  | n + 1, F, pref, prefixTs, top, ρ =>
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesExpansion choices n (choices F e).forest
              (pref ++ [e.val]) (prefixTs ++ [t]) t ρ)

theorem allBranchesExpansion_zero
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesExpansion choices 0 F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) :=
  rfl

theorem allBranchesExpansion_succ
    (choices : ActiveExtensionChoice V) (n : Nat)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesExpansion choices (n + 1) F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesExpansion choices n (choices F e).forest
              (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) :=
  rfl

/--
The pure boundary-sector tree with the same branching shape as
`allBranchesExpansion`, but with no fill-parameter remainder at the leaves.
-/
noncomputable def allBranchesBoundaryExpansion
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → ℝ
  | 0, F, pref, prefixTs, _, ρ =>
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs))
  | n + 1, F, pref, prefixTs, top, ρ =>
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices n (choices F e).forest
              (pref ++ [e.val]) (prefixTs ++ [t]) t ρ)

theorem allBranchesBoundaryExpansion_zero
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesBoundaryExpansion choices 0 F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) :=
  rfl

theorem allBranchesBoundaryExpansion_succ
    (choices : ActiveExtensionChoice V) (n : Nat)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesBoundaryExpansion choices (n + 1) F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices n (choices F e).forest
              (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) :=
  rfl

/--
Analytic assumptions needed by the finite all-branches induction through
`n` further layers from a node.

This is a precise recursion-tree version of the usual smoothness and
integrability requirements; the final smoothness API will discharge it in one
place rather than weakening the induction theorem.
-/
def allBranchesAnalytic
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, F, pref, prefixTs, top, ρ =>
      (∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e) ∧
      (∀ t ∈ Set.uIcc 0 top,
        DifferentiableAt ℝ (mixedPartialList pref.reverse ρ)
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)) ∧
      (∀ e ∈ F.activeEdges,
        IntervalIntegrable
          (fun t : ℝ => mixedPartialList (e :: pref.reverse) ρ
            (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
          MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges},
        IntervalIntegrable
          (fun t : ℝ => mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ [t]))))
          MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            Finset.sum (choices F e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices (choices F e).forest e').forest.activeEdges.card
                  (choices (choices F e).forest e').forest
                  ((pref ++ [e.val]) ++ [e'.val])
                  ((prefixTs ++ [t]) ++ [s]) s ρ))
          MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges}, ∀ t ∈ Set.uIcc 0 top,
        allBranchesAnalytic choices n (choices F e).forest
          (pref ++ [e.val]) (prefixTs ++ [t]) t ρ)

theorem allBranchesAnalytic_zero
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesAnalytic choices 0 F pref prefixTs top ρ :=
  trivial

/-- Analytic recursion-tree hypotheses can be truncated to a shallower depth. -/
theorem allBranchesAnalytic_of_le
    (choices : ActiveExtensionChoice V) :
    ∀ {m n : Nat} {F : Forest V} {pref : List (Edge V)}
      {prefixTs : List ℝ} {top : ℝ} {ρ : (Edge V → ℝ) → ℝ},
      m ≤ n →
      allBranchesAnalytic choices n F pref prefixTs top ρ →
      allBranchesAnalytic choices m F pref prefixTs top ρ
  | 0, _n, _F, _pref, _prefixTs, _top, _ρ, _hle, _hanalytic => by
      trivial
  | m + 1, 0, _F, _pref, _prefixTs, _top, _ρ, hle, _hanalytic => by
      exact False.elim (Nat.not_succ_le_zero m hle)
  | m + 1, n + 1, F, pref, prefixTs, top, ρ, hle, hanalytic => by
      rcases hanalytic with ⟨hbound, hρ, hint, hstd, hrec, hchild⟩
      refine ⟨hbound, hρ, hint, hstd, hrec, ?_⟩
      intro e t ht
      exact
        allBranchesAnalytic_of_le choices
          (Nat.succ_le_succ_iff.mp hle) (hchild e t ht)

/--
The all-branches induction invariant: expanding every active edge for `n`
layers preserves the current fill-parameter remainder.
-/
theorem mixedPartialList_interpWithFill_eq_allBranchesExpansion
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      pref.toFinset = F.edges →
      prefixTs.length = pref.length →
      allBranchesAnalytic choices n F pref prefixTs top ρ →
      mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) =
        allBranchesExpansion choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, ρ, _hpref, _hprefixTs, _hanalytic => by
      rw [allBranchesExpansion_zero]
  | n + 1, F, pref, prefixTs, top, ρ, hpref, hprefixTs, hanalytic => by
      rcases hanalytic with ⟨hbound, hρ, hint, _hstd, _hrec, hchild⟩
      have hstep :=
        F.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
          pref.reverse (F.paramsOfOrder pref prefixTs) ρ top
          hbound hρ hint (choices F)
      calc
        mixedPartialList pref.reverse ρ
            (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) =
          mixedPartialList pref.reverse ρ
              (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
            Finset.sum F.activeEdges.attach
              (fun e => ∫ t in 0..top,
                mixedPartialList (e.val :: pref.reverse) ρ
                  ((choices F e).forest.interpWithFill
                    ((choices F e).extension.extendParam
                      (F.paramsOfOrder pref prefixTs) t) t)) := by
            exact hstep
        _ =
          mixedPartialList pref.reverse ρ
              (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
            Finset.sum F.activeEdges.attach
              (fun e => ∫ t in 0..top,
                allBranchesExpansion choices n (choices F e).forest
                  (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) := by
            apply congrArg
              (fun r =>
                mixedPartialList pref.reverse ρ
                    (F.standardInterp (F.paramsOfOrder pref prefixTs)) + r)
            apply Finset.sum_congr rfl
            intro e _
            apply intervalIntegral.integral_congr
            intro t ht
            have hprefChild :
                (pref ++ [e.val]).toFinset = (choices F e).forest.edges := by
              rw [List.toFinset_append, (choices F e).extension.edges_eq,
                hpref]
              simp
            have hprefixTsChild :
                (prefixTs ++ [t]).length = (pref ++ [e.val]).length := by
              simp [hprefixTs]
            have horder :
                (pref ++ [e.val]).reverse = e.val :: pref.reverse := by
              rw [List.reverse_append]
              rfl
            have hparam :
                (choices F e).extension.extendParam
                    (F.paramsOfOrder pref prefixTs) t =
                  (choices F e).forest.paramsOfOrder (pref ++ [e.val])
                    (prefixTs ++ [t]) :=
              (choices F e).extension.extendParam_eq_paramsOfOrder_append_singleton
                pref prefixTs t hpref hprefixTs
            change mixedPartialList (e.val :: pref.reverse) ρ
                ((choices F e).forest.interpWithFill
                  ((choices F e).extension.extendParam
                    (F.paramsOfOrder pref prefixTs) t) t) =
              allBranchesExpansion choices n (choices F e).forest
                (pref ++ [e.val]) (prefixTs ++ [t]) t ρ
            rw [← horder, hparam]
            exact
              mixedPartialList_interpWithFill_eq_allBranchesExpansion
                choices n (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t ρ hprefChild hprefixTsChild
                (hchild e t ht)
        _ =
          allBranchesExpansion choices (n + 1) F pref prefixTs top ρ := by
            rw [allBranchesExpansion_succ]

/--
Once a node has no active edges, every positive all-branches level is just its
boundary ordered-sector term.
-/
theorem allBranchesExpansion_succ_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V) (n : Nat)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hF : F.activeEdges = ∅) :
    allBranchesExpansion choices (n + 1) F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) := by
  rw [allBranchesExpansion_succ]
  have hattach : F.activeEdges.attach = ∅ := by
    rw [hF]
    rfl
  rw [hattach, Finset.sum_empty, add_zero]

/--
Once the remaining depth dominates the number of active edges at a node, adding
one more all-branches layer does not change the expansion.
-/
theorem allBranchesExpansion_stable_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      allBranchesExpansion choices (n + 1) F pref prefixTs top ρ =
        allBranchesExpansion choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, ρ, hle => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      rw [allBranchesExpansion_succ_of_activeEdges_eq_empty choices 0 F
        pref prefixTs top ρ hF]
      rw [allBranchesExpansion_zero]
      rw [F.mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
        pref.reverse (F.paramsOfOrder pref prefixTs) ρ top hF]
  | n + 1, F, pref, prefixTs, top, ρ, hle => by
      rw [allBranchesExpansion_succ, allBranchesExpansion_succ]
      apply congrArg
        (fun r =>
          mixedPartialList pref.reverse ρ
            (F.standardInterp (F.paramsOfOrder pref prefixTs)) + r)
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr
      intro t _
      have hlt :
          (choices F e).forest.activeEdges.card < F.activeEdges.card :=
        (choices F e).activeEdges_card_lt
      have hchild_le : (choices F e).forest.activeEdges.card ≤ n :=
        Nat.lt_succ_iff.mp (hlt.trans_le hle)
      exact
        allBranchesExpansion_stable_of_activeEdges_card_le choices n
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ
          hchild_le

/--
The exact active-edge count is a canonical terminal depth for the all-branches
expansion: any extra fuel beyond that depth gives the same value.
-/
theorem allBranchesExpansion_activeEdges_card_add
    (choices : ActiveExtensionChoice V) :
    ∀ (k : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      allBranchesExpansion choices (F.activeEdges.card + k)
          F pref prefixTs top ρ =
        allBranchesExpansion choices F.activeEdges.card F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, ρ => by
      rw [Nat.add_zero]
  | k + 1, F, pref, prefixTs, top, ρ => by
      rw [Nat.add_succ]
      have hle : F.activeEdges.card ≤ F.activeEdges.card + k :=
        Nat.le_add_right _ _
      rw [allBranchesExpansion_stable_of_activeEdges_card_le choices
        (F.activeEdges.card + k) F pref prefixTs top ρ hle]
      exact
        allBranchesExpansion_activeEdges_card_add choices k
          F pref prefixTs top ρ

/--
At any depth at least the active-edge count, the all-branches expansion has no
fill-parameter leaves left: it is exactly the pure boundary-sector tree.
-/
theorem allBranchesExpansion_eq_boundaryExpansion_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      allBranchesExpansion choices n F pref prefixTs top ρ =
        allBranchesBoundaryExpansion choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, ρ, hle => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      rw [allBranchesExpansion_zero, allBranchesBoundaryExpansion_zero]
      rw [F.mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
        pref.reverse (F.paramsOfOrder pref prefixTs) ρ top hF]
  | n + 1, F, pref, prefixTs, top, ρ, hle => by
      rw [allBranchesExpansion_succ, allBranchesBoundaryExpansion_succ]
      apply congrArg
        (fun r =>
          mixedPartialList pref.reverse ρ
            (F.standardInterp (F.paramsOfOrder pref prefixTs)) + r)
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr
      intro t _
      have hlt :
          (choices F e).forest.activeEdges.card < F.activeEdges.card :=
        (choices F e).activeEdges_card_lt
      have hchild_le : (choices F e).forest.activeEdges.card ≤ n :=
        Nat.lt_succ_iff.mp (hlt.trans_le hle)
      exact
        allBranchesExpansion_eq_boundaryExpansion_of_activeEdges_card_le
          choices n (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ hchild_le

/-- Exact active-depth terminalization of the all-branches expansion. -/
theorem allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesExpansion choices F.activeEdges.card F pref prefixTs top ρ =
      allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ :=
  allBranchesExpansion_eq_boundaryExpansion_of_activeEdges_card_le
    choices F.activeEdges.card F pref prefixTs top ρ le_rfl

/--
The pure boundary-sector tree also stabilizes once the remaining depth
dominates the active-edge count.
-/
theorem allBranchesBoundaryExpansion_stable_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      allBranchesBoundaryExpansion choices (n + 1) F pref prefixTs top ρ =
        allBranchesBoundaryExpansion choices n F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, ρ, hle => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      rw [allBranchesBoundaryExpansion_succ,
        allBranchesBoundaryExpansion_zero]
      have hattach : F.activeEdges.attach = ∅ := by
        rw [hF]
        rfl
      rw [hattach, Finset.sum_empty, add_zero]
  | n + 1, F, pref, prefixTs, top, ρ, hle => by
      rw [allBranchesBoundaryExpansion_succ,
        allBranchesBoundaryExpansion_succ]
      apply congrArg
        (fun r =>
          mixedPartialList pref.reverse ρ
            (F.standardInterp (F.paramsOfOrder pref prefixTs)) + r)
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr
      intro t _
      have hlt :
          (choices F e).forest.activeEdges.card < F.activeEdges.card :=
        (choices F e).activeEdges_card_lt
      have hchild_le : (choices F e).forest.activeEdges.card ≤ n :=
        Nat.lt_succ_iff.mp (hlt.trans_le hle)
      exact
        allBranchesBoundaryExpansion_stable_of_activeEdges_card_le
          choices n (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ hchild_le

/-- Extra boundary-tree fuel beyond active depth gives the same value. -/
theorem allBranchesBoundaryExpansion_activeEdges_card_add
    (choices : ActiveExtensionChoice V) :
    ∀ (k : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      allBranchesBoundaryExpansion choices (F.activeEdges.card + k)
          F pref prefixTs top ρ =
        allBranchesBoundaryExpansion choices F.activeEdges.card
          F pref prefixTs top ρ
  | 0, F, pref, prefixTs, top, ρ => by
      rw [Nat.add_zero]
  | k + 1, F, pref, prefixTs, top, ρ => by
      rw [Nat.add_succ]
      have hle : F.activeEdges.card ≤ F.activeEdges.card + k :=
        Nat.le_add_right _ _
      rw [allBranchesBoundaryExpansion_stable_of_activeEdges_card_le
        choices (F.activeEdges.card + k) F pref prefixTs top ρ hle]
      exact
        allBranchesBoundaryExpansion_activeEdges_card_add choices k
          F pref prefixTs top ρ

/-- Collapse any sufficiently deep boundary tree to exact active depth. -/
theorem allBranchesBoundaryExpansion_eq_activeEdges_card_of_card_le
    (choices : ActiveExtensionChoice V)
    (n : Nat) (F : Forest V) (pref : List (Edge V))
    (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hle : F.activeEdges.card ≤ n) :
    allBranchesBoundaryExpansion choices n F pref prefixTs top ρ =
      allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ := by
  rcases exists_add_of_le hle with ⟨k, rfl⟩
  exact allBranchesBoundaryExpansion_activeEdges_card_add
    choices k F pref prefixTs top ρ

/--
Exact-depth unfolding of the boundary-sector tree. Each recursive child is
already evaluated at its own exact active depth.
-/
theorem allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices
              (choices F e).forest.activeEdges.card
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) := by
  by_cases hF : F.activeEdges = ∅
  · have hcard : F.activeEdges.card = 0 := by
      rw [hF, Finset.card_empty]
    rw [hcard, allBranchesBoundaryExpansion_zero]
    have hattach : F.activeEdges.attach = ∅ := by
      rw [hF]
      rfl
    rw [hattach, Finset.sum_empty, add_zero]
  · have hcard_pos : 0 < F.activeEdges.card := by
      exact Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hF)
    rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
      ⟨n, hn⟩
    rw [hn, allBranchesBoundaryExpansion_succ]
    apply congrArg
      (fun r =>
        mixedPartialList pref.reverse ρ
          (F.standardInterp (F.paramsOfOrder pref prefixTs)) + r)
    apply Finset.sum_congr rfl
    intro e _
    apply intervalIntegral.integral_congr
    intro t _
    have hlt :
        (choices F e).forest.activeEdges.card < F.activeEdges.card :=
      (choices F e).activeEdges_card_lt
    have hchild_le : (choices F e).forest.activeEdges.card ≤ n := by
      rw [hn] at hlt
      exact Nat.lt_succ_iff.mp hlt
    exact
      allBranchesBoundaryExpansion_eq_activeEdges_card_of_card_le
        choices n (choices F e).forest (pref ++ [e.val])
        (prefixTs ++ [t]) t ρ hchild_le

/-- Exact-depth boundary expansion at a terminal node is just its boundary term. -/
theorem allBranchesBoundaryExpansion_activeEdges_card_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hF : F.activeEdges = ∅) :
    allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) := by
  have hcard : F.activeEdges.card = 0 := by
    rw [hF, Finset.card_empty]
  rw [hcard, allBranchesBoundaryExpansion_zero]

/--
Exact-depth boundary expansion equals the current fill-parameter remainder
under the corresponding all-branches analytic hypotheses.
-/
theorem mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) =
      allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ := by
  rw [← allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
    choices F pref prefixTs top ρ]
  exact
    mixedPartialList_interpWithFill_eq_allBranchesExpansion
      choices F.activeEdges.card F pref prefixTs top ρ
      hpref hprefixTs hanalytic

/--
An active-edge summand in the parent fill-parameter remainder is exactly the
exact-depth boundary subtree below that active child.
-/
theorem mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 top) :
    mixedPartialList (e.val :: pref.reverse) ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t) =
      allBranchesBoundaryExpansion choices
        (choices F e).forest.activeEdges.card
        (choices F e).forest (pref ++ [e.val])
        (prefixTs ++ [t]) t ρ := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨hbound, _hρ, _hint, _hstd, _hrec, hchild⟩
  have horder :
      (pref ++ [e.val]).reverse = e.val :: pref.reverse := by
    rw [List.reverse_append]
    rfl
  have hparam :
      (choices F e).extension.extendParam
          (F.paramsOfOrder pref prefixTs) t =
        (choices F e).forest.paramsOfOrder (pref ++ [e.val])
          (prefixTs ++ [t]) :=
    (choices F e).extension.extendParam_eq_paramsOfOrder_append_singleton
      pref prefixTs t hpref hprefixTs
  have hprefChild :
      (pref ++ [e.val]).toFinset = (choices F e).forest.edges := by
    rw [List.toFinset_append, (choices F e).extension.edges_eq,
      hpref]
    simp
  have hprefixTsChild :
      (prefixTs ++ [t]).length = (pref ++ [e.val]).length := by
    simp [hprefixTs]
  have hchild_le :
      (choices F e).forest.activeEdges.card ≤ n := by
    have hlt :
        (choices F e).forest.activeEdges.card < F.activeEdges.card :=
      (choices F e).activeEdges_card_lt
    rw [hn] at hlt
    exact Nat.lt_succ_iff.mp hlt
  have hchildExactAnalytic :
      allBranchesAnalytic choices
        (choices F e).forest.activeEdges.card
        (choices F e).forest (pref ++ [e.val])
        (prefixTs ++ [t]) t ρ :=
    allBranchesAnalytic_of_le choices hchild_le (hchild e t ht)
  calc
    mixedPartialList (e.val :: pref.reverse) ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t) =
      partialDeriv e.val (mixedPartialList pref.reverse ρ)
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t) := by
        rw [mixedPartialList_cons_apply]
    _ =
      mixedPartialList (e.val :: pref.reverse) ρ
        ((choices F e).forest.interpWithFill
          ((choices F e).extension.extendParam
            (F.paramsOfOrder pref prefixTs) t) t) := by
        exact
          EdgeExtension.mixedPartialList_cons_interpWithFill_eq_extension
            ((choices F e).extension) pref.reverse
            (F.paramsOfOrder pref prefixTs) ρ
            (hbound t ht)
    _ =
      mixedPartialList (pref ++ [e.val]).reverse ρ
        ((choices F e).forest.interpWithFill
          ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
            (prefixTs ++ [t])) t) := by
        rw [horder, ← hparam]
    _ =
      allBranchesBoundaryExpansion choices
        (choices F e).forest.activeEdges.card
        (choices F e).forest (pref ++ [e.val])
        (prefixTs ++ [t]) t ρ := by
        exact
          mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
            choices (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t ρ hprefChild hprefixTsChild
            hchildExactAnalytic

/--
The exact-depth boundary subtree below an active child is interval-integrable
whenever the parent exact-depth all-branches analytic hypotheses hold.
-/
theorem intervalIntegrable_allBranchesBoundaryExpansion_activeEdges_card_child
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    IntervalIntegrable
      (fun t : ℝ =>
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ)
      MeasureTheory.volume 0 top := by
  have hanalyticExact := hanalytic
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨_hbound, _hρ, hint, _hstd, _hrec, _hchild⟩
  refine (hint e.val e.property).congr ?_
  intro t ht
  have ht_uIcc : t ∈ Set.uIcc 0 top :=
    Set.uIoc_subset_uIcc ht
  exact
    mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
      choices F e pref prefixTs hpref hprefixTs top ρ hanalyticExact
      ht_uIcc

/--
Integral form of the parent-summand/child-boundary identification.
-/
theorem integral_mixedPartialList_cons_interpWithFill_eq_integral_allBranchesBoundaryExpansion_child
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    (∫ t in 0..top,
        mixedPartialList (e.val :: pref.reverse) ρ
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)) =
      ∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ := by
  apply intervalIntegral.integral_congr
  intro t ht
  exact
    mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
      choices F e pref prefixTs hpref hprefixTs top ρ hanalytic ht

/--
Arbitrary-node exact-depth recursion: the current fill-parameter remainder is
the local boundary sector plus exact-depth boundary subtrees below all active
children.
-/
theorem mixedPartialList_interpWithFill_eq_standardInterp_add_sum_allBranchesBoundaryExpansion
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices
              (choices F e).forest.activeEdges.card
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) := by
  rw [mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
    choices F pref prefixTs top ρ hpref hprefixTs hanalytic]
  rw [allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum]

/--
Root form of the all-branches induction, specialized to the empty forest and
the all-one endpoint.
-/
theorem rho_oneConfig_eq_allBranchesExpansion_empty
    (choices : ActiveExtensionChoice V) (n : Nat)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices n (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      allBranchesExpansion choices n (Forest.empty V) [] [] 1 ρ := by
  have h :=
    mixedPartialList_interpWithFill_eq_allBranchesExpansion
      choices n (Forest.empty V) [] [] 1 ρ
      (by simp [Forest.empty_edges]) rfl hanalytic
  simpa [paramsOfOrder_empty, emptyParam_interpWithFill_one] using h

/--
Root all-branches identity at the canonical active depth, with the expansion
already rewritten as the pure boundary-sector tree.
-/
theorem rho_oneConfig_eq_allBranchesBoundaryExpansion_empty_activeEdges_card
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      allBranchesBoundaryExpansion choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ := by
  rw [← allBranchesExpansion_activeEdges_card_eq_boundaryExpansion
    choices (Forest.empty V) [] [] 1 ρ]
  exact rho_oneConfig_eq_allBranchesExpansion_empty choices
    (Forest.empty V).activeEdges.card ρ hanalytic

/--
Root exact-depth recursion in boundary-sector form: the BKAR value is the empty
sector plus the exact-depth boundary trees below each first active edge.
-/
theorem rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            allBranchesBoundaryExpansion choices
              (choices (Forest.empty V) e).forest.activeEdges.card
              (choices (Forest.empty V) e).forest [e.val] [t] t ρ) := by
  rw [rho_oneConfig_eq_allBranchesBoundaryExpansion_empty_activeEdges_card
    choices ρ hanalytic]
  rw [allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum]
  rw [orderedSectorSum_empty]
  simp [paramsOfOrder_empty, Forest.empty_standardInterp]

/--
The first boundary sector of a prefixed one-edge child is its one-edge ordered
simplex integral.
-/
theorem integral_prefixed_standardInterp_singleton_eq_orderedSimplexIntegralAux
    (G : Forest V) (e : Edge V)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (∫ t in 0..top,
        mixedPartialList (pref ++ [e]).reverse ρ
          (G.standardInterp (G.paramsOfOrder (pref ++ [e])
            (prefixTs ++ [t])))) =
      orderedSimplexIntegralAux top [e]
        (fun ts => mixedPartialList (pref ++ [e]).reverse ρ
          (G.standardInterp (G.paramsOfOrder (pref ++ [e])
            (prefixTs ++ ts)))) := by
  rfl

/--
The first boundary sector of any one-edge child from the empty forest is the
corresponding one-edge ordered contribution. No terminality is needed here.
-/
theorem integral_standardInterp_empty_singleton_eq_orderedContribution
    (G : Forest V) (e : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    (∫ t in 0..(1 : ℝ),
        mixedPartialList [e].reverse ρ
          (G.standardInterp (G.paramsOfOrder [e] [t]))) =
      G.orderedContribution [e] ρ := by
  rw [orderedContribution, orderedSimplexIntegral_singleton]

/--
Unfold one child exact-depth boundary subtree under its parent integral. This
is the nonterminal regrouping shape before applying interval-integral
linearity.
-/
theorem integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ) =
      ∫ t in 0..top,
        (mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ [t]))) +
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ)) := by
  apply intervalIntegral.integral_congr
  intro t _
  exact
    allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum
      choices (choices F e).forest (pref ++ [e.val])
      (prefixTs ++ [t]) t ρ

/--
One active-edge summand, after exact-depth all-branches expansion below that
edge, is the integral of the child's local boundary sector plus its recursive
exact-depth child subtrees.
-/
theorem integral_mixedPartialList_cons_interpWithFill_eq_integral_child_standard_add_sum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    (∫ t in 0..top,
        mixedPartialList (e.val :: pref.reverse) ρ
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)) =
      ∫ t in 0..top,
        (mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ [t]))) +
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ)) := by
  rw [integral_mixedPartialList_cons_interpWithFill_eq_integral_allBranchesBoundaryExpansion_child
    choices F e pref prefixTs hpref hprefixTs top ρ hanalytic]
  exact
    integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
      choices F e pref prefixTs top ρ

/--
Root boundary-tree identity with every first child unfolded once. The
recursive grandchildren are still exact-depth boundary subtrees.
-/
theorem rho_oneConfig_eq_orderedSectorSum_empty_add_sum_integral_child_standard_add_sum
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            (mixedPartialList [e.val].reverse ρ
              ((choices (Forest.empty V) e).forest.standardInterp
                ((choices (Forest.empty V) e).forest.paramsOfOrder
                  [e.val] [t])) +
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    choices ρ hanalytic]
  apply congrArg
    (fun r => (Forest.empty V).orderedSectorSum ρ + r)
  apply Finset.sum_congr rfl
  intro e _
  exact
    integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
      choices (Forest.empty V) e [] [] 1 ρ

/--
Terminal one-edge children at any prefixed recursion node are exactly the
corresponding prefixed one-edge ordered simplex.
-/
theorem integral_allBranchesBoundaryExpansion_singleton_eq_prefixed_orderedSimplexIntegralAux
    (choices : ActiveExtensionChoice V)
    (G : Forest V) (e : Edge V)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hG : G.activeEdges = ∅) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices G.activeEdges.card
          G (pref ++ [e]) (prefixTs ++ [t]) t ρ) =
      orderedSimplexIntegralAux top [e]
        (fun ts => mixedPartialList (pref ++ [e]).reverse ρ
          (G.standardInterp (G.paramsOfOrder (pref ++ [e])
            (prefixTs ++ ts)))) := by
  have hcard : G.activeEdges.card = 0 := by
    rw [hG, Finset.card_empty]
  rw [hcard]
  rfl

/--
A terminal child of the all-branches boundary tree is the singleton terminal
branch integral already used by the ordered-assembly API.
-/
theorem integral_allBranchesBoundaryExpansion_eq_terminalSingletonBranchIntegralAux
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : (choices F e).forest.activeEdges = ∅) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) =
      (TerminalGrowth.cons (choices F e)
          (TerminalGrowth.ofActiveEdgesEqEmpty
            (choices F e).forest hterm)).branchIntegralAux top
        (F.paramsOfOrder pref prefixTs) (mixedPartialList pref.reverse ρ) := by
  rw [TerminalGrowth.cons_branchIntegralAux_eq_integral_tail_partialDeriv]
  apply intervalIntegral.integral_congr
  intro t _
  change
    allBranchesBoundaryExpansion choices
        (choices F e).forest.activeEdges.card
        (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ =
      (TerminalGrowth.ofActiveEdgesEqEmpty
          (choices F e).forest hterm).branchIntegralAux t
        ((choices F e).extension.extendParam
          (F.paramsOfOrder pref prefixTs) t)
        (partialDeriv e.val (mixedPartialList pref.reverse ρ))
  rw [allBranchesBoundaryExpansion_activeEdges_card_of_activeEdges_eq_empty
    choices (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ
    hterm]
  rw [TerminalGrowth.ofActiveEdgesEqEmpty_branchIntegralAux]
  have horder : (pref ++ [e.val]).reverse = e.val :: pref.reverse := by
    rw [List.reverse_append]
    rfl
  have hparam :
      (choices F e).extension.extendParam
          (F.paramsOfOrder pref prefixTs) t =
        (choices F e).forest.paramsOfOrder (pref ++ [e.val])
          (prefixTs ++ [t]) :=
    (choices F e).extension.extendParam_eq_paramsOfOrder_append_singleton
      pref prefixTs t hpref hprefixTs
  rw [horder, ← hparam]
  rw [mixedPartialList_cons_apply]

/--
Terminal first-edge children in the boundary tree are exactly the corresponding
one-edge ordered-sector contributions.
-/
theorem integral_allBranchesBoundaryExpansion_empty_singleton_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (ρ : (Edge V → ℝ) → ℝ)
    (hterm :
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    (∫ t in 0..(1 : ℝ),
        allBranchesBoundaryExpansion choices
          (choices (Forest.empty V) e).forest.activeEdges.card
          (choices (Forest.empty V) e).forest [e.val] [t] t ρ) =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ := by
  have hcard :
      (choices (Forest.empty V) e).forest.activeEdges.card = 0 := by
    rw [hterm, Finset.card_empty]
  rw [hcard]
  change
    (∫ t in 0..(1 : ℝ),
        mixedPartialList [e.val].reverse ρ
          ((choices (Forest.empty V) e).forest.standardInterp
            ((choices (Forest.empty V) e).forest.paramsOfOrder [e.val] [t]))) =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ
  rw [orderedContribution, orderedSimplexIntegral_singleton]

/--
Root base case for the support/order regrouping: if every first active-edge
child is already terminal, the boundary tree has only empty and one-edge
ordered sectors.
-/
theorem rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_of_forall_child_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e =>
            (choices (Forest.empty V) e).forest.orderedContribution
              [e.val] ρ) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    choices ρ hanalytic]
  apply congrArg
    (fun r => (Forest.empty V).orderedSectorSum ρ + r)
  apply Finset.sum_congr rfl
  intro e _
  exact
    integral_allBranchesBoundaryExpansion_empty_singleton_eq_orderedContribution
      choices e ρ (hterm e)

/--
Root terminal-child base case, expressed through the singleton
`ActiveTerminalBranchData` branch sum.
-/
theorem rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_branchIntegral_of_forall_child_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (ActiveTerminalBranchData.singleton
          (fun e => choices (Forest.empty V) e) hterm).branchIntegral
            emptyParam ρ := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    choices ρ hanalytic]
  apply congrArg
    (fun r => (Forest.empty V).orderedSectorSum ρ + r)
  rw [ActiveTerminalBranchData.branchIntegral_eq_branchIntegralAux_one]
  rw [ActiveTerminalBranchData.branchIntegralAux_eq_sum_growth_branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  simpa [ActiveTerminalBranchData.singleton, ActiveTerminalBranchData.growth,
    paramsOfOrder_empty] using
    integral_allBranchesBoundaryExpansion_eq_terminalSingletonBranchIntegralAux
      choices (Forest.empty V) e [] [] (by simp [Forest.empty_edges]) rfl
      1 ρ (hterm e)

/--
Root terminal-child base case, already regrouped by finite support and
canonical edge order.
-/
theorem rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_supportOrderContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              ActiveTerminalBranchData.supportOrderContribution
                (ActiveTerminalBranchData.singleton
                  (fun e => choices (Forest.empty V) e) hterm)
                I order ρ)) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_branchIntegral_of_forall_child_activeEdges_eq_empty
    choices ρ hanalytic hterm]
  rw [ActiveTerminalBranchData.branchIntegral_empty_eq_sum_supportOrderContribution
    (ActiveTerminalBranchData.singleton
      (fun e => choices (Forest.empty V) e) hterm) ρ]

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
