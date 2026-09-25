/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesRegrouping

/-! # Telescoping the recursive boundary remainder

Defines the local recursive boundary remainder and the boundary
support/order tree contribution, and telescopes: after finitely many
regrouping steps — bounded by the number of active edges — the recursive
remainder is exhausted, leaving only integrals of boundary tree
contributions.  This closes the depth induction in the proof of the BKAR
forest interpolation formula (see `BKAR.Formula`).
-/

@[expose] public section

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
The exact recursive boundary remainder left after one arbitrary-node
support/order regrouping step.
-/
noncomputable def localRecursiveBoundaryRemainder
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum F.activeEdges.attach
    (fun e => ∫ t in 0..top,
      Finset.sum (choices F e).forest.activeEdges.attach
        (fun e' => ∫ s in 0..t,
          allBranchesBoundaryExpansion choices
            (choices (choices F e).forest e').forest.activeEdges.card
            (choices (choices F e).forest e').forest
            ((pref ++ [e.val]) ++ [e'.val])
            ((prefixTs ++ [t]) ++ [s]) s ρ))

theorem localRecursiveBoundaryRemainder_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    localRecursiveBoundaryRemainder choices F pref prefixTs top ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ)) :=
  rfl

/--
If every first child of a local node is already terminal, the local recursive
boundary remainder vanishes.
-/
theorem localRecursiveBoundaryRemainder_eq_zero_of_forall_child_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (choices F e).forest.activeEdges = ∅) :
    localRecursiveBoundaryRemainder choices F pref prefixTs top ρ = 0 := by
  rw [localRecursiveBoundaryRemainder_def]
  apply Finset.sum_eq_zero
  intro e _
  have hattach :
      (choices F e).forest.activeEdges.attach = ∅ := by
    rw [hterm e]
    rfl
  simp [hattach]

/-- The exact-depth child analytic hypothesis contained in `allBranchesAnalytic`. -/
theorem allBranchesAnalytic.child_activeEdges_card
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 top) :
    allBranchesAnalytic choices
      (choices F e).forest.activeEdges.card
      (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hanalytic
  rcases hanalytic with ⟨_hbound, _hρ, _hint, _hstd, _hrec, hchild⟩
  have hchild_le :
      (choices F e).forest.activeEdges.card ≤ n := by
    have hlt :
        (choices F e).forest.activeEdges.card < F.activeEdges.card :=
      (choices F e).activeEdges_card_lt
    rw [hn] at hlt
    exact Nat.lt_succ_iff.mp hlt
  exact allBranchesAnalytic_of_le choices hchild_le (hchild e t ht)

/-- The local support/order boundary layer at one recursion node. -/
noncomputable def localBoundarySupportOrderSum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum (Finset.univ : Finset (ForestIndex V))
    (fun I => Finset.sum (edgeSetOrders I.edges)
      (fun order =>
        localBoundarySupportOrderContribution choices F pref prefixTs top
          I order ρ))

theorem localBoundarySupportOrderSum_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportOrderSum choices F pref prefixTs top ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            localBoundarySupportOrderContribution choices F pref prefixTs top
              I order ρ)) :=
  rfl

theorem localBoundarySupportOrderSum_eq_zero_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hF : F.activeEdges = ∅) :
    localBoundarySupportOrderSum choices F pref prefixTs top ρ = 0 := by
  rw [localBoundarySupportOrderSum_def]
  apply Finset.sum_eq_zero
  intro I _
  apply Finset.sum_eq_zero
  intro order _
  rw [localBoundarySupportOrderContribution_def]
  have hattach : F.activeEdges.attach = ∅ := by
    rw [hF]
    rfl
  simp [hattach]

/--
The exact recursive sum of all support/order boundary layers below a node.
This is the invariant that folds the local recursive boundary remainder.
-/
noncomputable def boundarySupportOrderTreeContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  localBoundarySupportOrderSum choices F pref prefixTs top ρ +
    Finset.sum F.activeEdges.attach
      (fun e => ∫ t in 0..top,
        boundarySupportOrderTreeContribution choices
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ)
termination_by F.activeEdges.card
decreasing_by
  exact (choices F e).activeEdges_card_lt

theorem boundarySupportOrderTreeContribution_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeContribution choices F pref prefixTs top ρ =
      localBoundarySupportOrderSum choices F pref prefixTs top ρ +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeContribution choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) := by
  rw [boundarySupportOrderTreeContribution]

theorem boundarySupportOrderTreeContribution_eq_zero_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hF : F.activeEdges = ∅) :
    boundarySupportOrderTreeContribution choices F pref prefixTs top ρ = 0 := by
  rw [boundarySupportOrderTreeContribution_def]
  rw [localBoundarySupportOrderSum_eq_zero_of_activeEdges_eq_empty
    choices F pref prefixTs top ρ hF]
  have hattach : F.activeEdges.attach = ∅ := by
    rw [hF]
    rfl
  simp [hattach]

/--
One telescoping recurrence for the local recursive boundary remainder: each
child remainder splits into its local support/order boundary layer plus its
own recursive remainder.
-/
theorem recursiveRemainder_eq_childBoundarySum_add_remainder_of_analytic
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    localRecursiveBoundaryRemainder choices F pref prefixTs top ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          (Finset.sum (Finset.univ : Finset (ForestIndex V))
            (fun I => Finset.sum (edgeSetOrders I.edges)
              (fun order =>
                localBoundarySupportOrderContribution choices
                  (choices F e).forest (pref ++ [e.val])
                  (prefixTs ++ [t]) t I order ρ)) +
            localRecursiveBoundaryRemainder choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ)) := by
  rw [localRecursiveBoundaryRemainder_def]
  apply Finset.sum_congr rfl
  intro e _
  apply intervalIntegral.integral_congr
  intro t ht
  have hprefChild :
      (pref ++ [e.val]).toFinset = (choices F e).forest.edges := by
    rw [List.toFinset_append, (choices F e).extension.edges_eq, hpref]
    simp
  have hnodupChild : (pref ++ [e.val]).Nodup := by
    rw [List.nodup_append]
    refine ⟨hnodup, List.nodup_singleton e.val, ?_⟩
    intro a ha b hb hab
    rw [List.mem_singleton] at hb
    subst b
    subst a
    have he_mem : e.val ∈ F.edges := by
      rw [← hpref]
      exact List.mem_toFinset.mpr ha
    exact (choices F e).extension.new_not_mem he_mem
  have hsplit :=
    childIntegralSum_eq_boundarySum_add_childIntegral_of_analytic
      choices (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
      t ρ hprefChild hnodupChild
      (allBranchesAnalytic.child_activeEdges_card choices F e pref prefixTs
        top ρ hanalytic ht)
  simpa [localRecursiveBoundaryRemainder_def] using hsplit

/--
The local recursive remainder folds into the exact recursive support/order
tree contribution below the current node.
-/
theorem recursiveRemainder_eq_sum_integral_treeContribution_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      pref.toFinset = F.edges →
      pref.Nodup →
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ →
      localRecursiveBoundaryRemainder choices F pref prefixTs top ρ =
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeContribution choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
              t ρ)
  | 0, F, pref, prefixTs, top, ρ, hle, _hpref, _hnodup, _hanalytic => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      have hattach : F.activeEdges.attach = ∅ := by
        rw [hF]
        rfl
      rw [localRecursiveBoundaryRemainder_def, hattach]
      simp
  | n + 1, F, pref, prefixTs, top, ρ, hle, hpref, hnodup,
      hanalytic => by
      rw [
        recursiveRemainder_eq_childBoundarySum_add_remainder_of_analytic
          choices F pref prefixTs top ρ hpref hnodup hanalytic]
      apply Finset.sum_congr rfl
      intro e _
      apply intervalIntegral.integral_congr
      intro t ht
      have hprefChild :
          (pref ++ [e.val]).toFinset = (choices F e).forest.edges := by
        rw [List.toFinset_append, (choices F e).extension.edges_eq, hpref]
        simp
      have hnodupChild : (pref ++ [e.val]).Nodup := by
        rw [List.nodup_append]
        refine ⟨hnodup, List.nodup_singleton e.val, ?_⟩
        intro a ha b hb hab
        rw [List.mem_singleton] at hb
        subst b
        subst a
        have he_mem : e.val ∈ F.edges := by
          rw [← hpref]
          exact List.mem_toFinset.mpr ha
        exact (choices F e).extension.new_not_mem he_mem
      have hchild_le :
          (choices F e).forest.activeEdges.card ≤ n := by
        have hlt :
            (choices F e).forest.activeEdges.card < F.activeEdges.card :=
          (choices F e).activeEdges_card_lt
        exact Nat.lt_succ_iff.mp (hlt.trans_le hle)
      have hchildAnalytic :
          allBranchesAnalytic choices
            (choices F e).forest.activeEdges.card
            (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
            t ρ :=
        allBranchesAnalytic.child_activeEdges_card choices F e pref prefixTs
          top ρ hanalytic ht
      have hfold :=
        recursiveRemainder_eq_sum_integral_treeContribution_of_activeEdges_card_le
          choices n (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ hchild_le hprefChild hnodupChild
          hchildAnalytic
      calc
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
              (fun I => Finset.sum (edgeSetOrders I.edges)
                (fun order =>
                  localBoundarySupportOrderContribution choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t I order ρ)) +
            localRecursiveBoundaryRemainder choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) =
          Finset.sum (Finset.univ : Finset (ForestIndex V))
              (fun I => Finset.sum (edgeSetOrders I.edges)
                (fun order =>
                  localBoundarySupportOrderContribution choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t I order ρ)) +
            Finset.sum (choices F e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                boundarySupportOrderTreeContribution choices
                  (choices (choices F e).forest e').forest
                  ((pref ++ [e.val]) ++ [e'.val])
                  ((prefixTs ++ [t]) ++ [s]) s ρ) := by
            rw [hfold]
        _ =
          boundarySupportOrderTreeContribution choices
            (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
            t ρ := by
            rw [boundarySupportOrderTreeContribution_def choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
              t ρ]
            rw [localBoundarySupportOrderSum_def]

/-- The root recursive remainder is the empty-node instance of the local one. -/
theorem firstRecursiveBoundaryRemainder_eq_localRecursiveBoundaryRemainder_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    firstRecursiveBoundaryRemainder choices ρ =
      localRecursiveBoundaryRemainder choices (Forest.empty V) [] [] 1 ρ :=
  rfl

/--
Exact one-step support/order regrouping of the boundary tree at an arbitrary
node.
-/
theorem boundaryExpansion_eq_standard_add_boundarySum_add_remainder
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              localBoundarySupportOrderContribution choices F pref prefixTs
                top I order ρ)) +
          localRecursiveBoundaryRemainder choices F pref prefixTs top ρ) := by
  rw [allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum]
  rw [childIntegralSum_eq_boundarySum_add_childIntegral_of_analytic
    choices F pref prefixTs top ρ hpref hnodup hanalytic]
  rw [localRecursiveBoundaryRemainder_def]

/--
Exact-depth local boundary expansion with all recursive remainders folded into
the support/order tree contribution.
-/
theorem boundaryExpansion_activeEdges_card_eq_standard_add_treeContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        boundarySupportOrderTreeContribution choices F pref prefixTs top ρ := by
  rw [
    boundaryExpansion_eq_standard_add_boundarySum_add_remainder
      choices F pref prefixTs top ρ hpref hnodup hanalytic]
  have hfold :=
    recursiveRemainder_eq_sum_integral_treeContribution_of_activeEdges_card_le
      choices F.activeEdges.card F pref prefixTs top ρ le_rfl hpref hnodup
      hanalytic
  rw [hfold]
  rw [boundarySupportOrderTreeContribution_def choices F pref prefixTs top ρ]
  rw [localBoundarySupportOrderSum_def]

/--
Root exact boundary-tree regrouping with the remaining recursive contribution
expressed by the local remainder API.
-/
theorem oneConfig_eq_initialSectorSum_add_boundarySum_add_recursiveRemainder
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              localBoundarySupportOrderContribution choices
                (Forest.empty V) [] [] 1 I order ρ)) +
          localRecursiveBoundaryRemainder choices (Forest.empty V) [] [] 1 ρ) := by
  rw [oneConfig_eq_initialSectorSum_add_boundarySum_add_childIntegral
    choices ρ hanalytic]
  rw [localRecursiveBoundaryRemainder_def]
  simp

/--
Root exact boundary-tree regrouping with the recursive remainder completely
folded into the support/order tree contribution.
-/
theorem rho_oneConfig_eq_orderedSectorSum_empty_add_boundarySupportOrderTreeContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        boundarySupportOrderTreeContribution choices (Forest.empty V) [] []
          1 ρ := by
  rw [
    oneConfig_eq_initialSectorSum_add_boundarySum_add_recursiveRemainder
      choices ρ hanalytic]
  have hfold :=
    recursiveRemainder_eq_sum_integral_treeContribution_of_activeEdges_card_le
      choices (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ
      le_rfl (by simp [Forest.empty_edges]) List.nodup_nil hanalytic
  rw [hfold]
  rw [boundarySupportOrderTreeContribution_def choices (Forest.empty V) [] []
    1 ρ]
  rw [localBoundarySupportOrderSum_def]


end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
