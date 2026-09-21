/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesFiberBridge.FollowOrder

/-! # The fiber bridge: core identities

Identifies the boundary support/order tree fibers with intrinsic ordered
contributions: a fiber unfolds into an integral over its child fibers,
vanishes unless the order enumerates the support and follows active
extensions, and, when `followOrder` succeeds, the root fiber equals the
recursive ordered contribution of the grown forest.
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/--
At a node whose requested global order is exactly one edge longer than the
current prefix, the recursive fiber has no child remainder: every child has
already consumed the whole requested order.
-/
theorem boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hlen : order.length = pref.length + 1) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I order ρ =
      localBoundarySupportOrderContribution choices F pref prefixTs top
        I order ρ := by
  rw [boundarySupportOrderTreeFiber_def]
  have hsum :
      Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
              t I order ρ) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have hzero :
        (fun t : ℝ =>
          boundarySupportOrderTreeFiber choices
            (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
            t I order ρ) = fun _ => 0 := by
      funext t
      exact
        boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
          choices (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t I order ρ le_rfl (by
            rw [hlen]
            simp)
    rw [hzero]
    simp
  rw [hsum, add_zero]

/--
A support/order fiber can contribute only when the requested order has exactly
the requested support edge set.
-/
theorem boundarySupportOrderTreeFiber_eq_zero_of_order_toFinset_ne_edges
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (order : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      pref.toFinset = F.edges →
      order.toFinset ≠ I.edges →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
        I order ρ = 0
  | 0, F, pref, prefixTs, top, I, order, ρ, hle, _hpref, _hI => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      exact boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
        choices F pref prefixTs top I order ρ hF
  | n + 1, F, pref, prefixTs, top, I, order, ρ, hle, hpref, hI => by
      rw [boundarySupportOrderTreeFiber_def]
      have hlocal :
          localBoundarySupportOrderContribution choices F pref prefixTs top
            I order ρ = 0 := by
        rw [localBoundarySupportOrderContribution_def]
        rw [Finset.filter_eq_empty_iff.mpr]
        · exact Finset.sum_empty
        · intro e _ he
          apply hI
          rw [← he.2]
          rw [← he.1]
          rw [Forest.support_edges]
          rw [List.toFinset_append, (choices F e).extension.edges_eq, hpref]
          simp
      rw [hlocal, zero_add]
      apply Finset.sum_eq_zero
      intro e _
      have hchild_le :
          (choices F e).forest.activeEdges.card ≤ n := by
        have hlt :
            (choices F e).forest.activeEdges.card <
              F.activeEdges.card :=
          (choices F e).activeEdges_card_lt
        exact Nat.lt_succ_iff.mp (hlt.trans_le hle)
      have hprefChild :
          (pref ++ [e.val]).toFinset = (choices F e).forest.edges := by
        rw [List.toFinset_append, (choices F e).extension.edges_eq, hpref]
        simp
      have hzero :
          ∀ t : ℝ,
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ = 0 := by
        intro t
        exact
          boundarySupportOrderTreeFiber_eq_zero_of_order_toFinset_ne_edges
            choices n (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t I order ρ hchild_le hprefChild hI
      rw [show
          (fun t : ℝ =>
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ) = fun _ => 0 by
        funext t
        exact hzero t]
      simp

/--
A support/order fiber can only contribute along branches whose accumulated
prefix is still a prefix of the requested global order.
-/
theorem boundarySupportOrderTreeFiber_eq_zero_of_not_exists_pref_append
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (order : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      (¬ ∃ tail : List (Edge V), pref ++ tail = order) →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
        I order ρ = 0
  | 0, F, pref, prefixTs, top, I, order, ρ, hle, _hprefix => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      exact boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
        choices F pref prefixTs top I order ρ hF
  | n + 1, F, pref, prefixTs, top, I, order, ρ, hle, hprefix => by
      rw [boundarySupportOrderTreeFiber_def]
      have hlocal :
          localBoundarySupportOrderContribution choices F pref prefixTs top
            I order ρ = 0 := by
        rw [localBoundarySupportOrderContribution_def]
        rw [Finset.filter_eq_empty_iff.mpr]
        · exact Finset.sum_empty
        · intro e _ he
          apply hprefix
          exact ⟨[e.val], he.2⟩
      rw [hlocal, zero_add]
      apply Finset.sum_eq_zero
      intro e _
      have hchild_le :
          (choices F e).forest.activeEdges.card ≤ n := by
        have hlt :
            (choices F e).forest.activeEdges.card <
              F.activeEdges.card :=
          (choices F e).activeEdges_card_lt
        exact Nat.lt_succ_iff.mp (hlt.trans_le hle)
      have hchildPrefix :
          ¬ ∃ tail : List (Edge V),
            (pref ++ [e.val]) ++ tail = order := by
        intro hbad
        rcases hbad with ⟨tail, htail⟩
        apply hprefix
        refine ⟨e.val :: tail, ?_⟩
        rw [← @List.singleton_append (Edge V) e.val tail, ← List.append_assoc]
        exact htail
      have hzero :
          ∀ t : ℝ,
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ = 0 := by
        intro t
        exact
          boundarySupportOrderTreeFiber_eq_zero_of_not_exists_pref_append
            choices n (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t I order ρ hchild_le hchildPrefix
      rw [show
          (fun t : ℝ =>
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ) = fun _ => 0 by
        funext t
        exact hzero t]
      simp

/-- Root fibers vanish unless the requested order has the requested support. -/
theorem rootBoundarySupportOrderContribution_eq_zero_of_order_toFinset_ne_edges
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (hI : order.toFinset ≠ I.edges) :
    rootBoundarySupportOrderContribution choices ρ I order = 0 := by
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
    choices ρ I order (by
      intro hmarker
      apply hI
      rw [hmarker.2, hmarker.1]
      simp)]
  exact
    boundarySupportOrderTreeFiber_eq_zero_of_order_toFinset_ne_edges
      choices (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1
      I order ρ le_rfl (by simp [Forest.empty_edges]) hI

/--
A support/order fiber can contribute only for canonical orders of the requested
support.
-/
theorem boundarySupportOrderTreeFiber_eq_zero_of_order_not_mem_edgeSetOrders
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (order : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      pref.toFinset = F.edges →
      pref.Nodup →
      order ∉ edgeSetOrders I.edges →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
        I order ρ = 0
  | 0, F, pref, prefixTs, top, I, order, ρ, hle, _hpref, _hnodup, _horder => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      exact boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
        choices F pref prefixTs top I order ρ hF
  | n + 1, F, pref, prefixTs, top, I, order, ρ, hle, hpref, hnodup, horder => by
      rw [boundarySupportOrderTreeFiber_def]
      have hlocal :
          localBoundarySupportOrderContribution choices F pref prefixTs top
            I order ρ = 0 := by
        rw [localBoundarySupportOrderContribution_def]
        rw [Finset.filter_eq_empty_iff.mpr]
        · exact Finset.sum_empty
        · intro e _ he
          apply horder
          rw [← he.2]
          exact
            activeExtension_prefixed_order_mem_edgeSetOrders_of_support_eq
              (choices F e) hpref hnodup he.1
      rw [hlocal, zero_add]
      apply Finset.sum_eq_zero
      intro e _
      have hchild_le :
          (choices F e).forest.activeEdges.card ≤ n := by
        have hlt :
            (choices F e).forest.activeEdges.card <
              F.activeEdges.card :=
          (choices F e).activeEdges_card_lt
        exact Nat.lt_succ_iff.mp (hlt.trans_le hle)
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
        have ha_edges : e.val ∈ F.edges := by
          rw [← hpref]
          exact List.mem_toFinset.mpr ha
        exact (choices F e).extension.new_not_mem ha_edges
      have hzero :
          ∀ t : ℝ,
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ = 0 := by
        intro t
        exact
          boundarySupportOrderTreeFiber_eq_zero_of_order_not_mem_edgeSetOrders
            choices n (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t I order ρ hchild_le hprefChild
            hnodupChild horder
      rw [show
          (fun t : ℝ =>
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ) = fun _ => 0 by
        funext t
        exact hzero t]
      simp

/-- Root fibers vanish off the canonical order set of the requested support. -/
theorem rootBoundarySupportOrderContribution_eq_zero_of_order_not_mem_edgeSetOrders
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (horder : order ∉ edgeSetOrders I.edges) :
    rootBoundarySupportOrderContribution choices ρ I order = 0 := by
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
    choices ρ I order (by
      intro hmarker
      apply horder
      rw [hmarker.2, hmarker.1, edgeSetOrders_empty]
      exact Finset.mem_singleton_self [])]
  exact
    boundarySupportOrderTreeFiber_eq_zero_of_order_not_mem_edgeSetOrders
      choices (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1
      I order ρ le_rfl (by simp [Forest.empty_edges])
      List.nodup_nil horder

/--
If the requested order continues with a nonempty tail after the next edge,
then the tree fiber follows exactly the child indexed by that next edge.
-/
theorem boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V)
    (e₀ : Edge V) (tail : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (he₀ : e₀ ∈ F.activeEdges)
    (htail : tail ≠ []) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I
        (pref ++ e₀ :: tail) ρ =
      ∫ t in 0..top,
        boundarySupportOrderTreeFiber choices
          (choices F ⟨e₀, he₀⟩).forest (pref ++ [e₀])
          (prefixTs ++ [t]) t I (pref ++ e₀ :: tail) ρ := by
  rw [boundarySupportOrderTreeFiber_def]
  have hlocal :
      localBoundarySupportOrderContribution choices F pref prefixTs top
        I (pref ++ e₀ :: tail) ρ = 0 := by
    apply
      localBoundarySupportOrderContribution_eq_zero_of_length_ne
        choices F pref prefixTs top I (pref ++ e₀ :: tail) ρ
    intro hlen
    have htailLength : tail.length = 0 := by
      simp only [List.length_append, List.length_cons] at hlen
      omega
    exact htail (List.length_eq_zero_iff.mp htailLength)
  rw [hlocal, zero_add]
  rw [Finset.sum_eq_single_of_mem ⟨e₀, he₀⟩ (Finset.mem_attach _ _)]
  intro e _ hne
  have hnotPrefix :
      ¬ ∃ rest : List (Edge V),
        (pref ++ [e.val]) ++ rest = pref ++ e₀ :: tail := by
    intro hbad
    rcases hbad with ⟨rest, hrest⟩
    have hcancel : e.val :: rest = e₀ :: tail := by
      have hsame :
          pref ++ (e.val :: rest) = pref ++ (e₀ :: tail) := by
        rw [← @List.singleton_append (Edge V) e.val rest, ← List.append_assoc]
        exact hrest
      exact List.append_cancel_left hsame
    have hfirst : e.val = e₀ := by
      exact (List.cons.inj hcancel).1
    apply hne
    exact Subtype.ext hfirst
  have hzero :
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t I (pref ++ e₀ :: tail) ρ) = fun _ => 0 := by
    funext t
    exact
      boundarySupportOrderTreeFiber_eq_zero_of_not_exists_pref_append
        choices (choices F e).forest.activeEdges.card (choices F e).forest
        (pref ++ [e.val]) (prefixTs ++ [t]) t I (pref ++ e₀ :: tail)
        ρ le_rfl hnotPrefix
  rw [hzero]
  simp

/-- If the next requested edge is not active, the whole fiber is zero. -/
theorem boundarySupportOrderTreeFiber_eq_zero_of_next_not_mem_activeEdges
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V)
    (e₀ : Edge V) (tail : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (he₀ : e₀ ∉ F.activeEdges) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I
        (pref ++ e₀ :: tail) ρ = 0 := by
  rw [boundarySupportOrderTreeFiber_def]
  have hlocal :
      localBoundarySupportOrderContribution choices F pref prefixTs top
        I (pref ++ e₀ :: tail) ρ = 0 := by
    rw [localBoundarySupportOrderContribution_def]
    rw [Finset.filter_eq_empty_iff.mpr]
    · exact Finset.sum_empty
    · intro e _ he
      have hsame : [e.val] = e₀ :: tail := by
        have hsamePref : pref ++ [e.val] = pref ++ (e₀ :: tail) := by
          exact he.2
        exact List.append_cancel_left hsamePref
      have hfirst : e.val = e₀ :=
        (List.cons.inj hsame).1
      exact he₀ (hfirst ▸ e.property)
  rw [hlocal, zero_add]
  apply Finset.sum_eq_zero
  intro e _
  have hnotPrefix :
      ¬ ∃ rest : List (Edge V),
        (pref ++ [e.val]) ++ rest = pref ++ e₀ :: tail := by
    intro hbad
    rcases hbad with ⟨rest, hrest⟩
    have hsame : e.val :: rest = e₀ :: tail := by
      have hsamePref :
          pref ++ (e.val :: rest) = pref ++ (e₀ :: tail) := by
        rw [← @List.singleton_append (Edge V) e.val rest, ← List.append_assoc]
        exact hrest
      exact List.append_cancel_left hsamePref
    have hfirst : e.val = e₀ :=
      (List.cons.inj hsame).1
    exact he₀ (hfirst ▸ e.property)
  have hzero :
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t I (pref ++ e₀ :: tail) ρ) = fun _ => 0 := by
    funext t
    exact
      boundarySupportOrderTreeFiber_eq_zero_of_not_exists_pref_append
        choices (choices F e).forest.activeEdges.card (choices F e).forest
        (pref ++ [e.val]) (prefixTs ++ [t]) t I (pref ++ e₀ :: tail)
        ρ le_rfl hnotPrefix
  rw [hzero]
  simp

/--
If a requested suffix cannot be followed through the selected active
extensions, the corresponding fixed support/order fiber is zero.
-/
theorem boundarySupportOrderTreeFiber_eq_zero_of_followOrder_eq_none
    (choices : ActiveExtensionChoice V) :
    ∀ (order : List (Edge V)) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (ρ : (Edge V → ℝ) → ℝ),
      followOrderOption choices F order = none →
      boundarySupportOrderTreeFiber choices F pref prefixTs top I
        (pref ++ order) ρ = 0
  | [], _F, _pref, _prefixTs, _top, _I, _ρ, hnone => by
      simp [followOrderOption] at hnone
  | e :: tail, F, pref, prefixTs, top, I, ρ, hnone => by
      by_cases he : e ∈ F.activeEdges
      · simp only [followOrderOption, dite_eq_left he] at hnone
        by_cases htail : tail = []
        · subst tail
          simp [followOrderOption] at hnone
        · rw [show
            boundarySupportOrderTreeFiber choices F pref prefixTs top I
                (pref ++ (e :: tail)) ρ =
              ∫ t in 0..top,
                boundarySupportOrderTreeFiber choices
                  (choices F ⟨e, he⟩).forest (pref ++ [e])
                  (prefixTs ++ [t]) t I
                  (pref ++ (e :: tail)) ρ by
          exact
            boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
              choices F pref prefixTs top I e tail ρ he htail]
          have hzero :
              (fun t : ℝ =>
                boundarySupportOrderTreeFiber choices
                  (choices F ⟨e, he⟩).forest (pref ++ [e])
                  (prefixTs ++ [t]) t I
                  (pref ++ (e :: tail)) ρ) = fun _ => 0 := by
            funext t
            have hchild :=
              boundarySupportOrderTreeFiber_eq_zero_of_followOrder_eq_none
                choices tail (choices F ⟨e, he⟩).forest
                (pref ++ [e]) (prefixTs ++ [t]) t I ρ hnone
            rw [← @List.singleton_append (Edge V) e tail, ← List.append_assoc]
            exact hchild
          rw [hzero]
          simp
      · exact
          boundarySupportOrderTreeFiber_eq_zero_of_next_not_mem_activeEdges
            choices F pref prefixTs top I e tail ρ he

/--
Along a chosen growth path, the fixed support/order tree fiber is exactly the
corresponding ordered simplex integral.  This is the arbitrary finite-order
version of the explicit one- and two-edge bridge lemmas below.
-/
theorem boundarySupportOrderTreeFiber_chosenGrowth_eq_orderedSimplexIntegralAux
    (choices : ActiveExtensionChoice V)
    {F G : Forest V} {order : List (Edge V)}
    (path : ChosenGrowth choices F order G) :
    ∀ (pref : List (Edge V)) (prefixTs : List ℝ) (top : ℝ)
      (ρ : (Edge V → ℝ) → ℝ),
      order ≠ [] →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
          G.support (pref ++ order) ρ =
        orderedSimplexIntegralAux top order
          (fun ts => mixedPartialList (pref ++ order).reverse ρ
            (G.standardInterp
              (G.paramsOfOrder (pref ++ order) (prefixTs ++ ts))))
  := by
  induction path with
  | nil F =>
      intro pref prefixTs top ρ horder
      exact False.elim (horder rfl)
  | cons he tail ih =>
      rename_i F0 G0 e0 order0
      intro pref prefixTs top ρ _horder
      cases tail with
      | nil Fchild =>
          rw [boundarySupportOrderTreeFiber_eq_localBoundary_of_order_length_eq_succ
            choices F0 pref prefixTs top
            (choices F0 ⟨e0, he⟩).forest.support (pref ++ [e0]) ρ
            (by simp)]
          rw [localBoundarySupportOrderContribution_def]
          let e₁ : {e // e ∈ F0.activeEdges} := ⟨e0, he⟩
          have hfilter :
              F0.activeEdges.attach.filter
                  (fun e =>
                    (choices F0 e).forest.support =
                        (choices F0 ⟨e0, he⟩).forest.support ∧
                      pref ++ [e.val] = pref ++ [e₁.val]) =
                {e₁} := by
            ext e
            rw [Finset.mem_filter, Finset.mem_singleton]
            constructor
            · intro h
              exact Subtype.ext (by
                have hcancel : [e.val] = [e₁.val] :=
                  List.append_cancel_left h.2.2
                exact (List.cons.inj hcancel).1)
            · intro h
              rw [h]
              constructor
              · exact Finset.mem_attach _ _
              · constructor
                · rfl
                · rfl
          rw [hfilter, Finset.sum_singleton]
      | cons he₂ tail₂ =>
          rename_i F1 eNext orderTail
          rw [show
              boundarySupportOrderTreeFiber choices F0 pref prefixTs top
                  _ (pref ++ (e0 :: eNext :: orderTail)) ρ =
                ∫ t in 0..top,
                  boundarySupportOrderTreeFiber choices
                    (choices F0 ⟨e0, he⟩).forest (pref ++ [e0])
                    (prefixTs ++ [t]) t _
                    (pref ++ (e0 :: eNext :: orderTail)) ρ by
            exact
              boundarySupportOrderTreeFiber_eq_integral_child_of_tail_ne_nil
                choices F0 pref prefixTs top _ e0
                (eNext :: orderTail) ρ he (by simp)]
          rw [orderedSimplexIntegralAux_cons]
          apply intervalIntegral.integral_congr
          intro t _ht
          have hchild :=
            ih (pref ++ [e0]) (prefixTs ++ [t]) t ρ (by simp)
          simpa only [List.singleton_append, List.append_assoc] using hchild

/--
Root specialization of
`boundarySupportOrderTreeFiber_chosenGrowth_eq_orderedSimplexIntegralAux`.
-/
theorem rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (path : ChosenGrowth choices (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ)
    (horder : order ≠ []) :
    rootBoundarySupportOrderContribution choices ρ G.support order =
      G.orderedContribution order ρ := by
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
    choices ρ G.support order (by
      intro hmarker
      exact horder hmarker.2)]
  have h :=
    boundarySupportOrderTreeFiber_chosenGrowth_eq_orderedSimplexIntegralAux
      choices path [] [] 1 ρ horder
  rw [orderedContribution, orderedSimplexIntegral]
  simpa only [List.nil_append] using h

/-- Root fiber bridge stated in terms of the deterministic order follower. -/
theorem rootBoundarySupportOrderContribution_eq_orderedContribution_of_followOrder_eq_some
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (hG : followOrderOption choices (Forest.empty V) order = some G)
    (ρ : (Edge V → ℝ) → ℝ)
    (horder : order ≠ []) :
    rootBoundarySupportOrderContribution choices ρ G.support order =
      G.orderedContribution order ρ :=
  rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
    choices (chosenGrowth_of_followOrderOption_eq_some choices hG) ρ horder

/-- A failed deterministic root order has zero contribution in every support fiber. -/
theorem rootBoundarySupportOrderContribution_eq_zero_of_followOrder_eq_none
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) {order : List (Edge V)}
    (horder : followOrderOption choices (Forest.empty V) order = none)
    (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ I order = 0 := by
  cases order with
  | nil =>
      simp [followOrderOption] at horder
  | cons e tail =>
      rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
        choices ρ I (e :: tail) (by
          intro hmarker
          cases hmarker.2)]
      exact
        boundarySupportOrderTreeFiber_eq_zero_of_followOrder_eq_none
          choices (e :: tail) (Forest.empty V) [] [] 1 I ρ horder

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
