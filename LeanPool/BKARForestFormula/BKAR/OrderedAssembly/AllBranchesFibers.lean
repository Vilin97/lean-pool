/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import LeanPool.BKARForestFormula.BKAR.OrderedAssembly.AllBranchesTelescoping

/-! # Fibers of the boundary tree sum

Defines `boundarySupportOrderTreeFiber`, the contribution of the boundary
tree sum in the fiber over a prescribed final support and order, together
with `supportOrderPairs` and the integrability certificates for these
fibers.  Vanishing lemmas dispose of fibers whose order is too short or
whose node has no active edges.  The root fibers assemble into the
support/order form of the BKAR forest interpolation formula (see
`BKAR.Formula`).
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Finite support/order pairs used by the final folded tree sum. -/
noncomputable def supportOrderPairs (V : Type*) [Fintype V]
    [DecidableEq V] : Finset (Σ _ : ForestIndex V, List (Edge V)) :=
  (Finset.univ : Finset (ForestIndex V)).sigma
    (fun I => edgeSetOrders I.edges)

/--
The folded contribution of the boundary tree lying over one fixed global
support/order pair.
-/
noncomputable def boundarySupportOrderTreeFiber
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  localBoundarySupportOrderContribution choices F pref prefixTs top I order ρ +
    Finset.sum F.activeEdges.attach
      (fun e => ∫ t in 0..top,
        boundarySupportOrderTreeFiber choices
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t I order ρ)
termination_by F.activeEdges.card
decreasing_by
  exact (choices F e).activeEdges_card_lt

theorem boundarySupportOrderTreeFiber_def
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I order ρ =
      localBoundarySupportOrderContribution choices F pref prefixTs top
        I order ρ +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
              t I order ρ) := by
  rw [boundarySupportOrderTreeFiber]

theorem boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hF : F.activeEdges = ∅) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I order ρ =
      0 := by
  rw [boundarySupportOrderTreeFiber_def]
  rw [localBoundarySupportOrderContribution_def]
  have hattach : F.activeEdges.attach = ∅ := by
    rw [hF]
    rfl
  simp [hattach]

/--
A support/order fiber is zero once the requested global order is no longer
long enough to contain the current prefix plus one more boundary edge.
-/
theorem boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (I : ForestIndex V)
      (order : List (Edge V)) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      order.length ≤ pref.length →
      boundarySupportOrderTreeFiber choices F pref prefixTs top
        I order ρ = 0
  | 0, F, pref, prefixTs, top, I, order, ρ, hle, _hlen => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      exact boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
        choices F pref prefixTs top I order ρ hF
  | n + 1, F, pref, prefixTs, top, I, order, ρ, hle, hlen => by
      rw [boundarySupportOrderTreeFiber_def]
      have hlocal :
          localBoundarySupportOrderContribution choices F pref prefixTs top
            I order ρ = 0 := by
        rw [localBoundarySupportOrderContribution_def]
        rw [Finset.filter_eq_empty_iff.mpr]
        · simp
        · intro e _ he
          have horder : pref ++ [e.val] = order := he.2
          have hlen_eq :
              pref.length + 1 = order.length := by
            simpa using congrArg List.length horder
          have hbad : pref.length + 1 ≤ pref.length := by
            rw [hlen_eq]
            exact hlen
          exact Nat.not_succ_le_self pref.length hbad
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
      have hchild_len :
          order.length ≤ (pref ++ [e.val]).length := by
        exact hlen.trans (by simp)
      have hzero :
          ∀ t : ℝ,
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ = 0 := by
        intro t
        exact
          boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
            choices n (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t I order ρ hchild_le hchild_len
      rw [show
          (fun t : ℝ =>
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t I order ρ) = fun _ => 0 by
        funext t
        exact hzero t]
      simp

theorem boundarySupportOrderTreeFiber_empty_order_eq_zero
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
      I [] ρ = 0 :=
  boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
    choices (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1
    I [] ρ le_rfl (by simp)

theorem boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_le_pref_length
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hlen : order.length ≤ pref.length) :
    IntervalIntegrable
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices F pref prefixTs t I order ρ)
      MeasureTheory.volume 0 top := by
  have hzero :
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices F pref prefixTs t I order ρ) =
        fun _ => 0 := by
    funext t
    exact
      boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
        choices F.activeEdges.card F pref prefixTs t I order ρ le_rfl hlen
  rw [hzero]
  exact continuous_const.intervalIntegrable 0 top

theorem boundarySupportOrderTreeFiber_intervalIntegrable_of_support_edges_eq_empty
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ)
    (hI : I.edges = ∅)
    (horder : order ∈ edgeSetOrders I.edges) :
    IntervalIntegrable
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices F pref prefixTs t I order ρ)
      MeasureTheory.volume 0 top := by
  have horder_nil : order = [] := by
    have horder' : order ∈ edgeSetOrders (∅ : Finset (Edge V)) := by
      simpa [hI] using horder
    rw [edgeSetOrders_empty] at horder'
    exact Finset.mem_singleton.mp horder'
  rw [horder_nil]
  exact
    boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_le_pref_length
      choices F pref prefixTs top I [] ρ (by simp)

/--
Linearity hypotheses needed to commute the finite support/order fiber sum
through the recursive child integrals.
-/
def boundarySupportOrderTreeFiberIntegrable
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, F, pref, prefixTs, top, ρ =>
      (∀ e : {e // e ∈ F.activeEdges},
        ∀ x ∈ supportOrderPairs V,
          IntervalIntegrable
            (fun t : ℝ =>
              boundarySupportOrderTreeFiber choices
                (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t x.1 x.2 ρ)
            MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges}, ∀ t ∈ Set.uIcc 0 top,
        boundarySupportOrderTreeFiberIntegrable choices n
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t ρ)

theorem boundarySupportOrderTreeFiberIntegrable_zero
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeFiberIntegrable choices 0
      F pref prefixTs top ρ :=
  trivial

theorem boundarySupportOrderTreeFiberIntegrable_of_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges = ∅ →
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ
  | 0, _F, _pref, _prefixTs, _top, _ρ, _hF => by
      trivial
  | n + 1, F, _pref, _prefixTs, _top, _ρ, hF => by
      constructor
      · intro e _x _hx
        have he : e.val ∈ (∅ : Finset (Edge V)) := by
          simpa [hF] using e.property
        exact False.elim (Finset.notMem_empty e.val he)
      · intro e _t _ht
        have he : e.val ∈ (∅ : Finset (Edge V)) := by
          simpa [hF] using e.property
        exact False.elim (Finset.notMem_empty e.val he)

/--
The genuinely remaining fiber-integrability obligation. It only asks for
support/order fibers not already killed by the structural zero lemmas: the
target support is nonempty and the target order is strictly longer than the
child prefix.
-/
def boundarySupportOrderTreeFiberNontrivialIntegrable
    (choices : ActiveExtensionChoice V) :
    Nat → (F : Forest V) → List (Edge V) → List ℝ → ℝ →
      ((Edge V → ℝ) → ℝ) → Prop
  | 0, _, _, _, _, _ => True
  | n + 1, F, pref, prefixTs, top, ρ =>
      (∀ e : {e // e ∈ F.activeEdges},
        ∀ x ∈ supportOrderPairs V,
          (pref ++ [e.val]).length < x.2.length →
          x.1.edges ≠ ∅ →
          IntervalIntegrable
            (fun t : ℝ =>
              boundarySupportOrderTreeFiber choices
                (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t x.1 x.2 ρ)
            MeasureTheory.volume 0 top) ∧
      (∀ e : {e // e ∈ F.activeEdges}, ∀ t ∈ Set.uIcc 0 top,
        boundarySupportOrderTreeFiberNontrivialIntegrable choices n
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
          t ρ)

theorem boundarySupportOrderTreeFiberNontrivialIntegrable_zero
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeFiberNontrivialIntegrable choices 0
      F pref prefixTs top ρ :=
  trivial

theorem boundarySupportOrderTreeFiberNontrivialIntegrable_of_le
    (choices : ActiveExtensionChoice V) :
    ∀ {m n : Nat} {F : Forest V} {pref : List (Edge V)}
      {prefixTs : List ℝ} {top : ℝ} {ρ : (Edge V → ℝ) → ℝ},
      m ≤ n →
      boundarySupportOrderTreeFiberNontrivialIntegrable choices n
        F pref prefixTs top ρ →
      boundarySupportOrderTreeFiberNontrivialIntegrable choices m
        F pref prefixTs top ρ
  | 0, _n, _F, _pref, _prefixTs, _top, _ρ, _hle, _hfiber => by
      trivial
  | m + 1, 0, _F, _pref, _prefixTs, _top, _ρ, hle, _hfiber => by
      exact False.elim (Nat.not_succ_le_zero m hle)
  | m + 1, n + 1, F, pref, prefixTs, top, ρ, hle, hfiber => by
      rcases hfiber with ⟨hInt, hchild⟩
      refine ⟨hInt, ?_⟩
      intro e t ht
      exact
        boundarySupportOrderTreeFiberNontrivialIntegrable_of_le choices
          (Nat.succ_le_succ_iff.mp hle) (hchild e t ht)

/--
The exact-depth child nontrivial fiber-integrability hypothesis contained in
the parent exact-depth hypothesis.
-/
theorem boundarySupportOrderTreeFiberNontrivialIntegrable.child_activeEdges_card
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hfiber :
      boundarySupportOrderTreeFiberNontrivialIntegrable choices
        F.activeEdges.card F pref prefixTs top ρ)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 top) :
    boundarySupportOrderTreeFiberNontrivialIntegrable choices
      (choices F e).forest.activeEdges.card
      (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ := by
  have hcard_pos : 0 < F.activeEdges.card :=
    Finset.card_pos.mpr ⟨e.val, e.property⟩
  rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcard_pos) with
    ⟨n, hn⟩
  rw [hn] at hfiber
  rcases hfiber with ⟨_hInt, hchild⟩
  have hchild_le :
      (choices F e).forest.activeEdges.card ≤ n := by
    have hlt :
        (choices F e).forest.activeEdges.card < F.activeEdges.card :=
      (choices F e).activeEdges_card_lt
    rw [hn] at hlt
    exact Nat.lt_succ_iff.mp hlt
  exact
    boundarySupportOrderTreeFiberNontrivialIntegrable_of_le choices
      hchild_le (hchild e t ht)

theorem boundarySupportOrderTreeFiberIntegrable_of_nontrivialIntegrable
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      boundarySupportOrderTreeFiberNontrivialIntegrable choices n
        F pref prefixTs top ρ →
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ
  | 0, _F, _pref, _prefixTs, _top, _ρ, _hcore => by
      trivial
  | n + 1, F, pref, prefixTs, top, ρ, hcore => by
      rcases hcore with ⟨hInt, hchild⟩
      constructor
      · intro e x hx
        by_cases hlen : x.2.length ≤ (pref ++ [e.val]).length
        · have hzero :
              (fun t : ℝ =>
                boundarySupportOrderTreeFiber choices
                  (choices F e).forest (pref ++ [e.val])
                  (prefixTs ++ [t]) t x.1 x.2 ρ) = fun _ => 0 := by
            funext t
            exact
              boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
                choices (choices F e).forest.activeEdges.card
                (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
                t x.1 x.2 ρ le_rfl hlen
          rw [hzero]
          exact continuous_const.intervalIntegrable 0 top
        · have hlt : (pref ++ [e.val]).length < x.2.length :=
            Nat.lt_of_not_ge hlen
          have hxmem := hx
          rw [supportOrderPairs, Finset.mem_sigma] at hxmem
          by_cases hI : x.1.edges = ∅
          · have horder_nil : x.2 = [] := by
              have horder' :
                  x.2 ∈ edgeSetOrders (∅ : Finset (Edge V)) := by
                simpa [hI] using hxmem.2
              rw [edgeSetOrders_empty] at horder'
              exact Finset.mem_singleton.mp horder'
            have hzero :
                (fun t : ℝ =>
                  boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t x.1 x.2 ρ) = fun _ => 0 := by
              funext t
              rw [horder_nil]
              exact
                boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
                  choices (choices F e).forest.activeEdges.card
                  (choices F e).forest (pref ++ [e.val])
                  (prefixTs ++ [t]) t x.1 [] ρ le_rfl (by simp)
            rw [hzero]
            exact continuous_const.intervalIntegrable 0 top
          · exact hInt e x hx hlt hI
      · intro e t ht
        exact
          boundarySupportOrderTreeFiberIntegrable_of_nontrivialIntegrable
            choices n (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t ρ (hchild e t ht)

theorem localBoundarySupportOrderSum_eq_sum_supportOrderPairs
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    localBoundarySupportOrderSum choices F pref prefixTs top ρ =
      Finset.sum (supportOrderPairs V)
        (fun x =>
          localBoundarySupportOrderContribution choices F pref prefixTs top
            x.1 x.2 ρ) := by
  rw [localBoundarySupportOrderSum_def, supportOrderPairs, Finset.sum_sigma]

/--
The folded boundary tree is the finite sum of its global support/order fibers.
-/
theorem boundarySupportOrderTreeContribution_eq_sum_supportOrderPairs_treeFiber_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      F.activeEdges.card ≤ n →
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ →
      boundarySupportOrderTreeContribution choices F pref prefixTs top ρ =
        Finset.sum (supportOrderPairs V)
          (fun x =>
            boundarySupportOrderTreeFiber choices F pref prefixTs top
              x.1 x.2 ρ)
  | 0, F, pref, prefixTs, top, ρ, hle, _hfiber => by
      have hcard : F.activeEdges.card = 0 :=
        Nat.eq_zero_of_le_zero hle
      have hF : F.activeEdges = ∅ :=
        Finset.card_eq_zero.mp hcard
      rw [boundarySupportOrderTreeContribution_eq_zero_of_activeEdges_eq_empty
        choices F pref prefixTs top ρ hF]
      apply Eq.symm
      apply Finset.sum_eq_zero
      intro x _
      rw [boundarySupportOrderTreeFiber_eq_zero_of_activeEdges_eq_empty
        choices F pref prefixTs top x.1 x.2 ρ hF]
  | n + 1, F, pref, prefixTs, top, ρ, hle, hfiber => by
      rcases hfiber with ⟨hInt, hchildFiber⟩
      rw [boundarySupportOrderTreeContribution_def]
      rw [localBoundarySupportOrderSum_eq_sum_supportOrderPairs]
      rw [show
          Finset.sum (supportOrderPairs V)
              (fun x =>
                boundarySupportOrderTreeFiber choices F pref prefixTs top
                  x.1 x.2 ρ) =
            Finset.sum (supportOrderPairs V)
              (fun x =>
                localBoundarySupportOrderContribution choices F pref prefixTs
                    top x.1 x.2 ρ +
                  Finset.sum F.activeEdges.attach
                    (fun e => ∫ t in 0..top,
                      boundarySupportOrderTreeFiber choices
                        (choices F e).forest (pref ++ [e.val])
                        (prefixTs ++ [t]) t x.1 x.2 ρ)) by
        apply Finset.sum_congr rfl
        intro x _
        rw [boundarySupportOrderTreeFiber_def]]
      rw [Finset.sum_add_distrib]
      apply congrArg
        (fun r =>
          Finset.sum (supportOrderPairs V)
              (fun x =>
                localBoundarySupportOrderContribution choices F pref prefixTs
                  top x.1 x.2 ρ) + r)
      calc
        Finset.sum F.activeEdges.attach
            (fun e => ∫ t in 0..top,
              boundarySupportOrderTreeContribution choices
                (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t ρ) =
          Finset.sum F.activeEdges.attach
            (fun e => ∫ t in 0..top,
              Finset.sum (supportOrderPairs V)
                (fun x =>
                  boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t x.1 x.2 ρ)) := by
            apply Finset.sum_congr rfl
            intro e _
            apply intervalIntegral.integral_congr
            intro t ht
            have hchild_le :
                (choices F e).forest.activeEdges.card ≤ n := by
              have hlt :
                  (choices F e).forest.activeEdges.card <
                    F.activeEdges.card :=
                (choices F e).activeEdges_card_lt
              exact Nat.lt_succ_iff.mp (hlt.trans_le hle)
            exact
              boundarySupportOrderTreeContribution_eq_sum_supportOrderPairs_treeFiber_of_activeEdges_card_le
                choices n (choices F e).forest (pref ++ [e.val])
                (prefixTs ++ [t]) t ρ hchild_le (hchildFiber e t ht)
        _ =
          Finset.sum F.activeEdges.attach
            (fun e =>
              Finset.sum (supportOrderPairs V)
                (fun x => ∫ t in 0..top,
                  boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t x.1 x.2 ρ)) := by
            apply Finset.sum_congr rfl
            intro e _
            rw [intervalIntegral.integral_finsetSum (hInt e)]
        _ =
          Finset.sum (supportOrderPairs V)
            (fun x =>
              Finset.sum F.activeEdges.attach
                (fun e => ∫ t in 0..top,
                  boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t x.1 x.2 ρ)) := by
            rw [Finset.sum_comm]

theorem boundarySupportOrderTreeContribution_eq_sum_treeFiber_of_activeEdges_card_le
    (choices : ActiveExtensionChoice V)
    (n : Nat) (F : Forest V) (pref : List (Edge V))
    (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hle : F.activeEdges.card ≤ n)
    (hfiber :
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ) :
    boundarySupportOrderTreeContribution choices F pref prefixTs top ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            boundarySupportOrderTreeFiber choices F pref prefixTs top
              I order ρ)) := by
  have h :=
    boundarySupportOrderTreeContribution_eq_sum_supportOrderPairs_treeFiber_of_activeEdges_card_le
      choices n F pref prefixTs top ρ hle hfiber
  rw [supportOrderPairs, Finset.sum_sigma] at h
  exact h

/--
The final root support/order contribution: the empty sector contributes
`ρ zeroConfig`, and every nonempty sector is supplied by the folded tree fiber.
-/
noncomputable def rootBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V)) : ℝ :=
  (if I.edges = ∅ ∧ order = [] then ρ zeroConfig else 0) +
    boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
      I order ρ

theorem rootBoundarySupportOrderContribution_def
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V)) :
    rootBoundarySupportOrderContribution choices ρ I order =
      (if I.edges = ∅ ∧ order = [] then ρ zeroConfig else 0) +
        boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
          I order ρ :=
  rfl

theorem rootBoundarySupportOrderContribution_empty_order_eq_zeroConfig
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V)
    (hI : I.edges = ∅) :
    rootBoundarySupportOrderContribution choices ρ I [] = ρ zeroConfig := by
  rw [rootBoundarySupportOrderContribution_def]
  rw [if_pos ⟨hI, rfl⟩]
  rw [boundarySupportOrderTreeFiber_empty_order_eq_zero]
  simp

theorem rootBoundarySupportOrderContribution_eq_zeroConfig_of_edges_eq_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (hI : I.edges = ∅)
    (horder : order ∈ edgeSetOrders I.edges) :
    rootBoundarySupportOrderContribution choices ρ I order =
      ρ zeroConfig := by
  have horder_nil : order = [] := by
    have horder' : order ∈ edgeSetOrders (∅ : Finset (Edge V)) := by
      simpa [hI] using horder
    rw [edgeSetOrders_empty] at horder'
    exact Finset.mem_singleton.mp horder'
  rw [horder_nil]
  exact
    rootBoundarySupportOrderContribution_empty_order_eq_zeroConfig
      choices ρ I hI

theorem rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (hmarker : ¬ (I.edges = ∅ ∧ order = [])) :
    rootBoundarySupportOrderContribution choices ρ I order =
      boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
        I order ρ := by
  rw [rootBoundarySupportOrderContribution_def]
  rw [if_neg hmarker]
  simp

theorem rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V))
    (hI : I.edges ≠ ∅) :
    rootBoundarySupportOrderContribution choices ρ I order =
      boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
        I order ρ := by
  exact
    rootBoundarySupportOrderContribution_eq_treeFiber_of_not_empty_marker
      choices ρ I order (by
        intro hmarker
        exact hI hmarker.1)

theorem rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (hI : I.edges = ∅) :
    rootBoundarySupportOrderContribution choices ρ I [] =
      (Forest.empty V).orderedContribution [] ρ := by
  rw [rootBoundarySupportOrderContribution_empty_order_eq_zeroConfig
    choices ρ I hI]
  rw [orderedContribution_empty]

theorem boundarySupportOrderTreeFiber_empty_singleton_eq_localBoundary
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (a : Edge V)
    (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1 I [a] ρ =
      localBoundarySupportOrderContribution choices (Forest.empty V) [] [] 1
        I [a] ρ := by
  rw [boundarySupportOrderTreeFiber_def]
  have hsum :
      Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            boundarySupportOrderTreeFiber choices
              (choices (Forest.empty V) e).forest ([] ++ [e.val])
              ([] ++ [t]) t I [a] ρ) = 0 := by
    apply Finset.sum_eq_zero
    intro e _
    have hzero :
        (fun t : ℝ =>
          boundarySupportOrderTreeFiber choices
            (choices (Forest.empty V) e).forest ([] ++ [e.val])
            ([] ++ [t]) t I [a] ρ) = fun _ => 0 := by
      funext t
      exact
        boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
          choices (choices (Forest.empty V) e).forest.activeEdges.card
          (choices (Forest.empty V) e).forest ([] ++ [e.val])
          ([] ++ [t]) t I [a] ρ le_rfl (by simp)
    rw [hzero]
    simp
  rw [hsum, add_zero]

theorem rootBoundarySupportOrderContribution_singleton_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ (ForestIndex.singleton a) [a] =
      (choices (Forest.empty V) (emptyActiveEdge a)).forest.orderedContribution
        [a] ρ := by
  have hnonempty : (ForestIndex.singleton a : ForestIndex V).edges ≠ ∅ := by
    rw [ForestIndex.singleton_edges]
    exact Finset.singleton_ne_empty a
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
    choices ρ (ForestIndex.singleton a) [a] hnonempty]
  rw [boundarySupportOrderTreeFiber_empty_singleton_eq_localBoundary]
  rw [localBoundarySupportOrderContribution_def]
  have hfilter :
      (Forest.empty V).activeEdges.attach.filter
          (fun e =>
            (choices (Forest.empty V) e).forest.support =
                ForestIndex.singleton a ∧
              [] ++ [e.val] = [a]) =
        {emptyActiveEdge a} := by
    ext e
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · intro h
      apply Subtype.ext
      have horder := h.2.2
      simp only [List.nil_append] at horder
      injection horder
    · intro h
      rw [h]
      constructor
      · exact Finset.mem_attach _ _
      · constructor
        · exact activeExtension_forest_support_eq_singleton_empty
            (choices (Forest.empty V) (emptyActiveEdge a))
        · simp
  rw [hfilter, Finset.sum_singleton]
  simp only [orderedContribution, orderedSimplexIntegral, emptyActiveEdge_val,
    List.nil_append]

theorem sum_emptySupportOrderMarker
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            if I.edges = ∅ ∧ order = [] then ρ zeroConfig else 0)) =
      ρ zeroConfig := by
  classical
  let I0 : ForestIndex V := (Forest.empty V).support
  have hI0edges : I0.edges = ∅ := rfl
  rw [Finset.sum_eq_single_of_mem I0 (Finset.mem_univ I0)]
  · rw [hI0edges, edgeSetOrders_empty]
    rw [Finset.sum_singleton]
    simp
  · intro I _ hne
    apply Finset.sum_eq_zero
    intro order _
    have hIedges : I.edges ≠ ∅ := by
      intro hempty
      apply hne
      apply ForestIndex.ext
      rw [hempty, hI0edges]
    simp [hIedges]

theorem sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            rootBoundarySupportOrderContribution choices ρ I order)) =
      ρ zeroConfig +
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
                I order ρ)) := by
  rw [show
      Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              rootBoundarySupportOrderContribution choices ρ I order)) =
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I =>
            Finset.sum (edgeSetOrders I.edges)
              (fun order =>
                if I.edges = ∅ ∧ order = [] then ρ zeroConfig else 0) +
            Finset.sum (edgeSetOrders I.edges)
              (fun order =>
                boundarySupportOrderTreeFiber choices (Forest.empty V) [] []
                  1 I order ρ)) by
    apply Finset.sum_congr rfl
    intro I _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro order _
    rw [rootBoundarySupportOrderContribution_def]]
  rw [Finset.sum_add_distrib]
  rw [sum_emptySupportOrderMarker]

theorem sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            rootBoundarySupportOrderContribution choices ρ I order)) =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
                I order ρ)) := by
  classical
  rw [sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber]
  apply congrArg (fun r => ρ zeroConfig + r)
  let f : ForestIndex V → ℝ :=
    fun I => Finset.sum (edgeSetOrders I.edges)
      (fun order =>
        boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
          I order ρ)
  have hsplit :
      Finset.sum (Finset.univ : Finset (ForestIndex V)) f =
        Finset.sum
            ((Finset.univ : Finset (ForestIndex V)).filter
              (fun I => I.edges ≠ ∅)) f +
          Finset.sum
            ((Finset.univ : Finset (ForestIndex V)).filter
              (fun I => ¬ I.edges ≠ ∅)) f := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (ForestIndex V)))
      (p := fun I => I.edges ≠ ∅) (f := f)]
  rw [hsplit]
  have hzero :
      Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => ¬ I.edges ≠ ∅)) f = 0 := by
    apply Finset.sum_eq_zero
    intro I hI
    rw [Finset.mem_filter] at hI
    have hIempty : I.edges = ∅ := by
      exact Classical.not_not.mp hI.2
    simp [hIempty, edgeSetOrders_empty,
      boundarySupportOrderTreeFiber_empty_order_eq_zero]
  rw [hzero, add_zero]

/--
Root BKAR identity with the folded boundary tree flattened into the final
global support/order sector sum. The empty support/order sector contributes
`ρ zeroConfig`.
-/
theorem rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hfiber :
      boundarySupportOrderTreeFiberIntegrable choices
        (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            rootBoundarySupportOrderContribution choices ρ I order)) := by
  rw [rho_oneConfig_eq_orderedSectorSum_empty_add_boundarySupportOrderTreeContribution
    choices ρ hanalytic]
  rw [orderedSectorSum_empty]
  rw [boundarySupportOrderTreeContribution_eq_sum_treeFiber_of_activeEdges_card_le
    choices (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ
    le_rfl hfiber]
  rw [← sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber
    choices ρ]

/--
Equivalent final-shaped root identity with the empty support removed from the
remaining tree-fiber sum.
-/
theorem rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hfiber :
      boundarySupportOrderTreeFiberIntegrable choices
        (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
                I order ρ)) := by
  rw [rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution
    choices ρ hanalytic hfiber]
  rw [sum_rootBoundarySupportOrderContribution_eq_zeroConfig_add_sum_treeFiber_filter_edges_ne_empty]

/--
Root identity whose remaining analytic side condition is restricted to the
nontrivial support/order fibers.
-/
theorem rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_nontrivialIntegrable
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hfiber :
      boundarySupportOrderTreeFiberNontrivialIntegrable choices
        (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
                I order ρ)) := by
  exact
    rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty
      choices ρ hanalytic
      (boundarySupportOrderTreeFiberIntegrable_of_nontrivialIntegrable
        choices (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1
        ρ hfiber)

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
