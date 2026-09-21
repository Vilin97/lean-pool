/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
import Mathlib.Data.List.GetD
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.List.Permutation
import LeanPool.BKARForestFormula.BKAR.OrderedTerminalGrowth

/-! # Enumerations of a finite edge set

Defines `edgeSetOrders S`, the finite set of duplicate-free lists
enumerating a finset of edges, and `edgeOrders F`, the enumerations of a
forest's edge set, with membership, cardinality, and head/tail
decomposition lemmas, together with the cube-coordinate parametrization
`paramsOfOrder` sending an ordered simplex parameter list to the
corresponding edge-parameter vector.  Sums over these orders convert
between order-by-order sector contributions and the order-free contribution
of a forest in the BKAR forest interpolation formula (see `BKAR.Formula`).
-/

noncomputable section

namespace BKAR

namespace Forest

variable {V : Type*} [Fintype V] [DecidableEq V]

def edgeSetOrders (S : Finset (Edge V)) : Finset (List (Edge V)) :=
  S.toList.permutations.toFinset

omit [Fintype V] in
theorem mem_edgeSetOrders_iff (S : Finset (Edge V))
    {order : List (Edge V)} :
    order ∈ edgeSetOrders S ↔ order.Perm S.toList := by
  rw [edgeSetOrders, List.mem_toFinset, List.mem_permutations]

omit [Fintype V] in
theorem mem_edgeSetOrders_iff_toFinset_eq_and_nodup
    (S : Finset (Edge V)) {order : List (Edge V)} :
    order ∈ edgeSetOrders S ↔ order.toFinset = S ∧ order.Nodup := by
  constructor
  · intro h
    have hperm : order.Perm S.toList :=
      (mem_edgeSetOrders_iff S).mp h
    constructor
    · ext e
      rw [List.mem_toFinset, ← Finset.mem_toList]
      exact hperm.mem_iff
    · exact hperm.nodup_iff.mpr (Finset.nodup_toList S)
  · intro h
    rw [mem_edgeSetOrders_iff]
    have htoList : order.toFinset.toList.Perm order :=
      List.toFinset_toList h.2
    have hforest : order.toFinset.toList.Perm S.toList :=
      (Finset.perm_toList).mpr h.1
    exact htoList.symm.trans hforest

omit [Fintype V] in
theorem toFinset_eq_of_mem_edgeSetOrders
    {S : Finset (Edge V)} {order : List (Edge V)}
    (h : order ∈ edgeSetOrders S) :
    order.toFinset = S :=
  ((mem_edgeSetOrders_iff_toFinset_eq_and_nodup S).mp h).1

omit [Fintype V] in
theorem nodup_of_mem_edgeSetOrders
    {S : Finset (Edge V)} {order : List (Edge V)}
    (h : order ∈ edgeSetOrders S) :
    order.Nodup :=
  ((mem_edgeSetOrders_iff_toFinset_eq_and_nodup S).mp h).2

omit [Fintype V] in
theorem card_edgeSetOrders (S : Finset (Edge V)) :
    (edgeSetOrders S).card = S.card.factorial := by
  rw [edgeSetOrders]
  rw [List.toFinset_card_of_nodup]
  · rw [List.length_permutations, Finset.length_toList]
  · exact List.nodup_permutations S.toList (Finset.nodup_toList S)

omit [Fintype V] in
theorem length_eq_card_of_mem_edgeSetOrders
    {S : Finset (Edge V)} {order : List (Edge V)}
    (h : order ∈ edgeSetOrders S) :
    order.length = S.card := by
  have hset := toFinset_eq_of_mem_edgeSetOrders h
  have hnodup := nodup_of_mem_edgeSetOrders h
  rw [← hset]
  exact (List.toFinset_card_of_nodup hnodup).symm

omit [Fintype V] in
theorem edgeSetOrders_empty :
    edgeSetOrders (∅ : Finset (Edge V)) = {[]} := by
  rw [edgeSetOrders, Finset.toList_empty, List.permutations_nil]
  rfl

omit [Fintype V] in
theorem eq_and_tail_eq_nil_of_cons_toFinset_eq_singleton_of_nodup
    {e a : Edge V} {tail : List (Edge V)}
    (hset : (e :: tail).toFinset = ({a} : Finset (Edge V)))
    (hnodup : (e :: tail).Nodup) :
    e = a ∧ tail = [] := by
  have heq : e = a := by
    have he_mem : e ∈ ({a} : Finset (Edge V)) := by
      rw [← hset]
      exact List.mem_toFinset.mpr (by
        rw [List.mem_cons]
        exact Or.inl rfl)
    exact Finset.mem_singleton.mp he_mem
  have htail : tail = [] := by
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    have hx_single : x = a := by
      have hx_mem : x ∈ ({a} : Finset (Edge V)) := by
        rw [← hset]
        exact List.mem_toFinset.mpr (List.mem_cons_of_mem e hx)
      exact Finset.mem_singleton.mp hx_mem
    have hxe : x = e := by
      rw [hx_single, ← heq]
    exact hnodup.notMem (hxe ▸ hx)
  exact ⟨heq, htail⟩

omit [Fintype V] in
theorem edgeSetOrders_singleton (a : Edge V) :
    edgeSetOrders ({a} : Finset (Edge V)) = {[a]} := by
  ext order
  constructor
  · intro h
    have hdata :=
      (mem_edgeSetOrders_iff_toFinset_eq_and_nodup
        ({a} : Finset (Edge V))).mp h
    cases order with
    | nil =>
        have hbad : a ∈ ([] : List (Edge V)).toFinset := by
          rw [hdata.1]
          exact Finset.mem_singleton_self a
        simp at hbad
    | cons e tail =>
        rcases
          eq_and_tail_eq_nil_of_cons_toFinset_eq_singleton_of_nodup
            hdata.1 hdata.2 with
          ⟨he, htail⟩
        subst e
        subst tail
        exact Finset.mem_singleton_self [a]
  · intro h
    rw [Finset.mem_singleton] at h
    subst order
    rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
    exact ⟨by simp, List.nodup_singleton a⟩

omit [Fintype V] in
theorem cons_mem_edgeSetOrders_iff
    (S : Finset (Edge V)) {e : Edge V} {order : List (Edge V)} :
    e :: order ∈ edgeSetOrders S ↔
      e ∈ S ∧ order ∈ edgeSetOrders (S.erase e) := by
  rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
  rw [mem_edgeSetOrders_iff_toFinset_eq_and_nodup]
  constructor
  · intro h
    rw [List.toFinset_cons] at h
    rw [List.nodup_cons] at h
    rcases h with ⟨hset, hnotMem, hnodup⟩
    have heS : e ∈ S := by
      rw [← hset]
      exact Finset.mem_insert_self e order.toFinset
    refine ⟨heS, ?_⟩
    constructor
    · ext x
      by_cases hxe : x = e
      · subst x
        rw [Finset.mem_erase, List.mem_toFinset]
        constructor
        · intro hx
          exact False.elim (hnotMem hx)
        · intro hx
          exact False.elim (hx.1 rfl)
      · rw [Finset.mem_erase, List.mem_toFinset]
        constructor
        · intro hx
          exact ⟨hxe, by
            rw [← hset]
            exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hx)⟩
        · intro hx
          have hxS : x ∈ insert e order.toFinset := by
            rw [hset]
            exact hx.2
          rw [Finset.mem_insert] at hxS
          exact hxS.elim (fun h => False.elim (hxe h))
            (fun hxFin => List.mem_toFinset.mp hxFin)
    · exact hnodup
  · intro h
    rcases h with ⟨heS, htail⟩
    rcases htail with ⟨hset, hnodup⟩
    rw [List.toFinset_cons]
    rw [List.nodup_cons]
    constructor
    · ext x
      rw [Finset.mem_insert]
      by_cases hxe : x = e
      · subst x
        simp [heS]
      · rw [hset, Finset.mem_erase]
        constructor
        · intro hx
          exact hx.elim (fun h => False.elim (hxe h)) (fun h => h.2)
        · intro hx
          exact Or.inr ⟨hxe, hx⟩
    · constructor
      · intro heOrder
        have heErase : e ∈ S.erase e := by
          rw [← hset, List.mem_toFinset]
          exact heOrder
        exact (Finset.notMem_erase e S) heErase
      · exact hnodup

omit [Fintype V] in
/-- First-edge/tail-order pairs attached to a finite edge set. -/
def edgeSetOrderTails (S : Finset (Edge V)) :
    Finset (Σ _ : {x : Edge V // x ∈ S}, List (Edge V)) :=
  S.attach.sigma fun e => edgeSetOrders (S.erase e.val)

omit [Fintype V] in
theorem mem_edgeSetOrderTails_iff
    (S : Finset (Edge V))
    {x : Σ _ : {y : Edge V // y ∈ S}, List (Edge V)} :
    x ∈ edgeSetOrderTails S ↔
      x.2 ∈ edgeSetOrders (S.erase x.1.val) := by
  rw [edgeSetOrderTails, Finset.mem_sigma]
  constructor
  · intro h
    exact h.2
  · intro h
    exact ⟨Finset.mem_attach S x.1, h⟩

omit [Fintype V] in
theorem mem_edgeSetOrders_filter_ne_nil_iff_exists_orderTail
    (S : Finset (Edge V)) {order : List (Edge V)} :
    order ∈ (edgeSetOrders S).filter (fun order => order ≠ []) ↔
      ∃ x ∈ edgeSetOrderTails S, x.1.val :: x.2 = order := by
  rw [Finset.mem_filter]
  constructor
  · intro h
    rcases h with ⟨hmem, hne⟩
    cases order with
    | nil =>
        exact False.elim (hne rfl)
    | cons e order =>
        have hsplit := (cons_mem_edgeSetOrders_iff S).mp hmem
        refine ⟨⟨⟨e, hsplit.1⟩, order⟩, ?_, rfl⟩
        rw [mem_edgeSetOrderTails_iff]
        exact hsplit.2
  · intro h
    rcases h with ⟨x, hx, horder⟩
    rw [← horder]
    constructor
    · rw [cons_mem_edgeSetOrders_iff]
      exact ⟨x.1.property, (mem_edgeSetOrderTails_iff S).mp hx⟩
    · intro hnil
      cases hnil

omit [Fintype V] in
/-- The embedding sending a first-edge/tail-order pair to the consed order. -/
def edgeSetOrderTailConsEmbedding (S : Finset (Edge V)) :
    (Σ _ : {x : Edge V // x ∈ S}, List (Edge V)) ↪ List (Edge V) where
  toFun x := x.1.val :: x.2
  inj' := by
    intro x y hxy
    cases x with
    | mk ex orderX =>
        cases y with
        | mk ey orderY =>
            injection hxy with hhead htail
            have hey : ex = ey := Subtype.ext hhead
            cases hey
            cases htail
            rfl

omit [Fintype V] in
theorem sum_edgeSetOrders_filter_ne_nil_eq_sum_cons
    {β : Type*} [AddCommMonoid β]
    (S : Finset (Edge V)) (φ : List (Edge V) → β) :
    Finset.sum ((edgeSetOrders S).filter (fun order => order ≠ []))
        (fun ord => φ ord) =
      Finset.sum S.attach
        (fun e => Finset.sum (edgeSetOrders (S.erase e.val))
          (fun ord => φ (e.val :: ord))) := by
  have hbij :
      Finset.sum (edgeSetOrderTails S) (fun x => φ (x.1.val :: x.2)) =
        Finset.sum ((edgeSetOrders S).filter (fun order => order ≠ []))
          (fun ord => φ ord) := by
    refine Finset.sum_bij
      (fun x _ => x.1.val :: x.2) ?hi ?hinj ?hsurj ?hφ
    · intro x hx
      rw [Finset.mem_filter]
      constructor
      · rw [cons_mem_edgeSetOrders_iff]
        exact ⟨x.1.property, (mem_edgeSetOrderTails_iff S).mp hx⟩
      · intro hnil
        cases hnil
    · intro x _ y _ hxy
      cases x with
      | mk ex orderX =>
          cases y with
          | mk ey orderY =>
              injection hxy with hhead htail
              have hey : ex = ey := Subtype.ext hhead
              cases hey
              cases htail
              rfl
    · intro ord horder
      rw [Finset.mem_filter] at horder
      rcases horder with ⟨hmem, hne⟩
      cases ord with
      | nil =>
          exact False.elim (hne rfl)
      | cons e ord =>
          have hsplit := (cons_mem_edgeSetOrders_iff S).mp hmem
          refine ⟨⟨⟨e, hsplit.1⟩, ord⟩, ?_, rfl⟩
          rw [mem_edgeSetOrderTails_iff]
          exact hsplit.2
    · intro x _
      rfl
  exact hbij.symm.trans (Finset.sum_sigma S.attach
    (fun e : {e // e ∈ S} => edgeSetOrders (S.erase e.val))
    (fun x : Σ _ : {y : Edge V // y ∈ S}, List (Edge V) =>
      φ (x.1.val :: x.2)))

omit [Fintype V] in
theorem edgeSetOrders_filter_ne_nil_eq_self_of_nonempty
    {S : Finset (Edge V)} (hS : S.Nonempty) :
    (edgeSetOrders S).filter (fun order => order ≠ []) = edgeSetOrders S := by
  ext order
  rw [Finset.mem_filter]
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, ?_⟩
    intro hnil
    subst order
    rcases hS with ⟨e, he⟩
    have hset := toFinset_eq_of_mem_edgeSetOrders h
    rw [List.toFinset_nil] at hset
    rw [← hset] at he
    exact Finset.notMem_empty e he

omit [Fintype V] in
theorem sum_edgeSetOrders_eq_sum_cons_of_nonempty
    {β : Type*} [AddCommMonoid β]
    {S : Finset (Edge V)} (hS : S.Nonempty)
    (φ : List (Edge V) → β) :
    Finset.sum (edgeSetOrders S) (fun order => φ order) =
      Finset.sum S.attach
        (fun e => Finset.sum (edgeSetOrders (S.erase e.val))
          (fun order => φ (e.val :: order))) := by
  rw [← edgeSetOrders_filter_ne_nil_eq_self_of_nonempty hS]
  exact sum_edgeSetOrders_filter_ne_nil_eq_sum_cons S φ

/-- All linear orderings of the edge set of a forest. -/
def edgeOrders (F : Forest V) : Finset (List (Edge V)) :=
  edgeSetOrders F.edges

theorem mem_edgeOrders_iff (F : Forest V) {order : List (Edge V)} :
    order ∈ F.edgeOrders ↔ order.Perm F.edges.toList := by
  exact mem_edgeSetOrders_iff F.edges

theorem toList_mem_edgeOrders (F : Forest V) :
    F.edges.toList ∈ F.edgeOrders :=
  (F.mem_edgeOrders_iff).mpr (List.Perm.refl _)

theorem mem_edgeOrders_iff_toFinset_eq_and_nodup
    (F : Forest V) {order : List (Edge V)} :
    order ∈ F.edgeOrders ↔ order.toFinset = F.edges ∧ order.Nodup := by
  exact mem_edgeSetOrders_iff_toFinset_eq_and_nodup F.edges

theorem toFinset_eq_of_mem_edgeOrders (F : Forest V)
    {order : List (Edge V)} (h : order ∈ F.edgeOrders) :
    order.toFinset = F.edges :=
  ((F.mem_edgeOrders_iff_toFinset_eq_and_nodup).mp h).1

theorem nodup_of_mem_edgeOrders (F : Forest V)
    {order : List (Edge V)} (h : order ∈ F.edgeOrders) :
    order.Nodup :=
  ((F.mem_edgeOrders_iff_toFinset_eq_and_nodup).mp h).2

theorem length_eq_card_of_mem_edgeOrders (F : Forest V)
    {order : List (Edge V)} (h : order ∈ F.edgeOrders) :
    order.length = F.edges.card := by
  exact length_eq_card_of_mem_edgeSetOrders h

theorem card_edgeOrders (F : Forest V) :
    F.edgeOrders.card = F.edges.card.factorial := by
  exact card_edgeSetOrders F.edges

theorem empty_edgeOrders :
    (Forest.empty V).edgeOrders = {[]} := by
  rw [edgeOrders, Forest.empty_edges V, edgeSetOrders_empty]

theorem cons_mem_edgeOrders_iff (F : Forest V)
    {e : Edge V} {order : List (Edge V)} :
    e :: order ∈ F.edgeOrders ↔
      e ∈ F.edges ∧ order ∈ edgeSetOrders (F.edges.erase e) :=
  cons_mem_edgeSetOrders_iff F.edges

theorem edgeOrders_filter_ne_nil_eq_self_of_edges_nonempty
    (F : Forest V) (hF : F.edges.Nonempty) :
    F.edgeOrders.filter (fun order => order ≠ []) = F.edgeOrders :=
  edgeSetOrders_filter_ne_nil_eq_self_of_nonempty hF

theorem sum_edgeOrders_eq_sum_cons_of_edges_nonempty
    {β : Type*} [AddCommMonoid β] (F : Forest V)
    (hF : F.edges.Nonempty) (φ : List (Edge V) → β) :
    Finset.sum F.edgeOrders (fun order => φ order) =
      Finset.sum F.edges.attach
        (fun e => Finset.sum (edgeSetOrders (F.edges.erase e.val))
          (fun order => φ (e.val :: order))) :=
  sum_edgeSetOrders_eq_sum_cons_of_nonempty hF φ

/--
Read a list of simplex parameters as edge parameters for a forest, according
to a chosen edge order. Missing parameters default to zero; on valid orders
and simplex-length parameter lists, this default is never used.
-/
def paramsOfOrder (F : Forest V) (order : List (Edge V)) (ts : List ℝ) :
    F.EdgeParam → ℝ :=
  fun e => ts.getD (order.idxOf e.val) 0

theorem paramValue_paramsOfOrder_eq_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    (order : List (Edge V)) (ts : List ℝ) (e : Edge V) :
    F.paramValue (F.paramsOfOrder order ts) e =
      G.paramValue (G.paramsOfOrder order ts) e := by
  by_cases heF : e ∈ F.edges
  · have heG : e ∈ G.edges := by
      simpa [hedges] using heF
    rw [F.paramValue_of_mem (F.paramsOfOrder order ts) heF]
    rw [G.paramValue_of_mem (G.paramsOfOrder order ts) heG]
    rfl
  · have heG : e ∉ G.edges := by
      intro he
      exact heF (by
        simpa [hedges] using he)
    rw [paramValue, dif_neg heF]
    rw [paramValue, dif_neg heG]

/--
In a common edge order, `paramsOfOrder` gives the same standard interpolation
point for any two `Forest` representatives with the same underlying edge set.
-/
theorem standardInterp_paramsOfOrder_eq_of_edges_eq
    (F G : Forest V) (hedges : F.edges = G.edges)
    (order : List (Edge V)) (ts : List ℝ) :
    F.standardInterp (F.paramsOfOrder order ts) =
      G.standardInterp (G.paramsOfOrder order ts) :=
  F.standardInterp_eq_of_edges_eq G
    (F.paramsOfOrder order ts) (G.paramsOfOrder order ts)
    hedges
    (F.paramValue_paramsOfOrder_eq_of_edges_eq G hedges order ts)

theorem paramsOfOrder_empty (order : List (Edge V)) (ts : List ℝ) :
    (Forest.empty V).paramsOfOrder order ts = emptyParam :=
  emptyParam_unique ((Forest.empty V).paramsOfOrder order ts)

theorem paramsOfOrder_cons_self (F : Forest V)
    (e : Edge V) (order : List (Edge V)) (t : ℝ) (ts : List ℝ)
    (he : e ∈ F.edges) :
    F.paramsOfOrder (e :: order) (t :: ts) ⟨e, he⟩ = t := by
  rw [paramsOfOrder]
  change (t :: ts).getD ((e :: order).idxOf e) 0 = t
  rw [List.idxOf_cons_self]
  rfl

theorem paramsOfOrder_cons_of_ne (F : Forest V)
    {e e' : Edge V} (order : List (Edge V)) (t : ℝ) (ts : List ℝ)
    (he' : e' ∈ F.edges) (hne : e' ≠ e) :
    F.paramsOfOrder (e :: order) (t :: ts) ⟨e', he'⟩ =
      ts.getD (order.idxOf e') 0 := by
  rw [paramsOfOrder]
  change (t :: ts).getD ((e :: order).idxOf e') 0 =
    ts.getD (order.idxOf e') 0
  rw [List.idxOf_cons_ne order (fun h => hne h.symm)]
  rfl

namespace EdgeExtension

variable {F F' : Forest V} {e : Edge V}

theorem extendParam_eq_paramsOfOrder_cons
    (h : EdgeExtension F F' e) (order : List (Edge V)) (ts : List ℝ)
    (u : F.EdgeParam → ℝ) (t : ℝ)
    (hu : u = F.paramsOfOrder order ts) :
    h.extendParam u t = F'.paramsOfOrder (e :: order) (t :: ts) := by
  funext e'
  by_cases hnew : e'.val = e
  · rw [extendParam, dif_pos hnew]
    rw [show e' = ⟨e, hnew ▸ e'.property⟩ from Subtype.ext hnew]
    rw [F'.paramsOfOrder_cons_self e order t ts]
  · have hold : e'.val ∈ F.edges :=
      h.mem_old_of_mem_of_ne e'.property hnew
    rw [extendParam, dif_neg hnew]
    rw [hu, F'.paramsOfOrder_cons_of_ne order t ts e'.property hnew]
    rfl

theorem extendParam_empty_eq_paramsOfOrder_singleton
    (h : EdgeExtension (Forest.empty V) F' e) (t : ℝ) :
    h.extendParam emptyParam t = F'.paramsOfOrder [e] [t] := by
  rw [h.extendParam_eq_paramsOfOrder_cons [] [] emptyParam t
    (paramsOfOrder_empty [] []).symm]

/--
Appending one newly-added edge to an existing order is compatible with the
recursive one-edge parameter extension.
-/
theorem extendParam_eq_paramsOfOrder_append_singleton
    (h : EdgeExtension F F' e) (pref : List (Edge V))
    (prefixTs : List ℝ) (t : ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) :
    h.extendParam (F.paramsOfOrder pref prefixTs) t =
      F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t]) := by
  funext e'
  by_cases hnew : e'.val = e
  · rw [extendParam, dif_pos hnew]
    rw [show e' = ⟨e, hnew ▸ e'.property⟩ from Subtype.ext hnew]
    rw [paramsOfOrder]
    change t = (prefixTs ++ [t]).getD ((pref ++ [e]).idxOf e) 0
    have hnot : e ∉ pref := by
      intro he
      exact h.new_not_mem (by
        rw [← hpref, List.mem_toFinset]
        exact he)
    rw [List.idxOf_append_of_notMem hnot]
    simp [hprefixTs]
  · have hold : e'.val ∈ F.edges :=
      h.mem_old_of_mem_of_ne e'.property hnew
    rw [extendParam, dif_neg hnew]
    rw [paramsOfOrder]
    change prefixTs.getD (pref.idxOf e'.val) 0 =
      (prefixTs ++ [t]).getD ((pref ++ [e]).idxOf e'.val) 0
    have hmemPrefixFin : e'.val ∈ pref.toFinset := by
      rw [hpref]
      exact hold
    have hmemPrefix : e'.val ∈ pref := by
      rwa [List.mem_toFinset] at hmemPrefixFin
    rw [List.idxOf_append_of_mem hmemPrefix]
    rw [List.getD_append]
    rw [hprefixTs]
    exact List.idxOf_lt_length_of_mem hmemPrefix

end EdgeExtension

namespace OrderedGrowth

variable {F G : Forest V} {order : List (Edge V)}

/--
If the starting forest parameters are read from an ordered prefix, then an
ordered growth reads the combined prefix-plus-growth parameter list in the
canonical `paramsOfOrder` way. The length condition rules out the fallback
zeroes used for malformed parameter lists.
-/
theorem params_eq_paramsOfOrder_append_of_length
    (h : OrderedGrowth F order G) (pref : List (Edge V))
    (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    {ts : List ℝ} (hlen : ts.length = order.length) :
    h.params (F.paramsOfOrder pref prefixTs) ts =
      G.paramsOfOrder (pref ++ order) (prefixTs ++ ts) := by
  induction h generalizing pref prefixTs ts with
  | nil F =>
      cases ts with
      | nil =>
          simp
      | cons t ts =>
          cases hlen
  | @cons F0 F1 G0 e0 order0 step tail ih =>
      cases ts with
      | nil =>
          cases hlen
      | cons t ts =>
          rw [params_cons_cons]
          have hprefixTs' :
              (prefixTs ++ [t]).length = (pref ++ [e0]).length := by
            simp [hprefixTs]
          rw [step.extendParam_eq_paramsOfOrder_append_singleton
            pref prefixTs t hpref hprefixTs]
          rw [ih (pref ++ [e0]) (prefixTs ++ [t])
            (by
              rw [List.toFinset_append, step.edges_eq, hpref]
              simp)
            hprefixTs' (by simpa using hlen)]
          simp [List.append_assoc]

/--
For an ordered growth from the empty forest, the recursive branch parameters
are exactly the canonical parameters attached to its terminal edge order.
-/
theorem params_emptyStart_eq_paramsOfOrder_of_length
    (h : OrderedGrowth (Forest.empty V) order G)
    {ts : List ℝ} (hlen : ts.length = order.length) :
    h.params emptyParam ts = G.paramsOfOrder order ts := by
  have hparams := h.params_eq_paramsOfOrder_append_of_length
    [] [] (by simp [Forest.empty_edges]) rfl hlen
  rw [paramsOfOrder_empty [] []] at hparams
  simpa using hparams

end OrderedGrowth

/--
The ordered-simplex contribution attached to one concrete ordering of a
forest edge set.
-/
def orderedContribution (F : Forest V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  orderedSimplexIntegral order
    (fun ts => mixedPartialList order.reverse ρ
      (F.standardInterp (F.paramsOfOrder order ts)))

/-- The ordered-simplex contribution of the empty forest. -/
theorem orderedContribution_empty (ρ : (Edge V → ℝ) → ℝ) :
    (Forest.empty V).orderedContribution [] ρ = ρ zeroConfig := by
  rw [orderedContribution, orderedSimplexIntegral_nil]
  rw [List.reverse_nil, mixedPartialList_nil_apply]
  rw [Forest.empty_standardInterp]

/--
The canonical ordered-sector sum attached to a forest. The cube-partition
theorem identifies this with the usual cube integral over `F.edges`.
-/
def orderedSectorSum (F : Forest V) (ρ : (Edge V → ℝ) → ℝ) : ℝ :=
  Finset.sum F.edgeOrders fun order => F.orderedContribution order ρ

/-- The empty forest contributes exactly the zero-configuration term. -/
theorem orderedSectorSum_empty (ρ : (Edge V → ℝ) → ℝ) :
    (Forest.empty V).orderedSectorSum ρ = ρ zeroConfig := by
  rw [orderedSectorSum, empty_edgeOrders]
  rw [Finset.sum_singleton, orderedContribution_empty]

/--
For a nonempty forest, the ordered-sector sum splits by first edge and then by
an ordering of the remaining edge set.
-/
theorem orderedSectorSum_eq_sum_cons_of_edges_nonempty
    (F : Forest V) (hF : F.edges.Nonempty)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedSectorSum ρ =
      Finset.sum F.edges.attach
        (fun e => Finset.sum (edgeSetOrders (F.edges.erase e.val))
          (fun order => F.orderedContribution (e.val :: order) ρ)) := by
  rw [orderedSectorSum]
  exact F.sum_edgeOrders_eq_sum_cons_of_edges_nonempty hF
    (fun order => F.orderedContribution order ρ)

/--
Tail-pair version of `Forest.orderedSectorSum_eq_sum_cons_of_edges_nonempty`.
This is the indexing shape used by recursive branch assembly.
-/
theorem orderedSectorSum_eq_sum_orderTails_of_edges_nonempty
    (F : Forest V) (hF : F.edges.Nonempty)
    (ρ : (Edge V → ℝ) → ℝ) :
    F.orderedSectorSum ρ =
      Finset.sum (edgeSetOrderTails F.edges)
        (fun x => F.orderedContribution (x.1.val :: x.2) ρ) := by
  rw [F.orderedSectorSum_eq_sum_cons_of_edges_nonempty hF ρ]
  rw [edgeSetOrderTails, Finset.sum_sigma]

namespace ActiveExtension

variable {e : Edge V}

/--
The one-edge branch grown from the empty forest is exactly the canonical
one-edge ordered-sector contribution for its terminal forest.
-/
theorem singletonGrowth_branchIntegral_empty_eq_orderedContribution
    (h : ActiveExtension (Forest.empty V) e)
    (ρ : (Edge V → ℝ) → ℝ) :
    h.singletonGrowth.branchIntegral emptyParam ρ =
      h.forest.orderedContribution [e] ρ := by
  rw [singletonGrowth]
  rw [OrderedGrowth.branchIntegral_cons_nil_eq_integral_partialDeriv_standardInterp]
  rw [orderedContribution, orderedSimplexIntegral_singleton]
  apply intervalIntegral.integral_congr
  intro t _
  change partialDeriv e ρ
      (h.forest.standardInterp (h.extension.extendParam emptyParam t)) =
    partialDeriv e ρ
      (h.forest.standardInterp (h.forest.paramsOfOrder [e] [t]))
  rw [h.extension.extendParam_empty_eq_paramsOfOrder_singleton t]

end ActiveExtension

end Forest

end BKAR

/- Adapted for Lean Pool: module imports and compatibility with its pinned toolchain. -/
