/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.GlueFold

/-!
# The interface pair list of a composition

The pairs glued by `glueInterface`, top pair first, as data for the
iterated-gluing fold: their well-formedness, the membership
characterization of the glued labels, and the identification of the
surviving labels with `Fin s ⊕ Fin u`.  The normalization of
`glueInterface` as a `glueList` builds on these.
-/

@[expose] public section

namespace RS

/-- The interface pairs glued by `glueInterface`, top pair first. -/
def interfacePairs (s t u : ℕ) :
    List ((Fin (s + t) ⊕ Fin (t + u)) × (Fin (s + t) ⊕ Fin (t + u))) :=
  (List.finRange t).reverse.map (fun k =>
    (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
     Sum.inr ⟨k.val, by have := k.isLt; omega⟩))

/-- Membership in the flattened interface pairs. -/
theorem mem_interfacePairs_flat (s t u : ℕ)
    (x : Fin (s + t) ⊕ Fin (t + u)) :
    x ∈ (interfacePairs s t u).flatMap (fun p => [p.1, p.2]) ↔
      (∃ a : Fin (s + t), x = Sum.inl a ∧ s ≤ a.val) ∨
      (∃ b : Fin (t + u), x = Sum.inr b ∧ b.val < t) := by
  unfold interfacePairs
  rw [List.flatMap_map]
  simp only [List.mem_flatMap, List.mem_reverse, List.mem_finRange,
    List.mem_cons, List.not_mem_nil, or_false, true_and]
  constructor
  · rintro ⟨k, hk | hk⟩
    · exact Or.inl ⟨_, hk, by simp⟩
    · exact Or.inr ⟨_, hk, by simp⟩
  · rintro (⟨a, rfl, ha⟩ | ⟨b, rfl, hb⟩)
    · refine ⟨⟨a.val - s, by have := a.isLt; omega⟩, Or.inl ?_⟩
      congr 1
      exact Fin.ext (by simp; omega)
    · refine ⟨⟨b.val, hb⟩, Or.inr ?_⟩
      congr 1

/-- The interface pairs are well-formed. -/
theorem interfacePairs_wf (s t u : ℕ) :
    Fragment.PairsWF (interfacePairs s t u) := by
  unfold Fragment.PairsWF interfacePairs
  rw [List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun k _ => by simp, ?_⟩
  rw [List.pairwise_reverse]
  refine (List.nodup_finRange t).pairwise_of_forall_ne ?_
  intro k _ m _ hkm x hxm hxk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxm hxk
  rcases hxm with rfl | rfl <;> rcases hxk with h | h
  · rw [Sum.inl.injEq, Fin.mk.injEq] at h
    exact hkm (Fin.ext (by omega)).symm
  · exact Sum.inl_ne_inr h
  · exact Sum.inr_ne_inl h
  · rw [Sum.inr.injEq, Fin.mk.injEq] at h
    exact hkm (Fin.ext (by omega)).symm

/-- Left labels below the interface. -/
def finLtEquiv (s t : ℕ) : {a : Fin (s + t) // a.val < s} ≃ Fin s where
  toFun a := ⟨a.val.val, a.prop⟩
  invFun a := ⟨⟨a.val, by have := a.isLt; omega⟩, by
    change a.val < s
    exact a.isLt⟩
  left_inv a := Subtype.ext (Fin.ext rfl)
  right_inv a := Fin.ext rfl

/-- Right labels beyond the interface. -/
def finGeEquiv (t u : ℕ) : {b : Fin (t + u) // ¬ b.val < t} ≃ Fin u where
  toFun b := ⟨b.val.val - t, by
    have h1 := b.val.isLt
    have h2 := Nat.le_of_not_lt b.prop
    omega⟩
  invFun b := ⟨⟨t + b.val, by have := b.isLt; omega⟩, by
    change ¬ t + b.val < t
    omega⟩
  left_inv b := Subtype.ext (Fin.ext (by
    have := Nat.le_of_not_lt b.prop
    change t + (b.val.val - t) = b.val.val
    omega))
  right_inv b := Fin.ext (by
    change t + b.val - t = b.val
    omega)

/-- The survival predicate of the interface gluing. -/
def interfaceSurvPred (s t u : ℕ) : Fin (s + t) ⊕ Fin (t + u) → Prop :=
  Sum.elim (fun a => a.val < s) (fun b => ¬ b.val < t)

/-- Avoiding every pair component is avoiding the flat list. -/
theorem forall_ne_iff_not_mem_flat {α : Type} (ps : List (α × α))
    (x : α) :
    (∀ p ∈ ps, x ≠ p.1 ∧ x ≠ p.2) ↔
      x ∉ ps.flatMap (fun p => [p.1, p.2]) := by
  rw [List.mem_flatMap]
  constructor
  · rintro h ⟨p, hp, hx⟩
    rcases List.mem_cons.mp hx with rfl | hx'
    · exact (h p hp).1 rfl
    · exact (h p hp).2 (List.mem_singleton.mp hx')
  · intro h p hp
    exact ⟨fun hx => h ⟨p, hp, by rw [hx]; exact List.mem_cons_self⟩,
      fun hx => h ⟨p, hp, by
        rw [hx]
        exact List.mem_cons.mpr (Or.inr List.mem_cons_self)⟩⟩

/-- Survival equals the survival predicate. -/
theorem interfaceSurv_iff (s t u : ℕ) (x : Fin (s + t) ⊕ Fin (t + u)) :
    x ∉ (interfacePairs s t u).flatMap (fun p => [p.1, p.2]) ↔
      interfaceSurvPred s t u x := by
  rcases x with a | b
  · constructor
    · intro hx
      rcases Nat.lt_or_ge a.val s with h | h
      · exact h
      · exact absurd ((mem_interfacePairs_flat s t u _).mpr
          (Or.inl ⟨a, rfl, h⟩)) hx
    · intro hlt hmem
      rcases (mem_interfacePairs_flat s t u _).mp hmem with
        ⟨a', ha', hge⟩ | ⟨b', hb', _⟩
      · rw [Sum.inl.injEq] at ha'
        subst ha'
        have hlt' : a.val < s := hlt
        omega
      · exact Sum.inl_ne_inr hb'
  · constructor
    · intro hx h
      exact absurd ((mem_interfacePairs_flat s t u _).mpr
        (Or.inr ⟨b, rfl, h⟩)) hx
    · intro hq hmem
      rcases (mem_interfacePairs_flat s t u _).mp hmem with
        ⟨a', ha', _⟩ | ⟨b', hb', hlt⟩
      · exact Sum.inr_ne_inl ha'
      · rw [Sum.inr.injEq] at hb'
        subst hb'
        exact hq hlt

/-- The labels surviving the interface gluing: left labels below
`s` and right labels beyond `t`. -/
noncomputable def interfaceSurvEquiv (s t u : ℕ) :
    Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
      (interfacePairs s t u) ≃ Fin s ⊕ Fin u :=
  ((Equiv.subtypeEquivRight (fun x =>
      (forall_ne_iff_not_mem_flat _ x).trans (interfaceSurv_iff s t u x))).trans
    (Equiv.subtypeSum (p := interfaceSurvPred s t u))).trans
    (Equiv.sumCongr (finLtEquiv s t) (finGeEquiv t u))

/-! ### The step decomposition of the interface pairs -/

/-- The tail pairs of the `(t+1)`-interface: the same pairs one
level down, embedded in the larger index types. -/
def tailPairs (s t u : ℕ) :
    List ((Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ×
      (Fin (s + t + 1) ⊕ Fin (t + 1 + u))) :=
  (List.finRange t).reverse.map (fun k =>
    (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
     Sum.inr ⟨k.val, by have := k.isLt; omega⟩))

/-- The `(t+1)`-interface pairs decompose as the top pair followed
by the tail pairs. -/
theorem interfacePairs_succ (s t u : ℕ) :
    interfacePairs s (t + 1) u =
      (Sum.inl ⟨s + t, by omega⟩, Sum.inr ⟨t, by omega⟩) ::
        tailPairs s t u := by
  unfold interfacePairs tailPairs
  rw [List.finRange_succ_last, List.reverse_append,
    List.reverse_singleton, List.singleton_append, List.map_cons,
    ← List.map_reverse, List.map_map]
  exact congrArg₂ List.cons rfl (List.map_congr_left (fun k _ => rfl))

/-- The step re-indexing on surviving left labels: values are
preserved. -/
theorem interfaceStepEquiv_inl (s t u : ℕ) (a : Fin (s + t + 1))
    (h : (Sum.inl a : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
      (Sum.inl a : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inr ⟨t, by omega⟩)
    (ha : a.val < s + t) :
    interfaceStepEquiv s t u ⟨Sum.inl a, h⟩ = Sum.inl ⟨a.val, ha⟩ := by
  unfold interfaceStepEquiv
  rw [Equiv.trans_apply,
    show sumRemoveSplitEquiv (⟨s + t, Nat.lt_succ_self _⟩ : Fin (s + t + 1))
        (⟨t, by omega⟩ : Fin (t + 1 + u)) ⟨Sum.inl a, h⟩ =
      Sum.inl ⟨a, fun he => h.1 (congrArg Sum.inl he)⟩ from rfl]
  rw [show (Equiv.sumCongr (finRemoveEquiv _) (rightRemoveEquiv t u))
      (Sum.inl ⟨a, fun he => h.1 (congrArg Sum.inl he)⟩) =
    Sum.inl (finRemoveEquiv ⟨s + t, Nat.lt_succ_self _⟩
      ⟨a, fun he => h.1 (congrArg Sum.inl he)⟩) from rfl]
  refine congrArg Sum.inl (Fin.ext ?_)
  rw [finRemoveEquiv_val]
  change (if a.val < s + t then a.val else a.val - 1) = a.val
  rw [ite_eq_left ha]

/-- The step re-indexing on surviving right labels below the glued
index: values are preserved. -/
theorem interfaceStepEquiv_inr_below (s t u : ℕ) (b : Fin (t + 1 + u))
    (h : (Sum.inr b : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
      (Sum.inr b : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inr ⟨t, by omega⟩)
    (hb : b.val < t) :
    interfaceStepEquiv s t u ⟨Sum.inr b, h⟩ =
      Sum.inr ⟨b.val, by omega⟩ := by
  unfold interfaceStepEquiv
  rw [Equiv.trans_apply,
    show sumRemoveSplitEquiv (⟨s + t, Nat.lt_succ_self _⟩ : Fin (s + t + 1))
        (⟨t, by omega⟩ : Fin (t + 1 + u)) ⟨Sum.inr b, h⟩ =
      Sum.inr ⟨b, fun he => h.2 (congrArg Sum.inr he)⟩ from rfl]
  rw [show (Equiv.sumCongr (finRemoveEquiv _) (rightRemoveEquiv t u))
      (Sum.inr ⟨b, fun he => h.2 (congrArg Sum.inr he)⟩) =
    Sum.inr (rightRemoveEquiv t u
      ⟨b, fun he => h.2 (congrArg Sum.inr he)⟩) from rfl]
  refine congrArg Sum.inr (Fin.ext ?_)
  unfold rightRemoveEquiv
  rw [Equiv.trans_apply, finRemoveEquiv_val]
  change (if b.val < t then b.val else b.val - 1) = b.val
  rw [ite_eq_left hb]

/-- The step re-indexing on surviving right labels above the glued
index: values drop by one. -/
theorem interfaceStepEquiv_inr_above (s t u : ℕ) (b : Fin (t + 1 + u))
    (h : (Sum.inr b : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ ∧
      (Sum.inr b : Fin (s + t + 1) ⊕ Fin (t + 1 + u)) ≠
        Sum.inr ⟨t, by omega⟩)
    (hb : t < b.val) :
    interfaceStepEquiv s t u ⟨Sum.inr b, h⟩ =
      Sum.inr ⟨b.val - 1, by have := b.isLt; omega⟩ := by
  unfold interfaceStepEquiv
  rw [Equiv.trans_apply,
    show sumRemoveSplitEquiv (⟨s + t, Nat.lt_succ_self _⟩ : Fin (s + t + 1))
        (⟨t, by omega⟩ : Fin (t + 1 + u)) ⟨Sum.inr b, h⟩ =
      Sum.inr ⟨b, fun he => h.2 (congrArg Sum.inr he)⟩ from rfl]
  rw [show (Equiv.sumCongr (finRemoveEquiv _) (rightRemoveEquiv t u))
      (Sum.inr ⟨b, fun he => h.2 (congrArg Sum.inr he)⟩) =
    Sum.inr (rightRemoveEquiv t u
      ⟨b, fun he => h.2 (congrArg Sum.inr he)⟩) from rfl]
  refine congrArg Sum.inr (Fin.ext ?_)
  unfold rightRemoveEquiv
  rw [Equiv.trans_apply, finRemoveEquiv_val]
  change (if b.val < t then b.val else b.val - 1) = b.val - 1
  rw [ite_eq_right (by omega)]

/-! ### The coerced tail as a mapped pair list -/

/-- The step re-indexing pulls tail-pair left components back to
themselves. -/
theorem interfaceStepEquiv_symm_inl (s t u : ℕ) (k : ℕ) (hk : k < t) :
    (interfaceStepEquiv s t u).symm (Sum.inl ⟨s + k, by omega⟩) =
      ⟨Sum.inl ⟨s + k, by omega⟩,
        fun he => by
          have h2 : s + k = s + t := congrArg Fin.val (Sum.inl.inj he)
          omega,
        fun he => Sum.inl_ne_inr he⟩ := by
  rw [_root_.Equiv.symm_apply_eq]
  exact (interfaceStepEquiv_inl s t u ⟨s + k, by omega⟩ _
    (by change s + k < s + t; omega)).symm

/-- The step re-indexing pulls tail-pair right components back to
themselves. -/
theorem interfaceStepEquiv_symm_inr (s t u : ℕ) (k : ℕ) (hk : k < t) :
    (interfaceStepEquiv s t u).symm (Sum.inr ⟨k, by omega⟩) =
      ⟨Sum.inr ⟨k, by omega⟩,
        fun he => Sum.inr_ne_inl he,
        fun he => by
          have h2 : k = t := congrArg Fin.val (Sum.inr.inj he)
          omega⟩ := by
  rw [_root_.Equiv.symm_apply_eq]
  exact (interfaceStepEquiv_inr_below s t u ⟨k, by omega⟩ _ hk).symm

/-- Mapping back and forth through an equivalence is the identity
on pair lists. -/
theorem mapPairs_symm_cancel {α β : Type} (e : α ≃ β) :
    ∀ ps : List (β × β),
    Fragment.mapPairs e (Fragment.mapPairs e.symm ps) = ps
  | [] => rfl
  | p :: ps => by
    simp only [Fragment.mapPairs, List.map_cons, Prod.map]
    exact congrArg₂ List.cons
      (Prod.ext (e.apply_symm_apply p.1) (e.apply_symm_apply p.2))
      (mapPairs_symm_cancel e ps)

/-- The mapped-back interface pairs are the coerced tail pairs
(generalized over the index list). -/
private theorem interface_coerce_eq_aux (s t u : ℕ) :
    ∀ (l : List (Fin t))
    (hsep : Fragment.PairsSep
      (Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ :
        Fin (s + t + 1) ⊕ Fin (t + 1 + u))
      (Sum.inr ⟨t, by omega⟩)
      (l.map (fun k =>
        (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
         Sum.inr ⟨k.val, by have := k.isLt; omega⟩)))),
    Fragment.mapPairs (interfaceStepEquiv s t u).symm
        (l.map (fun k =>
          ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
              Fin (s + t) ⊕ Fin (t + u)),
           Sum.inr ⟨k.val, by have := k.isLt; omega⟩))) =
      Fragment.coercePairsList _ _ _ hsep
  | [], _ => rfl
  | k :: l, hsep => by
    simp only [List.map_cons, Fragment.mapPairs,
      Fragment.coercePairsList, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (interface_coerce_eq_aux s t u l _)
    · exact (interfaceStepEquiv_symm_inl s t u k.val k.isLt).trans
        (Subtype.ext rfl)
    · exact (interfaceStepEquiv_symm_inr s t u k.val k.isLt).trans
        (Subtype.ext rfl)

/-- The mapped-back interface pairs are the coerced tail pairs. -/
theorem interface_coerce_eq (s t u : ℕ)
    (hsep : Fragment.PairsSep
      (Sum.inl ⟨s + t, Nat.lt_succ_self _⟩ :
        Fin (s + t + 1) ⊕ Fin (t + 1 + u))
      (Sum.inr ⟨t, by omega⟩) (tailPairs s t u)) :
    Fragment.mapPairs (interfaceStepEquiv s t u).symm
        (interfacePairs s t u) =
      Fragment.coercePairsList _ _ (tailPairs s t u) hsep :=
  interface_coerce_eq_aux s t u (List.finRange t).reverse hsep

/-- The surviving-label identification on left labels. -/
theorem interfaceSurvEquiv_inl (s t u : ℕ)
    (x : Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
      (interfacePairs s t u))
    (a : Fin (s + t)) (hx : x.val = Sum.inl a) (ha : a.val < s) :
    interfaceSurvEquiv s t u x = Sum.inl ⟨a.val, ha⟩ := by
  obtain ⟨xv, hxp⟩ := x
  subst hx
  rfl

/-- The surviving-label identification on right labels. -/
theorem interfaceSurvEquiv_inr (s t u : ℕ)
    (x : Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
      (interfacePairs s t u))
    (b : Fin (t + u)) (hx : x.val = Sum.inr b) (hb : t ≤ b.val) :
    interfaceSurvEquiv s t u x =
      Sum.inr ⟨b.val - t, by have := b.isLt; omega⟩ := by
  obtain ⟨xv, hxp⟩ := x
  subst hx
  rfl

/-- Membership of a tail pair. -/
private theorem mem_tailPairs (s t u : ℕ) (k : ℕ) (hk : k < t) :
    ((Sum.inl ⟨s + k, by omega⟩,
      (Sum.inr ⟨k, by omega⟩ : Fin (s + t + 1) ⊕ Fin (t + 1 + u)))) ∈
      tailPairs s t u := by
  unfold tailPairs
  exact List.mem_map.mpr ⟨⟨k, hk⟩,
    List.mem_reverse.mpr (List.mem_finRange _), rfl⟩

/-! ### The normalization of glueInterface -/

/-- `glueInterface` is the iterated gluing along the interface
pairs, relabelled by the surviving-label identification. -/
noncomputable def glueInterfaceNormal (s u : ℕ) :
    (t : ℕ) → (W : Fragment (Fin (s + t) ⊕ Fin (t + u))) →
    (glueInterface s t u W).Equiv
      ((Fragment.glueList W (interfacePairs s t u)
        (interfacePairs_wf s t u)).relabel (interfaceSurvEquiv s t u))
  -- ═══════ t = 0: NOTHING TO GLUE ═══════
  | 0, W => by
    change (W.relabel (Equiv.sumCongr (finCongr (by omega))
      (finCongr (by omega)))).Equiv _
    have hnil : Fragment.glueList W (interfacePairs s 0 u)
        (interfacePairs_wf s 0 u) =
        W.relabel Fragment.foldSurvivingNilEquiv.symm :=
      Fragment.glueList_nil W _
    rw [hnil]
    refine Fragment.Equiv.trans ?_
      (Fragment.Equiv.relabelTrans W _ _).symm
    have heq : (Equiv.sumCongr (finCongr (by omega : s + 0 = s))
        (finCongr (by omega : 0 + u = u))) =
        Fragment.foldSurvivingNilEquiv.symm.trans
          (interfaceSurvEquiv s 0 u) :=
      Equiv.ext (fun x => by rcases x with a | b <;> rfl)
    exact heq ▸ Fragment.Equiv.refl _
  -- ═══════ t + 1: GLUE THE TOP PAIR, RECURSE ═══════
  | t + 1, W => by
    change (glueInterface s t u
      ((W.gluePair (Sum.inl ⟨s + t, by omega⟩) (Sum.inr ⟨t, by omega⟩)
        Sum.inl_ne_inr).relabel
        (interfaceStepEquiv s t u))).Equiv _
    have hwf_cons : Fragment.PairsWF
        ((Sum.inl ⟨s + t, Nat.lt_succ_self _⟩,
          (Sum.inr ⟨t, by omega⟩ :
            Fin (s + t + 1) ⊕ Fin (t + 1 + u))) :: tailPairs s t u) :=
      interfacePairs_succ s t u ▸ interfacePairs_wf s (t + 1) u
    have hlist : Fragment.mapPairs (interfaceStepEquiv s t u)
        (Fragment.coercePairsList _ _ (tailPairs s t u) hwf_cons.sep) =
        interfacePairs s t u := by
      rw [← interface_coerce_eq s t u hwf_cons.sep]
      exact mapPairs_symm_cancel _ _
    have hwf₀ := Fragment.coercePairsList_wf _ _ (tailPairs s t u)
      hwf_cons.tail hwf_cons.sep
    refine Fragment.Equiv.trans (glueInterfaceNormal s u t _) ?_
    refine Fragment.Equiv.trans (Fragment.Equiv.relabelCongr
      (Fragment.glueListEqEquiv _ hlist
        (Fragment.mapPairs_wf _ _ hwf₀) (interfacePairs_wf s t u)
        (by rw [hlist])).symm (interfaceSurvEquiv s t u)) ?_
    refine Fragment.Equiv.trans
      (Fragment.Equiv.relabelTrans _ _ _) ?_
    refine Fragment.Equiv.trans (Fragment.Equiv.relabelCongr
      (Fragment.glueListRelabel
        (W.gluePair (Sum.inl ⟨s + t, by omega⟩) (Sum.inr ⟨t, by omega⟩)
          Sum.inl_ne_inr)
        (interfaceStepEquiv s t u) _ hwf₀) _) ?_
    refine Fragment.Equiv.trans
      (Fragment.Equiv.relabelTrans _ _ _) ?_
    -- Both sides are now relabels of the same iterated glue; the
    -- composed relabellings agree pointwise.
    have heqF : (Fragment.foldSurvivingMapEquiv (interfaceStepEquiv s t u)
          (Fragment.coercePairsList _ _ (tailPairs s t u)
            hwf_cons.sep)).trans
          ((Fragment.foldSurvivingPermEquiv (by rw [hlist])).trans
            (interfaceSurvEquiv s t u)) =
        (Fragment.foldFlatten _ _ (tailPairs s t u) hwf_cons.sep).trans
          ((Fragment.foldSurvivingPermEquiv
              (by rw [interfacePairs_succ s t u] :
                (interfacePairs s (t + 1) u).Perm _)).symm.trans
            (interfaceSurvEquiv s (t + 1) u)) := by
      refine Equiv.ext (fun x => ?_)
      simp only [Equiv.trans_apply]
      rcases hval : x.val.val with a | b
      · have ha' : a.val < s + t := by
          have h1 := x.val.prop.1
          rw [hval] at h1
          have hne : a ≠ ⟨s + t, Nat.lt_succ_self _⟩ :=
            fun h => h1 (congrArg Sum.inl h)
          have := a.isLt
          rcases Nat.lt_or_ge a.val (s + t) with h | h
          · exact h
          · exact absurd (Fin.ext (show a.val = s + t by omega)) hne
        have ha : a.val < s := by
          rcases Nat.lt_or_ge a.val s with h | h
          · exact h
          · obtain ⟨r, hr, hr1, _⟩ := Fragment.coercePairsList_mem _ _
              (tailPairs s t u) hwf_cons.sep
              (Sum.inl ⟨s + (a.val - s), by omega⟩,
                Sum.inr ⟨a.val - s, by omega⟩)
              (by exact mem_tailPairs s t u (a.val - s) (by omega))
            refine absurd (Subtype.ext ?_ : x.val = r.1) (x.prop r hr).1
            rw [hr1, hval]
            exact congrArg Sum.inl (Fin.ext
              (by change a.val = s + (a.val - s); omega))
        have hxv : x.val = ⟨Sum.inl a,
            by rw [← hval]; exact x.val.prop.1,
            by rw [← hval]; exact x.val.prop.2⟩ :=
          Subtype.ext hval
        have hstep : interfaceStepEquiv s t u x.val =
            Sum.inl ⟨a.val, ha'⟩ := by
          rw [hxv]
          exact interfaceStepEquiv_inl s t u a _ ha'
        have hL := interfaceSurvEquiv_inl s t u
          ((Fragment.foldSurvivingPermEquiv (by rw [hlist]))
            ((Fragment.foldSurvivingMapEquiv (interfaceStepEquiv s t u)
              (Fragment.coercePairsList _ _ (tailPairs s t u)
                hwf_cons.sep)) x))
          ⟨a.val, ha'⟩ hstep ha
        have hR := interfaceSurvEquiv_inl s (t + 1) u
          ((Fragment.foldSurvivingPermEquiv
              (by rw [interfacePairs_succ s t u] :
                (interfacePairs s (t + 1) u).Perm _)).symm
            ((Fragment.foldFlatten _ _ (tailPairs s t u)
              hwf_cons.sep) x))
          a hval ha
        exact hL.trans hR.symm
      · have hbne : b ≠ ⟨t, by omega⟩ := by
          have h2 := x.val.prop.2
          rw [hval] at h2
          exact fun h => h2 (congrArg Sum.inr h)
        have hbt : t < b.val := by
          rcases Nat.lt_or_ge b.val t with h | h
          · obtain ⟨r, hr, _, hr2⟩ := Fragment.coercePairsList_mem _ _
              (tailPairs s t u) hwf_cons.sep
              (Sum.inl ⟨s + b.val, by omega⟩,
                Sum.inr ⟨b.val, by omega⟩)
              (by exact mem_tailPairs s t u b.val h)
            refine absurd (Subtype.ext ?_ : x.val = r.2) (x.prop r hr).2
            rw [hr2, hval]
          · rcases Nat.lt_or_ge t b.val with h' | h'
            · exact h'
            · exact absurd (Fin.ext (show b.val = t by omega)) hbne
        have hxv : x.val = ⟨Sum.inr b,
            by rw [← hval]; exact x.val.prop.1,
            by rw [← hval]; exact x.val.prop.2⟩ :=
          Subtype.ext hval
        have hstep : interfaceStepEquiv s t u x.val =
            Sum.inr ⟨b.val - 1, by have := b.isLt; omega⟩ := by
          rw [hxv]
          exact interfaceStepEquiv_inr_above s t u b _ hbt
        have hL := interfaceSurvEquiv_inr s t u
          ((Fragment.foldSurvivingPermEquiv (by rw [hlist]))
            ((Fragment.foldSurvivingMapEquiv (interfaceStepEquiv s t u)
              (Fragment.coercePairsList _ _ (tailPairs s t u)
                hwf_cons.sep)) x))
          ⟨b.val - 1, by have := b.isLt; omega⟩ hstep
          (by change t ≤ b.val - 1; omega)
        have hR := interfaceSurvEquiv_inr s (t + 1) u
          ((Fragment.foldSurvivingPermEquiv
              (by rw [interfacePairs_succ s t u] :
                (interfacePairs s (t + 1) u).Perm _)).symm
            ((Fragment.foldFlatten _ _ (tailPairs s t u)
              hwf_cons.sep) x))
          b hval (by omega)
        refine hL.trans (Eq.trans ?_ hR.symm)
        exact congrArg Sum.inr (Fin.ext (by
          change b.val - 1 - t = b.val - (t + 1)
          omega))
    rw [heqF]
    refine Fragment.Equiv.trans
      (Fragment.Equiv.relabelTrans _ _ _).symm ?_
    refine Fragment.Equiv.trans (Fragment.Equiv.relabelCongr
      ((Fragment.glueList_cons W _ (tailPairs s t u) hwf_cons ▸
        Fragment.glueListEqEquiv W (interfacePairs_succ s t u)
          (interfacePairs_wf s (t + 1) u) hwf_cons
          (by rw [interfacePairs_succ s t u])).symm) _) ?_
    refine Fragment.Equiv.trans
      (Fragment.Equiv.relabelTrans _ _ _) ?_
    have heqG : (Fragment.foldSurvivingPermEquiv
          (by rw [interfacePairs_succ s t u] :
            (interfacePairs s (t + 1) u).Perm
              ((Sum.inl ⟨s + t, Nat.lt_succ_self _⟩,
                Sum.inr ⟨t, Nat.lt_of_lt_of_le (Nat.lt_succ_self t)
                  (Nat.le_add_right _ _)⟩) :: tailPairs s t u))).trans
          ((Fragment.foldSurvivingPermEquiv
              (by rw [interfacePairs_succ s t u] :
                (interfacePairs s (t + 1) u).Perm
              ((Sum.inl ⟨s + t, Nat.lt_succ_self _⟩,
                Sum.inr ⟨t, Nat.lt_of_lt_of_le (Nat.lt_succ_self t)
                  (Nat.le_add_right _ _)⟩) :: tailPairs s t u))).symm.trans
            (interfaceSurvEquiv s (t + 1) u)) =
        interfaceSurvEquiv s (t + 1) u :=
      Equiv.ext (fun x => by simp)
    rw [heqG]
    exact Fragment.Equiv.refl _

/-- **Composition as a fold**: composing two fragments is the
iterated gluing of the interface pairs in their disjoint union,
relabelled by the surviving-label identification. -/
noncomputable def composeNormal {s t u : ℕ}
    (F : Fragment (Fin (s + t))) (G : Fragment (Fin (t + u))) :
    (F.compose G).Equiv
      ((Fragment.glueList (F.disjUnion G) (interfacePairs s t u)
        (interfacePairs_wf s t u)).relabel
        ((interfaceSurvEquiv s t u).trans finSumFinEquiv)) := by
  refine Fragment.Equiv.trans ?_ (Fragment.Equiv.relabelTrans _ _ _)
  change ((glueInterface s t u (F.disjUnion G)).relabel
    finSumFinEquiv).Equiv _
  exact Fragment.Equiv.relabelCongr
    (glueInterfaceNormal s u t (F.disjUnion G)) finSumFinEquiv

/-! ### Boundary permutations across an interface -/

/-- Permuting the last `t` labels of `Fin (s + t)`. -/
def outPermEquiv (s : ℕ) {t : ℕ} (σ : Equiv.Perm (Fin t)) :
    Fin (s + t) ≃ Fin (s + t) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr (Equiv.refl (Fin s)) σ).trans finSumFinEquiv)

/-- Permuting the first `t` labels of `Fin (t + u)`. -/
def inPermEquiv {t : ℕ} (σ : Equiv.Perm (Fin t)) (u : ℕ) :
    Fin (t + u) ≃ Fin (t + u) :=
  finSumFinEquiv.symm.trans
    ((Equiv.sumCongr σ (Equiv.refl (Fin u))).trans finSumFinEquiv)

/-- The outgoing permutation fixes the low labels. -/
theorem outPermEquiv_low (s : ℕ) {t : ℕ} (σ : Equiv.Perm (Fin t))
    (a : Fin s) :
    outPermEquiv s σ (Fin.castAdd t a) = Fin.castAdd t a := by
  unfold outPermEquiv
  simp [finSumFinEquiv_symm_apply_castAdd]

/-- The outgoing permutation acts on the high labels. -/
theorem outPermEquiv_high (s : ℕ) {t : ℕ} (σ : Equiv.Perm (Fin t))
    (k : Fin t) :
    outPermEquiv s σ (Fin.natAdd s k) = Fin.natAdd s (σ k) := by
  unfold outPermEquiv
  simp [finSumFinEquiv_symm_apply_natAdd]

/-- The incoming permutation acts on the low labels. -/
theorem inPermEquiv_low {t : ℕ} (σ : Equiv.Perm (Fin t)) (u : ℕ)
    (k : Fin t) :
    inPermEquiv σ u (Fin.castAdd u k) = Fin.castAdd u (σ k) := by
  unfold inPermEquiv
  simp [finSumFinEquiv_symm_apply_castAdd]

/-- The incoming permutation fixes the high labels. -/
theorem inPermEquiv_high {t : ℕ} (σ : Equiv.Perm (Fin t)) (u : ℕ)
    (b : Fin u) :
    inPermEquiv σ u (Fin.natAdd t b) = Fin.natAdd t b := by
  unfold inPermEquiv
  simp [finSumFinEquiv_symm_apply_natAdd]

end RS
