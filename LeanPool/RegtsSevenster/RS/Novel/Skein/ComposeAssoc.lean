/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeNormal

/-!
# Associativity of composition

Both associations of a triple composition normalize to iterated
gluing of the two interface pair lists over the common ambient
disjoint union `(F ⊔ G) ⊔ H`, so composition of fragments is
associative up to fragment equivalence (`composeAssoc`).

This file builds the associativity infrastructure in stages:
the associativity equivalence of disjoint unions, the embedding
of relabellings into disjoint unions, the normalization of each
association, and the final meet in the middle via two-stage
folding and reordering.
-/

namespace RS

namespace Fragment

variable {α β γ : Type}

/-- Disjoint union is associative, up to the sum-associativity
relabelling. -/
noncomputable def disjUnionAssoc (W₁ : Fragment α)
    (W₂ : Fragment β) (W₃ : Fragment γ) :
    ((W₁.disjUnion W₂).disjUnion W₃).Equiv
      ((W₁.disjUnion (W₂.disjUnion W₃)).relabel
        (_root_.Equiv.sumAssoc α β γ).symm) where
  flagEquiv := _root_.Equiv.sumAssoc W₁.Flag W₂.Flag W₃.Flag
  vertexEquiv := _root_.Equiv.sumAssoc W₁.Vertex W₂.Vertex W₃.Vertex
  attach_comm f := by
    rcases f with (f | f) | f
    · change ((W₁.attach f).map Sum.inl Sum.inl).map id
          (_root_.Equiv.sumAssoc α β γ).symm =
        (((W₁.attach f).map Sum.inl Sum.inl).map Sum.inl
          Sum.inl).map
          (_root_.Equiv.sumAssoc W₁.Vertex W₂.Vertex W₃.Vertex) id
      rcases W₁.attach f with v | ℓ <;> rfl
    · change (((W₂.attach f).map Sum.inl Sum.inl).map Sum.inr
          Sum.inr).map id (_root_.Equiv.sumAssoc α β γ).symm =
        (((W₂.attach f).map Sum.inr Sum.inr).map Sum.inl
          Sum.inl).map
          (_root_.Equiv.sumAssoc W₁.Vertex W₂.Vertex W₃.Vertex) id
      rcases W₂.attach f with v | ℓ <;> rfl
    · change (((W₃.attach f).map Sum.inr Sum.inr).map Sum.inr
          Sum.inr).map id (_root_.Equiv.sumAssoc α β γ).symm =
        ((W₃.attach f).map Sum.inr Sum.inr).map
          (_root_.Equiv.sumAssoc W₁.Vertex W₂.Vertex W₃.Vertex) id
      rcases W₃.attach f with v | ℓ <;> rfl
  pairing_comm f := by
    rcases f with (f | f) | f <;> rfl
  circles_eq := by
    change W₁.circles + W₂.circles + W₃.circles =
      W₁.circles + (W₂.circles + W₃.circles)
    omega

/-- Relabelling the left factor of a disjoint union equals
relabelling the whole union by a sum congruence. -/
noncomputable def relabelDisjUnionLeft {α' : Type}
    (W : Fragment α) (W' : Fragment β) (e : α ≃ α') :
    ((W.relabel e).disjUnion W').Equiv
      ((W.disjUnion W').relabel
        (_root_.Equiv.sumCongr e (_root_.Equiv.refl β))) where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm f := by
    rcases f with f | f
    · change ((W.attach f).map Sum.inl Sum.inl).map id
          (_root_.Equiv.sumCongr e (_root_.Equiv.refl β)) =
        (((W.attach f).map id e).map Sum.inl Sum.inl).map
          (_root_.Equiv.refl _) id
      rcases W.attach f with v | ℓ <;> rfl
    · change ((W'.attach f).map Sum.inr Sum.inr).map id
          (_root_.Equiv.sumCongr e (_root_.Equiv.refl β)) =
        ((W'.attach f).map Sum.inr Sum.inr).map
          (_root_.Equiv.refl _) id
      rcases W'.attach f with v | ℓ <;> rfl
  pairing_comm f := by rcases f with f | f <;> rfl
  circles_eq := rfl

/-- Relabelling the right factor of a disjoint union equals
relabelling the whole union by a sum congruence. -/
noncomputable def relabelDisjUnionRight {β' : Type}
    (W : Fragment α) (W' : Fragment β) (e : β ≃ β') :
    (W.disjUnion (W'.relabel e)).Equiv
      ((W.disjUnion W').relabel
        (_root_.Equiv.sumCongr (_root_.Equiv.refl α) e)) where
  flagEquiv := _root_.Equiv.refl _
  vertexEquiv := _root_.Equiv.refl _
  attach_comm f := by
    rcases f with f | f
    · change ((W.attach f).map Sum.inl Sum.inl).map id
          (_root_.Equiv.sumCongr (_root_.Equiv.refl α) e) =
        ((W.attach f).map Sum.inl Sum.inl).map
          (_root_.Equiv.refl _) id
      rcases W.attach f with v | ℓ <;> rfl
    · change ((W'.attach f).map Sum.inr Sum.inr).map id
          (_root_.Equiv.sumCongr (_root_.Equiv.refl α) e) =
        (((W'.attach f).map id e).map Sum.inr Sum.inr).map
          (_root_.Equiv.refl _) id
      rcases W'.attach f with v | ℓ <;> rfl
  pairing_comm f := by rcases f with f | f <;> rfl
  circles_eq := rfl

/-- Flip a relabelled equivalence to the other side. -/
noncomputable def Equiv.relabelFlip {W₁ : Fragment α}
    {W₂ : Fragment β} {e : β ≃ α}
    (E : W₁.Equiv (W₂.relabel e)) :
    W₂.Equiv (W₁.relabel e.symm) :=
  ((((_root_.Equiv.self_trans_symm e ▸
      Equiv.relabelTrans W₂ e e.symm).trans
    (Equiv.relabelRefl W₂)).symm).trans
    (Equiv.relabelCongr E.symm e.symm))

/-- Relabelling by equal equivalences. -/
noncomputable def Equiv.relabelEq (W : Fragment α) {e e' : α ≃ β}
    (h : e = e') : (W.relabel e).Equiv (W.relabel e') :=
  h ▸ Equiv.refl _

end Fragment

/-! ### The interface pair lists in the common ambient -/

/-- The `u`-interface pairs in the common ambient
`(F ⊔ G) ⊔ H`: the high labels of `G` against the low labels of
`H`, top pair first. -/
def uPairsAssoc (s t u v : ℕ) :
    List (((Fin (s + t) ⊕ Fin (t + u)) ⊕ Fin (u + v)) ×
      ((Fin (s + t) ⊕ Fin (t + u)) ⊕ Fin (u + v))) :=
  (List.finRange u).reverse.map (fun k =>
    (Sum.inl (Sum.inr ⟨t + k.val, by have := k.isLt; omega⟩),
     Sum.inr ⟨k.val, by have := k.isLt; omega⟩))

/-- The `u`-interface pairs are well-formed. -/
theorem uPairsAssoc_wf (s t u v : ℕ) :
    Fragment.PairsWF (uPairsAssoc s t u v) := by
  unfold Fragment.PairsWF uPairsAssoc
  rw [List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun k _ => by simp, ?_⟩
  rw [List.pairwise_reverse]
  refine (List.nodup_finRange u).pairwise_of_forall_ne ?_
  intro k _ m _ hkm x hxm hxk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxm hxk
  rcases hxm with rfl | rfl <;> rcases hxk with h | h
  · rw [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq] at h
    exact hkm (Fin.ext (by omega)).symm
  · exact Sum.inl_ne_inr h
  · exact Sum.inr_ne_inl h
  · rw [Sum.inr.injEq, Fin.mk.injEq] at h
    exact hkm (Fin.ext (by omega)).symm

/-- Membership in the `u`-interface pairs. -/
theorem mem_uPairsAssoc (s t u v : ℕ) (p) :
    p ∈ uPairsAssoc s t u v ↔
      ∃ k : Fin u,
        p = (Sum.inl (Sum.inr ⟨t + k.val, by have := k.isLt; omega⟩),
          Sum.inr ⟨k.val, by have := k.isLt; omega⟩) := by
  unfold uPairsAssoc
  simp only [List.mem_map, List.mem_reverse, List.mem_finRange,
    true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- The `t`-interface pairs in the common ambient, as a direct
index map. -/
def tPairsAssoc (s t u v : ℕ) :
    List (((Fin (s + t) ⊕ Fin (t + u)) ⊕ Fin (u + v)) ×
      ((Fin (s + t) ⊕ Fin (t + u)) ⊕ Fin (u + v))) :=
  (List.finRange t).reverse.map (fun k =>
    (Sum.inl (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩),
     Sum.inl (Sum.inr ⟨k.val, by have := k.isLt; omega⟩)))

/-- The direct `t`-interface pairs are the embedded interface
pairs. -/
theorem tPairsAssoc_eq (s t u v : ℕ) :
    tPairsAssoc s t u v =
      Fragment.inlPairs (β := Fin (u + v))
        (interfacePairs s t u) := by
  unfold tPairsAssoc Fragment.inlPairs interfacePairs
  rw [List.map_map]
  rfl

/-- Membership in the direct `t`-interface pairs. -/
theorem mem_tPairsAssoc' (s t u v : ℕ) (p) :
    p ∈ tPairsAssoc s t u v ↔
      ∃ k : Fin t,
        p = (Sum.inl (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩),
          Sum.inl (Sum.inr ⟨k.val, by have := k.isLt; omega⟩)) := by
  unfold tPairsAssoc
  simp only [List.mem_map, List.mem_reverse, List.mem_finRange,
    true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- Membership in the embedded `t`-interface pairs. -/
theorem mem_tPairsAssoc (s t u v : ℕ) (p) :
    p ∈ Fragment.inlPairs (β := Fin (u + v))
        (interfacePairs s t u) ↔
      ∃ k : Fin t,
        p = (Sum.inl (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩),
          Sum.inl (Sum.inr ⟨k.val, by have := k.isLt; omega⟩)) := by
  unfold Fragment.inlPairs interfacePairs
  simp only [List.map_map, List.mem_map, List.mem_reverse,
    List.mem_finRange, true_and, Function.comp]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, rfl⟩

/-- Membership in the interface pairs. -/
theorem mem_interfacePairs (s t u : ℕ) (p) :
    p ∈ interfacePairs s t u ↔
      ∃ k : Fin t,
        p = (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
          Sum.inr ⟨k.val, by have := k.isLt; omega⟩) := by
  unfold interfacePairs
  simp only [List.mem_map, List.mem_reverse, List.mem_finRange,
    true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- `mapPairs` composes. -/
theorem mapPairs_mapPairs {α β γ : Type} (e : α ≃ β) (e' : β ≃ γ) :
    ∀ ps, Fragment.mapPairs e' (Fragment.mapPairs e ps) =
      Fragment.mapPairs (e.trans e') ps
  | [] => rfl
  | p :: ps => by
    obtain ⟨a, b⟩ := p
    exact congrArg₂ List.cons rfl (mapPairs_mapPairs e e' ps)

/-- High `G`-labels survive the `t`-interface gluing. -/
theorem highG_surv (s t u : ℕ) (b : Fin (t + u)) (hb : t ≤ b.val) :
    ∀ p ∈ interfacePairs s t u,
      (Sum.inr b : Fin (s + t) ⊕ Fin (t + u)) ≠ p.1 ∧
        Sum.inr b ≠ p.2 := by
  intro p hp
  obtain ⟨k, rfl⟩ := (mem_interfacePairs s t u p).mp hp
  have hk := k.isLt
  refine ⟨Sum.inr_ne_inl, fun h => ?_⟩
  have h2 : b.val = k.val := congrArg Fin.val (Sum.inr.inj h)
  omega

/-- Low `F`-labels survive the `t`-interface gluing. -/
theorem lowF_surv (s t u : ℕ) (a : Fin (s + t)) (ha : a.val < s) :
    ∀ p ∈ interfacePairs s t u,
      (Sum.inl a : Fin (s + t) ⊕ Fin (t + u)) ≠ p.1 ∧
        Sum.inl a ≠ p.2 := by
  intro p hp
  obtain ⟨k, rfl⟩ := (mem_interfacePairs s t u p).mp hp
  have hk := k.isLt
  refine ⟨fun h => ?_, Sum.inl_ne_inr⟩
  have h2 : a.val = s + k.val := congrArg Fin.val (Sum.inl.inj h)
  omega

/-- The inverse boundary identification sends high output labels
to high `G`-labels. -/
theorem interfaceEquiv_symm_high (s t u : ℕ) (k : ℕ) (_hk : k < u)
    (h1 : s + k < s + u) (h2 : t + k < t + u) :
    ((((interfaceSurvEquiv s t u).trans finSumFinEquiv).symm
        ⟨s + k, h1⟩) :
      Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
        (interfacePairs s t u)).val =
      Sum.inr (⟨t + k, h2⟩ : Fin (t + u)) := by
  have hsurv := highG_surv s t u ⟨t + k, h2⟩
    (by change t ≤ t + k; omega)
  have hy : ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
      (⟨Sum.inr ⟨t + k, h2⟩, hsurv⟩ :
        Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
          (interfacePairs s t u)) = ⟨s + k, h1⟩ := by
    have h3 := congrArg finSumFinEquiv
      (interfaceSurvEquiv_inr s t u
        (⟨Sum.inr ⟨t + k, h2⟩, hsurv⟩ :
          Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
            (interfacePairs s t u))
        ⟨t + k, h2⟩ rfl (by change t ≤ t + k; omega))
    rw [finSumFinEquiv_apply_right] at h3
    exact h3.trans (Fin.ext (by change s + (t + k - t) = s + k; omega))
  exact congrArg Subtype.val
    ((_root_.Equiv.symm_apply_eq _).mpr hy.symm)

/-- The inverse boundary identification sends low output labels
to low `F`-labels. -/
theorem interfaceEquiv_symm_low (s t u : ℕ) (k : ℕ) (hk : k < s)
    (h1 : k < s + u) (h2 : k < s + t) :
    ((((interfaceSurvEquiv s t u).trans finSumFinEquiv).symm
        ⟨k, h1⟩) :
      Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
        (interfacePairs s t u)).val =
      Sum.inl (⟨k, h2⟩ : Fin (s + t)) := by
  have hsurv := lowF_surv s t u ⟨k, h2⟩ hk
  have hy : ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
      (⟨Sum.inl ⟨k, h2⟩, hsurv⟩ :
        Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
          (interfacePairs s t u)) = ⟨k, h1⟩ := by
    have h3 := congrArg finSumFinEquiv
      (interfaceSurvEquiv_inl s t u
        (⟨Sum.inl ⟨k, h2⟩, hsurv⟩ :
          Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
            (interfacePairs s t u))
        ⟨k, h2⟩ rfl hk)
    rw [finSumFinEquiv_apply_left] at h3
    exact h3.trans (Fin.ext rfl)
  exact congrArg Subtype.val
    ((_root_.Equiv.symm_apply_eq _).mpr hy.symm)

namespace Fragment

/-- Value of the left-embedding fold equivalence's inverse on an
embedded survivor. -/
theorem inlFoldEquiv_symm_inl_val {α β : Type} (ps : List (α × α))
    (x : FoldSurviving α ps) :
    ((inlFoldEquiv (β := β) ps).symm (Sum.inl x)).val =
      Sum.inl x.val := by
  obtain ⟨a, ha⟩ := x
  rfl

/-- Value of the left-embedding fold equivalence's inverse on a
right label. -/
theorem inlFoldEquiv_symm_inr_val {α β : Type} (ps : List (α × α))
    (b : β) :
    ((inlFoldEquiv (β := β) ps).symm (Sum.inr b)).val =
      Sum.inr b := rfl

/-- Value of the right-embedding fold equivalence's inverse on an
embedded survivor. -/
theorem inrFoldEquiv_symm_inr_val {α β : Type} (qs : List (β × β))
    (x : FoldSurviving β qs) :
    ((inrFoldEquiv (α := α) qs).symm (Sum.inr x)).val =
      Sum.inr x.val := by
  obtain ⟨b, hb⟩ := x
  rfl

/-- Value of the right-embedding fold equivalence's inverse on a
left label. -/
theorem inrFoldEquiv_symm_inl_val {α β : Type} (qs : List (β × β))
    (a : α) :
    ((inrFoldEquiv (α := α) qs).symm (Sum.inl a)).val =
      Sum.inl a := rfl

end Fragment

/-- The mapped-back outer interface pairs of the left association
are the lifted `u`-interface pairs (generalized over the index
list). -/
private theorem lhs_lift_eq_aux (s t u v : ℕ) :
    ∀ (l : List (Fin u))
      (hsep : Fragment.PairsSepAll
        (Fragment.inlPairs (β := Fin (u + v)) (interfacePairs s t u))
        (l.map (fun k =>
          (Sum.inl (Sum.inr ⟨t + k.val, by have := k.isLt; omega⟩),
           Sum.inr ⟨k.val, by have := k.isLt; omega⟩)))),
      Fragment.mapPairs
          ((_root_.Equiv.sumCongr
              ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
              (_root_.Equiv.refl (Fin (u + v)))).symm.trans
            (Fragment.inlFoldEquiv (β := Fin (u + v))
              (interfacePairs s t u)).symm)
          (l.map (fun k =>
            ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
                Fin (s + u) ⊕ Fin (u + v)),
             Sum.inr ⟨k.val, by have := k.isLt; omega⟩))) =
        Fragment.liftPairs _ _ hsep
  | [], _ => rfl
  | k :: l, hsep => by
    simp only [List.map_cons, Fragment.mapPairs,
      Fragment.liftPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (lhs_lift_eq_aux s t u v l _)
    · refine Subtype.ext ?_
      exact (Fragment.inlFoldEquiv_symm_inl_val
          (interfacePairs s t u) _).trans
        (congrArg Sum.inl
          (interfaceEquiv_symm_high s t u k.val k.isLt
            (by have := k.isLt; omega)
            (by have := k.isLt; omega)))
    · refine Subtype.ext ?_
      exact Fragment.inlFoldEquiv_symm_inr_val
        (interfacePairs s t u) _

/-- The mapped-back outer interface pairs of the left association
are the lifted `u`-interface pairs. -/
theorem lhs_pairs_eq (s t u v : ℕ)
    (hsep : Fragment.PairsSepAll
      (Fragment.inlPairs (β := Fin (u + v)) (interfacePairs s t u))
      (uPairsAssoc s t u v)) :
    Fragment.mapPairs
        (Fragment.inlFoldEquiv (β := Fin (u + v))
          (interfacePairs s t u)).symm
        (Fragment.mapPairs
          (_root_.Equiv.sumCongr
            ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
            (_root_.Equiv.refl (Fin (u + v)))).symm
          (interfacePairs s u v)) =
      Fragment.liftPairs _ _ hsep := by
  rw [mapPairs_mapPairs]
  exact lhs_lift_eq_aux s t u v (List.finRange u).reverse hsep

/-- The combined pair list is well-formed. -/
theorem assocPairs_wf (s t u v : ℕ) :
    Fragment.PairsWF
      (Fragment.inlPairs (β := Fin (u + v)) (interfacePairs s t u) ++
        uPairsAssoc s t u v) := by
  unfold Fragment.PairsWF
  rw [List.flatMap_append]
  refine List.Nodup.append
    (Fragment.inlPairs_wf _ (interfacePairs_wf s t u))
    (uPairsAssoc_wf s t u v) ?_
  intro x hx hy
  obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
  obtain ⟨q, hq, hyq⟩ := List.mem_flatMap.mp hy
  obtain ⟨j, rfl⟩ := (mem_tPairsAssoc s t u v p).mp hp
  obtain ⟨k, rfl⟩ := (mem_uPairsAssoc s t u v q).mp hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxp hyq
  have hj := j.isLt
  have hk := k.isLt
  rcases hxp with rfl | rfl <;> rcases hyq with h | h <;>
    (simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq,
      reduceCtorEq] at h <;> omega)

namespace Fragment

variable {α β : Type}

/-- Flip a relabelled equivalence to the other side, relabelled
form on the left. -/
noncomputable def Equiv.relabelFlip' {W₁ : Fragment α}
    {W₂ : Fragment β} {e : α ≃ β}
    (E : (W₁.relabel e).Equiv W₂) :
    W₁.Equiv (W₂.relabel e.symm) :=
  Equiv.relabelFlip E.symm

/-- Iterated gluing does not depend on the well-formedness
proof. -/
noncomputable def glueListProofIrrel (W : Fragment α)
    (ps : List (α × α)) (h1 h2 : PairsWF ps) :
    (glueList W ps h1).Equiv (glueList W ps h2) :=
  Equiv.refl (glueList W ps h1)

end Fragment

/-- Pull gluing pairs through a relabelling and compose a normalized inner fold. -/
noncomputable def glueListPullRelabelTrans {α β γ : Type} (W : Fragment α)
    (σ : α ≃ β) (ps : List (β × β)) (hp : Fragment.PairsWF ps)
    {V : Fragment γ}
    {τ : γ ≃ Fragment.FoldSurviving α (Fragment.mapPairs σ.symm ps)}
    (e : (Fragment.glueList W (Fragment.mapPairs σ.symm ps)
        (Fragment.mapPairs_wf σ.symm ps hp)).Equiv (V.relabel τ)) :=
  (Fragment.Equiv.relabelFlip'
    (Fragment.glueListEqEquiv (W.relabel σ) (mapPairs_symm_cancel σ ps).symm
      hp (Fragment.mapPairs_wf σ _ (Fragment.mapPairs_wf σ.symm ps hp))
      ((mapPairs_symm_cancel σ ps).symm ▸ List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.glueListRelabel W σ (Fragment.mapPairs σ.symm ps)
        (Fragment.mapPairs_wf σ.symm ps hp)).trans
        ((Fragment.Equiv.relabelCongr e
          (Fragment.foldSurvivingMapEquiv σ (Fragment.mapPairs σ.symm ps))).trans
          (Fragment.Equiv.relabelTrans _ _ _)))
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel σ ps).symm ▸ List.Perm.refl _)).symm).trans
      (Fragment.Equiv.relabelTrans _ _ _))

/-- Transport the two closure casts across a normalized right-hand fragment. -/
noncomputable def pairCloseAmbientEquiv {n : ℕ} (F G : Fragment (Fin n))
    {α : Type} {N : Fragment α} {e : α ≃ Fin n} (E : G.Equiv (N.relabel e)) :=
  (Fragment.relabelDisjUnionLeft F
    (G.relabel (finCongr (by omega : n = n + 0)))
    (finCongr (by omega : n = 0 + n))).trans
  ((Fragment.Equiv.relabelCongr
    (Fragment.relabelDisjUnionRight F G (finCongr (by omega : n = n + 0)))
    (_root_.Equiv.sumCongr (finCongr (by omega : n = 0 + n))
      (_root_.Equiv.refl _))).trans
  ((Fragment.Equiv.relabelTrans _ _ _).trans
  ((Fragment.Equiv.relabelCongr
    ((Fragment.Equiv.disjUnionCongr (Fragment.Equiv.refl F) E).trans
      (Fragment.relabelDisjUnionRight F N e))
    ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin n))
        (finCongr (by omega : n = n + 0))).trans
      (_root_.Equiv.sumCongr (finCongr (by omega : n = 0 + n))
        (_root_.Equiv.refl _)))).trans
    (Fragment.Equiv.relabelTrans _ _ _))))

/-! ### The left association, normalized -/

/-- The composed label identification of the left association:
flatten the two-stage survivors, pass through the embedded and
relabelled fold equivalences, and read off the outer boundary
identification. -/
noncomputable def lhsLabelEquiv (s t u v : ℕ) :
    Fragment.FoldSurviving
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕ Fin (u + v))
        (Fragment.inlPairs (interfacePairs s t u) ++
          uPairsAssoc s t u v) ≃
      Fin (s + v) :=
  ((Fragment.appendFlatten _ _
      ((assocPairs_wf s t u v).append_sep)).symm.trans
    ((Fragment.foldSurvivingPermEquiv
        ((lhs_pairs_eq s t u v
          ((assocPairs_wf s t u v).append_sep)) ▸
          List.Perm.refl _)).symm.trans
      ((Fragment.foldSurvivingMapEquiv
          (Fragment.inlFoldEquiv (β := Fin (u + v))
            (interfacePairs s t u))
          (Fragment.mapPairs
            (Fragment.inlFoldEquiv (β := Fin (u + v))
              (interfacePairs s t u)).symm
            (Fragment.mapPairs
              (_root_.Equiv.sumCongr
                ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
                (_root_.Equiv.refl (Fin (u + v)))).symm
              (interfacePairs s u v)))).trans
        ((Fragment.foldSurvivingPermEquiv
            ((mapPairs_symm_cancel
              (Fragment.inlFoldEquiv (β := Fin (u + v))
                (interfacePairs s t u))
              (Fragment.mapPairs
                (_root_.Equiv.sumCongr
                  ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
                  (_root_.Equiv.refl (Fin (u + v)))).symm
                (interfacePairs s u v))).symm ▸
              List.Perm.refl _)).symm.trans
          ((Fragment.foldSurvivingMapEquiv
              (_root_.Equiv.sumCongr
                ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
                (_root_.Equiv.refl (Fin (u + v))))
              (Fragment.mapPairs
                (_root_.Equiv.sumCongr
                  ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
                  (_root_.Equiv.refl (Fin (u + v)))).symm
                (interfacePairs s u v))).trans
            ((Fragment.foldSurvivingPermEquiv
                ((mapPairs_symm_cancel
                  (_root_.Equiv.sumCongr
                    ((interfaceSurvEquiv s t u).trans
                      finSumFinEquiv)
                    (_root_.Equiv.refl (Fin (u + v))))
                  (interfacePairs s u v)).symm ▸
                  List.Perm.refl _)).symm.trans
              ((interfaceSurvEquiv s u v).trans
                finSumFinEquiv)))))))

/-- The swapped combined pair list is well-formed. -/
theorem assocPairsR_wf (s t u v : ℕ) :
    Fragment.PairsWF
      (uPairsAssoc s t u v ++ tPairsAssoc s t u v) := by
  unfold Fragment.PairsWF
  rw [List.flatMap_append]
  refine List.Nodup.append (uPairsAssoc_wf s t u v)
    (tPairsAssoc_eq s t u v ▸
      Fragment.inlPairs_wf _ (interfacePairs_wf s t u)) ?_
  intro x hx hy
  obtain ⟨p, hp, hxp⟩ := List.mem_flatMap.mp hx
  obtain ⟨q, hq, hyq⟩ := List.mem_flatMap.mp hy
  obtain ⟨k, rfl⟩ := (mem_uPairsAssoc s t u v p).mp hp
  obtain ⟨j, rfl⟩ := (mem_tPairsAssoc' s t u v q).mp hq
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxp hyq
  have hj := j.isLt
  have hk := k.isLt
  rcases hxp with rfl | rfl <;> rcases hyq with h | h <;>
    (simp only [Sum.inl.injEq, Sum.inr.injEq, Fin.mk.injEq,
      reduceCtorEq] at h <;> omega)

/-- The associativity-transported right-embedded `u`-interface
pairs are the ambient `u`-interface pairs (generalized over the
index list). -/
private theorem rhs_ground_eq_aux (s t u v : ℕ) :
    ∀ (l : List (Fin u)),
      Fragment.mapPairs
          ((_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (t + u))
            (Fin (u + v))).symm.symm).symm
          ((l.map (fun k =>
            ((Sum.inl ⟨t + k.val, by have := k.isLt; omega⟩ :
                Fin (t + u) ⊕ Fin (u + v)),
             Sum.inr ⟨k.val, by have := k.isLt; omega⟩))).map
            (Prod.map Sum.inr Sum.inr)) =
        l.map (fun k =>
          (Sum.inl (Sum.inr ⟨t + k.val, by have := k.isLt; omega⟩),
           Sum.inr ⟨k.val, by have := k.isLt; omega⟩))
  | [] => rfl
  | k :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    exact congrArg₂ List.cons rfl (rhs_ground_eq_aux s t u v l)

/-- The associativity-transported right-embedded `u`-interface
pairs are the ambient `u`-interface pairs. -/
theorem rhs_ground_eq (s t u v : ℕ) :
    Fragment.mapPairs
        ((_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (t + u))
          (Fin (u + v))).symm.symm).symm
        (Fragment.inrPairs (α := Fin (s + t))
          (interfacePairs t u v)) =
      uPairsAssoc s t u v :=
  rhs_ground_eq_aux s t u v (List.finRange u).reverse

/-- The associativity bridge: survivors of the ambient
`u`-interface pairs are survivors of the right-embedded pairs in
the right-associated ambient. -/
noncomputable def rhsBridgeEquiv (s t u v : ℕ) :
    Fragment.FoldSurviving
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕ Fin (u + v))
        (uPairsAssoc s t u v) ≃
      Fragment.FoldSurviving
        (Fin (s + t) ⊕ (Fin (t + u) ⊕ Fin (u + v)))
        (Fragment.inrPairs (α := Fin (s + t))
          (interfacePairs t u v)) :=
  (Fragment.foldSurvivingPermEquiv
      ((rhs_ground_eq s t u v) ▸ List.Perm.refl _)).symm.trans
    ((Fragment.foldSurvivingMapEquiv
        ((_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (t + u))
          (Fin (u + v))).symm.symm)
        (Fragment.mapPairs
          ((_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (t + u))
            (Fin (u + v))).symm.symm).symm
          (Fragment.inrPairs (α := Fin (s + t))
            (interfacePairs t u v)))).trans
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel
          ((_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (t + u))
            (Fin (u + v))).symm.symm)
          (Fragment.inrPairs (α := Fin (s + t))
            (interfacePairs t u v))).symm ▸
          List.Perm.refl _)).symm)

/-- The lifted `t`-interface identification, generalized over any
transport with the expected boundary values. -/
private theorem rhs_lift_eq_aux (s t u v : ℕ)
    (E : (Fin (s + t) ⊕ Fin (t + v)) ≃
      Fragment.FoldSurviving
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕ Fin (u + v))
        (uPairsAssoc s t u v))
    (hEl : ∀ a : Fin (s + t),
      (E (Sum.inl a)).val = Sum.inl (Sum.inl a))
    (hEr : ∀ (k : ℕ) (_hk : k < t) (h1 : k < t + v)
      (h2 : k < t + u),
      (E (Sum.inr ⟨k, h1⟩)).val = Sum.inl (Sum.inr ⟨k, h2⟩)) :
    ∀ (l : List (Fin t))
      (hsep : Fragment.PairsSepAll (uPairsAssoc s t u v)
        (l.map (fun k =>
          (Sum.inl (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩),
           Sum.inl (Sum.inr
             ⟨k.val, by have := k.isLt; omega⟩))))),
      Fragment.mapPairs E
          (l.map (fun k =>
            ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
                Fin (s + t) ⊕ Fin (t + v)),
             Sum.inr ⟨k.val, by have := k.isLt; omega⟩))) =
        Fragment.liftPairs _ _ hsep
  | [], _ => rfl
  | k :: l, hsep => by
    simp only [List.map_cons, Fragment.mapPairs,
      Fragment.liftPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (rhs_lift_eq_aux s t u v E hEl hEr l _)
    · exact Subtype.ext (hEl ⟨s + k.val, by have := k.isLt; omega⟩)
    · exact Subtype.ext (hEr k.val k.isLt
        (by have := k.isLt; omega) (by have := k.isLt; omega))

/-- The mapped-back outer interface pairs of the right
association are the lifted `t`-interface pairs. -/
theorem rhs_pairs_eq (s t u v : ℕ)
    (hsep : Fragment.PairsSepAll (uPairsAssoc s t u v)
      (tPairsAssoc s t u v)) :
    Fragment.mapPairs (rhsBridgeEquiv s t u v).symm
        (Fragment.mapPairs
          (Fragment.inrFoldEquiv (α := Fin (s + t))
            (interfacePairs t u v)).symm
          (Fragment.mapPairs
            (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
              ((interfaceSurvEquiv t u v).trans
                finSumFinEquiv)).symm
            (interfacePairs s t v))) =
      Fragment.liftPairs _ _ hsep := by
  rw [mapPairs_mapPairs, mapPairs_mapPairs]
  refine rhs_lift_eq_aux s t u v
    ((_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
        ((interfaceSurvEquiv t u v).trans finSumFinEquiv)).symm.trans
      ((Fragment.inrFoldEquiv (α := Fin (s + t))
          (interfacePairs t u v)).symm.trans
        (rhsBridgeEquiv s t u v).symm))
    (fun a => rfl)
    (fun k hk h1 h2 => ?_) (List.finRange t).reverse hsep
  exact congrArg
    (fun z => ((_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (t + u))
      (Fin (u + v))).symm.symm).symm z)
    ((Fragment.inrFoldEquiv_symm_inr_val (interfacePairs t u v)
        (((interfaceSurvEquiv t u v).trans finSumFinEquiv).symm
          ⟨k, h1⟩)).trans
      (congrArg Sum.inr
        (interfaceEquiv_symm_low t u v k hk h1 h2)))

private theorem lhsOuterPairs_wf (s t u v : ℕ) :
    Fragment.PairsWF
      (Fragment.mapPairs (Fragment.inlFoldEquiv (β := Fin (u + v))
          (interfacePairs s t u)).symm
        (Fragment.mapPairs (_root_.Equiv.sumCongr
            ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
            (_root_.Equiv.refl (Fin (u + v)))).symm (interfacePairs s u v))) :=
  Fragment.mapPairs_wf _ _ (Fragment.mapPairs_wf _ _ (interfacePairs_wf s u v))

/-- **The left association, normalized**: composing `F` with `G`
and then with `H` is iterated gluing of the embedded
`t`-interface pairs followed by the `u`-interface pairs over the
common ambient `(F ⊔ G) ⊔ H`. -/
noncomputable def assocNormalLeft {s t u v : ℕ}
    (F : Fragment (Fin (s + t))) (G : Fragment (Fin (t + u)))
    (H : Fragment (Fin (u + v))) :
    ((F.compose G).compose H).Equiv
      ((Fragment.glueList ((F.disjUnion G).disjUnion H)
          (Fragment.inlPairs (interfacePairs s t u) ++
            uPairsAssoc s t u v)
          (assocPairs_wf s t u v)).relabel
        (lhsLabelEquiv s t u v)) := by
  let σ := _root_.Equiv.sumCongr
    ((interfaceSurvEquiv s t u).trans finSumFinEquiv)
    (_root_.Equiv.refl (Fin (u + v)))
  let i := Fragment.inlFoldEquiv (β := Fin (u + v))
    (interfacePairs s t u)
  let ps' := Fragment.mapPairs σ.symm (interfacePairs s u v)
  let ps'' := Fragment.mapPairs i.symm ps'
  let wfps' : Fragment.PairsWF ps' :=
    Fragment.mapPairs_wf σ.symm _ (interfacePairs_wf s u v)
  let wfps'' : Fragment.PairsWF ps'' :=
    lhsOuterPairs_wf s t u v
  let A := (F.disjUnion G).disjUnion H
  let X := Fragment.glueList A
    (Fragment.inlPairs (interfacePairs s t u))
    ((assocPairs_wf s t u v).append_left)
  let N₁ := Fragment.glueList (F.disjUnion G)
    (interfacePairs s t u) (interfacePairs_wf s t u)
  -- C8: the doubly-glued fragment against the two-stage fold.
  have C8 :=
    (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv X
        (lhs_pairs_eq s t u v ((assocPairs_wf s t u v).append_sep))
        wfps''
        (Fragment.liftPairs_wf _ _
          ((assocPairs_wf s t u v).append_right)
          ((assocPairs_wf s t u v).append_sep))
        ((lhs_pairs_eq s t u v
          ((assocPairs_wf s t u v).append_sep)) ▸
          List.Perm.refl _))).trans
      ((Fragment.Equiv.relabelCongr
        (Fragment.Equiv.relabelFlip
          (Fragment.glueListAppend A
            (Fragment.inlPairs (interfacePairs s t u))
            (uPairsAssoc s t u v)
            (assocPairs_wf s t u v)))
        (Fragment.foldSurvivingPermEquiv
          ((lhs_pairs_eq s t u v
            ((assocPairs_wf s t u v).append_sep)) ▸
            List.Perm.refl _)).symm).trans
      (Fragment.Equiv.relabelTrans _ _ _))
  -- C7: unfold the second relabelling stage.
  have C7 := (Fragment.glueListRelabel X i ps'' wfps'').trans
    ((Fragment.Equiv.relabelCongr C8
      (Fragment.foldSurvivingMapEquiv i ps'')).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C6: bridge the pair list back to ps'.
  have C6 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (X.relabel i)
        (mapPairs_symm_cancel i ps').symm
        wfps' (Fragment.mapPairs_wf i ps'' wfps'')
        ((mapPairs_symm_cancel i ps').symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr C7
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel i ps').symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- E4: the glued left factor is the embedded fold, relabelled.
  have E4 :=
    (Fragment.Equiv.relabelFlip
      (Fragment.glueListDisjUnionLeft (F.disjUnion G) H
        (interfacePairs s t u)
        (interfacePairs_wf s t u))).trans
    ((Fragment.Equiv.relabelEq _ (_root_.Equiv.symm_symm i)).trans
    (Fragment.Equiv.relabelCongr
      (Fragment.glueListProofIrrel A
        (Fragment.inlPairs (interfacePairs s t u))
        (Fragment.inlPairs_wf _ (interfacePairs_wf s t u))
        ((assocPairs_wf s t u v).append_left)) i))
  -- C4: transport the outer pairs across E4.
  have C4 := (Fragment.glueListCongr E4 ps' wfps').trans C6
  -- C3: unfold the first relabelling stage.
  have C3 := (Fragment.glueListRelabel (N₁.disjUnion H) σ ps'
      wfps').trans
    ((Fragment.Equiv.relabelCongr C4
      (Fragment.foldSurvivingMapEquiv σ ps')).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C2: bridge the outer interface pairs.
  have C2 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv ((N₁.disjUnion H).relabel σ)
        (mapPairs_symm_cancel σ (interfacePairs s u v)).symm
        (interfacePairs_wf s u v)
        (Fragment.mapPairs_wf σ ps' wfps')
        ((mapPairs_symm_cancel σ (interfacePairs s u v)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr C3
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel σ (interfacePairs s u v)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- E1: normalize the inner composition inside the disjoint union.
  have E1 :=
    (Fragment.Equiv.disjUnionCongr (composeNormal F G)
      (Fragment.Equiv.refl H)).trans
    (Fragment.relabelDisjUnionLeft N₁ H
      ((interfaceSurvEquiv s t u).trans finSumFinEquiv))
  -- C1: transport the outer gluing across E1.
  have C1 := (Fragment.glueListCongr E1 (interfacePairs s u v)
    (interfacePairs_wf s u v)).trans C2
  -- Assemble.
  exact (composeNormal (F.compose G) H).trans
    ((Fragment.Equiv.relabelCongr C1
      ((interfaceSurvEquiv s u v).trans finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

/-! ### The right association, normalized -/

/-- The outer interface pairs of the right association, pulled
back to the boundary of the inner composition. -/
noncomputable def rhsQs1 (s t u v : ℕ) :
    List ((Fin (s + t) ⊕
      Fragment.FoldSurviving (Fin (t + u) ⊕ Fin (u + v))
        (interfacePairs t u v)) ×
      (Fin (s + t) ⊕
      Fragment.FoldSurviving (Fin (t + u) ⊕ Fin (u + v))
        (interfacePairs t u v))) :=
  Fragment.mapPairs
    (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
      ((interfaceSurvEquiv t u v).trans finSumFinEquiv)).symm
    (interfacePairs s t v)

private theorem rhsQs1_wf (s t u v : ℕ) :
    Fragment.PairsWF (rhsQs1 s t u v) :=
  Fragment.mapPairs_wf _ _ (interfacePairs_wf s t v)

/-- The outer interface pairs, pulled into the right-embedded
fold survivors. -/
noncomputable def rhsQs2 (s t u v : ℕ) :=
  Fragment.mapPairs
    (Fragment.inrFoldEquiv (α := Fin (s + t))
      (interfacePairs t u v)).symm
    (rhsQs1 s t u v)

/-- The outer interface pairs, pulled across the associativity
bridge. -/
noncomputable def rhsQs3 (s t u v : ℕ) :=
  Fragment.mapPairs (rhsBridgeEquiv s t u v).symm
    (rhsQs2 s t u v)

/-- The composed label identification of the right
association. -/
noncomputable def rhsLabelEquiv (s t u v : ℕ) :
    Fragment.FoldSurviving
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕ Fin (u + v))
        (Fragment.inlPairs (interfacePairs s t u) ++
          uPairsAssoc s t u v) ≃
      Fin (s + v) :=
  ((Fragment.foldSurvivingPermEquiv
      ((congrArg (· ++ uPairsAssoc s t u v)
        (tPairsAssoc_eq s t u v)) ▸
        List.Perm.refl _)).symm.trans
    ((Fragment.foldSurvivingPermEquiv
        (List.perm_append_comm
          (l₁ := uPairsAssoc s t u v)
          (l₂ := tPairsAssoc s t u v))).symm.trans
      ((Fragment.appendFlatten _ _
          ((assocPairsR_wf s t u v).append_sep)).symm.trans
        ((Fragment.foldSurvivingPermEquiv
            ((rhs_pairs_eq s t u v
              ((assocPairsR_wf s t u v).append_sep)) ▸
              List.Perm.refl _)).symm.trans
          ((Fragment.foldSurvivingMapEquiv
              (rhsBridgeEquiv s t u v) (rhsQs3 s t u v)).trans
            ((Fragment.foldSurvivingPermEquiv
                ((mapPairs_symm_cancel (rhsBridgeEquiv s t u v)
                  (rhsQs2 s t u v)).symm ▸
                  List.Perm.refl _)).symm.trans
              ((Fragment.foldSurvivingMapEquiv
                  (Fragment.inrFoldEquiv (α := Fin (s + t))
                    (interfacePairs t u v))
                  (rhsQs2 s t u v)).trans
                ((Fragment.foldSurvivingPermEquiv
                    ((mapPairs_symm_cancel
                      (Fragment.inrFoldEquiv (α := Fin (s + t))
                        (interfacePairs t u v))
                      (rhsQs1 s t u v)).symm ▸
                      List.Perm.refl _)).symm.trans
                  ((Fragment.foldSurvivingMapEquiv
                      (_root_.Equiv.sumCongr
                        (_root_.Equiv.refl (Fin (s + t)))
                        ((interfaceSurvEquiv t u v).trans
                          finSumFinEquiv))
                      (rhsQs1 s t u v)).trans
                    ((Fragment.foldSurvivingPermEquiv
                        ((mapPairs_symm_cancel
                          (_root_.Equiv.sumCongr
                            (_root_.Equiv.refl (Fin (s + t)))
                            ((interfaceSurvEquiv t u v).trans
                              finSumFinEquiv))
                          (interfacePairs s t v)).symm ▸
                          List.Perm.refl _)).symm.trans
                      ((interfaceSurvEquiv s t v).trans
                        finSumFinEquiv)))))))))))

private theorem rhsQs3_wf (s t u v : ℕ) :
    Fragment.PairsWF (rhsQs3 s t u v) :=
  Fragment.mapPairs_wf _ _ (Fragment.mapPairs_wf _ _ (rhsQs1_wf s t u v))

/-- **The right association, normalized**: composing `F` with the
composition of `G` and `H` is the same iterated gluing over the
common ambient, through the associativity bridge. -/
noncomputable def assocNormalRight {s t u v : ℕ}
    (F : Fragment (Fin (s + t))) (G : Fragment (Fin (t + u)))
    (H : Fragment (Fin (u + v))) :
    (F.compose (G.compose H)).Equiv
      ((Fragment.glueList ((F.disjUnion G).disjUnion H)
          (Fragment.inlPairs (interfacePairs s t u) ++
            uPairsAssoc s t u v)
          (assocPairs_wf s t u v)).relabel
        (rhsLabelEquiv s t u v)) := by
  -- ═══════ SETUP ═══════
  -- The intermediate folds (`XR`, `N₂`, `YR`, `UPA`) over the common
  -- ambient, the relabels between them, and their well-formedness data.
  let σ' := _root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
    ((interfaceSurvEquiv t u v).trans finSumFinEquiv)
  let i' := Fragment.inrFoldEquiv (α := Fin (s + t))
    (interfacePairs t u v)
  let e2a := (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (t + u))
    (Fin (u + v))).symm.symm
  let wfqs1 : Fragment.PairsWF (rhsQs1 s t u v) :=
    rhsQs1_wf s t u v
  let wfqs2 : Fragment.PairsWF (rhsQs2 s t u v) :=
    Fragment.mapPairs_wf i'.symm _ wfqs1
  let wfqs3 : Fragment.PairsWF (rhsQs3 s t u v) :=
    rhsQs3_wf s t u v
  let uA' := Fragment.mapPairs e2a.symm
    (Fragment.inrPairs (α := Fin (s + t)) (interfacePairs t u v))
  let wfuA' : Fragment.PairsWF uA' :=
    Fragment.mapPairs_wf e2a.symm _
      (Fragment.inrPairs_wf _ (interfacePairs_wf t u v))
  let A := (F.disjUnion G).disjUnion H
  let XR := Fragment.glueList (F.disjUnion (G.disjUnion H))
    (Fragment.inrPairs (α := Fin (s + t)) (interfacePairs t u v))
    (Fragment.inrPairs_wf _ (interfacePairs_wf t u v))
  let N₂ := Fragment.glueList (G.disjUnion H)
    (interfacePairs t u v) (interfacePairs_wf t u v)
  let YR := Fragment.glueList A
    (uPairsAssoc s t u v ++ tPairsAssoc s t u v)
    (assocPairsR_wf s t u v)
  let UPA := Fragment.glueList A (uPairsAssoc s t u v)
    ((assocPairsR_wf s t u v).append_left)
  -- ═══════ STAGE 1: THE REORDER AND THE APPEND MERGE ═══════
  -- CP: reorder and rename the pair blocks.
  have CP :=
    (Fragment.glueListPerm A
      (List.perm_append_comm
        (l₁ := uPairsAssoc s t u v)
        (l₂ := tPairsAssoc s t u v))
      (assocPairsR_wf s t u v)).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.Equiv.relabelFlip'
        (Fragment.glueListEqEquiv A
          (congrArg (· ++ uPairsAssoc s t u v)
            (tPairsAssoc_eq s t u v))
          ((assocPairsR_wf s t u v).perm
            (List.perm_append_comm
              (l₁ := uPairsAssoc s t u v)
              (l₂ := tPairsAssoc s t u v)))
          (assocPairs_wf s t u v)
          ((congrArg (· ++ uPairsAssoc s t u v)
            (tPairsAssoc_eq s t u v)) ▸
            List.Perm.refl _)))
      (Fragment.foldSurvivingPermEquiv
        (List.perm_append_comm
          (l₁ := uPairsAssoc s t u v)
          (l₂ := tPairsAssoc s t u v))).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- CR8: the append merge, with the reorder folded in.
  have CR8 :=
    (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv UPA
        (rhs_pairs_eq s t u v
          ((assocPairsR_wf s t u v).append_sep))
        wfqs3
        (Fragment.liftPairs_wf _ _
          ((assocPairsR_wf s t u v).append_right)
          ((assocPairsR_wf s t u v).append_sep))
        ((rhs_pairs_eq s t u v
          ((assocPairsR_wf s t u v).append_sep)) ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.Equiv.relabelFlip
        (Fragment.glueListAppend A (uPairsAssoc s t u v)
          (tPairsAssoc s t u v)
          (assocPairsR_wf s t u v))).trans
        ((Fragment.Equiv.relabelCongr CP
          (Fragment.appendFlatten _ _
            ((assocPairsR_wf s t u v).append_sep)).symm).trans
        (Fragment.Equiv.relabelTrans _ _ _)))
      (Fragment.foldSurvivingPermEquiv
        ((rhs_pairs_eq s t u v
          ((assocPairsR_wf s t u v).append_sep)) ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- ═══════ STAGE 2: THE ASSOCIATIVITY BRIDGE ═══════
  -- CRX: the associativity bridge on the inner fold.
  have CRX :=
    (Fragment.glueListCongr
      (Fragment.Equiv.relabelFlip (Fragment.disjUnionAssoc F G H))
      _ _).trans
    ((Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (A.relabel e2a)
        (mapPairs_symm_cancel e2a
          (Fragment.inrPairs (α := Fin (s + t))
            (interfacePairs t u v))).symm
        (Fragment.inrPairs_wf _ (interfacePairs_wf t u v))
        (Fragment.mapPairs_wf e2a _ wfuA')
        ((mapPairs_symm_cancel e2a
          (Fragment.inrPairs (α := Fin (s + t))
            (interfacePairs t u v))).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.glueListRelabel A e2a uA' wfuA').trans
        ((Fragment.Equiv.relabelCongr
          (Fragment.Equiv.relabelFlip'
            (Fragment.glueListEqEquiv A
              (rhs_ground_eq s t u v)
              wfuA'
              ((assocPairsR_wf s t u v).append_left)
              ((rhs_ground_eq s t u v) ▸ List.Perm.refl _)))
          (Fragment.foldSurvivingMapEquiv e2a uA')).trans
        (Fragment.Equiv.relabelTrans _ _ _)))
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel e2a
          (Fragment.inrPairs (α := Fin (s + t))
            (interfacePairs t u v))).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
  -- CR5: transport the outer pairs across the bridge.
  have CR5 :=
    (Fragment.glueListCongr CRX _ _).trans
    ((Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv
        (UPA.relabel (rhsBridgeEquiv s t u v))
        (mapPairs_symm_cancel (rhsBridgeEquiv s t u v)
          (rhsQs2 s t u v)).symm
        wfqs2
        (Fragment.mapPairs_wf (rhsBridgeEquiv s t u v) _ wfqs3)
        ((mapPairs_symm_cancel (rhsBridgeEquiv s t u v)
          (rhsQs2 s t u v)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.glueListRelabel UPA (rhsBridgeEquiv s t u v)
        (rhsQs3 s t u v) wfqs3)
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel (rhsBridgeEquiv s t u v)
          (rhsQs2 s t u v)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
  -- ═══════ STAGE 3: THE EMBEDDED FOLD ═══════
  -- ER4: the inner composition is the embedded fold.
  have ER4 :=
    (Fragment.Equiv.relabelFlip
      (Fragment.glueListDisjUnionRight F (G.disjUnion H)
        (interfacePairs t u v)
        (interfacePairs_wf t u v))).trans
    (Fragment.Equiv.relabelEq XR (_root_.Equiv.symm_symm i'))
  -- CR3: the i'-relabelling stage.
  have CR3 :=
    (Fragment.glueListCongr ER4 _ _).trans
    ((Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (XR.relabel i')
        (mapPairs_symm_cancel i' (rhsQs1 s t u v)).symm
        wfqs1
        (Fragment.mapPairs_wf i' _ wfqs2)
        ((mapPairs_symm_cancel i' (rhsQs1 s t u v)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.glueListRelabel XR i' (rhsQs2 s t u v) wfqs2)
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel i' (rhsQs1 s t u v)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
  -- ═══════ STAGE 4: THE INNER COMPOSITION, NORMALIZED ═══════
  -- ER1: normalize the inner composition.
  have ER1 :=
    (Fragment.Equiv.disjUnionCongr (Fragment.Equiv.refl F)
      (composeNormal G H)).trans
    (Fragment.relabelDisjUnionRight F N₂
      ((interfaceSurvEquiv t u v).trans finSumFinEquiv))
  -- CR1: the σ'-relabelling stage.
  have CR1 :=
    (Fragment.glueListCongr ER1 _ _).trans
    ((Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv ((F.disjUnion N₂).relabel σ')
        (mapPairs_symm_cancel σ' (interfacePairs s t v)).symm
        (interfacePairs_wf s t v)
        (Fragment.mapPairs_wf σ' _ wfqs1)
        ((mapPairs_symm_cancel σ'
          (interfacePairs s t v)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.glueListRelabel (F.disjUnion N₂) σ'
        (rhsQs1 s t u v) wfqs1)
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel σ'
          (interfacePairs s t v)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
  -- ═══════ ASSEMBLY ═══════
  exact (composeNormal F (G.compose H)).trans
    ((Fragment.Equiv.relabelCongr
      (CR1.trans
        ((Fragment.Equiv.relabelCongr
          (CR3.trans
            ((Fragment.Equiv.relabelCongr
              (CR5.trans
                ((Fragment.Equiv.relabelCongr CR8 _).trans
                (Fragment.Equiv.relabelTrans _ _ _))) _).trans
            (Fragment.Equiv.relabelTrans _ _ _))) _).trans
        (Fragment.Equiv.relabelTrans _ _ _)))
      ((interfaceSurvEquiv s t v).trans finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

/-! ### The meet -/

/-- The two label identifications agree: every survivor of the
combined gluing is a low `F`-label or a high `H`-label, and both
composites read off the same boundary position. -/
theorem label_equiv_meet (s t u v : ℕ) :
    lhsLabelEquiv s t u v = rhsLabelEquiv s t u v := by
  refine _root_.Equiv.ext fun x => ?_
  obtain ⟨xv, hxp⟩ := x
  rcases xv with (a | g) | b
  · rcases Nat.lt_or_ge a.val s with ha | ha
    · rfl
    · exfalso
      have hk : a.val - s < t := by have := a.isLt; omega
      have hmem : _ ∈ Fragment.inlPairs (interfacePairs s t u) ++
          uPairsAssoc s t u v := List.mem_append.mpr (Or.inl
        ((mem_tPairsAssoc s t u v _).mpr ⟨⟨a.val - s, hk⟩, rfl⟩))
      exact (hxp _ hmem).1
        (congrArg (fun z => Sum.inl (Sum.inl z))
          (Fin.ext (show a.val = s + (a.val - s) by omega)))
  · exfalso
    rcases Nat.lt_or_ge g.val t with hg | hg
    · have hmem : _ ∈ Fragment.inlPairs (interfacePairs s t u) ++
          uPairsAssoc s t u v := List.mem_append.mpr (Or.inl
        ((mem_tPairsAssoc s t u v _).mpr ⟨⟨g.val, hg⟩, rfl⟩))
      exact (hxp _ hmem).2
        (congrArg (fun z => Sum.inl (Sum.inr z))
          (Fin.ext (rfl : g.val = g.val)))
    · have hk : g.val - t < u := by have := g.isLt; omega
      have hmem : _ ∈ Fragment.inlPairs (interfacePairs s t u) ++
          uPairsAssoc s t u v := List.mem_append.mpr (Or.inr
        ((mem_uPairsAssoc s t u v _).mpr ⟨⟨g.val - t, hk⟩, rfl⟩))
      exact (hxp _ hmem).1
        (congrArg (fun z => Sum.inl (Sum.inr z))
          (Fin.ext (show g.val = t + (g.val - t) by omega)))
  · rcases Nat.lt_or_ge b.val u with hb | hb
    · exfalso
      have hmem : _ ∈ Fragment.inlPairs (interfacePairs s t u) ++
          uPairsAssoc s t u v := List.mem_append.mpr (Or.inr
        ((mem_uPairsAssoc s t u v _).mpr ⟨⟨b.val, hb⟩, rfl⟩))
      exact (hxp _ hmem).2
        (congrArg Sum.inr (Fin.ext (rfl : b.val = b.val)))
    · exact Fin.ext
        (by change s + (b.val - u) = s + (t + (b.val - u) - t); omega)

/-- **Associativity of composition**: the two associations of a
triple composition are equivalent fragments. -/
noncomputable def composeAssoc {s t u v : ℕ}
    (F : Fragment (Fin (s + t))) (G : Fragment (Fin (t + u)))
    (H : Fragment (Fin (u + v))) :
    ((F.compose G).compose H).Equiv (F.compose (G.compose H)) :=
  (assocNormalLeft F G H).trans
    ((Fragment.Equiv.relabelEq _ (label_equiv_meet s t u v)).trans
      (assocNormalRight F G H).symm)

end RS
