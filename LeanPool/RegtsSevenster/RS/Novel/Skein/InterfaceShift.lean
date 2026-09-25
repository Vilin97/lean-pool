/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.ComposeAssoc

/-!
# The interface shift

Permuting the outgoing boundary of the left factor of a
composition is the same as permuting the incoming boundary of the
right factor by the inverse (`interfaceShift`): both sides glue
`F`'s high label `s + j` to `G`'s low label `σ j`, merely
enumerating the interface in different orders.  This is the
engine of the permutation calculus of §3.1: strand fragments
compose by composing their permutations.
-/

@[expose] public section

namespace RS

/-- The permuted interface pairs: `F`'s high label `s + j`
against `G`'s low label `σ j`, top pair first. -/
noncomputable def shiftPairs (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (u : ℕ) :
    List ((Fin (s + t) ⊕ Fin (t + u)) ×
      (Fin (s + t) ⊕ Fin (t + u))) :=
  (List.finRange t).reverse.map (fun k =>
    (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
     Sum.inr ⟨(σ k).val, by have := (σ k).isLt; omega⟩))

/-- The permuted interface pairs are a permutation of the
`σ`-precomposed enumeration. -/
theorem shiftPairs_perm (s : ℕ) {t : ℕ}
    (σ τ : Equiv.Perm (Fin t)) (u : ℕ) :
    ((List.finRange t).reverse.map (fun k =>
      ((Sum.inl ⟨s + (τ k).val, by have := (τ k).isLt; omega⟩ :
          Fin (s + t) ⊕ Fin (t + u)),
       Sum.inr ⟨(σ (τ k)).val,
         by have := (σ (τ k)).isLt; omega⟩))).Perm
      (shiftPairs s σ u) := by
  unfold shiftPairs
  have h1 : ((List.finRange t).reverse.map τ).Perm
      (List.finRange t).reverse :=
    ((List.reverse_perm (List.finRange t)).map τ).trans
      ((Equiv.Perm.map_finRange_perm τ).trans
        (List.reverse_perm _).symm)
  have h2 := h1.map (fun k : Fin t =>
    ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
        Fin (s + t) ⊕ Fin (t + u)),
     (Sum.inr ⟨(σ k).val, by have := (σ k).isLt; omega⟩ :
        Fin (s + t) ⊕ Fin (t + u))))
  rw [List.map_map] at h2
  exact h2

/-- The inverse outgoing permutation on high labels. -/
theorem outPermEquiv_symm_high (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (k : Fin t) :
    (outPermEquiv s σ).symm (Fin.natAdd s k) =
      Fin.natAdd s (σ.symm k) :=
  (_root_.Equiv.symm_apply_eq _).mpr
    ((outPermEquiv_high s σ (σ.symm k)).trans
      (congrArg (Fin.natAdd s) (σ.apply_symm_apply k))).symm

/-- The inverse incoming permutation on low labels. -/
theorem inPermEquiv_symm_low {t : ℕ} (σ : Equiv.Perm (Fin t))
    (u : ℕ) (k : Fin t) :
    (inPermEquiv σ u).symm (Fin.castAdd u k) =
      Fin.castAdd u (σ.symm k) :=
  (_root_.Equiv.symm_apply_eq _).mpr
    ((inPermEquiv_low σ u (σ.symm k)).trans
      (congrArg (Fin.castAdd u) (σ.apply_symm_apply k))).symm

/-- The left ground list: pulling the outgoing permutation out
of the interface pairs (generalized over the index list). -/
private theorem shift_ground_left_aux (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (u : ℕ) :
    ∀ (l : List (Fin t)),
      Fragment.mapPairs
          (_root_.Equiv.sumCongr (outPermEquiv s σ)
            (_root_.Equiv.refl (Fin (t + u)))).symm
          (l.map (fun k =>
            ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
                Fin (s + t) ⊕ Fin (t + u)),
             Sum.inr ⟨k.val, by have := k.isLt; omega⟩))) =
        l.map (fun k =>
          ((Sum.inl ⟨s + (σ.symm k).val,
              by have := (σ.symm k).isLt; omega⟩ :
              Fin (s + t) ⊕ Fin (t + u)),
           Sum.inr ⟨k.val, by have := k.isLt; omega⟩))
  | [] => rfl
  | k :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ rfl)
      (shift_ground_left_aux s σ u l)
    change Sum.inl ((outPermEquiv s σ).symm ⟨s + k.val, _⟩) = _
    exact congrArg Sum.inl
      ((congrArg (outPermEquiv s σ).symm
        (show (⟨s + k.val, _⟩ : Fin (s + t)) =
          Fin.natAdd s k from Fin.ext rfl)).trans
        ((outPermEquiv_symm_high s σ k).trans (Fin.ext rfl)))

/-- The right ground list: pulling the incoming permutation out
of the interface pairs (generalized over the index list). -/
private theorem shift_ground_right_aux (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (u : ℕ) :
    ∀ (l : List (Fin t)),
      Fragment.mapPairs
          (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
            (inPermEquiv σ.symm u)).symm
          (l.map (fun k =>
            ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
                Fin (s + t) ⊕ Fin (t + u)),
             Sum.inr ⟨k.val, by have := k.isLt; omega⟩))) =
        l.map (fun k =>
          ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
              Fin (s + t) ⊕ Fin (t + u)),
           Sum.inr ⟨(σ k).val, by have := (σ k).isLt; omega⟩))
  | [] => rfl
  | k :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (shift_ground_right_aux s σ u l)
    change Sum.inr ((inPermEquiv σ.symm u).symm ⟨k.val, _⟩) = _
    exact congrArg Sum.inr
      ((congrArg (inPermEquiv σ.symm u).symm
        (show (⟨k.val, _⟩ : Fin (t + u)) =
          Fin.castAdd u k from Fin.ext rfl)).trans
        ((inPermEquiv_symm_low σ.symm u k).trans
          ((congrArg (Fin.castAdd u)
            (rfl : σ.symm.symm k = σ.symm.symm k)).trans
            (Fin.ext rfl))))

/-- The right ground list is the permuted interface. -/
theorem shift_ground_right (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (u : ℕ) :
    Fragment.mapPairs
        (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
          (inPermEquiv σ.symm u)).symm
        (interfacePairs s t u) = shiftPairs s σ u :=
  shift_ground_right_aux s σ u (List.finRange t).reverse

/-- The left ground list, in enumerated form. -/
theorem shift_ground_left (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (u : ℕ) :
    Fragment.mapPairs
        (_root_.Equiv.sumCongr (outPermEquiv s σ)
          (_root_.Equiv.refl (Fin (t + u)))).symm
        (interfacePairs s t u) =
      (List.finRange t).reverse.map (fun k =>
        ((Sum.inl ⟨s + (σ.symm k).val,
            by have := (σ.symm k).isLt; omega⟩ :
            Fin (s + t) ⊕ Fin (t + u)),
         Sum.inr ⟨k.val, by have := k.isLt; omega⟩)) :=
  shift_ground_left_aux s σ u (List.finRange t).reverse

/-- The left ground list is a permutation of the permuted
interface. -/
theorem shift_ground_left_perm (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (u : ℕ) :
    ((List.finRange t).reverse.map (fun k =>
      ((Sum.inl ⟨s + (σ.symm k).val,
          by have := (σ.symm k).isLt; omega⟩ :
          Fin (s + t) ⊕ Fin (t + u)),
       Sum.inr ⟨k.val, by have := k.isLt; omega⟩))).Perm
      (shiftPairs s σ u) := by
  have heq : ((List.finRange t).reverse.map (fun k =>
      ((Sum.inl ⟨s + (σ.symm k).val,
          by have := (σ.symm k).isLt; omega⟩ :
          Fin (s + t) ⊕ Fin (t + u)),
       Sum.inr ⟨k.val, by have := k.isLt; omega⟩))) =
      ((List.finRange t).reverse.map (fun k =>
        ((Sum.inl ⟨s + (σ.symm k).val,
            by have := (σ.symm k).isLt; omega⟩ :
            Fin (s + t) ⊕ Fin (t + u)),
         (Sum.inr ⟨(σ (σ.symm k)).val,
            by have := (σ (σ.symm k)).isLt; omega⟩ :
            Fin (s + t) ⊕ Fin (t + u))))) :=
    List.map_congr_left (fun k _ =>
      Prod.ext rfl (congrArg (fun z : Fin t =>
        (Sum.inr (⟨z.val, by have := z.isLt; omega⟩ :
          Fin (t + u)) : Fin (s + t) ⊕ Fin (t + u)))
        (σ.apply_symm_apply k).symm))
  exact heq ▸ shiftPairs_perm s σ σ.symm u

/-- Membership in the permuted interface pairs. -/
theorem mem_shiftPairs (s : ℕ) {t : ℕ} (σ : Equiv.Perm (Fin t))
    (u : ℕ) (q) :
    q ∈ shiftPairs s σ u ↔
      ∃ k : Fin t,
        q = (Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩,
          Sum.inr ⟨(σ k).val, by have := (σ k).isLt; omega⟩) := by
  unfold shiftPairs
  simp only [List.mem_map, List.mem_reverse, List.mem_finRange,
    true_and]
  exact ⟨fun ⟨k, hk⟩ => ⟨k, hk.symm⟩, fun ⟨k, hk⟩ => ⟨k, hk.symm⟩⟩

/-- The permuted interface pairs are well-formed. -/
theorem shiftPairs_wf (s : ℕ) {t : ℕ} (σ : Equiv.Perm (Fin t))
    (u : ℕ) : Fragment.PairsWF (shiftPairs s σ u) := by
  unfold Fragment.PairsWF shiftPairs
  rw [List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun k _ => by simp, ?_⟩
  rw [List.pairwise_reverse]
  refine (List.nodup_finRange t).pairwise_of_forall_ne ?_
  intro k _ j _ hkj x hxj hxk
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxj hxk
  rcases hxj with rfl | rfl <;> rcases hxk with h | h
  · rw [Sum.inl.injEq, Fin.mk.injEq] at h
    exact hkj (Fin.ext (by omega)).symm
  · exact Sum.inl_ne_inr h
  · exact Sum.inr_ne_inl h
  · rw [Sum.inr.injEq, Fin.mk.injEq] at h
    exact hkj (σ.injective (Fin.ext h)).symm

/-- The composed label identification of the shifted left
side. -/
noncomputable def shiftLabelL (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (u : ℕ) :
    Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
        (shiftPairs s σ u) ≃ Fin (s + u) :=
  ((Fragment.foldSurvivingPermEquiv
      (shift_ground_left_perm s σ u)).symm.trans
    ((Fragment.foldSurvivingPermEquiv
        ((shift_ground_left s σ u) ▸ List.Perm.refl _)).symm.trans
      ((Fragment.foldSurvivingMapEquiv
          (_root_.Equiv.sumCongr (outPermEquiv s σ)
            (_root_.Equiv.refl (Fin (t + u))))
          (Fragment.mapPairs
            (_root_.Equiv.sumCongr (outPermEquiv s σ)
              (_root_.Equiv.refl (Fin (t + u)))).symm
            (interfacePairs s t u))).trans
        ((Fragment.foldSurvivingPermEquiv
            ((mapPairs_symm_cancel
              (_root_.Equiv.sumCongr (outPermEquiv s σ)
                (_root_.Equiv.refl (Fin (t + u))))
              (interfacePairs s t u)).symm ▸
              List.Perm.refl _)).symm.trans
          ((interfaceSurvEquiv s t u).trans finSumFinEquiv)))))

/-- The composed label identification of the shifted right
side. -/
noncomputable def shiftLabelR (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (u : ℕ) :
    Fragment.FoldSurviving (Fin (s + t) ⊕ Fin (t + u))
        (shiftPairs s σ u) ≃ Fin (s + u) :=
  ((Fragment.foldSurvivingPermEquiv
      ((shift_ground_right s σ u) ▸ List.Perm.refl _)).symm.trans
    ((Fragment.foldSurvivingMapEquiv
        (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
          (inPermEquiv σ.symm u))
        (Fragment.mapPairs
          (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
            (inPermEquiv σ.symm u)).symm
          (interfacePairs s t u))).trans
      ((Fragment.foldSurvivingPermEquiv
          ((mapPairs_symm_cancel
            (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
              (inPermEquiv σ.symm u))
            (interfacePairs s t u)).symm ▸
            List.Perm.refl _)).symm.trans
        ((interfaceSurvEquiv s t u).trans finSumFinEquiv))))

-- Raised budget: normalising the shifted side chains the glue-list
-- presentation with two relabels.
/-- The shifted left side, normalized. -/
noncomputable def shiftNormalLeft {s t u : ℕ}
    (σ : Equiv.Perm (Fin t)) (F : Fragment (Fin (s + t)))
    (G : Fragment (Fin (t + u))) :
    ((F.relabel (outPermEquiv s σ)).compose G).Equiv
      ((Fragment.glueList (F.disjUnion G) (shiftPairs s σ u)
          (shiftPairs_wf s σ u)).relabel (shiftLabelL s σ u)) := by
  let scO := _root_.Equiv.sumCongr (outPermEquiv s σ)
    (_root_.Equiv.refl (Fin (t + u)))
  let gL := Fragment.mapPairs scO.symm (interfacePairs s t u)
  let wfgL : Fragment.PairsWF gL :=
    Fragment.mapPairs_wf scO.symm _ (interfacePairs_wf s t u)
  have C2 : (Fragment.glueList (F.disjUnion G) gL wfgL).Equiv
      ((Fragment.glueList (F.disjUnion G) (shiftPairs s σ u)
          (shiftPairs_wf s σ u)).relabel
        ((Fragment.foldSurvivingPermEquiv
            (shift_ground_left_perm s σ u)).symm.trans
          (Fragment.foldSurvivingPermEquiv
            ((shift_ground_left s σ u) ▸
              List.Perm.refl _)).symm)) :=
    (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (F.disjUnion G)
        (shift_ground_left s σ u) wfgL
        ((shiftPairs_wf s σ u).perm
          (shift_ground_left_perm s σ u).symm)
        ((shift_ground_left s σ u) ▸ List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.glueListPerm (F.disjUnion G)
        (shift_ground_left_perm s σ u)
        ((shiftPairs_wf s σ u).perm
          (shift_ground_left_perm s σ u).symm)).trans
        (Fragment.Equiv.relabelCongr
          (Fragment.glueListProofIrrel (F.disjUnion G)
            (shiftPairs s σ u)
            (((shiftPairs_wf s σ u).perm
              (shift_ground_left_perm s σ u).symm).perm
              (shift_ground_left_perm s σ u))
            (shiftPairs_wf s σ u))
          (Fragment.foldSurvivingPermEquiv
            (shift_ground_left_perm s σ u)).symm))
      (Fragment.foldSurvivingPermEquiv
        ((shift_ground_left s σ u) ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  have CIN := (Fragment.glueListCongr
    (Fragment.relabelDisjUnionLeft F G (outPermEquiv s σ))
    (interfacePairs s t u) (interfacePairs_wf s t u)).trans
    ((Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv ((F.disjUnion G).relabel scO)
        (mapPairs_symm_cancel scO (interfacePairs s t u)).symm
        (interfacePairs_wf s t u)
        (Fragment.mapPairs_wf scO _ wfgL)
        ((mapPairs_symm_cancel scO
          (interfacePairs s t u)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.glueListRelabel (F.disjUnion G) scO gL
        wfgL).trans
        ((Fragment.Equiv.relabelCongr C2
          (Fragment.foldSurvivingMapEquiv scO gL)).trans
        (Fragment.Equiv.relabelTrans _ _ _)))
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel scO
          (interfacePairs s t u)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
  exact (composeNormal (F.relabel (outPermEquiv s σ)) G).trans
    ((Fragment.Equiv.relabelCongr CIN
      ((interfaceSurvEquiv s t u).trans finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

-- As for the left side.
/-- The shifted right side, normalized. -/
noncomputable def shiftNormalRight {s t u : ℕ}
    (σ : Equiv.Perm (Fin t)) (F : Fragment (Fin (s + t)))
    (G : Fragment (Fin (t + u))) :
    (F.compose (G.relabel (inPermEquiv σ.symm u))).Equiv
      ((Fragment.glueList (F.disjUnion G) (shiftPairs s σ u)
          (shiftPairs_wf s σ u)).relabel (shiftLabelR s σ u)) := by
  let scI := _root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
    (inPermEquiv σ.symm u)
  let gR := Fragment.mapPairs scI.symm (interfacePairs s t u)
  let wfgR : Fragment.PairsWF gR :=
    Fragment.mapPairs_wf scI.symm _ (interfacePairs_wf s t u)
  have C2 : (Fragment.glueList (F.disjUnion G) gR wfgR).Equiv
      ((Fragment.glueList (F.disjUnion G) (shiftPairs s σ u)
          (shiftPairs_wf s σ u)).relabel
        (Fragment.foldSurvivingPermEquiv
          ((shift_ground_right s σ u) ▸
            List.Perm.refl _)).symm) :=
    Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (F.disjUnion G)
        (shift_ground_right s σ u) wfgR (shiftPairs_wf s σ u)
        ((shift_ground_right s σ u) ▸ List.Perm.refl _))
  have CIN := (Fragment.glueListCongr
    (Fragment.relabelDisjUnionRight F G (inPermEquiv σ.symm u))
    (interfacePairs s t u) (interfacePairs_wf s t u)).trans
    ((Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv ((F.disjUnion G).relabel scI)
        (mapPairs_symm_cancel scI (interfacePairs s t u)).symm
        (interfacePairs_wf s t u)
        (Fragment.mapPairs_wf scI _ wfgR)
        ((mapPairs_symm_cancel scI
          (interfacePairs s t u)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.glueListRelabel (F.disjUnion G) scI gR
        wfgR).trans
        ((Fragment.Equiv.relabelCongr C2
          (Fragment.foldSurvivingMapEquiv scI gR)).trans
        (Fragment.Equiv.relabelTrans _ _ _)))
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel scI
          (interfacePairs s t u)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
  exact (composeNormal F
    (G.relabel (inPermEquiv σ.symm u))).trans
    ((Fragment.Equiv.relabelCongr CIN
      ((interfaceSurvEquiv s t u).trans finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

/-- The two shifted label identifications agree: the boundary
permutation only touches interface labels, which do not
survive. -/
theorem shiftLabel_meet (s : ℕ) {t : ℕ} (σ : Equiv.Perm (Fin t))
    (u : ℕ) : shiftLabelL s σ u = shiftLabelR s σ u := by
  refine _root_.Equiv.ext fun x => ?_
  obtain ⟨xv, hxp⟩ := x
  rcases xv with a | b
  · rcases Nat.lt_or_ge a.val s with ha | ha
    · refine Fin.ext ?_
      change ((outPermEquiv s σ) a).val = a.val
      exact congrArg Fin.val
        ((congrArg (outPermEquiv s σ)
          (Fin.ext rfl : a = Fin.castAdd t ⟨a.val, ha⟩)).trans
        (outPermEquiv_low s σ ⟨a.val, ha⟩))
    · exfalso
      have hk : a.val - s < t := by have := a.isLt; omega
      have hmem : _ ∈ shiftPairs s σ u :=
        (mem_shiftPairs s σ u _).mpr ⟨⟨a.val - s, hk⟩, rfl⟩
      exact (hxp _ hmem).1
        (congrArg Sum.inl
          (Fin.ext (show a.val = s + (a.val - s) by omega)))
  · rcases Nat.lt_or_ge b.val t with hb | hb
    · exfalso
      have hmem : _ ∈ shiftPairs s σ u :=
        (mem_shiftPairs s σ u _).mpr ⟨σ.symm ⟨b.val, hb⟩, rfl⟩
      exact (hxp _ hmem).2
        (congrArg Sum.inr
          (Fin.ext (show b.val =
              (σ (σ.symm ⟨b.val, hb⟩)).val from
            congrArg Fin.val
              (σ.apply_symm_apply ⟨b.val, hb⟩).symm)))
    · have hk : b.val - t < u := by have := b.isLt; omega
      have hv : (inPermEquiv σ.symm u) b = b :=
        ((congrArg (inPermEquiv σ.symm u)
          (Fin.ext (show b.val = t + (b.val - t) by omega) :
            b = Fin.natAdd t ⟨b.val - t, hk⟩)).trans
        ((inPermEquiv_high σ.symm u ⟨b.val - t, hk⟩).trans
          (Fin.ext (show t + (b.val - t) = b.val by omega))))
      refine Fin.ext ?_
      change s + (b.val - t) =
        s + (((inPermEquiv σ.symm u) b).val - t)
      have := congrArg Fin.val hv
      omega

/-- **The interface shift** (accompanying paper §3.1): permuting the
outgoing
boundary of the left factor is permuting the incoming boundary of
the right factor by the inverse. -/
noncomputable def interfaceShift {s t u : ℕ}
    (σ : Equiv.Perm (Fin t)) (F : Fragment (Fin (s + t)))
    (G : Fragment (Fin (t + u))) :
    ((F.relabel (outPermEquiv s σ)).compose G).Equiv
      (F.compose (G.relabel (inPermEquiv σ.symm u))) :=
  (shiftNormalLeft σ F G).trans
    ((Fragment.Equiv.relabelEq _ (shiftLabel_meet s σ u)).trans
      (shiftNormalRight σ F G).symm)

end RS
