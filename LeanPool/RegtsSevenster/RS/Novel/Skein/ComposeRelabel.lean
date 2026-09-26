/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.PermCompose
public import LeanPool.RegtsSevenster.RS.Novel.Skein.IdentityLawRight

/-!
# Free-side relabels pass through composition

Relabelling the free (non-interface) boundary of a factor
relabels the composite: permuting the outgoing boundary of the
right factor commutes with `compose` (`composeRelabelOut`),
because the interface pairs are untouched.  That is the naturality
law of the boundary identifications, and the engine that lets a
permutation fragment be absorbed into a relabel
(`composePermFragment`, `permFragmentComposeLeft`).

The outgoing relabel's own inverse law (`outPermEquiv_symm`, with
its two halves `outPermEquiv_symm_low` and
`outPermEquiv_symm_high`) lives here too, since it is what lets the
absorption run in either direction.
-/

@[expose] public section

namespace RS

/-- The inverse outgoing permutation fixes low labels. -/
theorem outPermEquiv_symm_low (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) (a : Fin s) :
    (outPermEquiv s σ).symm (Fin.castAdd t a) = Fin.castAdd t a :=
  (_root_.Equiv.symm_apply_eq _).mpr
    (outPermEquiv_low s σ a).symm

/-! ### The interface pairs are untouched -/

/-- The inverse of an outgoing permutation is the outgoing
inverse permutation. -/
theorem outPermEquiv_symm (s : ℕ) {t : ℕ}
    (σ : Equiv.Perm (Fin t)) :
    (outPermEquiv s σ).symm = outPermEquiv s σ.symm := by
  apply _root_.Equiv.ext
  intro x
  by_cases h : x.val < s
  · rw [show x = Fin.castAdd t (⟨x.val, h⟩ : Fin s) from
      Fin.ext rfl, outPermEquiv_symm_low, outPermEquiv_low]
  · have hk : x.val - s < t := by have := x.isLt; omega
    rw [show x = Fin.natAdd s (⟨x.val - s, hk⟩ : Fin t) from
      Fin.ext (by change x.val = s + (x.val - s); omega),
      outPermEquiv_symm_high, outPermEquiv_high]

private theorem out_ground_aux (s t u : ℕ)
    (σ : Equiv.Perm (Fin u)) :
    ∀ (l : List (Fin t)),
      Fragment.mapPairs
          (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
            (outPermEquiv t σ)).symm
          (l.map (fun k =>
            ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
              Fin (s + t) ⊕ Fin (t + u)),
             Sum.inr ⟨k.val, by have := k.isLt; omega⟩))) =
        l.map (fun k =>
          ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
            Fin (s + t) ⊕ Fin (t + u)),
           Sum.inr ⟨k.val, by have := k.isLt; omega⟩))
  | [] => rfl
  | k :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (out_ground_aux s t u σ l)
    change Sum.inr ((outPermEquiv t σ).symm
      ⟨k.val, by have := k.isLt; omega⟩) = _
    refine congrArg Sum.inr ?_
    rw [show (⟨k.val, by have := k.isLt; omega⟩ : Fin (t + u)) =
        Fin.castAdd u k from Fin.ext rfl,
      outPermEquiv_symm_low]

/-- Peeling an outgoing permutation of the right factor leaves
the interface pairs untouched. -/
theorem out_ground (s t u : ℕ) (σ : Equiv.Perm (Fin u)) :
    Fragment.mapPairs
        (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
          (outPermEquiv t σ)).symm
        (interfacePairs s t u) = interfacePairs s t u := by
  unfold interfacePairs
  exact out_ground_aux s t u σ (List.finRange t).reverse

/-! ### The outgoing relabel -/

/-- The peeled pairs of the outgoing relabel. -/
noncomputable def outQs (s t u : ℕ) (σ : Equiv.Perm (Fin u)) :=
  Fragment.mapPairs
    (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
      (outPermEquiv t σ)).symm
    (interfacePairs s t u)

/-- The label meet of the outgoing relabel: the survivor chase. -/
theorem out_label_meet (s t u : ℕ) (σ : Equiv.Perm (Fin u)) :
    (Fragment.foldSurvivingPermEquiv
        ((out_ground s t u σ) ▸ List.Perm.refl _)).symm.trans
      ((Fragment.foldSurvivingMapEquiv
          (_root_.Equiv.sumCongr
            (_root_.Equiv.refl (Fin (s + t)))
            (outPermEquiv t σ))
          (outQs s t u σ)).trans
        ((Fragment.foldSurvivingPermEquiv
            ((mapPairs_symm_cancel
              (_root_.Equiv.sumCongr
                (_root_.Equiv.refl (Fin (s + t)))
                (outPermEquiv t σ))
              (interfacePairs s t u)).symm ▸
              List.Perm.refl _)).symm.trans
          ((interfaceSurvEquiv s t u).trans finSumFinEquiv))) =
      ((interfaceSurvEquiv s t u).trans finSumFinEquiv).trans
        (outPermEquiv s σ) := by
  apply _root_.Equiv.ext
  intro x
  obtain ⟨xv, hx⟩ := x
  have hpred := (interfaceSurv_iff s t u xv).mp
    ((forall_ne_iff_not_mem_flat _ xv).mp hx)
  rcases xv with a | b
  · change finSumFinEquiv (interfaceSurvEquiv s t u
      ⟨Sum.inl a, hx⟩) =
      outPermEquiv s σ (finSumFinEquiv (interfaceSurvEquiv s t u
        ⟨Sum.inl a, hx⟩))
    rw [interfaceSurvEquiv_inl s t u ⟨Sum.inl a, hx⟩ a rfl hpred,
      finSumFinEquiv_apply_left, outPermEquiv_low]
  · have hb : t ≤ b.val := Nat.le_of_not_lt hpred
    have hj : b.val - t < u := by have := b.isLt; omega
    have hb2 : b = Fin.natAdd t ⟨b.val - t, hj⟩ :=
      Fin.ext (by change b.val = t + (b.val - t); omega)
    have hbv : outPermEquiv t σ b =
        Fin.natAdd t (σ ⟨b.val - t, hj⟩) := by
      conv_lhs => rw [hb2]
      exact outPermEquiv_high t σ ⟨b.val - t, hj⟩
    have hsurvL : ∀ p ∈ interfacePairs s t u,
        (Sum.inr (outPermEquiv t σ b) :
          Fin (s + t) ⊕ Fin (t + u)) ≠ p.1 ∧
        (Sum.inr (outPermEquiv t σ b) :
          Fin (s + t) ⊕ Fin (t + u)) ≠ p.2 :=
      (forall_ne_iff_not_mem_flat _ _).mpr
        ((interfaceSurv_iff s t u _).mpr
          (by change ¬ (outPermEquiv t σ b).val < t
              rw [hbv]
              change ¬ t + (σ ⟨b.val - t, hj⟩).val < t
              omega))
    change finSumFinEquiv (interfaceSurvEquiv s t u
      ⟨Sum.inr (outPermEquiv t σ b), hsurvL⟩) =
      outPermEquiv s σ (finSumFinEquiv (interfaceSurvEquiv s t u
        ⟨Sum.inr b, hx⟩))
    rw [interfaceSurvEquiv_inr s t u
        ⟨Sum.inr (outPermEquiv t σ b), hsurvL⟩ _ rfl
        (by rw [hbv]; change t ≤ t + _; omega),
      interfaceSurvEquiv_inr s t u ⟨Sum.inr b, hx⟩ b rfl hb,
      finSumFinEquiv_apply_right, finSumFinEquiv_apply_right,
      outPermEquiv_high]
    refine congrArg (Fin.natAdd s) ?_
    refine Fin.ext ?_
    change (outPermEquiv t σ b).val - t = (σ ⟨b.val - t, hj⟩).val
    rw [hbv]
    change t + (σ ⟨b.val - t, hj⟩).val - t = (σ ⟨b.val - t, hj⟩).val
    omega

/-- **Outgoing relabels pass through composition**: permuting the
outgoing boundary of the right factor permutes the outgoing
boundary of the composite. -/
noncomputable def composeRelabelOut {s t u : ℕ}
    (σ : Equiv.Perm (Fin u)) (F : Fragment (Fin (s + t)))
    (G : Fragment (Fin (t + u))) :
    (F.compose (G.relabel (outPermEquiv t σ))).Equiv
      ((F.compose G).relabel (outPermEquiv s σ)) := by
  let e := _root_.Equiv.sumCongr
    (_root_.Equiv.refl (Fin (s + t))) (outPermEquiv t σ)
  let qs := outQs s t u σ
  have wfqs : Fragment.PairsWF qs :=
    Fragment.mapPairs_wf e.symm _ (interfacePairs_wf s t u)
  let Amb := F.disjUnion G
  -- C5: bridge the peeled pairs to the interface pairs.
  have C5 : (Fragment.glueList Amb qs wfqs).Equiv
      ((Fragment.glueList Amb (interfacePairs s t u)
          (interfacePairs_wf s t u)).relabel
        (Fragment.foldSurvivingPermEquiv
          ((out_ground s t u σ) ▸ List.Perm.refl _)).symm) :=
    Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv Amb (out_ground s t u σ)
        wfqs (interfacePairs_wf s t u)
        (List.Perm.of_eq (out_ground s t u σ)))
  -- C3: the relabelling stage.
  have C3 := (Fragment.glueListRelabel Amb e qs wfqs).trans
    ((Fragment.Equiv.relabelCongr C5
      (Fragment.foldSurvivingMapEquiv e qs)).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C2: bridge the interface pairs.
  have C2 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (Amb.relabel e)
        (mapPairs_symm_cancel e (interfacePairs s t u)).symm
        (interfacePairs_wf s t u)
        (Fragment.mapPairs_wf e _ wfqs)
        (List.Perm.of_eq (mapPairs_symm_cancel e
          (interfacePairs s t u)).symm))).trans
    ((Fragment.Equiv.relabelCongr C3
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel e
          (interfacePairs s t u)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C1: transport across the peel.
  have C1 := (Fragment.glueListCongr
    (Fragment.relabelDisjUnionRight F G (outPermEquiv t σ))
    (interfacePairs s t u) (interfacePairs_wf s t u)).trans C2
  -- Assemble both sides.
  exact (composeNormal F (G.relabel (outPermEquiv t σ))).trans
    ((Fragment.Equiv.relabelCongr C1
      ((interfaceSurvEquiv s t u).trans finSumFinEquiv)).trans
    ((Fragment.Equiv.relabelTrans _ _ _).trans
    ((Fragment.Equiv.relabelEq _ (out_label_meet s t u σ)).trans
    ((Fragment.Equiv.relabelTrans _ _ _).symm.trans
    (Fragment.Equiv.relabelCongr
      (composeNormal F G).symm (outPermEquiv s σ))))))

/-! ### Permutation fragments absorb into relabels -/

/-- Composing with a permutation fragment on the right relabels
the outgoing boundary. -/
noncomputable def composePermFragment {s t : ℕ}
    (σ : Equiv.Perm (Fin t)) (F : Fragment (Fin (s + t))) :
    (F.compose (permFragment σ)).Equiv
      (F.relabel (outPermEquiv s σ)) :=
  (Fragment.composeCongr (Fragment.Equiv.refl F)
      (permFragmentRelabelOutPerm σ)).trans
    ((composeRelabelOut σ F (strandBundle t)).trans
      (Fragment.Equiv.relabelCongr
        (composeStrandBundleRight s t F) (outPermEquiv s σ)))

/-- Composing with a permutation fragment on the left relabels
the incoming boundary by the inverse. -/
noncomputable def permFragmentComposeLeft {t u : ℕ}
    (σ : Equiv.Perm (Fin t)) (F : Fragment (Fin (t + u))) :
    ((permFragment σ).compose F).Equiv
      (F.relabel (inPermEquiv σ.symm u)) :=
  (Fragment.composeCongr (permFragmentRelabelOutPerm σ)
      (Fragment.Equiv.refl F)).trans
    ((interfaceShift σ (strandBundle t) F).trans
      (composeStrandBundleLeft t u
        (F.relabel (inPermEquiv σ.symm u))))

end RS
