/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.PartialCloseTensor
import LeanPool.RegtsSevenster.RS.Novel.Skein.Multiplicativity
import LeanPool.RegtsSevenster.RS.Novel.Skein.TraceCyclic
import LeanPool.RegtsSevenster.RS.Novel.Skein.BundleTensor

/-!
# Closure against a fragment with a closed attachment

A closed component riding along the test fragment falls out of
the closure as a disjoint union:

`pairClose F ((H ⊔ C) · clean) ≃ (pairClose F H) ∪ C`.

Combined with `partialCloseTensor`, `strandBundleTensor` and
the multiplicativity of the parameter (Lemma 3.2), this yields the
trace multiplicativity (Lemma 3.5(b)).
-/

namespace RS

/-- The peel of the union closure: the closure casts against the
clean label. -/
noncomputable def unionPeel (s t : ℕ) :
    (Fin (s + t) ⊕ (Fin (s + t) ⊕ Fin (0 + 0))) ≃
      (Fin (0 + (s + t)) ⊕ Fin ((s + t) + 0)) :=
  _root_.Equiv.sumCongr
    (finCongr (by omega : s + t = 0 + (s + t)))
    ((pcTensorClose s t).trans
      (finCongr (by omega : s + t = (s + t) + 0)))

/-- The peeled union-closure pairs. -/
noncomputable def unionQs (s t : ℕ) :=
  Fragment.mapPairs (unionPeel s t).symm
    (interfacePairs 0 (s + t) 0)

private theorem union_ground_high_aux (s t : ℕ) :
    ∀ (l : List (Fin t)),
      Fragment.mapPairs (unionPeel s t).symm
          (l.map (fun k =>
            ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
              Fin (0 + (s + t)) ⊕ Fin ((s + t) + 0)),
             Sum.inr ⟨s + k.val, by have := k.isLt; omega⟩))) =
        l.map (fun k =>
          ((Sum.inl ⟨s + k.val, by have := k.isLt; omega⟩ :
            Fin (s + t) ⊕ (Fin (s + t) ⊕ Fin (0 + 0))),
           Sum.inr (Sum.inl ⟨s + k.val,
             by have := k.isLt; omega⟩)))
  | [] => rfl
  | k :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    exact congrArg₂ List.cons (Prod.ext rfl rfl)
      (union_ground_high_aux s t l)

private theorem union_ground_low_aux (s t : ℕ) :
    ∀ (l : List (Fin s)),
      Fragment.mapPairs (unionPeel s t).symm
          (l.map (fun i =>
            ((Sum.inl ⟨i.val, by have := i.isLt; omega⟩ :
              Fin (0 + (s + t)) ⊕ Fin ((s + t) + 0)),
             Sum.inr ⟨i.val, by have := i.isLt; omega⟩))) =
        l.map (fun i =>
          ((Sum.inl ⟨i.val, by have := i.isLt; omega⟩ :
            Fin (s + t) ⊕ (Fin (s + t) ⊕ Fin (0 + 0))),
           Sum.inr (Sum.inl ⟨i.val, by have := i.isLt; omega⟩)))
  | [] => rfl
  | i :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    exact congrArg₂ List.cons (Prod.ext rfl rfl)
      (union_ground_low_aux s t l)

/-- The peeled union-closure pairs are the associated embedding
of the inner closure pairs. -/
theorem union_ground (s t : ℕ) :
    Fragment.mapPairs (unionPeel s t).symm
        (interfacePairs 0 (s + t) 0) =
      Fragment.mapPairs
        (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (s + t))
          (Fin (0 + 0))).symm.symm
        (Fragment.inlPairs (β := Fin (0 + 0))
          (innerClosePairs s t)) := by
  rw [interfacePairs_closure_split s t, mapPairs_append]
  unfold ipHigh ipLow
  rw [union_ground_high_aux s t, union_ground_low_aux s t]
  unfold Fragment.mapPairs Fragment.inlPairs innerClosePairs
  simp only [List.map_append, List.map_map]
  rfl

/-- The composed label identification of the union closure. -/
noncomputable def unionLabel (s t : ℕ) :
    (Fin (0 + 0) ⊕ Fin (0 + 0)) ≃ Fin (0 + 0) :=
  (_root_.Equiv.sumCongr (innerLabel s t).symm
      (_root_.Equiv.refl (Fin (0 + 0)))).trans
    ((Fragment.inlFoldEquiv (β := Fin (0 + 0))
        (innerClosePairs s t)).symm.trans
      ((Fragment.foldSurvivingMapEquiv
          (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (s + t))
            (Fin (0 + 0))).symm.symm
          (Fragment.inlPairs (β := Fin (0 + 0))
            (innerClosePairs s t))).trans
        ((Fragment.foldSurvivingPermEquiv
            ((union_ground s t) ▸ List.Perm.refl _)).symm.trans
          ((Fragment.foldSurvivingMapEquiv (unionPeel s t)
              (unionQs s t)).trans
            ((Fragment.foldSurvivingPermEquiv
                ((mapPairs_symm_cancel (unionPeel s t)
                  (interfacePairs 0 (s + t) 0)).symm ▸
                  List.Perm.refl _)).symm.trans
              ((interfaceSurvEquiv 0 (s + t) 0).trans
                finSumFinEquiv))))))

/-- **The union closure, normalized.** -/
noncomputable def unionNormal {s t : ℕ}
    (F H : Fragment (Fin (s + t))) (C : ClosedFragment) :
    (pairClose F ((H.disjUnion C).relabel
        (pcTensorClose s t))).Equiv
      (((pairClose F H).disjUnion C).relabel
        (unionLabel s t)) := by
  let σU := unionPeel s t
  let qsU := unionQs s t
  have wfqsU : Fragment.PairsWF qsU :=
    Fragment.mapPairs_wf σU.symm _ (interfacePairs_wf 0 (s + t) 0)
  let aES := (_root_.Equiv.sumAssoc (Fin (s + t)) (Fin (s + t))
    (Fin (0 + 0))).symm
  let ps₃ := Fragment.inlPairs (β := Fin (0 + 0))
    (innerClosePairs s t)
  have wfps₃ : Fragment.PairsWF ps₃ :=
    Fragment.inlPairs_wf _ (innerClosePairs_wf s t)
  let AmbS := F.disjUnion (H.disjUnion C)
  let AmbT := (F.disjUnion H).disjUnion C
  -- M5: the inner closure identified, inside the union.
  have M5 : ((( Fragment.glueList (F.disjUnion H)
      (innerClosePairs s t)
      (innerClosePairs_wf s t)).disjUnion C).relabel
      (Fragment.inlFoldEquiv (β := Fin (0 + 0))
        (innerClosePairs s t)).symm).Equiv
      ((((pairClose F H).disjUnion C).relabel
        (_root_.Equiv.sumCongr (innerLabel s t).symm
          (_root_.Equiv.refl (Fin (0 + 0))))).relabel
        (Fragment.inlFoldEquiv (β := Fin (0 + 0))
          (innerClosePairs s t)).symm) :=
    Fragment.Equiv.relabelCongr
      ((Fragment.Equiv.disjUnionCongr
        (Fragment.Equiv.relabelFlip (innerNormal F H))
        (Fragment.Equiv.refl C)).trans
      (Fragment.relabelDisjUnionLeft (pairClose F H) C
        (innerLabel s t).symm))
      (Fragment.inlFoldEquiv (β := Fin (0 + 0))
        (innerClosePairs s t)).symm
  -- M4: localize the inner pairs to the F, H summands.
  have M4 : (Fragment.glueList AmbT ps₃ wfps₃).Equiv
      ((((pairClose F H).disjUnion C).relabel
        (_root_.Equiv.sumCongr (innerLabel s t).symm
          (_root_.Equiv.refl (Fin (0 + 0))))).relabel
        (Fragment.inlFoldEquiv (β := Fin (0 + 0))
          (innerClosePairs s t)).symm) :=
    (Fragment.glueListDisjUnionLeft (F.disjUnion H) C
      (innerClosePairs s t) (innerClosePairs_wf s t)).trans M5
  -- M3: the association relabelling stage.
  have M3 := (Fragment.glueListRelabel AmbT aES.symm ps₃
      wfps₃).trans
    ((Fragment.Equiv.relabelCongr M4
      (Fragment.foldSurvivingMapEquiv aES.symm ps₃)).trans
    ((Fragment.Equiv.relabelTrans _ _ _).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
  -- M2b: bridge the peeled pairs to the associated pairs.
  have M2b := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (AmbT.relabel aES.symm)
        (union_ground s t)
        wfqsU (Fragment.mapPairs_wf aES.symm _ wfps₃)
        ((union_ground s t) ▸ List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr M3
      (Fragment.foldSurvivingPermEquiv
        ((union_ground s t) ▸ List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- MA: the association of the ambient.
  have MA := (Fragment.glueListCongr
    (Fragment.Equiv.relabelFlip
      (Fragment.disjUnionAssoc F H C)) qsU wfqsU).trans M2b
  -- M2: the peel relabelling stage.
  have M2 := (Fragment.glueListRelabel AmbS σU qsU wfqsU).trans
    ((Fragment.Equiv.relabelCongr MA
      (Fragment.foldSurvivingMapEquiv σU qsU)).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- M1: bridge the closure pairs.
  have M1 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (AmbS.relabel σU)
        (mapPairs_symm_cancel σU
          (interfacePairs 0 (s + t) 0)).symm
        (interfacePairs_wf 0 (s + t) 0)
        (Fragment.mapPairs_wf σU _ wfqsU)
        ((mapPairs_symm_cancel σU
          (interfacePairs 0 (s + t) 0)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr M2
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel σU
          (interfacePairs 0 (s + t) 0)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- E1: peel the closure casts.
  have E1 : ((F.relabel
      (finCongr (by omega : s + t = 0 + (s + t)))).disjUnion
        (((H.disjUnion C).relabel
          (pcTensorClose s t)).relabel
          (finCongr (by omega : s + t = (s + t) + 0)))).Equiv
      (AmbS.relabel σU) :=
    (Fragment.Equiv.disjUnionCongr (Fragment.Equiv.refl _)
      (Fragment.Equiv.relabelTrans (H.disjUnion C)
        (pcTensorClose s t)
        (finCongr (by omega : s + t = (s + t) + 0)))).trans
    ((Fragment.relabelDisjUnionLeft F _
      (finCongr (by omega : s + t = 0 + (s + t)))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.relabelDisjUnionRight F (H.disjUnion C)
        ((pcTensorClose s t).trans
          (finCongr (by omega : s + t = (s + t) + 0))))
      (_root_.Equiv.sumCongr
        (finCongr (by omega : s + t = 0 + (s + t)))
        (_root_.Equiv.refl _))).trans
    ((Fragment.Equiv.relabelTrans _ _ _).trans
    (Fragment.Equiv.relabelEq _
      (_root_.Equiv.ext (fun x => by cases x <;> rfl))))))
  -- C1: transport the closure gluing across E1.
  have C1 := (Fragment.glueListCongr E1
    (interfacePairs 0 (s + t) 0)
    (interfacePairs_wf 0 (s + t) 0)).trans M1
  -- Assemble.
  exact (composeNormal
      (F.relabel (finCongr (by omega : s + t = 0 + (s + t))))
      (((H.disjUnion C).relabel (pcTensorClose s t)).relabel
        (finCongr (by omega : s + t = (s + t) + 0)))).trans
    ((Fragment.Equiv.relabelCongr C1
      ((interfaceSurvEquiv 0 (s + t) 0).trans
        finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

/-- **The union closure** (closed components fall out): closing
against a test fragment with a closed attachment is the union of
the closure with the attachment. -/
noncomputable def pairCloseUnionRight {s t : ℕ}
    (F H : Fragment (Fin (s + t))) (C : ClosedFragment) :
    (pairClose F ((H.disjUnion C).relabel
        (pcTensorClose s t))).Equiv
      (ClosedFragment.union (pairClose F H) C) :=
  (unionNormal F H C).trans
    (Fragment.Equiv.relabelEq _
      (_root_.Equiv.ext (fun x => by
        rcases x with x0 | x0 <;>
          exact absurd x0.isLt (by omega))))

/-- **Trace multiplicativity** (accompanying paper, Lemma 3.5(b)):
the trace of a tensor is the product of the traces. -/
theorem fragTrace_tensor {R : ℕ} (f : EdgeRankParameter R)
    {a b : ℕ} (F₁ : Fragment (Fin (a + a)))
    (F₂ : Fragment (Fin (b + b))) :
    fragTrace f.val (tensorFragment F₁ F₂) =
      fragTrace f.val F₁ * fragTrace f.val F₂ := by
  have E : (pairClose (tensorFragment F₁ F₂)
      (strandBundle (a + b))).Equiv
      (ClosedFragment.union (pairClose F₁ (strandBundle a))
        (pairClose F₂ (strandBundle b))) :=
    (pairCloseCongr (Fragment.Equiv.refl _)
      (strandBundleTensor a b)).trans
    ((pairCloseTensorAbsorb F₁ F₂
      (tensorFragment (strandBundle a) (strandBundle b))).trans
    ((pairCloseCongr (Fragment.Equiv.refl F₁)
      (partialCloseTensor F₂ (strandBundle a)
        (strandBundle b))).trans
    (pairCloseUnionRight F₁ (strandBundle a)
      (pairClose F₂ (strandBundle b)))))
  show f.val (pairClose (tensorFragment F₁ F₂)
    (strandBundle (a + b))) = _
  rw [f.iso_invariant _ _ E, EdgeRankParameter.val_union]
  rfl

end RS
