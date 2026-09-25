/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Novel.Skein.TensorIdeal

/-!
# Partial closure of a tensor

`partialClose z (X' ⊗ z')` glues `z`'s ends onto the `z`-block of
the tensor — which is exactly `z'`'s boundary.  The result is
`X'` sitting untouched next to the full closure of `z` against
`z'`:

`partialClose z (X' ⊗ z') ≃ X' ⊔ pairClose z z'`.

This is the engine of the trace multiplicativity (Lemma 3.5(b)):
with `X' := strandBundle a`, `z' := strandBundle b` and
`strandBundleTensor`, the trace of a tensor splits.

This file: the three-summand shuffle, the ground computation
(the `z`-gluing pairs localize to the `z, z'` summands), and the
inner-pair identification.
-/

@[expose] public section

namespace RS

/-- The three-summand shuffle: pull the middle summand out
front. -/
def sumShuffleEquiv (α β γ : Type) :
    (β ⊕ (α ⊕ γ)) ≃ (α ⊕ (β ⊕ γ)) where
  toFun x :=
    match x with
    | Sum.inl b => Sum.inr (Sum.inl b)
    | Sum.inr (Sum.inl a) => Sum.inl a
    | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c)
  invFun x :=
    match x with
    | Sum.inl a => Sum.inr (Sum.inl a)
    | Sum.inr (Sum.inl b) => Sum.inl b
    | Sum.inr (Sum.inr c) => Sum.inr (Sum.inr c)
  left_inv x := by rcases x with b | (a | c) <;> rfl
  right_inv x := by rcases x with a | (b | c) <;> rfl

/-- The disjoint union shuffles: the middle factor pulls out
front, up to the shuffle relabelling. -/
noncomputable def disjUnionShuffle {α β γ : Type}
    (W₁ : Fragment α) (W₂ : Fragment β) (W₃ : Fragment γ) :
    (W₁.disjUnion (W₂.disjUnion W₃)).Equiv
      ((W₂.disjUnion (W₁.disjUnion W₃)).relabel
        (sumShuffleEquiv α β γ)) where
  flagEquiv := sumShuffleEquiv W₂.Flag W₁.Flag W₃.Flag
  vertexEquiv := sumShuffleEquiv W₂.Vertex W₁.Vertex W₃.Vertex
  attach_comm := fun f => by
    rcases f with f | (f | f)
    · change ((((W₁.attach f).map Sum.inl Sum.inl).map
          Sum.inr Sum.inr).map id (sumShuffleEquiv α β γ)) =
        (((W₁.attach f).map Sum.inl Sum.inl).map
          (sumShuffleEquiv W₂.Vertex W₁.Vertex W₃.Vertex) id)
      rcases W₁.attach f with v | ℓ <;> rfl
    · change (((W₂.attach f).map Sum.inl Sum.inl).map id
          (sumShuffleEquiv α β γ)) =
        ((((W₂.attach f).map Sum.inl Sum.inl).map
          Sum.inr Sum.inr).map
          (sumShuffleEquiv W₂.Vertex W₁.Vertex W₃.Vertex) id)
      rcases W₂.attach f with v | ℓ <;> rfl
    · change ((((W₃.attach f).map Sum.inr Sum.inr).map
          Sum.inr Sum.inr).map id (sumShuffleEquiv α β γ)) =
        ((((W₃.attach f).map Sum.inr Sum.inr).map
          Sum.inr Sum.inr).map
          (sumShuffleEquiv W₂.Vertex W₁.Vertex W₃.Vertex) id)
      rcases W₃.attach f with v | ℓ <;> rfl
  pairing_comm := fun f => by
    rcases f with f | (f | f) <;> rfl
  circles_eq := by
    change W₁.circles + (W₂.circles + W₃.circles) =
      W₂.circles + (W₁.circles + W₃.circles)
    omega

/-! ### The localized inner pairs -/

/-- The closure pairs of `z` against `z'`, over the pair of
`(u + v)`-boundaries: high block, then low block. -/
def innerClosePairs (u v : ℕ) :
    List ((Fin (u + v) ⊕ Fin (u + v)) ×
      (Fin (u + v) ⊕ Fin (u + v))) :=
  (List.finRange v).reverse.map (fun l =>
    (Sum.inl ⟨u + l.val, by have := l.isLt; omega⟩,
     Sum.inr ⟨u + l.val, by have := l.isLt; omega⟩)) ++
  (List.finRange u).reverse.map (fun j =>
    (Sum.inl ⟨j.val, by have := j.isLt; omega⟩,
     Sum.inr ⟨j.val, by have := j.isLt; omega⟩))

/-! ### The ground computation: peeling the interleave -/

private theorem pc_tensor_ground_v_aux (s t u v : ℕ) :
    ∀ (l : List (Fin v)),
      Fragment.mapPairs
          (_root_.Equiv.sumCongr
            (_root_.Equiv.refl (Fin (u + v)))
            (interleaveEquiv s t u v)).symm
          (l.map (fun l' =>
            ((Sum.inl ⟨u + l'.val, by have := l'.isLt; omega⟩ :
              Fin (u + v) ⊕ Fin ((s + u) + (t + v))),
             Sum.inr ⟨(s + u) + (t + l'.val),
               by have := l'.isLt; omega⟩))) =
        l.map (fun l' =>
          (Sum.inl ⟨u + l'.val, by have := l'.isLt; omega⟩,
           Sum.inr (Sum.inr ⟨u + l'.val,
             by have := l'.isLt; omega⟩)))
  | [] => rfl
  | l' :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (pc_tensor_ground_v_aux s t u v l)
    change Sum.inr ((interleaveEquiv s t u v).symm
      ⟨(s + u) + (t + l'.val), by have := l'.isLt; omega⟩) = _
    refine congrArg Sum.inr ?_
    rw [show (⟨(s + u) + (t + l'.val),
        by have := l'.isLt; omega⟩ :
          Fin ((s + u) + (t + v))) =
        Fin.natAdd (s + u) (Fin.natAdd t l') from Fin.ext rfl,
      interleaveEquiv_symm_high_right]
    exact congrArg Sum.inr (Fin.ext rfl)

private theorem pc_tensor_ground_u_aux (s t u v : ℕ) :
    ∀ (l : List (Fin u)),
      Fragment.mapPairs
          (_root_.Equiv.sumCongr
            (_root_.Equiv.refl (Fin (u + v)))
            (interleaveEquiv s t u v)).symm
          (l.map (fun j =>
            ((Sum.inl ⟨j.val, by have := j.isLt; omega⟩ :
              Fin (u + v) ⊕ Fin ((s + u) + (t + v))),
             Sum.inr ⟨s + j.val, by have := j.isLt; omega⟩))) =
        l.map (fun j =>
          (Sum.inl ⟨j.val, by have := j.isLt; omega⟩,
           Sum.inr (Sum.inr ⟨j.val, by have := j.isLt; omega⟩)))
  | [] => rfl
  | j :: l => by
    simp only [List.map_cons, Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext rfl ?_)
      (pc_tensor_ground_u_aux s t u v l)
    change Sum.inr ((interleaveEquiv s t u v).symm
      ⟨s + j.val, by have := j.isLt; omega⟩) = _
    refine congrArg Sum.inr ?_
    rw [show (⟨s + j.val, by have := j.isLt; omega⟩ :
          Fin ((s + u) + (t + v))) =
        Fin.castAdd (t + v) (Fin.natAdd s j) from Fin.ext rfl,
      interleaveEquiv_symm_low_right]
    exact congrArg Sum.inr (Fin.ext rfl)

/-- Peeling the interleave from the `z`-gluing pairs localizes
them to the `z, z'` summands. -/
theorem pc_tensor_ground (s t u v : ℕ) :
    Fragment.mapPairs
        (_root_.Equiv.sumCongr
          (_root_.Equiv.refl (Fin (u + v)))
          (interleaveEquiv s t u v)).symm
        (zClosePairs s t u v) =
      Fragment.mapPairs
        (sumShuffleEquiv (Fin (u + v)) (Fin (s + t))
          (Fin (u + v)))
        (Fragment.inrPairs (α := Fin (s + t))
          (innerClosePairs u v)) := by
  unfold zClosePairs
  rw [mapPairs_append]
  rw [pc_tensor_ground_v_aux s t u v, pc_tensor_ground_u_aux]
  unfold Fragment.mapPairs Fragment.inrPairs innerClosePairs
  simp only [List.map_append, List.map_map]
  rfl

/-! ### The inner closure, normalized -/

/-- The closure label of the inner pair: the two closure casts. -/
noncomputable def innerCloseLabel (u v : ℕ) :
    (Fin (u + v) ⊕ Fin (u + v)) ≃
      (Fin (0 + (u + v)) ⊕ Fin ((u + v) + 0)) :=
  _root_.Equiv.sumCongr
    (finCongr (by omega : u + v = 0 + (u + v)))
    (finCongr (by omega : u + v = (u + v) + 0))

/-- The transported closure pairs of the inner closure are the
inner pairs. -/
theorem inner_ground (u v : ℕ) :
    Fragment.mapPairs (innerCloseLabel u v).symm
        (interfacePairs 0 (u + v) 0) =
      innerClosePairs u v := by
  rw [interfacePairs_closure_split u v]
  unfold Fragment.mapPairs innerClosePairs ipHigh ipLow
  simp only [List.map_append, List.map_map]
  rfl

/-- The inner pairs are well-formed. -/
theorem innerClosePairs_wf (u v : ℕ) :
    Fragment.PairsWF (innerClosePairs u v) :=
  (inner_ground u v) ▸
    Fragment.mapPairs_wf (innerCloseLabel u v).symm _
      (interfacePairs_wf 0 (u + v) 0)

/-- The transported inner closure pairs. -/
noncomputable def innerQs (u v : ℕ) :=
  Fragment.mapPairs (innerCloseLabel u v).symm
    (interfacePairs 0 (u + v) 0)

/-- The composed label identification of the inner closure. -/
noncomputable def innerLabel (u v : ℕ) :
    Fragment.FoldSurviving (Fin (u + v) ⊕ Fin (u + v))
      (innerClosePairs u v) ≃ Fin (0 + 0) :=
  (Fragment.foldSurvivingPermEquiv
      ((inner_ground u v) ▸ List.Perm.refl _)).symm.trans
    ((Fragment.foldSurvivingMapEquiv (innerCloseLabel u v)
        (innerQs u v)).trans
      ((Fragment.foldSurvivingPermEquiv
          ((mapPairs_symm_cancel (innerCloseLabel u v)
            (interfacePairs 0 (u + v) 0)).symm ▸
            List.Perm.refl _)).symm.trans
        ((interfaceSurvEquiv 0 (u + v) 0).trans finSumFinEquiv)))

/-- **The inner closure, normalized**: the closure of `z` against
`z'` is iterated gluing of the inner pairs over `z ⊔ z'`. -/
noncomputable def innerNormal {u v : ℕ}
    (z z' : Fragment (Fin (u + v))) :
    (pairClose z z').Equiv
      ((Fragment.glueList (z.disjUnion z')
          (innerClosePairs u v)
          (innerClosePairs_wf u v)).relabel
        (innerLabel u v)) := by
  let σC := innerCloseLabel u v
  let qs0 := innerQs u v
  have wfqs0 : Fragment.PairsWF qs0 :=
    Fragment.mapPairs_wf σC.symm _ (interfacePairs_wf 0 (u + v) 0)
  let Amb := z.disjUnion z'
  -- C5: bridge the transported pairs to the inner pairs.
  have C5 : (Fragment.glueList Amb qs0 wfqs0).Equiv
      ((Fragment.glueList Amb (innerClosePairs u v)
          (innerClosePairs_wf u v)).relabel
        (Fragment.foldSurvivingPermEquiv
          ((inner_ground u v) ▸ List.Perm.refl _)).symm) :=
    Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv Amb (inner_ground u v)
        wfqs0 (innerClosePairs_wf u v)
        ((inner_ground u v) ▸ List.Perm.refl _))
  -- C3: the fold-survivor relabelling stage.
  have C3 := (Fragment.glueListRelabel Amb σC qs0 wfqs0).trans
    ((Fragment.Equiv.relabelCongr C5
      (Fragment.foldSurvivingMapEquiv σC qs0)).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- C2: bridge the closure pairs.
  have C2 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (Amb.relabel σC)
        (mapPairs_symm_cancel σC
          (interfacePairs 0 (u + v) 0)).symm
        (interfacePairs_wf 0 (u + v) 0)
        (Fragment.mapPairs_wf σC _ wfqs0)
        ((mapPairs_symm_cancel σC
          (interfacePairs 0 (u + v) 0)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr C3
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel σC
          (interfacePairs 0 (u + v) 0)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- E1: peel the closure casts.
  have E1 : ((z.relabel
      (finCongr (by omega : u + v = 0 + (u + v)))).disjUnion
        (z'.relabel
          (finCongr (by omega : u + v = (u + v) + 0)))).Equiv
      (Amb.relabel σC) :=
    (Fragment.relabelDisjUnionLeft z _
      (finCongr (by omega : u + v = 0 + (u + v)))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.relabelDisjUnionRight z z'
        (finCongr (by omega : u + v = (u + v) + 0)))
      (_root_.Equiv.sumCongr
        (finCongr (by omega : u + v = 0 + (u + v)))
        (_root_.Equiv.refl _))).trans
    ((Fragment.Equiv.relabelTrans _ _ _).trans
    (Fragment.Equiv.relabelEq _
      (_root_.Equiv.ext (fun x => by cases x <;> rfl)))))
  -- C1: transport the closure gluing across E1.
  have C1 := (Fragment.glueListCongr E1
    (interfacePairs 0 (u + v) 0)
    (interfacePairs_wf 0 (u + v) 0)).trans C2
  -- Assemble.
  exact (composeNormal
      (z.relabel (finCongr (by omega : u + v = 0 + (u + v))))
      (z'.relabel
        (finCongr (by omega : u + v = (u + v) + 0)))).trans
    ((Fragment.Equiv.relabelCongr C1
      ((interfaceSurvEquiv 0 (u + v) 0).trans
        finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans _ _ _))

/-! ### The main chain -/

/-- The clean label of the partial closure of a tensor. -/
noncomputable def pcTensorClose (s t : ℕ) :
    (Fin (s + t) ⊕ Fin (0 + 0)) ≃ Fin (s + t) :=
  (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
    (finCongr (by omega : 0 + 0 = 0))).trans
    (_root_.Equiv.sumEmpty (Fin (s + t)) (Fin 0))

/-- The interleave peel of the `z`-gluing ambient. -/
noncomputable def pcTensorPeel (s t u v : ℕ) :
    (Fin (u + v) ⊕ (Fin (s + t) ⊕ Fin (u + v))) ≃
      (Fin (u + v) ⊕ Fin ((s + u) + (t + v))) :=
  _root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (u + v)))
    (interleaveEquiv s t u v)

/-- The peeled `z`-gluing pairs. -/
noncomputable def pcTensorQs (s t u v : ℕ) :=
  Fragment.mapPairs (pcTensorPeel s t u v).symm
    (zClosePairs s t u v)

private theorem pcTensorQs_wf (s t u v : ℕ) :
    Fragment.PairsWF (pcTensorQs s t u v) :=
  Fragment.mapPairs_wf (pcTensorPeel s t u v).symm _ (zClosePairs_wf s t u v)

/-- The composed label identification of the partial closure of a
tensor. -/
noncomputable def pcTensorLabel (s t u v : ℕ) :
    (Fin (s + t) ⊕ Fin (0 + 0)) ≃ Fin (s + t) :=
  (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
      (innerLabel u v).symm).trans
    ((Fragment.inrFoldEquiv (α := Fin (s + t))
        (innerClosePairs u v)).symm.trans
      ((Fragment.foldSurvivingMapEquiv
          (sumShuffleEquiv (Fin (u + v)) (Fin (s + t))
            (Fin (u + v)))
          (Fragment.inrPairs (α := Fin (s + t))
            (innerClosePairs u v))).trans
        ((Fragment.foldSurvivingPermEquiv
            ((pc_tensor_ground s t u v) ▸
              List.Perm.refl _)).symm.trans
          ((Fragment.foldSurvivingMapEquiv (pcTensorPeel s t u v)
              (pcTensorQs s t u v)).trans
            ((Fragment.foldSurvivingPermEquiv
                ((mapPairs_symm_cancel (pcTensorPeel s t u v)
                  (zClosePairs s t u v)).symm ▸
                  List.Perm.refl _)).symm.trans
              (pcSurvEquiv s t u v))))))

/-- **The partial closure of a tensor, normalized**: `X'` next to
the inner closure, up to the composed label. -/
noncomputable def pcTensorNormal {s t u v : ℕ}
    (z : Fragment (Fin (u + v))) (X' : Fragment (Fin (s + t)))
    (z' : Fragment (Fin (u + v))) :
    (partialClose z (tensorFragment X' z')).Equiv
      ((X'.disjUnion (pairClose z z')).relabel
        (pcTensorLabel s t u v)) := by
  let eP := pcTensorPeel s t u v
  let qsP := pcTensorQs s t u v
  have wfqsP : Fragment.PairsWF qsP :=
    pcTensorQs_wf s t u v
  let shufE := sumShuffleEquiv (Fin (u + v)) (Fin (s + t))
    (Fin (u + v))
  let ps₂ := Fragment.inrPairs (α := Fin (s + t))
    (innerClosePairs u v)
  have wfps₂ : Fragment.PairsWF ps₂ :=
    Fragment.inrPairs_wf _ (innerClosePairs_wf u v)
  let Zin := Fragment.glueList (z.disjUnion z')
    (innerClosePairs u v) (innerClosePairs_wf u v)
  let AmbP := z.disjUnion (X'.disjUnion z')
  let AmbQ := X'.disjUnion (z.disjUnion z')
  -- M5: the inner closure identified, inside the union.
  have M5 : ((X'.disjUnion Zin).relabel
      (Fragment.inrFoldEquiv (α := Fin (s + t))
        (innerClosePairs u v)).symm).Equiv
      (((X'.disjUnion (pairClose z z')).relabel
        (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
          (innerLabel u v).symm)).relabel
        (Fragment.inrFoldEquiv (α := Fin (s + t))
          (innerClosePairs u v)).symm) :=
    Fragment.Equiv.relabelCongr
      ((Fragment.Equiv.disjUnionCongr (Fragment.Equiv.refl X')
        (Fragment.Equiv.relabelFlip (innerNormal z z'))).trans
      (Fragment.relabelDisjUnionRight X' (pairClose z z')
        (innerLabel u v).symm))
      (Fragment.inrFoldEquiv (α := Fin (s + t))
        (innerClosePairs u v)).symm
  -- M4: localize the inner pairs to the z, z' summands.
  have M4 : (Fragment.glueList AmbQ ps₂ wfps₂).Equiv
      (((X'.disjUnion (pairClose z z')).relabel
        (_root_.Equiv.sumCongr (_root_.Equiv.refl (Fin (s + t)))
          (innerLabel u v).symm)).relabel
        (Fragment.inrFoldEquiv (α := Fin (s + t))
          (innerClosePairs u v)).symm) :=
    (Fragment.glueListDisjUnionRight X' (z.disjUnion z')
      (innerClosePairs u v) (innerClosePairs_wf u v)).trans M5
  -- M3: the shuffle relabelling stage.
  have M3 := (Fragment.glueListRelabel AmbQ shufE ps₂
      wfps₂).trans
    ((Fragment.Equiv.relabelCongr M4
      (Fragment.foldSurvivingMapEquiv shufE ps₂)).trans
    ((Fragment.Equiv.relabelTrans _ _ _).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
  -- M2b: bridge the peeled pairs to the shuffled pairs.
  have M2b := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (AmbQ.relabel shufE)
        (pc_tensor_ground s t u v)
        wfqsP (Fragment.mapPairs_wf shufE _ wfps₂)
        ((pc_tensor_ground s t u v) ▸ List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr M3
      (Fragment.foldSurvivingPermEquiv
        ((pc_tensor_ground s t u v) ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- MA: the shuffle of the ambient.
  have MA := (Fragment.glueListCongr
    (disjUnionShuffle z X' z') qsP wfqsP).trans M2b
  -- M2: the peel relabelling stage.
  have M2 := (Fragment.glueListRelabel AmbP eP qsP wfqsP).trans
    ((Fragment.Equiv.relabelCongr MA
      (Fragment.foldSurvivingMapEquiv eP qsP)).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- M1: bridge the z-gluing pairs.
  have M1 := (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv (AmbP.relabel eP)
        (mapPairs_symm_cancel eP (zClosePairs s t u v)).symm
        (zClosePairs_wf s t u v)
        (Fragment.mapPairs_wf eP _ wfqsP)
        ((mapPairs_symm_cancel eP
          (zClosePairs s t u v)).symm ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr M2
      (Fragment.foldSurvivingPermEquiv
        ((mapPairs_symm_cancel eP
          (zClosePairs s t u v)).symm ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- M0: peel the interleave off the gluing ambient.
  have M0 := (Fragment.glueListCongr
    (Fragment.relabelDisjUnionRight z (X'.disjUnion z')
      (interleaveEquiv s t u v))
    (zClosePairs s t u v) (zClosePairs_wf s t u v)).trans M1
  -- Assemble.
  exact (Fragment.Equiv.relabelCongr M0
    (pcSurvEquiv s t u v)).trans
    (Fragment.Equiv.relabelTrans _ _ _)

/-! ### The label meet -/

/-- The forward survivor identification on low labels. -/
theorem pcSurvEquiv_val_low (s t u v : ℕ)
    (b : Fin ((s + u) + (t + v)))
    (hsurv : ∀ p ∈ zClosePairs s t u v,
      (Sum.inr b : Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.1 ∧
      (Sum.inr b : Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.2)
    (hb : b.val < s) :
    pcSurvEquiv s t u v ⟨Sum.inr b, hsurv⟩ =
      ⟨b.val, by omega⟩ := by
  change (if h : b.val < s then _ else _ : Fin (s + t)) = _
  rw [dite_eq_left hb]

/-- The forward survivor identification on high labels. -/
theorem pcSurvEquiv_val_high (s t u v : ℕ)
    (b : Fin ((s + u) + (t + v)))
    (hsurv : ∀ p ∈ zClosePairs s t u v,
      (Sum.inr b : Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.1 ∧
      (Sum.inr b : Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.2)
    (hb : ¬ b.val < s) (h1 : (s + u) ≤ b.val)
    (h2 : b.val < (s + u) + t) :
    pcSurvEquiv s t u v ⟨Sum.inr b, hsurv⟩ =
      ⟨s + (b.val - (s + u)), by omega⟩ := by
  change (if h : b.val < s then _ else _ : Fin (s + t)) = _
  rw [dite_eq_right hb]

/-- The composed label is the clean label: the live value chase
on the surviving `x`-labels. -/
theorem pcTensorLabel_eq (s t u v : ℕ) :
    pcTensorLabel s t u v = pcTensorClose s t := by
  apply _root_.Equiv.ext
  intro x
  rcases x with x' | f0
  · by_cases hx : x'.val < s
    · have h1 : interleaveEquiv s t u v (Sum.inl x') =
          Fin.castAdd (t + v) (Fin.castAdd u ⟨x'.val, hx⟩) :=
        interleaveEquiv_inl_low s t u v ⟨x'.val, hx⟩
      have hval : (interleaveEquiv s t u v (Sum.inl x')).val =
          x'.val := by rw [h1]; rfl
      have hsurv : ∀ p ∈ zClosePairs s t u v,
          (Sum.inr (interleaveEquiv s t u v (Sum.inl x')) :
            Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.1 ∧
          (Sum.inr (interleaveEquiv s t u v (Sum.inl x')) :
            Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.2 :=
        (forall_ne_iff_not_mem_flat _ _).mpr
          ((pcSurv_iff s t u v _).mpr
            (Or.inl (by rw [hval]; exact hx)))
      change pcSurvEquiv s t u v
        ⟨Sum.inr (interleaveEquiv s t u v (Sum.inl x')),
          hsurv⟩ = _
      rw [pcSurvEquiv_val_low s t u v _ _ (by rw [hval]; exact hx)]
      exact Fin.ext hval
    · have hk : x'.val - s < t := by have := x'.isLt; omega
      have hx2 : x' = Fin.natAdd s ⟨x'.val - s, hk⟩ :=
        Fin.ext (by change x'.val = s + (x'.val - s); omega)
      have h1 : interleaveEquiv s t u v (Sum.inl x') =
          Fin.natAdd (s + u) (Fin.castAdd v ⟨x'.val - s, hk⟩) := by
        conv_lhs => rw [hx2]
        exact interleaveEquiv_inl_high s t u v ⟨x'.val - s, hk⟩
      have hval : (interleaveEquiv s t u v (Sum.inl x')).val =
          (s + u) + (x'.val - s) := by rw [h1]; rfl
      have hsurv : ∀ p ∈ zClosePairs s t u v,
          (Sum.inr (interleaveEquiv s t u v (Sum.inl x')) :
            Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.1 ∧
          (Sum.inr (interleaveEquiv s t u v (Sum.inl x')) :
            Fin (u + v) ⊕ Fin ((s + u) + (t + v))) ≠ p.2 :=
        (forall_ne_iff_not_mem_flat _ _).mpr
          ((pcSurv_iff s t u v _).mpr
            (Or.inr ⟨by rw [hval]; omega,
              by rw [hval]; have := x'.isLt; omega⟩))
      change pcSurvEquiv s t u v
        ⟨Sum.inr (interleaveEquiv s t u v (Sum.inl x')),
          hsurv⟩ = _
      rw [pcSurvEquiv_val_high s t u v _ _
        (by rw [hval]; omega) (by rw [hval]; omega)
        (by rw [hval]; have := x'.isLt; omega)]
      refine Fin.ext ?_
      change s + ((interleaveEquiv s t u v (Sum.inl x')).val -
        (s + u)) = x'.val
      rw [hval]
      omega
  · exact absurd f0.isLt (by omega)

/-- **The partial closure of a tensor**: `X'` unscathed next to
the full closure of `z` against `z'`. -/
noncomputable def partialCloseTensor {s t u v : ℕ}
    (z : Fragment (Fin (u + v))) (X' : Fragment (Fin (s + t)))
    (z' : Fragment (Fin (u + v))) :
    (partialClose z (tensorFragment X' z')).Equiv
      ((X'.disjUnion (pairClose z z')).relabel
        (pcTensorClose s t)) :=
  (pcTensorNormal z X' z').trans
    (Fragment.Equiv.relabelEq _ (pcTensorLabel_eq s t u v))

end RS
