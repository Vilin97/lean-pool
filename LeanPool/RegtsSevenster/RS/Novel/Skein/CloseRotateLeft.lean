/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Novel.Skein.CloseRotate

/-!
# Mirror rotation of closures

For an `(s,t)`-fragment `W`, a `(t,u)`-fragment `F`, and an
`(s,u)`-fragment `K`,

    (W ∘ F) ∗ K  ≃  F ∗ (Wᵀ ∘ K),

where `Wᵀ` transposes the boundary of `W`.  This is the
left-mirror variant of `pairCloseComposeRotate`.
-/

namespace RS

/-! ### The inner-pair pullback -/

/-- The inner composition interface of the left-rotated
side, pairing W-low with K-low. -/
def wkPairs (s t u : ℕ) :
    List ((Fin (s + t) ⊕ Fin (s + u)) ×
      (Fin (s + t) ⊕ Fin (s + u))) :=
  (List.finRange s).reverse.map (fun j =>
    (Sum.inl ⟨j.val,
       by have := j.isLt; omega⟩,
     Sum.inr ⟨j.val,
       by have := j.isLt; omega⟩))

/-- wkPairs is well-formed. -/
theorem wkPairs_wf (s t u : ℕ) :
    Fragment.PairsWF (wkPairs s t u) := by
  unfold Fragment.PairsWF wkPairs
  rw [List.flatMap_map, List.nodup_flatMap]
  refine ⟨fun k _ => by simp, ?_⟩
  rw [List.pairwise_reverse]
  refine
    (List.nodup_finRange s).pairwise_of_forall_ne ?_
  intro k _ j _ hkj x hxj hxk
  simp only [List.mem_cons, List.not_mem_nil,
    or_false] at hxj hxk
  rcases hxj with rfl | rfl <;>
    rcases hxk with h | h <;>
    (simp only [Sum.inl.injEq, Sum.inr.injEq,
      Fin.mk.injEq, reduceCtorEq] at h <;>
     exact hkj (Fin.ext (by omega)).symm)

/-- The transpose-pullback gives wkPairs
(generalized over the index list). -/
private theorem wk_pullback_aux (s t u : ℕ) :
    ∀ (l : List (Fin s)),
      Fragment.mapPairs
          (_root_.Equiv.sumCongr
            (transposeEquiv s t)
            (_root_.Equiv.refl
              (Fin (s + u)))).symm
          (l.map (fun j =>
            ((Sum.inl ⟨t + j.val,
                by have := j.isLt; omega⟩ :
              Fin (t + s) ⊕ Fin (s + u)),
             Sum.inr ⟨j.val,
               by have := j.isLt; omega⟩))) =
        l.map (fun j =>
          (Sum.inl ⟨j.val,
             by have := j.isLt; omega⟩,
           Sum.inr ⟨j.val,
             by have := j.isLt; omega⟩))
  | [] => rfl
  | j :: l => by
    simp only [List.map_cons,
      Fragment.mapPairs, Prod.map]
    refine congrArg₂ List.cons
      (Prod.ext ?_ rfl)
      (wk_pullback_aux s t u l)
    change Sum.inl
      ((transposeEquiv s t).symm
        ⟨t + j.val, _⟩) = _
    exact congrArg Sum.inl
      (transposeEquiv_symm_high s t
        j.val j.isLt
        (by have := j.isLt; omega)
        (by have := j.isLt; omega))

/-- The transpose-pullback of interfacePairs gives
wkPairs. -/
theorem wk_pullback (s t u : ℕ) :
    Fragment.mapPairs
        (_root_.Equiv.sumCongr
          (transposeEquiv s t)
          (_root_.Equiv.refl
            (Fin (s + u)))).symm
        (interfacePairs t s u) =
      wkPairs s t u :=
  wk_pullback_aux s t u
    (List.finRange s).reverse

/-! ### The bridge equiv and ground lemma -/

/-- The ambient bridge for the left rotation:
`F ⊔ (W ⊔ K) ≃ (W ⊔ F) ⊔ K`. -/
noncomputable def leftRotBridge (s t u : ℕ) :
    (Fin (t + u) ⊕
      (Fin (s + t) ⊕ Fin (s + u))) ≃
      ((Fin (s + t) ⊕ Fin (t + u)) ⊕
        Fin (s + u)) :=
  (_root_.Equiv.sumAssoc (Fin (t + u))
    (Fin (s + t)) (Fin (s + u))).symm.trans
    (_root_.Equiv.sumCongr
      (_root_.Equiv.sumComm (Fin (t + u))
        (Fin (s + t)))
      (_root_.Equiv.refl (Fin (s + u))))

/-- The bridge-pullback of embedded wkPairs is
mBlock (generalized over the index list). -/
private theorem leftRot_ground_aux
    (s t u : ℕ) :
    ∀ (l : List (Fin s)),
      Fragment.mapPairs
        ((leftRotBridge s t u).symm).symm
        ((l.map (fun j =>
          ((Sum.inl ⟨j.val,
              by have := j.isLt; omega⟩ :
            Fin (s + t) ⊕ Fin (s + u)),
           Sum.inr ⟨j.val,
             by have := j.isLt; omega⟩))).map
          (Prod.map Sum.inr Sum.inr)) =
      l.map (fun j =>
        (Sum.inl (Sum.inl ⟨j.val,
           by have := j.isLt; omega⟩),
         Sum.inr ⟨j.val,
           by have := j.isLt; omega⟩))
  | [] => rfl
  | j :: l => by
    simp only [List.map_cons,
      Fragment.mapPairs, Prod.map]
    exact congrArg₂ List.cons rfl
      (leftRot_ground_aux s t u l)

/-- The bridge-pullback of embedded wkPairs is
mBlock. -/
theorem leftRot_ground (s t u : ℕ) :
    Fragment.mapPairs
        ((leftRotBridge s t u).symm).symm
        (Fragment.inrPairs
          (α := Fin (t + u))
          (wkPairs s t u)) =
      mBlock s t u :=
  leftRot_ground_aux s t u
    (List.finRange s).reverse

/-! ### The transport composites -/

/-- The inner transport: from `wkPairs` survivors to the
boundary of the rotated composition (no swap needed). -/
noncomputable def leftRotM2 (s t u : ℕ) :
    Fragment.FoldSurviving
        (Fin (s + t) ⊕ Fin (s + u))
        (wkPairs s t u) ≃
      Fragment.FoldSurviving
        (Fin (t + s) ⊕ Fin (s + u))
        (interfacePairs t s u) :=
  (Fragment.foldSurvivingPermEquiv
    (show (Fragment.mapPairs
        (_root_.Equiv.sumCongr
          (transposeEquiv s t)
          (_root_.Equiv.refl
            (Fin (s + u)))).symm
        (interfacePairs t s u)).Perm
          (wkPairs s t u)
      from (wk_pullback s t u) ▸
        List.Perm.refl _)).symm.trans
  ((Fragment.foldSurvivingMapEquiv
      (_root_.Equiv.sumCongr
        (transposeEquiv s t)
        (_root_.Equiv.refl (Fin (s + u))))
      (Fragment.mapPairs
        (_root_.Equiv.sumCongr
          (transposeEquiv s t)
          (_root_.Equiv.refl
            (Fin (s + u)))).symm
        (interfacePairs t s u))).trans
    (Fragment.foldSurvivingPermEquiv
      (show (interfacePairs t s u).Perm
          (Fragment.mapPairs
            (_root_.Equiv.sumCongr
              (transposeEquiv s t)
              (_root_.Equiv.refl
                (Fin (s + u))))
            (Fragment.mapPairs
              (_root_.Equiv.sumCongr
                (transposeEquiv s t)
                (_root_.Equiv.refl
                  (Fin (s + u)))).symm
              (interfacePairs t s u)))
        from (mapPairs_symm_cancel
          (_root_.Equiv.sumCongr
            (transposeEquiv s t)
            (_root_.Equiv.refl
              (Fin (s + u))))
          (interfacePairs t s u)).symm ▸
          List.Perm.refl _)).symm)

/-- The outer bridge transport: from `mBlock` survivors
to the embedded `wkPairs` fold survivors. -/
noncomputable def leftRotMR (s t u : ℕ) :
    Fragment.FoldSurviving
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕
          Fin (s + u))
        (mBlock s t u) ≃
      Fragment.FoldSurviving
        (Fin (t + u) ⊕
          (Fin (s + t) ⊕ Fin (s + u)))
        (Fragment.inrPairs
          (α := Fin (t + u))
          (wkPairs s t u)) :=
  (Fragment.foldSurvivingPermEquiv
    ((leftRot_ground s t u) ▸
      List.Perm.refl _)).symm.trans
  ((Fragment.foldSurvivingMapEquiv
      (leftRotBridge s t u).symm
      (Fragment.mapPairs
        ((leftRotBridge s t u).symm).symm
        (Fragment.inrPairs
          (α := Fin (t + u))
          (wkPairs s t u)))).trans
    (Fragment.foldSurvivingPermEquiv
      ((mapPairs_symm_cancel
        (leftRotBridge s t u).symm
        (Fragment.inrPairs
          (α := Fin (t + u))
          (wkPairs s t u))).symm ▸
        List.Perm.refl _)).symm)

/-- The composed transport of the right side's closure
pairs. -/
noncomputable def leftRotE (s t u : ℕ) :
    (Fin (0 + (t + u)) ⊕ Fin (t + u + 0)) ≃
      Fragment.FoldSurviving
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕
          Fin (s + u))
        (mBlock s t u) :=
  (rotSigma t u s).symm.trans
    ((_root_.Equiv.sumCongr
        (_root_.Equiv.refl (Fin (t + u)))
        (leftRotM2 s t u)).symm.trans
      ((Fragment.inrFoldEquiv
          (α := Fin (t + u))
          (wkPairs s t u)).symm.trans
        (leftRotMR s t u).symm))

/-! ### Lifting the closure halves -/

/-- The high closure half lifts to the `p`-block. -/
private theorem leftRot_lift_pblock_aux
    (s t u : ℕ)
    (ps₀ : List
      (((Fin (s + t) ⊕ Fin (t + u)) ⊕
          Fin (s + u)) ×
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕
          Fin (s + u))))
    (E : (Fin (0 + (t + u)) ⊕ Fin (t + u + 0)) ≃
      Fragment.FoldSurviving
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕
          Fin (s + u)) ps₀)
    (hE1 : ∀ (ℓ : ℕ) (_ : ℓ < u)
      (h1 : t + ℓ < 0 + (t + u))
      (h2 : t + ℓ < t + u),
      (E (Sum.inl ⟨t + ℓ, h1⟩)).val =
        Sum.inl (Sum.inr ⟨t + ℓ, h2⟩))
    (hE2 : ∀ (ℓ : ℕ) (_ : ℓ < u)
      (h1 : t + ℓ < t + u + 0)
      (h2 : s + ℓ < s + u),
      (E (Sum.inr ⟨t + ℓ, h1⟩)).val =
        Sum.inr ⟨s + ℓ, h2⟩) :
    ∀ (l : List (Fin u))
      (hsep : Fragment.PairsSepAll ps₀
        (l.map (fun ℓ =>
          (Sum.inl (Sum.inr
              ⟨t + ℓ.val,
               by have := ℓ.isLt; omega⟩),
           Sum.inr
              ⟨s + ℓ.val,
               by have := ℓ.isLt; omega⟩)))),
      Fragment.mapPairs E
          (l.map (fun ℓ =>
            ((Sum.inl ⟨t + ℓ.val,
                by have := ℓ.isLt; omega⟩ :
              Fin (0 + (t + u)) ⊕
                Fin (t + u + 0)),
             Sum.inr ⟨t + ℓ.val,
               by have := ℓ.isLt; omega⟩))) =
        Fragment.liftPairs _ _ hsep
  | [], _ => rfl
  | ℓ :: l, hsep => by
    simp only [List.map_cons,
      Fragment.mapPairs,
      Fragment.liftPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (leftRot_lift_pblock_aux s t u ps₀ E
        hE1 hE2 l _)
    · exact Subtype.ext (hE1 ℓ.val ℓ.isLt
        (by omega) (by omega))
    · exact Subtype.ext (hE2 ℓ.val ℓ.isLt
        (by omega) (by omega))

/-- The low closure half lifts to `nBlock.map swap`. -/
private theorem leftRot_lift_nswap_aux
    (s t u : ℕ)
    (ps₀ : List
      (((Fin (s + t) ⊕ Fin (t + u)) ⊕
          Fin (s + u)) ×
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕
          Fin (s + u))))
    (E : (Fin (0 + (t + u)) ⊕ Fin (t + u + 0)) ≃
      Fragment.FoldSurviving
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕
          Fin (s + u)) ps₀)
    (hE1 : ∀ (j : ℕ) (_ : j < t)
      (h1 : j < 0 + (t + u))
      (h2 : j < t + u),
      (E (Sum.inl ⟨j, h1⟩)).val =
        Sum.inl (Sum.inr ⟨j, h2⟩))
    (hE2 : ∀ (j : ℕ) (_ : j < t)
      (h1 : j < t + u + 0)
      (h2 : s + j < s + t),
      (E (Sum.inr ⟨j, h1⟩)).val =
        Sum.inl (Sum.inl ⟨s + j, h2⟩)) :
    ∀ (l : List (Fin t))
      (hsep : Fragment.PairsSepAll ps₀
        (l.map (fun j =>
          (Sum.inl (Sum.inr
              ⟨j.val,
               by have := j.isLt; omega⟩),
           Sum.inl (Sum.inl
              ⟨s + j.val,
               by have := j.isLt; omega⟩))))),
      Fragment.mapPairs E
          (l.map (fun j =>
            ((Sum.inl ⟨j.val,
                by have := j.isLt; omega⟩ :
              Fin (0 + (t + u)) ⊕
                Fin (t + u + 0)),
             Sum.inr ⟨j.val,
               by have := j.isLt; omega⟩))) =
        Fragment.liftPairs _ _ hsep
  | [], _ => rfl
  | j :: l, hsep => by
    simp only [List.map_cons,
      Fragment.mapPairs,
      Fragment.liftPairs, Prod.map]
    refine congrArg₂ List.cons (Prod.ext ?_ ?_)
      (leftRot_lift_nswap_aux s t u ps₀ E
        hE1 hE2 l _)
    · exact Subtype.ext (hE1 j.val j.isLt
        (by omega) (by omega))
    · exact Subtype.ext (hE2 j.val j.isLt
        (by omega) (by omega))

/-- The `nBlock.map Prod.swap` block list. -/
abbrev nBlockSwap (s t u : ℕ) :=
  (nBlock s t u).map Prod.swap

/-- Membership in `nBlockSwap`. -/
theorem mem_nBlockSwap (s t u : ℕ) (q) :
    q ∈ nBlockSwap s t u ↔
      ∃ j : Fin t,
        q = (Sum.inl (Sum.inr ⟨j.val,
              by have := j.isLt; omega⟩),
             Sum.inl (Sum.inl ⟨s + j.val,
              by have := j.isLt; omega⟩)) := by
  simp only [nBlockSwap, List.mem_map]
  constructor
  · rintro ⟨x, hmem, rfl⟩
    obtain ⟨j, rfl⟩ :=
      (mem_nBlock s t u _).mp hmem
    exact ⟨j, rfl⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_,
      (mem_nBlock s t u _).mpr ⟨j, rfl⟩, rfl⟩

/-- `nBlockSwap` is the map of the nBlock swap. -/
private theorem nBlockSwap_unfold (s t u : ℕ) :
    nBlockSwap s t u =
      (List.finRange t).reverse.map (fun j =>
        ((Sum.inl (Sum.inr ⟨j.val,
            by have := j.isLt; omega⟩) :
          (Fin (s + t) ⊕ Fin (t + u)) ⊕
            Fin (s + u)),
         Sum.inl (Sum.inl ⟨s + j.val,
           by have := j.isLt; omega⟩))) := by
  unfold nBlockSwap nBlock
  rw [List.map_map]
  rfl

/-- The right-side block list for the left rotation. -/
abbrev leftRotPairsR (s t u : ℕ) :=
  mBlock s t u ++
    (pBlock s t u ++ nBlockSwap s t u)

/-- Well-formedness of `leftRotPairsR`. -/
theorem leftRotPairsR_wf (s t u : ℕ) :
    Fragment.PairsWF (leftRotPairsR s t u) := by
  unfold Fragment.PairsWF leftRotPairsR nBlockSwap
  rw [List.flatMap_append, List.flatMap_append]
  refine List.Nodup.append (mBlock_wf s t u)
    (List.Nodup.append (pBlock_wf s t u)
      (Fragment.swapPairs_wf _
        (nBlock_wf s t u)) ?_) ?_
  · intro x hx hy
    obtain ⟨q₁, hq₁, hx₁⟩ :=
      List.mem_flatMap.mp hx
    obtain ⟨q₂, hq₂, hy₁⟩ :=
      List.mem_flatMap.mp hy
    obtain ⟨l, rfl⟩ :=
      (mem_pBlock s t u _).mp hq₁
    obtain ⟨j, rfl⟩ :=
      (mem_nBlockSwap s t u _).mp hq₂
    have hl := l.isLt; have hj := j.isLt
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hx₁ hy₁
    rcases hx₁ with rfl | rfl <;>
      rcases hy₁ with h | h <;>
      (simp only [Sum.inl.injEq, Sum.inr.injEq,
        Fin.mk.injEq, reduceCtorEq] at h <;>
       omega)
  · intro x hx hy
    obtain ⟨q₁, hq₁, hx₁⟩ :=
      List.mem_flatMap.mp hx
    obtain ⟨i, rfl⟩ :=
      (mem_mBlock s t u _).mp hq₁
    have hi := i.isLt
    simp only [List.mem_cons,
      List.not_mem_nil, or_false] at hx₁
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨q₂, hq₂, hy₁⟩ :=
        List.mem_flatMap.mp hy
      obtain ⟨l, rfl⟩ :=
        (mem_pBlock s t u _).mp hq₂
      have hl := l.isLt
      simp only [List.mem_cons,
        List.not_mem_nil, or_false] at hy₁
      rcases hx₁ with rfl | rfl <;>
        rcases hy₁ with h | h <;>
        (simp only [Sum.inl.injEq, Sum.inr.injEq,
          Fin.mk.injEq, reduceCtorEq] at h <;>
         omega)
    · obtain ⟨q₂, hq₂, hy₁⟩ :=
        List.mem_flatMap.mp hy
      obtain ⟨j, rfl⟩ :=
        (mem_nBlockSwap s t u _).mp hq₂
      have hj := j.isLt
      simp only [List.mem_cons,
        List.not_mem_nil, or_false] at hy₁
      rcases hx₁ with rfl | rfl <;>
        rcases hy₁ with h | h <;>
        (simp only [Sum.inl.injEq,
          Fin.mk.injEq, reduceCtorEq] at h <;>
         omega)

/-- The transported closure pairs are the lifted
right-side blocks. -/
theorem leftRot_pairs_lift (s t u : ℕ) :
    Fragment.mapPairs (leftRotE s t u)
        (interfacePairs 0 (t + u) 0) =
      Fragment.liftPairs _ _
        ((leftRotPairsR_wf s t u
          ).append_sep) := by
  rw [interfacePairs_closure_split t u,
      mapPairs_append,
      liftPairs_append]
  apply congrArg₂ (· ++ ·)
  · exact leftRot_lift_pblock_aux s t u _
      (leftRotE s t u)
      (fun ℓ _ _ _ =>
        congrArg (fun z =>
          ((leftRotBridge s t u).symm
            ).symm z)
          (Fragment.inrFoldEquiv_symm_inl_val
            (wkPairs s t u) _))
      (fun ℓ hℓ h1 h2 =>
        congrArg (fun z =>
          ((leftRotBridge s t u).symm
            ).symm z)
          ((Fragment.inrFoldEquiv_symm_inr_val
            (wkPairs s t u)
            ((leftRotM2 s t u).symm
              (((interfaceSurvEquiv t s u
                  ).trans
                finSumFinEquiv).symm
                ⟨t + ℓ, by omega⟩))).trans
            (congrArg Sum.inr
              (congrArg (fun w =>
                (_root_.Equiv.sumCongr
                  (transposeEquiv s t)
                  (_root_.Equiv.refl
                    (Fin (s + u)))).symm w)
                (interfaceEquiv_symm_high
                  t s u ℓ hℓ
                  (by omega)
                  (by omega))))))
      (List.finRange u).reverse _
  · simp only [nBlockSwap_unfold]
    exact leftRot_lift_nswap_aux s t u _
      (leftRotE s t u)
      (fun j _ _ _ =>
        congrArg (fun z =>
          ((leftRotBridge s t u).symm
            ).symm z)
          (Fragment.inrFoldEquiv_symm_inl_val
            (wkPairs s t u) _))
      (fun j hj h1 h2 =>
        congrArg (fun z =>
          ((leftRotBridge s t u).symm
            ).symm z)
          ((Fragment.inrFoldEquiv_symm_inr_val
            (wkPairs s t u)
            ((leftRotM2 s t u).symm
              (((interfaceSurvEquiv t s u
                  ).trans
                finSumFinEquiv).symm
                ⟨j, by omega⟩))).trans
            (congrArg Sum.inr
              ((congrArg (fun w =>
                (_root_.Equiv.sumCongr
                  (transposeEquiv s t)
                  (_root_.Equiv.refl
                    (Fin (s + u)))).symm w)
                (interfaceEquiv_symm_low
                  t s u j hj
                  (by omega)
                  (by omega))).trans
              (congrArg Sum.inl
                (transposeEquiv_symm_low
                  s t j hj
                  (by omega)
                  (by omega)))))))
      (List.finRange t).reverse _

/-! ### The Q stages -/

/-- The right side's closure pairs, boundary stage. -/
noncomputable def leftRotQ1 (s t u : ℕ) :=
  Fragment.mapPairs (rotSigma t u s).symm
    (interfacePairs 0 (t + u) 0)

/-- The right side's closure pairs, inner stage. -/
noncomputable def leftRotQ2 (s t u : ℕ) :=
  Fragment.mapPairs
    (_root_.Equiv.sumCongr
      (_root_.Equiv.refl (Fin (t + u)))
      (leftRotM2 s t u)).symm
    (leftRotQ1 s t u)

/-- The right side's closure pairs, embedded stage. -/
noncomputable def leftRotQ3 (s t u : ℕ) :=
  Fragment.mapPairs
    (Fragment.inrFoldEquiv
      (α := Fin (t + u))
      (wkPairs s t u)).symm
    (leftRotQ2 s t u)

/-- The right side's closure pairs, ambient stage. -/
noncomputable def leftRotQ4 (s t u : ℕ) :=
  Fragment.mapPairs
    (leftRotMR s t u).symm
    (leftRotQ3 s t u)

/-- The fully transported closure pairs are the lifted
right-side blocks. -/
theorem leftRot_q4_eq (s t u : ℕ) :
    leftRotQ4 s t u =
      Fragment.liftPairs _ _
        ((leftRotPairsR_wf s t u
          ).append_sep) := by
  change Fragment.mapPairs
      (leftRotMR s t u).symm
    (Fragment.mapPairs
      (Fragment.inrFoldEquiv
        (α := Fin (t + u))
        (wkPairs s t u)).symm
      (Fragment.mapPairs
        (_root_.Equiv.sumCongr
          (_root_.Equiv.refl (Fin (t + u)))
          (leftRotM2 s t u)).symm
        (Fragment.mapPairs
          (rotSigma t u s).symm
          (interfacePairs 0 (t + u) 0)))) = _
  rw [mapPairs_mapPairs, mapPairs_mapPairs,
    mapPairs_mapPairs]
  exact leftRot_pairs_lift s t u

/-! ### The label composite -/

/-- The label composite for the left-rotated right
side: peels through every Q-stage and finishes at
the empty surviving type. -/
noncomputable def leftRotLabelR (s t u : ℕ) :
    Fragment.FoldSurviving
        ((Fin (s + t) ⊕ Fin (t + u)) ⊕
          Fin (s + u))
        (mBlock s t u ++
          (pBlock s t u ++
            nBlockSwap s t u)) ≃
      Fin (0 + 0) :=
  ((Fragment.appendFlatten _ _
      ((leftRotPairsR_wf s t u
        ).append_sep)).symm.trans
    ((Fragment.foldSurvivingPermEquiv
        ((leftRot_q4_eq s t u) ▸
          List.Perm.refl _)).symm.trans
      ((Fragment.foldSurvivingMapEquiv
          (leftRotMR s t u)
          (leftRotQ4 s t u)).trans
        ((Fragment.foldSurvivingPermEquiv
            ((mapPairs_symm_cancel
              (leftRotMR s t u)
              (leftRotQ3 s t u)).symm ▸
              List.Perm.refl _
              )).symm.trans
          ((Fragment.foldSurvivingMapEquiv
              (Fragment.inrFoldEquiv
                (α := Fin (t + u))
                (wkPairs s t u))
              (leftRotQ3 s t u)).trans
            ((Fragment.foldSurvivingPermEquiv
                ((mapPairs_symm_cancel
                  (Fragment.inrFoldEquiv
                    (α := Fin (t + u))
                    (wkPairs s t u))
                  (leftRotQ2 s t u)).symm ▸
                  List.Perm.refl _
                  )).symm.trans
              ((Fragment.foldSurvivingMapEquiv
                  (_root_.Equiv.sumCongr
                    (_root_.Equiv.refl
                      (Fin (t + u)))
                    (leftRotM2 s t u))
                  (leftRotQ2 s t u)).trans
                ((Fragment.foldSurvivingPermEquiv
                    ((mapPairs_symm_cancel
                      (_root_.Equiv.sumCongr
                        (_root_.Equiv.refl
                          (Fin (t + u)))
                        (leftRotM2 s t u))
                      (leftRotQ1 s t u)).symm ▸
                      List.Perm.refl _
                      )).symm.trans
                  ((Fragment.foldSurvivingMapEquiv
                      (rotSigma t u s)
                      (leftRotQ1 s t u)).trans
                    ((Fragment.foldSurvivingPermEquiv
                        ((mapPairs_symm_cancel
                          (rotSigma t u s)
                          (interfacePairs 0
                            (t + u) 0)).symm ▸
                          List.Perm.refl _
                          )).symm.trans
                      ((interfaceSurvEquiv 0
                          (t + u) 0).trans
                        finSumFinEquiv
                        )))))))))))

/-! ### The right side, normalized -/

private theorem leftRotQ4_wf (s t u : ℕ) :
    Fragment.PairsWF (leftRotQ4 s t u) :=
  Fragment.mapPairs_wf _ _ (Fragment.mapPairs_wf _ _
    (Fragment.mapPairs_wf _ _ (Fragment.mapPairs_wf _ _ (interfacePairs_wf 0 (t + u) 0))))

/-- **The right side, normalized**: the closure of `F`
against the left-rotated composite is iterated gluing
of the three interface blocks over the common ambient,
`m`-block first. -/
noncomputable def leftRotNormalRight
    {s t u : ℕ}
    (W : Fragment (Fin (s + t)))
    (F : Fragment (Fin (t + u)))
    (K : Fragment (Fin (s + u))) :
    (pairClose F
        ((W.relabel (transposeEquiv s t)).compose
          K)).Equiv
      ((Fragment.glueList
          ((W.disjUnion F).disjUnion K)
          (mBlock s t u ++
            (pBlock s t u ++
              nBlockSwap s t u))
          (leftRotPairsR_wf s t u)).relabel
        (leftRotLabelR s t u)) := by
  -- ═══════ SETUP ═══════
  -- The three intermediate folds (`XWK`, `XR`, `N₂`, `UMB`), the
  -- relabels between them, and their well-formedness certificates.
  let σR := rotSigma t u s
  let M₂ := leftRotM2 s t u
  let MR := leftRotMR s t u
  let i' := Fragment.inrFoldEquiv
    (α := Fin (t + u)) (wkPairs s t u)
  let sτ := _root_.Equiv.sumCongr
    (transposeEquiv s t)
    (_root_.Equiv.refl (Fin (s + u)))
  let wfq1 : Fragment.PairsWF
      (leftRotQ1 s t u) :=
    Fragment.mapPairs_wf σR.symm _
      (interfacePairs_wf 0 (t + u) 0)
  let wfq2 : Fragment.PairsWF
      (leftRotQ2 s t u) :=
    Fragment.mapPairs_wf
      (_root_.Equiv.sumCongr
        (_root_.Equiv.refl (Fin (t + u)))
        M₂).symm _ wfq1
  let wfq3 : Fragment.PairsWF
      (leftRotQ3 s t u) :=
    Fragment.mapPairs_wf i'.symm _ wfq2
  let wfq4 : Fragment.PairsWF
      (leftRotQ4 s t u) :=
    leftRotQ4_wf s t u
  let A := (W.disjUnion F).disjUnion K
  let XWK := Fragment.glueList
    (W.disjUnion K) (wkPairs s t u)
    (wkPairs_wf s t u)
  let XR := Fragment.glueList
    (F.disjUnion (W.disjUnion K))
    (Fragment.inrPairs (α := Fin (t + u))
      (wkPairs s t u))
    (Fragment.inrPairs_wf _
      (wkPairs_wf s t u))
  let N₂ := Fragment.glueList
    ((W.relabel
        (transposeEquiv s t)).disjUnion K)
    (interfacePairs t s u)
    (interfacePairs_wf t s u)
  let UMB := Fragment.glueList A
    (mBlock s t u)
    ((leftRotPairsR_wf s t u).append_left)
  let ground :=
    Fragment.mapPairs
      ((leftRotBridge s t u).symm).symm
      (Fragment.inrPairs (α := Fin (t + u))
        (wkPairs s t u))
  let wfground : Fragment.PairsWF ground :=
    Fragment.mapPairs_wf
      ((leftRotBridge s t u).symm).symm _
      (Fragment.inrPairs_wf _
        (wkPairs_wf s t u))
  -- ═══════ STAGE 1: THE APPEND MERGE AND THE AMBIENT BRIDGE ═══════
  -- `CRapp` merges the appended fold into one glue list; `BE` carries
  -- the ambient `(W ⊔ F) ⊔ K` to `F ⊔ (W ⊔ K)`, which is the shape the
  -- m-fold is stated over; `CRX` transports the fold along it.
  have CRapp :=
    (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv UMB
        (leftRot_q4_eq s t u)
        wfq4
        (Fragment.liftPairs_wf _ _
          ((leftRotPairsR_wf s t u
            ).append_right)
          ((leftRotPairsR_wf s t u
            ).append_sep))
        ((leftRot_q4_eq s t u) ▸
          List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.Equiv.relabelFlip
        (Fragment.glueListAppend A
          (mBlock s t u)
          (pBlock s t u ++
            nBlockSwap s t u)
          (leftRotPairsR_wf s t u)))
      (Fragment.foldSurvivingPermEquiv
        ((leftRot_q4_eq s t u) ▸
          List.Perm.refl _)).symm).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- BE: the ambient bridge.
  have BE :=
    (Fragment.Equiv.disjUnionCongr
      (Fragment.disjUnionComm W F)
      (Fragment.Equiv.refl K)).trans
    ((Fragment.relabelDisjUnionLeft
      (F.disjUnion W) K
      (_root_.Equiv.sumComm
        (Fin (t + u))
        (Fin (s + t)))).trans
    ((Fragment.Equiv.relabelCongr
      (Fragment.disjUnionAssoc F W K)
      (_root_.Equiv.sumCongr
        (_root_.Equiv.sumComm
          (Fin (t + u)) (Fin (s + t)))
        (_root_.Equiv.refl
          (Fin (s + u))))).trans
    (Fragment.Equiv.relabelTrans _ _ _)))
  -- CRX: the ambient bridge on the m-fold.
  have CRX := (Fragment.glueListCongr (Fragment.Equiv.relabelFlip BE) _ _).trans
    (glueListPullRelabelTrans A (leftRotBridge s t u).symm
      (Fragment.inrPairs (α := Fin (t + u)) (wkPairs s t u))
      (Fragment.inrPairs_wf _ (wkPairs_wf s t u))
      (Fragment.Equiv.relabelFlip'
        (Fragment.glueListEqEquiv A (leftRot_ground s t u) wfground
          ((leftRotPairsR_wf s t u).append_left)
          ((leftRot_ground s t u) ▸ List.Perm.refl _))))
  -- CR5: transport across the bridge.
  -- ═══════ STAGE 2: THE EMBEDDED FOLD ═══════
  -- The fold sitting inside `F ⊔ –`: `CR5` transports along the
  -- ambient bridge, `E5` identifies `F ⊔ XWK` with `XR` relabelled,
  -- and `CR3` carries the fold across that identification.
  have CR5 := (Fragment.glueListCongr CRX (leftRotQ3 s t u) wfq3).trans
    (glueListPullRelabelTrans UMB MR (leftRotQ3 s t u) wfq3 CRapp)
  -- E5: the embedded fold.
  have E5 :=
    (Fragment.Equiv.relabelFlip
      (Fragment.glueListDisjUnionRight
        F (W.disjUnion K) (wkPairs s t u)
        (wkPairs_wf s t u))).trans
    (Fragment.Equiv.relabelEq XR
      (_root_.Equiv.symm_symm i'))
  -- CR3: the embedded-fold stage.
  have CR3 := (Fragment.glueListCongr E5 (leftRotQ2 s t u) wfq2).trans
    (glueListPullRelabelTrans XR i' (leftRotQ2 s t u) wfq2 CR5)
  -- E3: the inner fold (no swap needed).
  -- ═══════ STAGE 3: THE TRANSPOSE ON `W ⊔ K` ═══════
  -- `E3` absorbs the `transposeEquiv` on `W` into the fold's own
  -- relabel; `CR2` carries the next block across it.
  have E3 := (Fragment.glueListCongr
    (Fragment.relabelDisjUnionLeft W K (transposeEquiv s t)) _ _).trans
    (glueListPullRelabelTrans (W.disjUnion K) sτ (interfacePairs t s u)
      (interfacePairs_wf t s u)
      (Fragment.Equiv.relabelFlip'
        (Fragment.glueListEqEquiv (W.disjUnion K) (wk_pullback s t u)
          (Fragment.mapPairs_wf sτ.symm _ (interfacePairs_wf t s u))
          (wkPairs_wf s t u) ((wk_pullback s t u) ▸ List.Perm.refl _))))
  -- CR2: the inner-transport stage.
  have CR2 := (Fragment.glueListCongr
    ((Fragment.Equiv.disjUnionCongr (Fragment.Equiv.refl F) E3).trans
      (Fragment.relabelDisjUnionRight F XWK M₂)) (leftRotQ1 s t u) wfq1).trans
    (glueListPullRelabelTrans (F.disjUnion XWK)
      (_root_.Equiv.sumCongr (_root_.Equiv.refl _) M₂)
      (leftRotQ1 s t u) wfq1 CR3)
  -- E1: peel closure casts, normalize composite.
  -- ═══════ STAGE 4: THE CLOSURE'S OWN INTERFACE ═══════
  -- The outermost `pairClose`, whose interface is the single block of
  -- `t + u` labels; `CR1` carries the accumulated fold across it.
  have E1 := pairCloseAmbientEquiv F _ (composeNormal (W.relabel (transposeEquiv s t)) K)
  -- CR1: transport the closure gluing.
  have CR1 := (Fragment.glueListCongr E1
    (interfacePairs 0 (t + u) 0)
    (interfacePairs_wf 0 (t + u) 0)).trans
    (glueListPullRelabelTrans (F.disjUnion N₂) σR
      (interfacePairs 0 (t + u) 0)
      (interfacePairs_wf 0 (t + u) 0) CR2)
  -- Assemble.
  -- ═══════ ASSEMBLY ═══════
  exact (composeNormal
      (F.relabel (finCongr
        (by omega : t + u = 0 + (t + u))))
      (((W.relabel
          (transposeEquiv s t)).compose
        K).relabel (finCongr
          (by omega :
            t + u = t + u + 0)))).trans
    ((Fragment.Equiv.relabelCongr CR1
      ((interfaceSurvEquiv 0
        (t + u) 0).trans
        finSumFinEquiv)).trans
    (Fragment.Equiv.relabelTrans
      _ _ _))

/-! ### Bridge helpers -/

/-- Swapping each pair in a liftPairs list amounts to
lifting the swapped suffix. -/
private theorem liftPairs_map_swap
    {α : Type}
    (ps : List (α × α)) :
    ∀ (qs : List (α × α))
      (h : Fragment.PairsSepAll ps qs)
      (h' : Fragment.PairsSepAll ps
        (qs.map Prod.swap)),
      (Fragment.liftPairs ps qs h).map
          Prod.swap =
        Fragment.liftPairs ps
          (qs.map Prod.swap) h'
  | [], _, _ => rfl
  | _ :: qs, _, _ =>
    congrArg₂ List.cons
      (Prod.ext (Subtype.ext rfl)
        (Subtype.ext rfl))
      (liftPairs_map_swap ps qs _ _)

/-- Permutation from rotatePairsL to the
intermediate form mBlock ++ (pBlock ++ nBlock). -/
private theorem leftRotPairs_perm
    (s t u : ℕ) :
    (nBlock s t u ++
      (pBlock s t u ++
        mBlock s t u)).Perm
    (mBlock s t u ++
      (pBlock s t u ++
        nBlock s t u)) :=
  (List.perm_append_comm_assoc _ _ _).trans
    ((List.Perm.append_left _
        List.perm_append_comm).trans
      (List.perm_append_comm_assoc _ _ _))

/-! ### The meet -/

/-- No label survives the full left-rotation
gluing. -/
theorem leftRot_surv_empty (s t u : ℕ)
    (x : Fragment.FoldSurviving
      ((Fin (s + t) ⊕ Fin (t + u)) ⊕
        Fin (s + u))
      (mBlock s t u ++
        (pBlock s t u ++
          nBlockSwap s t u))) :
    False := by
  obtain ⟨xv, hxp⟩ := x
  rcases xv with (a | g) | b
  · rcases Nat.lt_or_ge a.val s with ha | ha
    · have hmem :
          _ ∈ mBlock s t u ++
            (pBlock s t u ++
              nBlockSwap s t u) :=
        List.mem_append.mpr (Or.inl
          ((mem_mBlock s t u _).mpr
            ⟨⟨a.val, ha⟩, rfl⟩))
      exact (hxp _ hmem).1
        (congrArg (fun z =>
            Sum.inl (Sum.inl z))
          (Fin.ext rfl))
    · have hj : a.val - s < t := by
        have := a.isLt; omega
      have hmem :
          _ ∈ mBlock s t u ++
            (pBlock s t u ++
              nBlockSwap s t u) :=
        List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inr
            ((mem_nBlockSwap s t u _).mpr
              ⟨⟨a.val - s, hj⟩, rfl⟩))))
      exact (hxp _ hmem).2
        (congrArg (fun z =>
            Sum.inl (Sum.inl z))
          (Fin.ext
            (show a.val =
                s + (a.val - s)
              by omega)))
  · rcases Nat.lt_or_ge g.val t with hg | hg
    · have hmem :
          _ ∈ mBlock s t u ++
            (pBlock s t u ++
              nBlockSwap s t u) :=
        List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inr
            ((mem_nBlockSwap s t u _).mpr
              ⟨⟨g.val, hg⟩, rfl⟩))))
      exact (hxp _ hmem).1
        (congrArg (fun z =>
            Sum.inl (Sum.inr z))
          (Fin.ext rfl))
    · have hk : g.val - t < u := by
        have := g.isLt; omega
      have hmem :
          _ ∈ mBlock s t u ++
            (pBlock s t u ++
              nBlockSwap s t u) :=
        List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inl
            ((mem_pBlock s t u _).mpr
              ⟨⟨g.val - t, hk⟩, rfl⟩))))
      exact (hxp _ hmem).1
        (congrArg (fun z =>
            Sum.inl (Sum.inr z))
          (Fin.ext
            (show g.val =
                t + (g.val - t)
              by omega)))
  · rcases Nat.lt_or_ge b.val s with hb | hb
    · have hmem :
          _ ∈ mBlock s t u ++
            (pBlock s t u ++
              nBlockSwap s t u) :=
        List.mem_append.mpr (Or.inl
          ((mem_mBlock s t u _).mpr
            ⟨⟨b.val, hb⟩, rfl⟩))
      exact (hxp _ hmem).2
        (congrArg Sum.inr
          (Fin.ext rfl))
    · have hk : b.val - s < u := by
        have := b.isLt; omega
      have hmem :
          _ ∈ mBlock s t u ++
            (pBlock s t u ++
              nBlockSwap s t u) :=
        List.mem_append.mpr (Or.inr
          (List.mem_append.mpr (Or.inl
            ((mem_pBlock s t u _).mpr
              ⟨⟨b.val - s, hk⟩, rfl⟩))))
      exact (hxp _ hmem).2
        (congrArg Sum.inr
          (Fin.ext
            (show b.val =
                s + (b.val - s)
              by omega)))

/-! ### The final theorem -/

private theorem leftRotPairs_assoc_wf (s t u : ℕ) :
    Fragment.PairsWF ((mBlock s t u ++ pBlock s t u) ++ nBlock s t u) := by
  simpa only [List.append_assoc] using
    (rotatePairsL_wf s t u).perm (leftRotPairs_perm s t u)

/-- **Mirror rotation of closures**: the closure of
a composite equals the closure of the second factor
against the left-rotated composite. -/
noncomputable def pairCloseComposeRotateLeft
    {s t u : ℕ}
    (W : Fragment (Fin (s + t)))
    (F : Fragment (Fin (t + u)))
    (K : Fragment (Fin (s + u))) :
    (pairClose (W.compose F) K).Equiv
      (pairClose F
        ((W.relabel
            (transposeEquiv s t)).compose
          K)) := by
  -- ═══════ SETUP: THE AMBIENT AND THE INTERMEDIATE PAIR LISTS ═══════
  set A := (W.disjUnion F).disjUnion K
  -- nBlock ↔ inlPairs
  have hnb :=
    (congrArg
      (· ++ (pBlock s t u ++ mBlock s t u))
      (nBlock_eq_inlPairs s t u)).symm
  -- Intermediate pair lists
  set mp := mBlock s t u ++ pBlock s t u
  have wf_M :
      Fragment.PairsWF
        (mBlock s t u ++
          (pBlock s t u ++
            nBlock s t u)) :=
    (rotatePairsL_wf s t u).perm
      (leftRotPairs_perm s t u)
  have hassocM :
      mBlock s t u ++
        (pBlock s t u ++ nBlock s t u) =
      mp ++ nBlock s t u :=
    (List.append_assoc _ _ _).symm
  have wf_MA :
      Fragment.PairsWF
        (mp ++ nBlock s t u) :=
    leftRotPairs_assoc_wf s t u
  have hassocR :
      mp ++ nBlockSwap s t u =
      mBlock s t u ++
        (pBlock s t u ++
          nBlockSwap s t u) :=
    List.append_assoc _ _ _
  have wf_RA :
      Fragment.PairsWF
        (mp ++ nBlockSwap s t u) :=
    hassocR ▸ leftRotPairsR_wf s t u
  -- Abbreviate the inner fragment
  set X := Fragment.glueList A mp
    wf_MA.append_left
  -- Suffix swap intermediates
  set lPN := Fragment.liftPairs mp
    (nBlock s t u) wf_MA.append_sep
  set wfPN := Fragment.liftPairs_wf mp
    (nBlock s t u) wf_MA.append_right
    wf_MA.append_sep
  set lPNS := Fragment.liftPairs mp
    (nBlockSwap s t u) wf_RA.append_sep
  set wfPNS := Fragment.liftPairs_wf mp
    (nBlockSwap s t u)
    wf_RA.append_right
    wf_RA.append_sep
  have lPeq :=
    liftPairs_map_swap mp (nBlock s t u)
      wf_MA.append_sep wf_RA.append_sep
  -- ═══════ STAGE 1: THE SUFFIX SWAP, IN SIX STEPS ═══════
  -- h1: GL_M → GL_MA (assoc)
  have h1 :=
    Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv A
        hassocM wf_M wf_MA
        (hassocM ▸ List.Perm.refl _))
  -- h2: GL_MA → GL(X, lPN) (split)
  have h2 :=
    Fragment.glueListAppend A mp
      (nBlock s t u) wf_MA
  -- h3: GL(X, lPN) → GL(X, swap) (swap)
  have h3 :=
    Fragment.Equiv.relabelFlip
      (Fragment.glueListSwap X lPN wfPN)
  -- h4: GL(X, swap) → GL(X, lPNS) (eq)
  have h4 :=
    Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv X lPeq
        (Fragment.swapPairs_wf lPN wfPN)
        wfPNS
        (lPeq ▸ List.Perm.refl _))
  -- h5: GL(X, lPNS) → GL_RA (recombine)
  have h5 :=
    Fragment.Equiv.relabelFlip'
      ((Fragment.glueListAppend A mp
        (nBlockSwap s t u)
        wf_RA).symm)
  -- h6: GL_RA → GL_R (assoc back)
  have h6 :=
    Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv A
        hassocR wf_RA
        (leftRotPairsR_wf s t u)
        (hassocR ▸ List.Perm.refl _))
  -- suffix_swap: GL_M ≡ GL_R.relabel(_)
  have suffix_swap :=
    h1.trans
    ((Fragment.Equiv.relabelCongr
      (h2.trans
      ((Fragment.Equiv.relabelCongr
        (h3.trans
        ((Fragment.Equiv.relabelCongr
          (h4.trans
          ((Fragment.Equiv.relabelCongr
            (h5.trans
            ((Fragment.Equiv.relabelCongr
              h6 _).trans
            (Fragment.Equiv.relabelTrans
              _ _ _)))
           _).trans
          (Fragment.Equiv.relabelTrans
            _ _ _)))
         _).trans
        (Fragment.Equiv.relabelTrans
          _ _ _)))
       _).trans
      (Fragment.Equiv.relabelTrans
        _ _ _)))
     _).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- ═══════ STAGE 2: THE BRIDGE FROM THE LEFT FORM ═══════
  -- BRIDGE: GL_L ≡ GL_R.relabel(_)
  have BRIDGE :=
    (Fragment.Equiv.relabelFlip'
      (Fragment.glueListEqEquiv A hnb
        (lhsCA_wf s t u)
        (rotatePairsL_wf s t u)
        (hnb ▸ List.Perm.refl _))).trans
    ((Fragment.Equiv.relabelCongr
      ((Fragment.glueListPerm A
        (leftRotPairs_perm s t u)
        (rotatePairsL_wf s t u)).trans
      ((Fragment.Equiv.relabelCongr
        suffix_swap _).trans
      (Fragment.Equiv.relabelTrans
        _ _ _)))
     _).trans
    (Fragment.Equiv.relabelTrans _ _ _))
  -- ═══════ ASSEMBLY ═══════
  refine
    (rotateNormalLeft W F K).trans ?_
  refine Fragment.Equiv.trans ?_
    (leftRotNormalRight W F K).symm
  refine
    (Fragment.Equiv.relabelCongr
      BRIDGE
      (rotateLabelL s t u)).trans ?_
  refine
    (Fragment.Equiv.relabelTrans
      _ _ _).trans ?_
  exact Fragment.Equiv.relabelEq _
    (_root_.Equiv.ext (fun x =>
      absurd
        (leftRot_surv_empty s t u x)
        not_false))

end RS
