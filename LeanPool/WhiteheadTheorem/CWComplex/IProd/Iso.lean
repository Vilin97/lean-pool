/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/

import LeanPool.WhiteheadTheorem.CWComplex.IProd.Def
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
This file verifies that the pair `(X.IProd.sk 0, X.IProd)` is homeomorphic to
`({0, 1} × X, I × X)`, where `X.IProd` is the relative CW-complex constructed in
`CWComplex/IProd/Def.lean`, `X.IProd.sk 0` is its $(-1)$-skeleton,
and `I` is the unit interval.
-/


open CategoryTheory unitInterval TopCat


universe u

variable (X : CWComplex.{u})



namespace CWComplex.IProd

lemma inl_l_r_eq_relCWComplex_skInclSucc_zero :
    Limits.pushout.inl (l X 0) (r X 0) = RelCWComplex.skInclSucc X.IProd 0 := by
  haveI : IsEmpty (X.IProd.attachCells 0).cells := PEmpty.instIsEmpty
  change _ = Limits.pushout.inl .. ≫
    ((IProd.skZeroIsoSkOne X).symm.trans <| asIso <| Limits.pushout.inl
        (Limits.Sigma.desc fun a ↦ isEmptyElim a)
        (Limits.Sigma.map fun _ ↦ diskBoundaryIncl 0) ).inv
  simp only [Nat.reduceAdd, Iso.trans_inv, asIso_inv, Iso.symm_inv, IsIso.hom_inv_id_assoc]
  rfl

lemma skInclSucc_eq_relCWComplex_skInclSucc (n : ℕ) :
    IProd.skInclSucc X n = RelCWComplex.skInclSucc X.IProd (n + 1) := by
  unfold IProd.skInclSucc RelCWComplex.skInclSucc RelCWComplex.AttachCells.incl
  simp only [TopCat.hom_comp]
  change _ = Limits.pushout.inl .. ≫ (IProd.pushoutSkSk X n).isoPushout.inv
  rw [IsPushout.inl_isoPushout_inv]
  apply Limits.pushout.hom_ext
  · simp only [Limits.pushout.inl_desc]
    exact (IProd.inl_skInclSucc X).symm
  · simp only [Limits.pushout.inr_desc]
    exact (IProd.inr_skInclSucc X).symm

/-- Two maps from `X.IProd.sk 0 = TopCat.of (zeroOne × X.toTopCat)`
to `X.IProd.sk (n + 1)` are equal. -/
lemma skInclSucc_map_zero_le (n : ℕ) :
    (Functor.ofSequence X.IProd.skInclSucc).map (homOfLE (by omega : 0 ≤ n + 1)) =
      Limits.pushout.inl (l X n) (r X n) :=
  match n with
  | 0 => by
      change RelCWComplex.skInclSucc X.IProd 0 = _
      rw [← inl_l_r_eq_relCWComplex_skInclSucc_zero]
  | n + 1 => by
      have : (Functor.ofSequence X.IProd.skInclSucc).map (homOfLE (by omega : 0 ≤ n + 1 + 1)) = _ :=
        (Functor.ofSequence X.IProd.skInclSucc).map_comp
          (homOfLE (by omega : 0 ≤ n + 1)) (homOfLE (by omega : n + 1 ≤ n + 1 + 1))
      rw [this, Functor.ofSequence_map_homOfLE_succ, skInclSucc_map_zero_le n]
      rw [← IProd.inl_skInclSucc X, skInclSucc_eq_relCWComplex_skInclSucc]
      rfl


namespace colimitCocone

variable (Z : Limits.Cocone (Functor.ofSequence X.IProd.skInclSucc))
variable (n : ℕ)

/-- `r'` -/
noncomputable abbrev r' : TopCat.of (I × X.sk n) ⟶ of (I × X.toTopCat) :=
  ofHom <| (ContinuousMap.id I).prodMap (X.skIncl n).hom

lemma w' : l X n ≫ zeroOneProdInclIProd X = r X n ≫ r' X n := by
  ext ⟨t, x⟩
  all_goals simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply,
    ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq, ContinuousMap.coe_mk]

/-- `incl` -/
noncomputable def incl : X.IProd.sk n ⟶ of (I × X.toTopCat) :=
  match n with
  | 0 => zeroOneProdInclIProd X
  | n + 1 => Limits.pushout.desc (zeroOneProdInclIProd X) (r' X n) (w' X n)

lemma naturality : X.IProd.skInclSucc n ≫ incl X (n + 1) = incl X n :=
  match n with
  | 0 => by
      change _ = X.zeroOneProdInclIProd
      rw [← inl_l_r_eq_relCWComplex_skInclSucc_zero, incl]
      exact Limits.pushout.inl_desc _ _ _
  | n + 1 => by
      rw [← skInclSucc_eq_relCWComplex_skInclSucc]
      change IProd.skInclSucc X n ≫ _ = _
      simp only [incl]
      apply Limits.pushout.hom_ext
      · have hinl := IProd.inl_skInclSucc_assoc (X := X) (n := n)
          (Limits.pushout.desc X.zeroOneProdInclIProd (r' X (n + 1)) (w' X (n + 1)))
        refine hinl.trans ?_
        rw [show (Limits.pushout.inl (l X n) (r X n) ≫
            Limits.pushout.desc X.zeroOneProdInclIProd (r' X n) (w' X n) :
              of (↑zeroOne × ↑X.toTopCat) ⟶ of (↑I × ↑X.toTopCat))
              = X.zeroOneProdInclIProd from Limits.pushout.inl_desc _ _ _]
        exact Limits.pushout.inl_desc _ _ _
      · have hinr := IProd.inr_skInclSucc_assoc (X := X) (n := n)
          (Limits.pushout.desc X.zeroOneProdInclIProd (r' X (n + 1)) (w' X (n + 1)))
        refine hinr.trans ?_
        change ofHom ((ContinuousMap.id (↑I : Set ℝ)).prodMap (Hom.hom (X.skInclSucc n))) ≫
          (Limits.pushout.inr (l X (n + 1)) (r X (n + 1)) ≫
            Limits.pushout.desc X.zeroOneProdInclIProd (r' X (n + 1)) (w' X (n + 1))) = _
        rw [Limits.pushout.inr_desc, Limits.pushout.inr_desc]
        unfold r'
        ext ⟨t, x⟩
        all_goals simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply,
          ContinuousMap.prodMap_apply, ContinuousMap.coe_id, Prod.map_apply, id_eq]
        change (X.skInclSucc n ≫ X.skIncl (n + 1)) _ = (X.skIncl n) _
        rw [X.skInclSucc_skIncl_eq]

/-- The cocone with `X.IProd.sk 0 ⟶ X.IProd.sk 1 ⟶ ⋯` as base
and `TopCat.of (I × X.toTopCat)` as vertex.
This is actually a colimit cocone (see `CWComplex.IProd.colimitCocone`). -/
noncomputable def cocone : Limits.Cocone (Functor.ofSequence X.IProd.skInclSucc) :=
  { pt := TopCat.of (I × X.toTopCat)
    ι := NatTrans.ofSequence (incl X) <| by
      convert naturality X
      simp only [Functor.ofSequence_obj, homOfLE_leOfHom, Functor.ofSequence_map_homOfLE_succ] }

/-- The cocone with `I × X.sk 0 ⟶ I × X.sk 1 ⟶ ⋯` as base and `Z.pt` as vertex -/
noncomputable def IXZ : Limits.Cocone (Functor.ofSequence X.skInclSucc ⋙ topBinProdLeft' I) :=
  { pt := Z.pt
    ι := NatTrans.ofSequence
      (fun n ↦ Limits.pushout.inr (l X n) (r X n) ≫ Z.ι.app (n + 1)) <| by
        intro n
        simp only [Functor.comp_obj, Functor.ofSequence_obj, Functor.const_obj_obj,
          homOfLE_leOfHom, Functor.comp_map, Functor.ofSequence_map_homOfLE_succ,
          Functor.const_obj_map, Category.comp_id]
        have := Z.ι.naturality (homOfLE (n + 1).le_succ)
        simp only [Functor.ofSequence_obj, Functor.const_obj_obj, homOfLE_leOfHom,
          Functor.ofSequence_map_homOfLE_succ, Functor.const_obj_map, Category.comp_id] at this
        rw [← this, ← skInclSucc_eq_relCWComplex_skInclSucc]
        exact (IProd.inr_skInclSucc_assoc X (Z.ι.app (n + 1 + 1))).symm }

/-- Functor constructed from the sequence of morphisms `I × X.sk 0 ⟶ I × X.sk 1 ⟶ ⋯` -/
noncomputable abbrev IF : ℕ ⥤ TopCat :=
  Functor.ofSequence X.skInclSucc ⋙ topBinProdLeft' I

/-- The cocone with `I × X.sk 0 ⟶ I × X.sk 1 ⟶ ⋯` as base
and `TopCat.of (I × X.toTopCat)` as vertex.
This is actually a colimit cocone (see `IX`). -/
noncomputable def IXCocone : Limits.Cocone (IF X) :=
  (topBinProdLeft' I).mapCocone <| Limits.colimit.cocone <| Functor.ofSequence X.skInclSucc

/-- `I × X` is the colimit of `I × X.sk 0 ⟶ I × X.sk 1 ⟶ ⋯`,
because the left adjoint functor `I × ·` preserves colimtis. -/
lemma isColim_IXCocone : Nonempty <| Limits.IsColimit <| IXCocone X :=
  (Adjunction.leftAdjoint_preservesColimits <| topBinProdLeftAdjExp' <| TopCat.of I)
    |>.preservesColimitsOfShape.preservesColimit.preserves <|
      Limits.colimit.isColimit <| Functor.ofSequence X.skInclSucc

/-- `IXCocone` is a colimit cocone. -/
noncomputable def IX : Limits.ColimitCocone (IF X) :=
  { cocone := IXCocone X
    isColimit := (isColim_IXCocone X).some }

/-- Note: The type is definitionally equal to `(IXCocone X).pt ⟶ Z.pt`. -/
noncomputable def desc : (cocone X).pt ⟶ Z.pt :=
  (IX X).isColimit.desc (IXZ X Z)

lemma zeroOneProdInclIProd_desc : X.zeroOneProdInclIProd ≫ desc X Z = Z.ι.app 0 := by
  ext ⟨t, x⟩
  let iIsk n : X.sk n ⟶ TopCat.of (I × X.sk n) := ofHom ⟨fun x ↦ ⟨zeroOneIncl t, x⟩, by fun_prop⟩
  let i01sk n : X.sk n ⟶ TopCat.of (zeroOne × X.sk n) := ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩
  let iIX : X.toTopCat ⟶ TopCat.of (I × X.toTopCat) :=
    ofHom ⟨fun x ↦ ⟨zeroOneIncl t, x⟩, by fun_prop⟩
  let i01X : X.toTopCat ⟶ TopCat.of (zeroOne × X.toTopCat) := ofHom ⟨fun x ↦ ⟨t, x⟩, by fun_prop⟩
  obtain ht | ht := zeroOne.eq_zero_or_eq_one t
  all_goals
    subst ht
    simp only [TopCat.hom_comp, hom_ofHom, ContinuousMap.comp_apply, ContinuousMap.prodMap_apply,
      ContinuousMap.coe_mk, ContinuousMap.coe_id, Prod.map_apply, id_eq]
    change (iIX ≫ desc X Z) x = (i01X ≫ Z.ι.app 0) x
    congr 2
    -- Goal: prove two maps of type `X.toTopCat ⟶ Z.pt` are equal.
    -- It suffices to show that they agree on each skeleton of `X`.
    apply Limits.colimit.hom_ext
    intro n
    change (X.skIncl n ≫ iIX) ≫ desc X Z = X.skIncl n ≫ i01X ≫ Z.ι.app 0
    have hfac : (X.skIncl n ≫ iIX) ≫ desc X Z =
        iIsk n ≫ Limits.pushout.inr (l X n) (r X n) ≫ Z.ι.app (n + 1) := by
      change (iIsk n ≫ (IX X).cocone.ι.app n) ≫ (IX X).isColimit.desc (IXZ X Z) =
        iIsk n ≫ Limits.pushout.inr (l X n) (r X n) ≫ Z.ι.app (n + 1)
      rw [Category.assoc]
      congr 1
      exact (IX X).isColimit.fac (IXZ X Z) n
    rw [hfac]
    change iIsk n ≫ Limits.pushout.inr (l X n) (r X n) ≫ Z.ι.app (n + 1) = _
    replace := Z.ι.naturality (homOfLE (by omega : 0 ≤ n + 1))
    change _ = Z.ι.app 0 at this
    rw [← this]
    change (_ ≫ _) ≫ Z.ι.app (n + 1) = (_ ≫ _ ≫ _) ≫ Z.ι.app (n + 1)
    congr 1
    rw [skInclSucc_map_zero_le]
    have hiIsk : iIsk n = i01sk n ≫ r X n := rfl
    have hi01X : X.skIncl n ≫ i01X = i01sk n ≫ l X n := rfl
    change (i01sk n ≫ r X n) ≫ Limits.pushout.inr (l X n) (r X n) =
      (i01sk n ≫ l X n) ≫ Limits.pushout.inl (l X n) (r X n)
    rw [Category.assoc, Category.assoc, Limits.pushout.condition]

lemma fac : incl X n ≫ desc X Z = Z.ι.app n :=
  match n with
  | 0 => zeroOneProdInclIProd_desc X Z
  | n + 1 => by
      change Limits.pushout.desc .. ≫ _ = _
      apply Limits.pushout.hom_ext
      · rw [Limits.pushout.inl_desc_assoc, zeroOneProdInclIProd_desc]
        have := Z.ι.naturality (homOfLE (by omega : 0 ≤ n + 1))
        change _ = Z.ι.app 0 at this
        rw [← this, skInclSucc_map_zero_le]
        rfl
      · rw [Limits.pushout.inr_desc_assoc]
        change (IX X).cocone.ι.app n ≫ desc X Z = _
        rw [desc]
        exact (IX X).isColimit.fac (IXZ X Z) n

lemma uniq (d : (cocone X).pt ⟶ Z.pt) (d_fac : ∀ n, (cocone X).ι.app n ≫ d = Z.ι.app n) :
    d = colimitCocone.desc X Z := by
  apply (IX X).isColimit.hom_ext
  intro n
  change (IX X).cocone.ι.app n ≫ d =
    (IX X).cocone.ι.app n ≫ (IX X).isColimit.desc (IXZ X Z)
  rw [(IX X).isColimit.fac (IXZ X Z) n]
  change ofHom ((ContinuousMap.id I).prodMap (X.skIncl n).hom) ≫ d =
    Limits.pushout.inr (l X n) (r X n) ≫ Z.ι.app (n + 1)
  rw [← d_fac (n + 1)]
  change ofHom ((ContinuousMap.id I).prodMap (X.skIncl n).hom) ≫ d =
    (Limits.pushout.inr (l X n) (r X n) ≫ (cocone X).ι.app (n + 1)) ≫ d
  congr 1
  change _ = Limits.pushout.inr (l X n) (r X n) ≫ incl X (n + 1)
  rw [incl, Limits.pushout.inr_desc]

end colimitCocone


/-- The cocone `CWComplex.IProd.colimitCocone.cocone X` is actually a colimit cocone. -/
noncomputable def colimitCocone : Limits.ColimitCocone (Functor.ofSequence X.IProd.skInclSucc) where
  cocone := colimitCocone.cocone X
  isColimit :=
    { desc := colimitCocone.desc X
      fac := colimitCocone.fac X
      uniq := colimitCocone.uniq X }

/-- `iso` -/
noncomputable def iso : X.IProd.toTopCat ≅ TopCat.of (I × X.toTopCat) :=
  Limits.IsColimit.coconePointUniqueUpToIso
    (Limits.getColimitCocone (Functor.ofSequence X.IProd.skInclSucc)).isColimit
    (colimitCocone X).isColimit

/-- The arrow `X.IProd.sk 0 ⟶ X.IProd.toTopCat` is isomorphic to `{0, 1} × X ⟶ I × X`. -/
noncomputable def arrowIso : Arrow.mk (X.IProd.skIncl 0) ≅ Arrow.mk X.zeroOneProdInclIProd :=
  Arrow.isoMk (Iso.refl _) (IProd.iso X) <| by
    simp only [Arrow.mk_left, Arrow.mk_right, Iso.refl_hom, Arrow.mk_hom]
    rw [show X.IProd.skIncl 0 = (Limits.getColimitCocone
          (Functor.ofSequence X.IProd.skInclSucc)).cocone.ι.app 0 by rfl]
    rw [IProd.iso]
    have h := Limits.IsColimit.comp_coconePointUniqueUpToIso_hom
      (Limits.getColimitCocone (Functor.ofSequence X.IProd.skInclSucc)).isColimit
      (colimitCocone X).isColimit 0
    refine Eq.trans ?_ h.symm
    change 𝟙 (X.IProd.sk 0) ≫ X.zeroOneProdInclIProd = (colimitCocone X).cocone.ι.app 0
    rw [Category.id_comp]
    rfl

end CWComplex.IProd

