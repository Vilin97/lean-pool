/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.CatTheory.UnitEnd
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaModuleFunctor
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPair
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SandwichRetract
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModMonoidal

/-!
# The comparison map at the regular module

The regular module is the unit of the relative tensor product, and
its realization is the Γ-algebra viewed over itself, that is, the
unit of the tensor product of super modules.  Under those two
identifications the comparison map of Deligne's (2.11.1) is
literally a unitor, so it is an isomorphism whenever one of the two
arguments is the regular module.

The Koszul sign carried by the right unitor of super modules is
exactly the self-braiding of the odd line: pushing a scalar past a
module element on the odd-odd block braids `L` past `L`, which is
`−1`.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

open SuperCommAlgebra.Mod

/-! ## The regular module on the left -/

/-- Pairing against the regular module and collapsing is the
convolution action. -/
theorem gpair_unitLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R]
    (N : Mod D R) {X Y : D} (a : X ⟶ R)
    (m : Y ⟶ N.X) :
    gpair (M := regularMod R) (N := N) a m ≫
        (modTensorUnitLeftMod R N).hom.hom = gact a m := by
  erw [gpair_def, Category.assoc]
  exact whisker_eq _ (modTensorπ_desc R (regularMod R) N _ _)

/-- The reindexed form of `RS.gpair_unitLeft`. -/
theorem gpair_unitLeft'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R]
    (N : Mod D R) {W X Y : D} (s : W ⟶ X ⊗ Y)
    (a : X ⟶ R) (m : Y ⟶ N.X) :
    (s ≫ gpair (M := regularMod R) (N := N) a m) ≫
        (modTensorUnitLeftMod R N).hom.hom = s ≫ gact a m :=
  Eq.trans (Category.assoc _ _ _)
    (whisker_eq _ (gpair_unitLeft R N a m))

/-- **The comparison map at the regular module on the left is the
left unitor.** -/
theorem gammaPairComparison_unitLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (N : Mod D R) :
    gammaPairComparison L R (regularMod R) N ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitLeftMod R N).hom =
      leftUnitorHom (gammaModule D L R N.X) := by
  refine hom_ext (fun a m => ?_) (fun a m => ?_) (fun a m => ?_)
    (fun a m => ?_)
  · have h : (gammaPairComparison L R (regularMod R) N ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitLeftMod R N).hom).evenMap
          (tmulEE _ _ a m) =
        gammaPairEven L R (regularMod R) N (tmulEE _ _ a m) ≫
          (modTensorUnitLeftMod R N).hom.hom := rfl
    erw [h, gammaPairEven_tmulEE, gpairLin_apply]
    refine Eq.trans ?_ (leftUnitorHom_evenMap_tmulEE
      (M := gammaModule D L R N.X) a m).symm
    exact gpair_unitLeft' R N _ a m
  · have h : (gammaPairComparison L R (regularMod R) N ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitLeftMod R N).hom).evenMap
          (tmulOO _ _ a m) =
        gammaPairEven L R (regularMod R) N (tmulOO _ _ a m) ≫
          (modTensorUnitLeftMod R N).hom.hom := rfl
    erw [h, gammaPairEven_tmulOO, gpairLin_apply]
    refine Eq.trans ?_ (leftUnitorHom_evenMap_tmulOO
      (M := gammaModule D L R N.X) a m).symm
    exact gpair_unitLeft' R N _ a m
  · have h : (gammaPairComparison L R (regularMod R) N ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitLeftMod R N).hom).oddMap
          (tmulEO _ _ a m) =
        gammaPairOdd L R (regularMod R) N (tmulEO _ _ a m) ≫
          (modTensorUnitLeftMod R N).hom.hom := rfl
    erw [h, gammaPairOdd_tmulEO, gpairLin_apply]
    refine Eq.trans ?_ (leftUnitorHom_oddMap_tmulEO
      (M := gammaModule D L R N.X) a m).symm
    exact gpair_unitLeft' R N _ a m
  · have h : (gammaPairComparison L R (regularMod R) N ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitLeftMod R N).hom).oddMap
          (tmulOE _ _ a m) =
        gammaPairOdd L R (regularMod R) N (tmulOE _ _ a m) ≫
          (modTensorUnitLeftMod R N).hom.hom := rfl
    erw [h, gammaPairOdd_tmulOE, gpairLin_apply]
    refine Eq.trans ?_ (leftUnitorHom_oddMap_tmulOE
      (M := gammaModule D L R N.X) a m).symm
    exact gpair_unitLeft' R N _ a m

/-! ## The regular module on the right -/

/-- Pairing with the regular module on the right and collapsing is
the convolution action after a braiding. -/
theorem gpair_unitRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R]
    (M : Mod D R) {X Y : D} (m : X ⟶ M.X)
    (a : Y ⟶ R) :
    gpair (M := M) (N := regularMod R) m a ≫
        (modTensorUnitRightMod R M).hom.hom =
      (β_ X Y).hom ≫ gact a m := by
  have h : gpair (M := M) (N := regularMod R) m a ≫
      (modTensorUnitRightMod R M).hom.hom =
        (m ⊗ₘ a) ≫ actRight R M.X := by
    erw [gpair_def, Category.assoc]
    exact whisker_eq _ (modTensorπ_desc R M (regularMod R) _ _)
  refine h.trans ?_
  rw [actRight, ← Category.assoc,
    BraidedCategory.braiding_naturality]
  exact Category.assoc _ _ _

/-- The reindexed form of `RS.gpair_unitRight`. -/
theorem gpair_unitRight'
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R]
    (M : Mod D R) {W X Y : D} (s : W ⟶ X ⊗ Y)
    (t : W ⟶ Y ⊗ X) (hst : s ≫ (β_ X Y).hom = t) (m : X ⟶ M.X)
    (a : Y ⟶ R) :
    (s ≫ gpair (M := M) (N := regularMod R) m a) ≫
        (modTensorUnitRightMod R M).hom.hom = t ≫ gact a m := by
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (whisker_eq _ (gpair_unitRight R M m a)) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact eq_whisker hst _

/-- **The comparison map at the regular module on the right is the
right unitor**, Koszul sign and all: the sign is the self-braiding
of the odd line. -/
theorem gammaPairComparison_unitRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (M : Mod D R) :
    gammaPairComparison L R M (regularMod R) ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitRightMod R M).hom =
      rightUnitorHom (gammaModule D L R M.X) := by
  refine hom_ext (fun m a => ?_) (fun m a => ?_) (fun m a => ?_)
    (fun m a => ?_)
  · have h : (gammaPairComparison L R M (regularMod R) ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitRightMod R M).hom).evenMap
          (tmulEE _ _ m a) =
        gammaPairEven L R M (regularMod R) (tmulEE _ _ m a) ≫
          (modTensorUnitRightMod R M).hom.hom := rfl
    erw [h, gammaPairEven_tmulEE, gpairLin_apply]
    refine Eq.trans ?_ (rightUnitorHom_evenMap_tmulEE
      (M := gammaModule D L R M.X) m a).symm
    refine gpair_unitRight' R M _ _ ?_ m a
    rw [braiding_unit_self, Category.comp_id]
  · have h : (gammaPairComparison L R M (regularMod R) ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitRightMod R M).hom).evenMap
          (tmulOO _ _ m a) =
        gammaPairEven L R M (regularMod R) (tmulOO _ _ m a) ≫
          (modTensorUnitRightMod R M).hom.hom := rfl
    erw [h, gammaPairEven_tmulOO, gpairLin_apply]
    refine Eq.trans ?_ (rightUnitorHom_evenMap_tmulOO
      (M := gammaModule D L R M.X) m a).symm
    refine Eq.trans (gpair_unitRight' R M _ (-L.sq.inv) ?_ m a) ?_
    · rw [L.braid_neg, Preadditive.comp_neg, Category.comp_id]
    · exact Preadditive.neg_comp _ _
  · have h : (gammaPairComparison L R M (regularMod R) ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitRightMod R M).hom).oddMap
          (tmulEO _ _ m a) =
        gammaPairOdd L R M (regularMod R) (tmulEO _ _ m a) ≫
          (modTensorUnitRightMod R M).hom.hom := rfl
    erw [h, gammaPairOdd_tmulEO, gpairLin_apply]
    refine Eq.trans ?_ (rightUnitorHom_oddMap_tmulEO
      (M := gammaModule D L R M.X) m a).symm
    refine gpair_unitRight' R M _ _ ?_ m a
    rw [(Iso.eq_comp_inv (ρ_ L.obj)).mpr
      (braiding_rightUnitor L.obj), Iso.inv_hom_id_assoc]
  · have h : (gammaPairComparison L R M (regularMod R) ≫
        (gammaModuleFunctor L R).map
          (modTensorUnitRightMod R M).hom).oddMap
          (tmulOE _ _ m a) =
        gammaPairOdd L R M (regularMod R) (tmulOE _ _ m a) ≫
          (modTensorUnitRightMod R M).hom.hom := rfl
    erw [h, gammaPairOdd_tmulOE, gpairLin_apply]
    refine Eq.trans ?_ (rightUnitorHom_oddMap_tmulOE
      (M := gammaModule D L R M.X) m a).symm
    refine gpair_unitRight' R M _ _ ?_ m a
    rw [(Iso.eq_comp_inv (λ_ L.obj)).mpr
      (braiding_leftUnitor L.obj), Iso.inv_hom_id_assoc]

/-! ## Invertibility -/

/-- The comparison isomorphism at the regular module on the
left. -/
noncomputable def gammaPairIsoUnitLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (N : Mod D R) :
    ((gammaModuleFunctor L R).obj (regularMod R)).tensor
        ((gammaModuleFunctor L R).obj N) ≅
      (gammaModuleFunctor L R).obj
        (modTensorMod R (regularMod R) N) :=
  (gammaModule D L R N.X).leftUnitor ≪≫
    ((gammaModuleFunctor L R).mapIso
      (modTensorUnitLeftMod R N)).symm

theorem gammaPairIsoUnitLeft_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (N : Mod D R) :
    (gammaPairIsoUnitLeft L R N).hom =
      gammaPairComparison L R (regularMod R) N := by
  have key : (gammaModuleFunctor L R).map (modTensorUnitLeftMod R N).hom ≫
      (gammaModuleFunctor L R).map (modTensorUnitLeftMod R N).inv = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  refine Eq.trans (eq_whisker
    (gammaPairComparison_unitLeft L R N).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact Eq.trans (whisker_eq _ key) (Category.comp_id _)

/-- **The comparison map is an isomorphism when the left argument
is the regular module.** -/
instance isIso_gammaPairComparison_unitLeft
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (N : Mod D R) :
    IsIso (gammaPairComparison L R (regularMod R) N) := by
  rw [← gammaPairIsoUnitLeft_hom]
  exact (gammaPairIsoUnitLeft L R N).isIso_hom

/-- The comparison isomorphism at the regular module on the
right. -/
noncomputable def gammaPairIsoUnitRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (M : Mod D R) :
    ((gammaModuleFunctor L R).obj M).tensor
        ((gammaModuleFunctor L R).obj (regularMod R)) ≅
      (gammaModuleFunctor L R).obj
        (modTensorMod R M (regularMod R)) :=
  (gammaModule D L R M.X).rightUnitor ≪≫
    ((gammaModuleFunctor L R).mapIso
      (modTensorUnitRightMod R M)).symm

theorem gammaPairIsoUnitRight_hom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (M : Mod D R) :
    (gammaPairIsoUnitRight L R M).hom =
      gammaPairComparison L R M (regularMod R) := by
  have key : (gammaModuleFunctor L R).map (modTensorUnitRightMod R M).hom ≫
      (gammaModuleFunctor L R).map (modTensorUnitRightMod R M).inv = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id]
  refine Eq.trans (eq_whisker
    (gammaPairComparison_unitRight L R M).symm _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact Eq.trans (whisker_eq _ key) (Category.comp_id _)

/-- **The comparison map is an isomorphism when the right argument
is the regular module.** -/
instance isIso_gammaPairComparison_unitRight
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (M : Mod D R) :
    IsIso (gammaPairComparison L R M (regularMod R)) := by
  rw [← gammaPairIsoUnitRight_hom]
  exact (gammaPairIsoUnitRight L R M).isIso_hom

end

end RS
