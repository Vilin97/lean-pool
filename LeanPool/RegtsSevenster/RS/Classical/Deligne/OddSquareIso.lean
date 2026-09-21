/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.OddSquare
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FibreMu
import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaShift
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModShiftUnit

/-!
# The comparison map at the odd line against itself

The realization of the free module on the odd line is the parity
shift of the Γ-algebra, and the parity shift of the algebra is
invertible for the tensor product of super modules.  Under those
two identifications the comparison map of Deligne's (2.11.1) at the
odd line against itself is minus the canonical isomorphism, so it
is an isomorphism.  The sign is the self-braiding of the line and
is the same on all four blocks.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

section

variable {D : Type u}

/-! ## The two parity swaps, inverted -/

/-- The odd parity swap, unfolded. -/
theorem rhoOddOdd_apply
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D)
    (M : D) (g : L.obj ⟶ M ⊗ L.obj) :
    rhoOddOdd L M g = (L.sq.inv ≫ (g ▷ L.obj)) ≫
      ((α_ M L.obj L.obj).hom ≫ (M ◁ L.sq.hom) ≫
        (ρ_ M).hom) := by
  rw [rhoOddOdd, LinearEquiv.trans_apply, Linear.homCongr_apply,
    Iso.refl_inv, Category.id_comp]
  rfl

/-- The odd parity swap, inverted. -/
theorem rhoOddOdd_symm_apply
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D)
    (y : 𝟙_ D ⟶ R) :
    (rhoOddOdd L R).symm y = (λ_ L.obj).inv ≫ (y ▷ L.obj) := by
  refine (LinearEquiv.symm_apply_eq _).mpr ?_
  have hc : ((λ_ L.obj).inv ▷ L.obj) ≫
      (α_ (𝟙_ D) L.obj L.obj).hom = (λ_ (L.obj ⊗ L.obj)).inv := by
    monoidal
  rw [rhoOddOdd_apply, MonoidalCategory.comp_whiskerRight]
  simp only [Category.assoc]
  rw [← Category.assoc ((y ▷ L.obj) ▷ L.obj),
    associator_naturality_left]
  simp only [Category.assoc]
  rw [← Category.assoc (y ▷ (L.obj ⊗ L.obj)), ← whisker_exchange]
  simp only [Category.assoc]
  rw [rightUnitor_naturality,
    ← Category.assoc ((λ_ L.obj).inv ▷ L.obj), hc,
    ← Category.assoc (λ_ (L.obj ⊗ L.obj)).inv,
    ← leftUnitor_inv_naturality]
  simp only [Category.assoc]
  rw [← Category.assoc L.sq.inv, L.sq.inv_hom_id, Category.id_comp,
    ← Category.assoc, unitors_inv_equal, Iso.inv_hom_id,
    Category.id_comp]

/-! ## The comparison at the odd line against itself -/

attribute [local instance] CategoryTheory.ModObj.regular

open SuperCommAlgebra.Mod

/-- The comparison map at the odd line against itself, followed by
the two identifications of the target with the algebra. -/
noncomputable abbrev oddSqMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)] :
    (gammaModule D L R (freeMod R L.obj).X).tensor
        (gammaModule D L R (freeMod R L.obj).X) ⟶
      (gammaAlgebra D L R).unitMod :=
  fibreMu L R L.obj L.obj ≫
    gammaFunMap L R (freeModMap R L.sq.hom) ≫
      gammaFunMap L R (freeModUnitIso R).hom

/-- The identification of the source with the parity shift of the
algebra, on both factors. -/
noncomputable abbrev oddSqShift
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] :
    (gammaModule D L R (freeMod R L.obj).X).tensor
        (gammaModule D L R (freeMod R L.obj).X) ⟶
      (gammaAlgebra D L R).unitMod :=
  SuperCommAlgebra.Mod.tensorHom (gammaShiftIso L R).hom
      (gammaShiftIso L R).hom ≫
    (shiftUnitTensor (shift (gammaAlgebra D L R).unitMod)).hom

/-! ### Evaluation on the four generator families -/

private theorem oddSqMap_ee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (u v : 𝟙_ D ⟶ R ⊗ L.obj) :
    (oddSqMap L R).evenMap (tmulEE _ _ u v) =
      (λ_ (𝟙_ D)).inv ≫ (u ⊗ₘ v) ≫
        freeModShuffle R L.obj L.obj ≫ (R ◁ L.sq.hom) ≫
          (ρ_ R).hom := by
  show ((fibreMu L R L.obj L.obj).evenMap (tmulEE _ _ u v) ≫
      (R ◁ L.sq.hom)) ≫ (ρ_ R).hom = _
  rw [fibreMu_evenMap_tmulEE]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (Category.assoc _ _ _)

private theorem oddSqMap_oo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (u v : L.obj ⟶ R ⊗ L.obj) :
    (oddSqMap L R).evenMap (tmulOO _ _ u v) =
      L.sq.inv ≫ (u ⊗ₘ v) ≫
        freeModShuffle R L.obj L.obj ≫ (R ◁ L.sq.hom) ≫
          (ρ_ R).hom := by
  show ((fibreMu L R L.obj L.obj).evenMap (tmulOO _ _ u v) ≫
      (R ◁ L.sq.hom)) ≫ (ρ_ R).hom = _
  rw [fibreMu_evenMap_tmulOO]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (Category.assoc _ _ _)

private theorem oddSqMap_eo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (u : 𝟙_ D ⟶ R ⊗ L.obj)
    (v : L.obj ⟶ R ⊗ L.obj) :
    (oddSqMap L R).oddMap (tmulEO _ _ u v) =
      (λ_ L.obj).inv ≫ (u ⊗ₘ v) ≫
        freeModShuffle R L.obj L.obj ≫ (R ◁ L.sq.hom) ≫
          (ρ_ R).hom := by
  show ((fibreMu L R L.obj L.obj).oddMap (tmulEO _ _ u v) ≫
      (R ◁ L.sq.hom)) ≫ (ρ_ R).hom = _
  rw [fibreMu_oddMap_tmulEO]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (Category.assoc _ _ _)

private theorem oddSqMap_oe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (u : L.obj ⟶ R ⊗ L.obj)
    (v : 𝟙_ D ⟶ R ⊗ L.obj) :
    (oddSqMap L R).oddMap (tmulOE _ _ u v) =
      (ρ_ L.obj).inv ≫ (u ⊗ₘ v) ≫
        freeModShuffle R L.obj L.obj ≫ (R ◁ L.sq.hom) ≫
          (ρ_ R).hom := by
  show ((fibreMu L R L.obj L.obj).oddMap (tmulOE _ _ u v) ≫
      (R ◁ L.sq.hom)) ≫ (ρ_ R).hom = _
  rw [fibreMu_oddMap_tmulOE]
  refine Eq.trans (Category.assoc _ _ _) ?_
  refine Eq.trans (Category.assoc _ _ _) ?_
  exact whisker_eq _ (Category.assoc _ _ _)

private theorem rhoEvenOdd_expand
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D)
    (a : L.obj ⟶ R) :
    rhoEvenOdd L R (L.sq.inv ≫ (a ▷ L.obj)) = a :=
  (rhoEvenOdd L R).apply_symm_apply a

private theorem rhoOddOdd_expand
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D)
    (x : 𝟙_ D ⟶ R) :
    rhoOddOdd L R ((λ_ L.obj).inv ≫ (x ▷ L.obj)) = x := by
  rw [← rhoOddOdd_symm_apply]
  exact (rhoOddOdd L R).apply_symm_apply x

private theorem oddSqShift_ee
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (a b : L.obj ⟶ R) :
    (oddSqShift L R).evenMap (tmulEE _ _
        (L.sq.inv ≫ (a ▷ L.obj)) (L.sq.inv ≫ (b ▷ L.obj))) =
      L.sq.inv ≫ (a ⊗ₘ b) ≫ μ[R] := by
  show (shiftUnitHom (shift (gammaAlgebra D L R).unitMod)).evenMap
      (tmulEE (shift (gammaAlgebra D L R).unitMod)
        (shift (gammaAlgebra D L R).unitMod)
        (rhoEvenOdd L R (L.sq.inv ≫ (a ▷ L.obj)))
        (rhoEvenOdd L R (L.sq.inv ≫ (b ▷ L.obj)))) = _
  rw [rhoEvenOdd_expand, rhoEvenOdd_expand,
    shiftUnitHom_evenMap_tmulEE]
  rfl

private theorem oddSqShift_oo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (x y : 𝟙_ D ⟶ R) :
    (oddSqShift L R).evenMap (tmulOO _ _
        ((λ_ L.obj).inv ≫ (x ▷ L.obj))
        ((λ_ L.obj).inv ≫ (y ▷ L.obj))) =
      -((λ_ (𝟙_ D)).inv ≫ (x ⊗ₘ y) ≫ μ[R]) := by
  show (shiftUnitHom (shift (gammaAlgebra D L R).unitMod)).evenMap
      (tmulOO (shift (gammaAlgebra D L R).unitMod)
        (shift (gammaAlgebra D L R).unitMod)
        (rhoOddOdd L R ((λ_ L.obj).inv ≫ (x ▷ L.obj)))
        (rhoOddOdd L R ((λ_ L.obj).inv ≫ (y ▷ L.obj)))) = _
  rw [rhoOddOdd_expand, rhoOddOdd_expand,
    shiftUnitHom_evenMap_tmulOO]
  rfl

private theorem oddSqShift_eo
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (a : L.obj ⟶ R) (x : 𝟙_ D ⟶ R) :
    (oddSqShift L R).oddMap (tmulEO _ _
        (L.sq.inv ≫ (a ▷ L.obj))
        ((λ_ L.obj).inv ≫ (x ▷ L.obj))) =
      -((ρ_ L.obj).inv ≫ (a ⊗ₘ x) ≫ μ[R]) := by
  show (shiftUnitHom (shift (gammaAlgebra D L R).unitMod)).oddMap
      (tmulEO (shift (gammaAlgebra D L R).unitMod)
        (shift (gammaAlgebra D L R).unitMod)
        (rhoEvenOdd L R (L.sq.inv ≫ (a ▷ L.obj)))
        (rhoOddOdd L R ((λ_ L.obj).inv ≫ (x ▷ L.obj)))) = _
  rw [rhoEvenOdd_expand, rhoOddOdd_expand,
    shiftUnitHom_oddMap_tmulEO]
  rfl

private theorem oddSqShift_oe
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (x : 𝟙_ D ⟶ R) (a : L.obj ⟶ R) :
    (oddSqShift L R).oddMap (tmulOE _ _
        ((λ_ L.obj).inv ≫ (x ▷ L.obj))
        (L.sq.inv ≫ (a ▷ L.obj))) =
      (λ_ L.obj).inv ≫ (x ⊗ₘ a) ≫ μ[R] := by
  show (shiftUnitHom (shift (gammaAlgebra D L R).unitMod)).oddMap
      (tmulOE (shift (gammaAlgebra D L R).unitMod)
        (shift (gammaAlgebra D L R).unitMod)
        (rhoOddOdd L R ((λ_ L.obj).inv ≫ (x ▷ L.obj)))
        (rhoEvenOdd L R (L.sq.inv ≫ (a ▷ L.obj)))) = _
  rw [rhoOddOdd_expand, rhoEvenOdd_expand,
    shiftUnitHom_oddMap_tmulOE]
  rfl

/-! ### The identification -/

private theorem exists_even
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D)
    (u : 𝟙_ D ⟶ R ⊗ L.obj) :
    ∃ a : L.obj ⟶ R, L.sq.inv ≫ (a ▷ L.obj) = u :=
  ⟨rhoEvenOdd L R u, (rhoEvenOdd L R).symm_apply_apply u⟩

private theorem exists_odd
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D)
    (u : L.obj ⟶ R ⊗ L.obj) :
    ∃ x : 𝟙_ D ⟶ R, (λ_ L.obj).inv ≫ (x ▷ L.obj) = u := by
  refine ⟨rhoOddOdd L R u, ?_⟩
  rw [← rhoOddOdd_symm_apply]
  exact (rhoOddOdd L R).symm_apply_apply u

/-- **The comparison map at the odd line against itself is minus
the canonical isomorphism.**  The sign is the self-braiding of the
line, and it is the same on all four blocks. -/
theorem oddSqMap_eq [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)] :
    oddSqMap L R = -oddSqShift L R := by
  refine hom_ext (fun u v => ?_) (fun u v => ?_) (fun u v => ?_)
    (fun u v => ?_)
  · obtain ⟨a, rfl⟩ := exists_even L R u
    obtain ⟨b, rfl⟩ := exists_even L R v
    rw [oddSqMap_ee, shuffle_contract, ← Category.assoc,
      oddContract_ee, Preadditive.neg_comp, neg_evenMap,
      LinearMap.neg_apply]
    exact congrArg Neg.neg (oddSqShift_ee L R a b).symm
  · obtain ⟨x, rfl⟩ := exists_odd L R u
    obtain ⟨y, rfl⟩ := exists_odd L R v
    rw [oddSqMap_oo, shuffle_contract, ← Category.assoc,
      oddContract_oo, neg_evenMap, LinearMap.neg_apply]
    exact Eq.trans (neg_neg _).symm
      (congrArg Neg.neg (oddSqShift_oo L R x y).symm)
  · obtain ⟨a, rfl⟩ := exists_even L R u
    obtain ⟨x, rfl⟩ := exists_odd L R v
    rw [oddSqMap_eo, shuffle_contract, ← Category.assoc,
      oddContract_eo, neg_oddMap, LinearMap.neg_apply]
    exact Eq.trans (neg_neg _).symm
      (congrArg Neg.neg (oddSqShift_eo L R a x).symm)
  · obtain ⟨x, rfl⟩ := exists_odd L R u
    obtain ⟨a, rfl⟩ := exists_even L R v
    rw [oddSqMap_oe, shuffle_contract, ← Category.assoc,
      oddContract_oe, Preadditive.neg_comp, neg_oddMap,
      LinearMap.neg_apply]
    exact congrArg Neg.neg (oddSqShift_oe L R x a).symm

/-! ### Invertibility -/

/-- **The comparison map of (2.11.1) at the odd line against
itself is an isomorphism.** -/
theorem isIso_gammaPairComparison_oddSquare
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)] :
    IsIso (gammaPairComparison L R (freeMod R L.obj)
      (freeMod R L.obj)) := by
  haveI hsh : IsIso (oddSqShift L R) := by
    haveI : IsIso (SuperCommAlgebra.Mod.tensorHom
        (gammaShiftIso L R).hom (gammaShiftIso L R).hom) :=
      (SuperCommAlgebra.Mod.tensorIso (gammaShiftIso L R)
        (gammaShiftIso L R)).isIso_hom
    exact IsIso.comp_isIso
  haveI hmap : IsIso (oddSqMap L R) := by
    rw [oddSqMap_eq]
    refine ⟨-inv (oddSqShift L R), ?_, ?_⟩
    · rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
        IsIso.hom_inv_id]
    · rw [Preadditive.neg_comp, Preadditive.comp_neg, neg_neg,
        IsIso.inv_hom_id]
  haveI h1 : IsIso (gammaFunMap L R (freeModMap R L.sq.hom)) :=
    ((gammaModuleFunctor L R).mapIso
      (freeModMapIso R L.sq)).isIso_hom
  haveI h2 : IsIso (gammaFunMap L R (freeModUnitIso R).hom) :=
    ((gammaModuleFunctor L R).mapIso (freeModUnitIso R)).isIso_hom
  haveI h3 : IsIso (gammaFunMap L R (freeModMap R L.sq.hom) ≫
      gammaFunMap L R (freeModUnitIso R).hom) := IsIso.comp_isIso
  haveI h4 : IsIso (gammaFunMap L R
      (freeModTensorIso R L.obj L.obj).hom) :=
    ((gammaModuleFunctor L R).mapIso
      (freeModTensorIso R L.obj L.obj)).isIso_hom
  haveI hmu : IsIso (gammaPairComparison L R (freeMod R L.obj)
      (freeMod R L.obj) ≫
        gammaFunMap L R (freeModTensorIso R L.obj L.obj).hom) :=
    @IsIso.of_isIso_comp_right _ _ _ _ _
      (fibreMu L R L.obj L.obj)
      (gammaFunMap L R (freeModMap R L.sq.hom) ≫
        gammaFunMap L R (freeModUnitIso R).hom) h3 hmap
  exact IsIso.of_isIso_comp_right _
    (gammaFunMap L R (freeModTensorIso R L.obj L.obj).hom)

end

end RS
