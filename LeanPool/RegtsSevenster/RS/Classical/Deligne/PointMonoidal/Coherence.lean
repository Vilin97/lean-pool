/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.PointMonoidal.Calculus

/-!
# Coherence and invertibility of the comparison

The comparison of [Comparison.lean](Comparison.lean) satisfies the
three laws of a lax monoidal structure and intertwines the
braidings: each is transported from the corresponding law over the
algebra, proved in [Residue.lean](Residue.lean), through the
coordinates, using the generator calculus of
[Calculus.lean](Calculus.lean).  It is moreover invertible for
*every* pair of modules — the inverse built alongside it undoes it
on generators — as is the unit comparison; this is the usual
strength of base change along an algebra map, in super form.

## Contents

* `RS.superVectMu_associativity`, `RS.superVectMu_left_unitality`,
  `RS.superVectMu_right_unitality`, `RS.superVectMu_braiding`: the
  coherence of the comparison in `RS.SuperVect`.
* `RS.superVectMu_naturality_left`,
  `RS.superVectMu_naturality_right`,
  `RS.superVectMuEvenRaw_naturality` and its odd companion:
  naturality in either variable, before and after the coordinates.
* `RS.superVectMuEvenRaw_baseNuEven`,
  `RS.baseNuEven_superVectMuEvenRaw` and their odd companions: the
  two composites of the comparison with its inverse.
* `RS.SuperVect.isoOfBijective`: a morphism of super vector spaces
  with bijective components is an isomorphism.
* `RS.superVectEps`: the unit of the fibre functor.
* `RS.superVectMuIso`, `RS.isIso_superVectMu`,
  `RS.superVectEpsIso`, `RS.isIso_superVectEps`: both comparisons
  are invertible.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory
open SuperCommAlgebra (pointMod)
open SuperCommAlgebra.Mod

universe u

/-! ## Associativity of the comparison -/

section SuperVectAssoc

open scoped TensorProduct

attribute [local irreducible] superVectMu

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)
  (M N Q : S.Mod.{u, u, u, u})

private theorem superVectMu_associativity_evenMap
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (Q.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (Q.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((N.tensor Q).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((N.tensor Q).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (((M.tensor N).tensor Q).tensor (pointMod P)).even]
    [FiniteDimensional ℂ (((M.tensor N).tensor Q).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor (N.tensor Q)).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor (N.tensor Q)).tensor (pointMod P)).odd] :
    ((superVectMu P M N ▷ toSuperVect P Q) ≫
        superVectMu P (M.tensor N) Q ≫
        superVectHom P (α_ M N Q).hom).evenMap =
      ((α_ (toSuperVect P M) (toSuperVect P N)
          (toSuperVect P Q)).hom ≫
        (toSuperVect P M ◁ superVectMu P N Q) ≫
        superVectMu P M (N.tensor Q)).evenMap := by
  refine superVectTripleEven_ext (fun a b c => ?_) (fun a b c => ?_)
    (fun a b c => ?_) (fun a b c => ?_)
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_associativity P M N Q))
      (tmulEE ((M.tensor (pointMod P)).tensor (N.tensor (pointMod P)))
        (Q.tensor (pointMod P))
        (tmulEE (M.tensor (pointMod P)) (N.tensor (pointMod P))
          ((toSuperVectEvenEquiv P M).symm a)
          ((toSuperVectEvenEquiv P N).symm b))
        ((toSuperVectEvenEquiv P Q).symm c))
    simp only [modComp_evenMap_apply] at key
    rw [whiskerRight_evenMap_tmulEE, modAssoc_evenMap_ee,
      whiskerLeft_evenMap_tmulEE (pointBaseMu P N Q)
        (M.tensor (pointMod P))] at key
    simp only [svComp_evenMap_apply,
      svWhiskerRight_evenMap_inl,
      svWhiskerLeft_evenMap_inl,
      svAssoc_evenMap_ee,
      superVectMu_evenMap_ee,
      superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply]
    rw [key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_associativity P M N Q))
      (tmulEE ((M.tensor (pointMod P)).tensor (N.tensor (pointMod P)))
        (Q.tensor (pointMod P))
        (tmulOO (M.tensor (pointMod P)) (N.tensor (pointMod P))
          ((toSuperVectOddEquiv P M).symm a)
          ((toSuperVectOddEquiv P N).symm b))
        ((toSuperVectEvenEquiv P Q).symm c))
    simp only [modComp_evenMap_apply] at key
    rw [whiskerRight_evenMap_tmulEE, modAssoc_evenMap_oo,
      whiskerLeft_evenMap_tmulOO (pointBaseMu P N Q)
        (M.tensor (pointMod P))] at key
    simp only [svComp_evenMap_apply,
      svWhiskerRight_evenMap_inl,
       svWhiskerLeft_evenMap_inr,
       svAssoc_evenMap_oo,
      superVectMu_evenMap_ee, superVectMu_evenMap_oo,
       superVectMu_oddMap_oe,
      superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply]
    rw [key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_associativity P M N Q))
      (tmulOO ((M.tensor (pointMod P)).tensor (N.tensor (pointMod P)))
        (Q.tensor (pointMod P))
        (tmulEO (M.tensor (pointMod P)) (N.tensor (pointMod P))
          ((toSuperVectEvenEquiv P M).symm a)
          ((toSuperVectOddEquiv P N).symm b))
        ((toSuperVectOddEquiv P Q).symm c))
    simp only [modComp_evenMap_apply] at key
    rw [whiskerRight_evenMap_tmulOO, modAssoc_evenMap_eo,
      whiskerLeft_evenMap_tmulEE (pointBaseMu P N Q)
        (M.tensor (pointMod P))] at key
    simp only [svComp_evenMap_apply,
       svWhiskerRight_evenMap_inr,
      svWhiskerLeft_evenMap_inl,
        svAssoc_evenMap_eo,
       superVectMu_evenMap_oo,
      superVectMu_oddMap_eo,
      superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply]
    rw [key, superVectMu_evenMap_ee,
      LinearEquiv.symm_apply_apply]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_associativity P M N Q))
      (tmulOO ((M.tensor (pointMod P)).tensor (N.tensor (pointMod P)))
        (Q.tensor (pointMod P))
        (tmulOE (M.tensor (pointMod P)) (N.tensor (pointMod P))
          ((toSuperVectOddEquiv P M).symm a)
          ((toSuperVectEvenEquiv P N).symm b))
        ((toSuperVectOddEquiv P Q).symm c))
    simp only [modComp_evenMap_apply] at key
    rw [whiskerRight_evenMap_tmulOO, modAssoc_evenMap_oe,
      whiskerLeft_evenMap_tmulOO (pointBaseMu P N Q)
        (M.tensor (pointMod P))] at key
    simp only [svComp_evenMap_apply,
       svWhiskerRight_evenMap_inr,
       svWhiskerLeft_evenMap_inr,
      svAssoc_evenMap_oe,
       superVectMu_evenMap_oo,
      superVectMu_oddMap_eo, superVectMu_oddMap_oe,
      superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply]
    rw [key]
    rfl

private theorem superVectMu_associativity_oddMap
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (Q.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (Q.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((N.tensor Q).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((N.tensor Q).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (((M.tensor N).tensor Q).tensor (pointMod P)).even]
    [FiniteDimensional ℂ (((M.tensor N).tensor Q).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor (N.tensor Q)).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor (N.tensor Q)).tensor (pointMod P)).odd] :
    ((superVectMu P M N ▷ toSuperVect P Q) ≫
        superVectMu P (M.tensor N) Q ≫
        superVectHom P (α_ M N Q).hom).oddMap =
      ((α_ (toSuperVect P M) (toSuperVect P N)
          (toSuperVect P Q)).hom ≫
        (toSuperVect P M ◁ superVectMu P N Q) ≫
        superVectMu P M (N.tensor Q)).oddMap := by
  refine superVectTripleOdd_ext (fun a b c => ?_) (fun a b c => ?_)
    (fun a b c => ?_) (fun a b c => ?_)
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_associativity P M N Q))
      (tmulEO ((M.tensor (pointMod P)).tensor (N.tensor (pointMod P)))
        (Q.tensor (pointMod P))
        (tmulEE (M.tensor (pointMod P)) (N.tensor (pointMod P))
          ((toSuperVectEvenEquiv P M).symm a)
          ((toSuperVectEvenEquiv P N).symm b))
        ((toSuperVectOddEquiv P Q).symm c))
    simp only [modComp_oddMap_apply] at key
    rw [whiskerRight_oddMap_tmulEO, modAssoc_oddMap_ee,
      whiskerLeft_oddMap_tmulEO (pointBaseMu P N Q)
        (M.tensor (pointMod P))] at key
    simp only [ svComp_oddMap_apply,
      svWhiskerRight_oddMap_inl,
      svWhiskerLeft_oddMap_inl,
       svAssoc_oddMap_ee,
      superVectMu_evenMap_ee,
      superVectMu_oddMap_eo,
       superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply]
    rw [key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_associativity P M N Q))
      (tmulEO ((M.tensor (pointMod P)).tensor (N.tensor (pointMod P)))
        (Q.tensor (pointMod P))
        (tmulOO (M.tensor (pointMod P)) (N.tensor (pointMod P))
          ((toSuperVectOddEquiv P M).symm a)
          ((toSuperVectOddEquiv P N).symm b))
        ((toSuperVectOddEquiv P Q).symm c))
    simp only [modComp_oddMap_apply] at key
    rw [whiskerRight_oddMap_tmulEO, modAssoc_oddMap_oo,
      whiskerLeft_oddMap_tmulOE (pointBaseMu P N Q)
        (M.tensor (pointMod P))] at key
    simp only [ svComp_oddMap_apply,
      svWhiskerRight_oddMap_inl,
       svWhiskerLeft_oddMap_inr,
        svAssoc_oddMap_oo,
       superVectMu_evenMap_oo,
      superVectMu_oddMap_eo,
       superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply]
    rw [key, superVectMu_oddMap_oe,
      LinearEquiv.symm_apply_apply]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_associativity P M N Q))
      (tmulOE ((M.tensor (pointMod P)).tensor (N.tensor (pointMod P)))
        (Q.tensor (pointMod P))
        (tmulEO (M.tensor (pointMod P)) (N.tensor (pointMod P))
          ((toSuperVectEvenEquiv P M).symm a)
          ((toSuperVectOddEquiv P N).symm b))
        ((toSuperVectEvenEquiv P Q).symm c))
    simp only [modComp_oddMap_apply] at key
    rw [whiskerRight_oddMap_tmulOE, modAssoc_oddMap_eo,
      whiskerLeft_oddMap_tmulEO (pointBaseMu P N Q)
        (M.tensor (pointMod P))] at key
    simp only [ svComp_oddMap_apply,
       svWhiskerRight_oddMap_inr,
      svWhiskerLeft_oddMap_inl,
      svAssoc_oddMap_eo,
      superVectMu_oddMap_eo, superVectMu_oddMap_oe,
       superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply]
    rw [key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_associativity P M N Q))
      (tmulOE ((M.tensor (pointMod P)).tensor (N.tensor (pointMod P)))
        (Q.tensor (pointMod P))
        (tmulOE (M.tensor (pointMod P)) (N.tensor (pointMod P))
          ((toSuperVectOddEquiv P M).symm a)
          ((toSuperVectEvenEquiv P N).symm b))
        ((toSuperVectEvenEquiv P Q).symm c))
    simp only [modComp_oddMap_apply] at key
    rw [whiskerRight_oddMap_tmulOE, modAssoc_oddMap_oe,
      whiskerLeft_oddMap_tmulOE (pointBaseMu P N Q)
        (M.tensor (pointMod P))] at key
    simp only [ svComp_oddMap_apply,
       svWhiskerRight_oddMap_inr,
       svWhiskerLeft_oddMap_inr,
       svAssoc_oddMap_oe,
      superVectMu_evenMap_ee,
       superVectMu_oddMap_oe,
       superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply]
    rw [key]
    rfl

/-- **Associativity of the monoidal comparison.** -/
@[reassoc]
theorem superVectMu_associativity
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (Q.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (Q.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((N.tensor Q).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((N.tensor Q).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (((M.tensor N).tensor Q).tensor (pointMod P)).even]
    [FiniteDimensional ℂ (((M.tensor N).tensor Q).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor (N.tensor Q)).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor (N.tensor Q)).tensor (pointMod P)).odd] :
    (superVectMu P M N ▷ toSuperVect P Q) ≫
        superVectMu P (M.tensor N) Q ≫
        superVectHom P (α_ M N Q).hom =
      (α_ (toSuperVect P M) (toSuperVect P N)
          (toSuperVect P Q)).hom ≫
        (toSuperVect P M ◁ superVectMu P N Q) ≫
        superVectMu P M (N.tensor Q) := by
  exact SuperVect.hom_ext (superVectMu_associativity_evenMap P M N Q)
    (superVectMu_associativity_oddMap P M N Q)

end SuperVectAssoc

/-! ## Naturality of the comparison in super vector spaces -/

section SuperVectNaturality

open scoped TensorProduct

attribute [local irreducible] superVectMu

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)
  {M M' N N' : S.Mod.{u, u, u, u}}

/-- **The comparison is natural in the left variable.** -/
theorem superVectMu_naturality_left
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (M'.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M'.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M'.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M'.tensor N).tensor (pointMod P)).odd]
    (f : M ⟶ M') :
    (superVectHom P f ▷ toSuperVect P N) ≫ superVectMu P M' N =
      superVectMu P M N ≫ superVectHom P (f ▷ N) := by
  refine SuperVect.hom_ext
    (superVectPairEven_ext (fun x y => ?_) (fun x y => ?_))
    (superVectPairOdd_ext (fun x y => ?_) (fun x y => ?_))
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_naturality P f (𝟙 N)))
      (tmulEE (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectEvenEquiv P M).symm x)
        ((toSuperVectEvenEquiv P N).symm y))
    simp only [modComp_evenMap_apply] at key
    rw [mcTensorHom_evenMap_tmulEE,
      MonoidalCategory.id_tensorHom_id, id_evenMap,
      LinearMap.id_coe, id_eq, MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id] at key
    simp only [modTensorObj] at key
    simp only [svComp_evenMap_apply]
    rw [svWhiskerRight_evenMap_inl, superVectHom_evenMap_apply,
      superVectMu_evenMap_ee, LinearEquiv.symm_apply_apply,
      superVectMu_evenMap_ee, superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply, key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_naturality P f (𝟙 N)))
      (tmulOO (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectOddEquiv P M).symm x)
        ((toSuperVectOddEquiv P N).symm y))
    simp only [modComp_evenMap_apply] at key
    rw [mcTensorHom_evenMap_tmulOO, MonoidalCategory.id_tensorHom_id, id_oddMap,
      LinearMap.id_coe, id_eq, MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id] at key
    simp only [modTensorObj] at key
    simp only [svComp_evenMap_apply]
    rw [svWhiskerRight_evenMap_inr, superVectHom_oddMap_apply,
      superVectMu_evenMap_oo, LinearEquiv.symm_apply_apply,
      superVectMu_evenMap_oo, superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply, key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_naturality P f (𝟙 N)))
      (tmulEO (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectEvenEquiv P M).symm x)
        ((toSuperVectOddEquiv P N).symm y))
    simp only [modComp_oddMap_apply] at key
    rw [mcTensorHom_oddMap_tmulEO, MonoidalCategory.id_tensorHom_id, id_oddMap,
      LinearMap.id_coe, id_eq, MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id] at key
    simp only [modTensorObj] at key
    simp only [svComp_oddMap_apply]
    rw [svWhiskerRight_oddMap_inl, superVectHom_evenMap_apply,
      superVectMu_oddMap_eo, LinearEquiv.symm_apply_apply,
      superVectMu_oddMap_eo, superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply, key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_naturality P f (𝟙 N)))
      (tmulOE (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectOddEquiv P M).symm x)
        ((toSuperVectEvenEquiv P N).symm y))
    simp only [modComp_oddMap_apply] at key
    rw [mcTensorHom_oddMap_tmulOE, MonoidalCategory.id_tensorHom_id, id_evenMap,
      LinearMap.id_coe, id_eq, MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id,
      MonoidalCategory.tensorHom_id] at key
    simp only [modTensorObj] at key
    simp only [svComp_oddMap_apply]
    rw [svWhiskerRight_oddMap_inr, superVectHom_oddMap_apply,
      superVectMu_oddMap_oe, LinearEquiv.symm_apply_apply,
      superVectMu_oddMap_oe, superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply, key]
    rfl

/-- **The comparison is natural in the right variable.** -/
theorem superVectMu_naturality_right
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N'.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N'.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N').tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N').tensor (pointMod P)).odd]
    (g : N ⟶ N') :
    (toSuperVect P M ◁ superVectHom P g) ≫ superVectMu P M N' =
      superVectMu P M N ≫ superVectHom P (M ◁ g) := by
  refine SuperVect.hom_ext
    (superVectPairEven_ext (fun x y => ?_) (fun x y => ?_))
    (superVectPairOdd_ext (fun x y => ?_) (fun x y => ?_))
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_naturality P (𝟙 M) g))
      (tmulEE (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectEvenEquiv P M).symm x)
        ((toSuperVectEvenEquiv P N).symm y))
    simp only [modComp_evenMap_apply] at key
    rw [mcTensorHom_evenMap_tmulEE,
      MonoidalCategory.id_tensorHom_id, id_evenMap,
      LinearMap.id_coe, id_eq, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_id] at key
    simp only [modTensorObj] at key
    simp only [svComp_evenMap_apply]
    rw [svWhiskerLeft_evenMap_inl, superVectHom_evenMap_apply,
      superVectMu_evenMap_ee, LinearEquiv.symm_apply_apply,
      superVectMu_evenMap_ee, superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply, key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_naturality P (𝟙 M) g))
      (tmulOO (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectOddEquiv P M).symm x)
        ((toSuperVectOddEquiv P N).symm y))
    simp only [modComp_evenMap_apply] at key
    rw [mcTensorHom_evenMap_tmulOO, MonoidalCategory.id_tensorHom_id, id_oddMap,
      LinearMap.id_coe, id_eq, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_id] at key
    simp only [modTensorObj] at key
    simp only [svComp_evenMap_apply]
    rw [svWhiskerLeft_evenMap_inr, superVectHom_oddMap_apply,
      superVectMu_evenMap_oo, LinearEquiv.symm_apply_apply,
      superVectMu_evenMap_oo, superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply, key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_naturality P (𝟙 M) g))
      (tmulEO (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectEvenEquiv P M).symm x)
        ((toSuperVectOddEquiv P N).symm y))
    simp only [modComp_oddMap_apply] at key
    rw [mcTensorHom_oddMap_tmulEO, MonoidalCategory.id_tensorHom_id, id_evenMap,
      LinearMap.id_coe, id_eq, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_id] at key
    simp only [modTensorObj] at key
    simp only [svComp_oddMap_apply]
    rw [svWhiskerLeft_oddMap_inl, superVectHom_oddMap_apply,
      superVectMu_oddMap_eo, LinearEquiv.symm_apply_apply,
      superVectMu_oddMap_eo, superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply, key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_naturality P (𝟙 M) g))
      (tmulOE (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectOddEquiv P M).symm x)
        ((toSuperVectEvenEquiv P N).symm y))
    simp only [modComp_oddMap_apply] at key
    rw [mcTensorHom_oddMap_tmulOE, MonoidalCategory.id_tensorHom_id, id_oddMap,
      LinearMap.id_coe, id_eq, MonoidalCategory.tensorHom_id,
      MonoidalCategory.id_tensorHom,
      MonoidalCategory.tensorHom_id] at key
    simp only [modTensorObj] at key
    simp only [svComp_oddMap_apply]
    rw [svWhiskerLeft_oddMap_inr, superVectHom_evenMap_apply,
      superVectMu_oddMap_oe, LinearEquiv.symm_apply_apply,
      superVectMu_oddMap_oe, superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply, key]
    rfl

end SuperVectNaturality

/-! ## The comparison is invertible -/

section Invertible

open scoped TensorProduct

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)
  (M N : S.Mod.{u, u, u, u})

/-- A residue class is its own coordinate times the unit. -/
theorem pointEven_eq_smul_one (a : (pointMod P : S.Mod.{u, u, u, u}).even) :
    a = a.down • pointOne P :=
  ULift.ext _ _ (by
    change a.down = a.down * 1
    rw [mul_one])

/-- The unit of the residue module is idempotent. -/
theorem pointOne_mul_self :
    (ULift.up ((pointOne P).down * (pointOne P).down) :
      (pointMod P : S.Mod.{u, u, u, u}).even) = pointOne P :=
  ULift.ext _ _ (by
    change (1 : ℂ) * 1 = 1
    rw [one_mul])

variable {M N}

/-- An even product with a residue class is a multiple of the
product with the unit. -/
theorem tmulEE_point_eq_smul (m : M.even)
    (a : (pointMod P : S.Mod.{u, u, u, u}).even) :
    tmulEE M (pointMod P) m a =
      a.down • tmulEE M (pointMod P) m (pointOne P) := by
  rw [← map_smul]
  exact congrArg _ (pointEven_eq_smul_one P a)

/-- An odd product with a residue class is a multiple of the
product with the unit. -/
theorem tmulOE_point_eq_smul (m : M.odd)
    (a : (pointMod P : S.Mod.{u, u, u, u}).even) :
    tmulOE M (pointMod P) m a =
      a.down • tmulOE M (pointMod P) m (pointOne P) := by
  rw [← map_smul]
  exact congrArg _ (pointEven_eq_smul_one P a)

variable (M N)

/-- **The comparison undoes the inverse**, in even degree. -/
theorem superVectMuEvenRaw_baseNuEven (w : ((M.tensor N).tensor (pointMod P) :
      S.Mod.{u, u, u, u}).even) :
    superVectMuEvenRaw P M N (baseNuEven P M N w) = w := by
  refine LinearMap.congr_fun (liftEven_unique (M.tensor N)
    (pointMod P) ((superVectMuEvenRaw P M N).comp
      (baseNuEven P M N)) LinearMap.id (fun t a => ?_)
    (fun t v => ?_)) w
  · change superVectMuEvenRaw P M N
        (baseNuEven P M N (tmulEE (M.tensor N) (pointMod P) t a))
      = tmulEE (M.tensor N) (pointMod P) t a
    rw [baseNuEven_tmulEE]
    refine LinearMap.congr_fun (liftEven_unique M N
      ((superVectMuEvenRaw P M N).comp
        ((baseNuInnerEven P M N).flip a))
      ((tmulEE (M.tensor N) (pointMod P)).flip a)
      (fun m n => ?_) (fun m n => ?_)) t
    · change superVectMuEvenRaw P M N (baseNuFee P M N m n a) = _
      rw [baseNuFee_apply, map_smul]
      change a.down • (pointBaseMu P M N).evenMap
        (tmulEE (M.tensor (pointMod P)) (N.tensor (pointMod P))
          (tmulEE M (pointMod P) m (pointOne P))
          (tmulEE N (pointMod P) n (pointOne P))) = _
      rw [pointBaseMu_evenMap_ee, pointOne_mul_self, ← map_smul]
      exact congrArg _ (pointEven_eq_smul_one P a).symm
    · change superVectMuEvenRaw P M N (baseNuFoo P M N m n a) = _
      rw [baseNuFoo_apply, map_smul]
      change a.down • (pointBaseMu P M N).evenMap
        (tmulOO (M.tensor (pointMod P)) (N.tensor (pointMod P))
          (tmulOE M (pointMod P) m (pointOne P))
          (tmulOE N (pointMod P) n (pointOne P))) = _
      rw [pointBaseMu_evenMap_oo, pointOne_mul_self, ← map_smul]
      exact congrArg _ (pointEven_eq_smul_one P a).symm
  · rw [pointMod_odd_eq_zero P v, map_zero]
    change superVectMuEvenRaw P M N (baseNuEven P M N 0) = 0
    rw [map_zero, map_zero]

/-- **The comparison undoes the inverse**, in odd degree. -/
theorem superVectMuOddRaw_baseNuOdd (w : ((M.tensor N).tensor (pointMod P) :
      S.Mod.{u, u, u, u}).odd) :
    superVectMuOddRaw P M N (baseNuOdd P M N w) = w := by
  refine LinearMap.congr_fun (liftOdd_unique (M.tensor N)
    (pointMod P) ((superVectMuOddRaw P M N).comp
      (baseNuOdd P M N)) LinearMap.id (fun t v => ?_)
    (fun t a => ?_)) w
  · rw [pointMod_odd_eq_zero P v, map_zero]
    change superVectMuOddRaw P M N (baseNuOdd P M N 0) = 0
    rw [map_zero, map_zero]
  · change superVectMuOddRaw P M N
        (baseNuOdd P M N (tmulOE (M.tensor N) (pointMod P) t a))
      = tmulOE (M.tensor N) (pointMod P) t a
    rw [baseNuOdd_tmulOE]
    refine LinearMap.congr_fun (liftOdd_unique M N
      ((superVectMuOddRaw P M N).comp
        ((baseNuInnerOdd P M N).flip a))
      ((tmulOE (M.tensor N) (pointMod P)).flip a)
      (fun m n => ?_) (fun m n => ?_)) t
    · change superVectMuOddRaw P M N (baseNuFeo P M N m n a) = _
      rw [baseNuFeo_apply, map_smul]
      change a.down • (pointBaseMu P M N).oddMap
        (tmulEO (M.tensor (pointMod P)) (N.tensor (pointMod P))
          (tmulEE M (pointMod P) m (pointOne P))
          (tmulOE N (pointMod P) n (pointOne P))) = _
      rw [pointBaseMu_oddMap_eo, pointOne_mul_self, ← map_smul]
      exact congrArg _ (pointEven_eq_smul_one P a).symm
    · change superVectMuOddRaw P M N (baseNuFoe P M N m n a) = _
      rw [baseNuFoe_apply, map_smul]
      change a.down • (pointBaseMu P M N).oddMap
        (tmulOE (M.tensor (pointMod P)) (N.tensor (pointMod P))
          (tmulOE M (pointMod P) m (pointOne P))
          (tmulEE N (pointMod P) n (pointOne P))) = _
      rw [pointBaseMu_oddMap_oe, pointOne_mul_self, ← map_smul]
      exact congrArg _ (pointEven_eq_smul_one P a).symm

/-- A scaled pure tensor in the first summand of a pair. -/
theorem smulPairInl {X Y Z : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (c d : ℂ) (x : X) (y : Y) :
    (c * d) • ((x ⊗ₜ[ℂ] y, (0 : Z))) =
      ((c • x) ⊗ₜ[ℂ] (d • y), (0 : Z)) := by
  have h : (c • x) ⊗ₜ[ℂ] (d • y) = (c * d) • (x ⊗ₜ[ℂ] y) := by
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      smul_smul, mul_comm]
  rw [h, Prod.smul_mk, smul_zero]

/-- A scaled pure tensor in the second summand of a pair. -/
theorem smulPairInr {X Y Z : Type*} [AddCommGroup X] [Module ℂ X]
    [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]
    (c d : ℂ) (x : X) (y : Y) :
    (c * d) • (((0 : Z), x ⊗ₜ[ℂ] y)) =
      ((0 : Z), (c • x) ⊗ₜ[ℂ] (d • y)) := by
  have h : (c • x) ⊗ₜ[ℂ] (d • y) = (c * d) • (x ⊗ₜ[ℂ] y) := by
    rw [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul',
      smul_smul, mul_comm]
  rw [h, Prod.smul_mk, smul_zero]

/-! ### The inverse undoes the comparison -/

/-- The even-even half of the inverse identity. -/
theorem baseNuEven_muRaw_inl :
    LinearMap.compr₂
        (LinearMap.compr₂ (TensorProduct.mk ℂ
            (M.tensor (pointMod P)).even
            (N.tensor (pointMod P)).even) (LinearMap.inl ℂ _ _))
        ((baseNuEven P M N).comp (superVectMuEvenRaw P M N)) =
      LinearMap.compr₂ (TensorProduct.mk ℂ
        (M.tensor (pointMod P)).even
        (N.tensor (pointMod P)).even) (LinearMap.inl ℂ _ _) := by
  refine liftEven_unique M (pointMod P) _ _ (fun m a => ?_)
    (fun m v => ?_)
  · refine liftEven_unique N (pointMod P) _ _ (fun n b => ?_)
      (fun n w => ?_)
    · change baseNuEven P M N ((pointBaseMu P M N).evenMap
        (gradedTensorEven (M.tensor (pointMod P))
          (N.tensor (pointMod P))
          (tmulEE M (pointMod P) m a ⊗ₜ[ℂ]
            tmulEE N (pointMod P) n b, 0))) = _
      rw [gradedTensorEven_ee, pointBaseMu_evenMap_ee]
      erw [baseNuEven_tmulEE, baseNuInnerEven_tmulEE, baseNuFee_apply]
      change (a.down * b.down) • _ = _
      rw [tmulEE_point_eq_smul P m a, tmulEE_point_eq_smul P n b]
      exact smulPairInl _ _ _ _
    · rw [pointMod_odd_eq_zero P w, map_zero, map_zero, map_zero]
  · rw [pointMod_odd_eq_zero P v, map_zero, map_zero, map_zero]

/-- The odd-odd half of the inverse identity in even degree. -/
theorem baseNuEven_muRaw_inr :
    LinearMap.compr₂
        (LinearMap.compr₂ (TensorProduct.mk ℂ
            (M.tensor (pointMod P)).odd
            (N.tensor (pointMod P)).odd) (LinearMap.inr ℂ _ _))
        ((baseNuEven P M N).comp (superVectMuEvenRaw P M N)) =
      LinearMap.compr₂ (TensorProduct.mk ℂ
        (M.tensor (pointMod P)).odd
        (N.tensor (pointMod P)).odd) (LinearMap.inr ℂ _ _) := by
  refine liftOdd_unique M (pointMod P) _ _ (fun m v => ?_)
    (fun m a => ?_)
  · rw [pointMod_odd_eq_zero P v, map_zero, map_zero, map_zero]
  · refine liftOdd_unique N (pointMod P) _ _ (fun n w => ?_)
      (fun n b => ?_)
    · rw [pointMod_odd_eq_zero P w, map_zero, map_zero, map_zero]
    · change baseNuEven P M N ((pointBaseMu P M N).evenMap
        (gradedTensorEven (M.tensor (pointMod P))
          (N.tensor (pointMod P))
          (0, tmulOE M (pointMod P) m a ⊗ₜ[ℂ]
            tmulOE N (pointMod P) n b))) = _
      rw [gradedTensorEven_oo, pointBaseMu_evenMap_oo]
      erw [baseNuEven_tmulEE, baseNuInnerEven_tmulOO, baseNuFoo_apply]
      change (a.down * b.down) • _ = _
      rw [tmulOE_point_eq_smul P m a, tmulOE_point_eq_smul P n b]
      exact smulPairInr _ _ _ _

/-- The even-odd half of the inverse identity in odd degree. -/
theorem baseNuOdd_muRaw_inl :
    LinearMap.compr₂
        (LinearMap.compr₂ (TensorProduct.mk ℂ
            (M.tensor (pointMod P)).even
            (N.tensor (pointMod P)).odd) (LinearMap.inl ℂ _ _))
        ((baseNuOdd P M N).comp (superVectMuOddRaw P M N)) =
      LinearMap.compr₂ (TensorProduct.mk ℂ
        (M.tensor (pointMod P)).even
        (N.tensor (pointMod P)).odd) (LinearMap.inl ℂ _ _) := by
  refine liftEven_unique M (pointMod P) _ _ (fun m a => ?_)
    (fun m v => ?_)
  · refine liftOdd_unique N (pointMod P) _ _ (fun n w => ?_)
      (fun n b => ?_)
    · rw [pointMod_odd_eq_zero P w, map_zero, map_zero, map_zero]
    · change baseNuOdd P M N ((pointBaseMu P M N).oddMap
        (gradedTensorOdd (M.tensor (pointMod P))
          (N.tensor (pointMod P))
          (tmulEE M (pointMod P) m a ⊗ₜ[ℂ]
            tmulOE N (pointMod P) n b, 0))) = _
      rw [gradedTensorOdd_eo, pointBaseMu_oddMap_eo]
      erw [baseNuOdd_tmulOE, baseNuInnerOdd_tmulEO, baseNuFeo_apply]
      change (a.down * b.down) • _ = _
      rw [tmulEE_point_eq_smul P m a, tmulOE_point_eq_smul P n b]
      exact smulPairInl _ _ _ _
  · rw [pointMod_odd_eq_zero P v, map_zero, map_zero, map_zero]

/-- The odd-even half of the inverse identity in odd degree. -/
theorem baseNuOdd_muRaw_inr :
    LinearMap.compr₂
        (LinearMap.compr₂ (TensorProduct.mk ℂ
            (M.tensor (pointMod P)).odd
            (N.tensor (pointMod P)).even) (LinearMap.inr ℂ _ _))
        ((baseNuOdd P M N).comp (superVectMuOddRaw P M N)) =
      LinearMap.compr₂ (TensorProduct.mk ℂ
        (M.tensor (pointMod P)).odd
        (N.tensor (pointMod P)).even) (LinearMap.inr ℂ _ _) := by
  refine liftOdd_unique M (pointMod P) _ _ (fun m v => ?_)
    (fun m a => ?_)
  · rw [pointMod_odd_eq_zero P v, map_zero, map_zero, map_zero]
  · refine liftEven_unique N (pointMod P) _ _ (fun n b => ?_)
      (fun n w => ?_)
    · change baseNuOdd P M N ((pointBaseMu P M N).oddMap
        (gradedTensorOdd (M.tensor (pointMod P))
          (N.tensor (pointMod P))
          (0, tmulOE M (pointMod P) m a ⊗ₜ[ℂ]
            tmulEE N (pointMod P) n b))) = _
      rw [gradedTensorOdd_oe, pointBaseMu_oddMap_oe]
      erw [baseNuOdd_tmulOE, baseNuInnerOdd_tmulOE, baseNuFoe_apply]
      change (a.down * b.down) • _ = _
      rw [tmulOE_point_eq_smul P m a, tmulEE_point_eq_smul P n b]
      exact smulPairInr _ _ _ _
    · rw [pointMod_odd_eq_zero P w, map_zero, map_zero, map_zero]

/-- **The inverse undoes the comparison**, in even degree. -/
theorem baseNuEven_superVectMuEvenRaw (z : basePairEven P M N) :
    baseNuEven P M N (superVectMuEvenRaw P M N z) = z := by
  have h : (baseNuEven P M N).comp (superVectMuEvenRaw P M N)
      = LinearMap.id := by
    refine LinearMap.prod_ext ?_ ?_
    · exact TensorProduct.ext' fun x y => LinearMap.congr_fun
        (LinearMap.congr_fun (baseNuEven_muRaw_inl P M N) x) y
    · exact TensorProduct.ext' fun x y => LinearMap.congr_fun
        (LinearMap.congr_fun (baseNuEven_muRaw_inr P M N) x) y
  exact LinearMap.congr_fun h z

/-- **The inverse undoes the comparison**, in odd degree. -/
theorem baseNuOdd_superVectMuOddRaw (z : basePairOdd P M N) :
    baseNuOdd P M N (superVectMuOddRaw P M N z) = z := by
  have h : (baseNuOdd P M N).comp (superVectMuOddRaw P M N)
      = LinearMap.id := by
    refine LinearMap.prod_ext ?_ ?_
    · exact TensorProduct.ext' fun x y => LinearMap.congr_fun
        (LinearMap.congr_fun (baseNuOdd_muRaw_inl P M N) x) y
    · exact TensorProduct.ext' fun x y => LinearMap.congr_fun
        (LinearMap.congr_fun (baseNuOdd_muRaw_inr P M N) x) y
  exact LinearMap.congr_fun h z

end Invertible

/-! ## The comparison is an isomorphism -/

section MuIso

open scoped TensorProduct

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)

/-- **A morphism of super vector spaces with bijective components
is an isomorphism.** -/
noncomputable def SuperVect.isoOfBijective {V W : SuperVect}
    (f : V ⟶ W) (he : Function.Bijective (f : V.Hom W).evenMap)
    (ho : Function.Bijective (f : V.Hom W).oddMap) : V ≅ W where
  hom := f
  inv :=
    { evenMap := (LinearEquiv.ofBijective
        (f : V.Hom W).evenMap he).symm.toLinearMap
      oddMap := (LinearEquiv.ofBijective
        (f : V.Hom W).oddMap ho).symm.toLinearMap }
  hom_inv_id := SuperVect.hom_ext
    (LinearMap.ext fun x => LinearEquiv.symm_apply_apply
      (LinearEquiv.ofBijective (f : V.Hom W).evenMap he) x)
    (LinearMap.ext fun x => LinearEquiv.symm_apply_apply
      (LinearEquiv.ofBijective (f : V.Hom W).oddMap ho) x)
  inv_hom_id := SuperVect.hom_ext
    (LinearMap.ext fun x => LinearEquiv.apply_symm_apply
      (LinearEquiv.ofBijective (f : V.Hom W).evenMap he) x)
    (LinearMap.ext fun x => LinearEquiv.apply_symm_apply
      (LinearEquiv.ofBijective (f : V.Hom W).oddMap ho) x)

variable (M N : S.Mod.{u, u, u, u})

/-- **The raw comparison is bijective in even degree.** -/
theorem superVectMuEvenRaw_bijective :
    Function.Bijective (superVectMuEvenRaw P M N) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨baseNuEven P M N, baseNuEven_superVectMuEvenRaw P M N,
      superVectMuEvenRaw_baseNuEven P M N⟩

/-- **The raw comparison is bijective in odd degree.** -/
theorem superVectMuOddRaw_bijective :
    Function.Bijective (superVectMuOddRaw P M N) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨baseNuOdd P M N, baseNuOdd_superVectMuOddRaw P M N,
      superVectMuOddRaw_baseNuOdd P M N⟩

/-- The even component of the comparison is bijective. -/
theorem superVectMu_evenMap_bijective
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd] :
    Function.Bijective (superVectMu P M N).evenMap := by
  have h : ⇑(superVectMu P M N).evenMap =
      (⇑(toSuperVectEvenEquiv P (M.tensor N)) ∘
        ⇑(superVectMuEvenRaw P M N)) ∘
        ⇑(superVectPairEvenEquiv P M N).symm := rfl
  rw [h]
  exact Function.Bijective.comp
    (Function.Bijective.comp
      (toSuperVectEvenEquiv P (M.tensor N)).bijective
      (superVectMuEvenRaw_bijective P M N))
    (superVectPairEvenEquiv P M N).symm.bijective

/-- The odd component of the comparison is bijective. -/
theorem superVectMu_oddMap_bijective
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd] :
    Function.Bijective (superVectMu P M N).oddMap := by
  have h : ⇑(superVectMu P M N).oddMap =
      (⇑(toSuperVectOddEquiv P (M.tensor N)) ∘
        ⇑(superVectMuOddRaw P M N)) ∘
        ⇑(superVectPairOddEquiv P M N).symm := rfl
  rw [h]
  exact Function.Bijective.comp
    (Function.Bijective.comp
      (toSuperVectOddEquiv P (M.tensor N)).bijective
      (superVectMuOddRaw_bijective P M N))
    (superVectPairOddEquiv P M N).symm.bijective

/-- **The monoidal comparison is an isomorphism of super vector
spaces**: base change at a complex point is strong, not merely
lax. -/
noncomputable def superVectMuIso
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd] :
    toSuperVect P M ⊗ toSuperVect P N ≅ toSuperVect P (M.tensor N) :=
  SuperVect.isoOfBijective (superVectMu P M N)
    (superVectMu_evenMap_bijective P M N)
    (superVectMu_oddMap_bijective P M N)

/-- **The monoidal comparison is invertible.** -/
instance isIso_superVectMu [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd] :
    IsIso (superVectMu P M N) :=
  (superVectMuIso P M N).isIso_hom

end MuIso

section SuperVectUnit

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)

/-- **The unit comparison of the fibre functor**, before the
coordinates are installed: a complex number is scaled into the
algebra and pushed into the base change. -/
noncomputable def superVectEpsRaw :
    ℂ →ₗ[ℂ] ((S.unitMod : S.Mod.{u, u, u, u}).tensor
      (pointMod P)).even :=
  (pointBaseEps P).evenMap ∘ₗ
    LinearMap.toSpanSingleton ℂ S.even S.one

/-- **The unit comparison of the fibre functor**: the unit super
vector space maps to the base change of the unit module. -/
noncomputable def superVectEps
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd] :
    𝟙_ SuperVect ⟶ toSuperVect P (S.unitMod : S.Mod.{u, u, u, u}) where
  evenMap :=
    LinearMap.comp
      (toSuperVectEvenEquiv P
        (S.unitMod : S.Mod.{u, u, u, u})).toLinearMap
      (superVectEpsRaw P)
  oddMap := 0

/-- The raw unit comparison, evaluated. -/
theorem superVectEpsRaw_apply (r : ℂ) :
    superVectEpsRaw P r =
      (pointBaseEps P).evenMap
        (LinearMap.toSpanSingleton ℂ S.even S.one r) := rfl

/-- The unit comparison, evaluated. -/
theorem superVectEps_evenMap_apply
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd]
    (r : ℂ) :
    (superVectEps P).evenMap r =
      toSuperVectEvenEquiv P (S.unitMod : S.Mod.{u, u, u, u})
        (superVectEpsRaw P r) := rfl

end SuperVectUnit

/-! ## The unit comparison is an isomorphism -/

section EpsIso

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)

/-- **The unit comparison, read through the left unitor**, is the
canonical copy of a complex number in the residue module. -/
theorem unitTensorPoint_superVectEpsRaw (c : ℂ) :
    (unitTensorPoint P).hom.evenMap (superVectEpsRaw P c) =
      ULift.up c := by
  have h1 : (pointBaseEps P).evenMap (c • S.one) =
      tmulEE (S.unitMod : S.Mod.{u, u, u, u}) (pointMod P)
        (c • S.one) (pointOne P) := by
    change (SuperCommAlgebra.Mod.tensorHom (𝟙 S.unitMod)
        (pointUnitHom P)).evenMap
      ((rightUnitorInv (S.unitMod : S.Mod.{u, u, u, u})).evenMap
        (c • S.one)) = _
    rw [rightUnitorInv_evenMap, tensorHom_evenMap_tmulEE,
      pointUnitHom_evenMap]
    change tmulEE (S.unitMod : S.Mod.{u, u, u, u}) (pointMod P)
      (LinearMap.id (c • S.one)) (ULift.up (P.chi 1)) = _
    rw [map_one]
    rfl
  change (leftUnitorHom (pointMod P)).evenMap
    ((pointBaseEps P).evenMap (c • S.one)) = _
  rw [h1, leftUnitorHom_evenMap_tmulEE]
  refine ULift.ext _ _ ?_
  change P.chi (c • S.one) * 1 = c
  rw [mul_one, map_smul]
  change c * P.chi 1 = c
  rw [map_one, mul_one]

/-- **The raw unit comparison is bijective.** -/
theorem superVectEpsRaw_bijective :
    Function.Bijective (superVectEpsRaw P) := by
  rw [← Function.Bijective.of_comp_iff'
    (evenEquiv (unitTensorPoint P)).bijective (superVectEpsRaw P)]
  have h : ⇑(evenEquiv (unitTensorPoint P)) ∘ ⇑(superVectEpsRaw P) =
      (ULift.up : ℂ → ULift.{u} ℂ) :=
    funext fun c => unitTensorPoint_superVectEpsRaw P c
  rw [h]
  exact (Equiv.ulift (α := ℂ)).symm.bijective

/-- The odd part of the base change of the unit module vanishes. -/
instance subsingleton_unitMod_tensor_point_odd :
    Subsingleton ((S.unitMod : S.Mod.{u, u, u, u}).tensor
      (pointMod P)).odd :=
  (oddEquiv (unitTensorPoint P)).toEquiv.subsingleton

section EpsIsoSuper

/-- The odd part of the fibre of the unit module vanishes. -/
instance subsingleton_toSuperVect_unitMod_odd
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd] :
    Subsingleton
      (toSuperVect P (S.unitMod : S.Mod.{u, u, u, u})).odd :=
  (toSuperVectOddEquiv P
    (S.unitMod : S.Mod.{u, u, u, u})).symm.toEquiv.subsingleton

/-- The even component of the unit comparison is bijective. -/
theorem superVectEps_evenMap_bijective
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd] :
    Function.Bijective (superVectEps P).evenMap := by
  have h : ⇑(superVectEps P).evenMap =
      ⇑(toSuperVectEvenEquiv P (S.unitMod : S.Mod.{u, u, u, u})) ∘
        ⇑(superVectEpsRaw P) := rfl
  rw [h]
  exact Function.Bijective.comp
    (toSuperVectEvenEquiv P
      (S.unitMod : S.Mod.{u, u, u, u})).bijective
    (superVectEpsRaw_bijective P)

/-- The odd component of the unit comparison is bijective: both
sides vanish. -/
theorem superVectEps_oddMap_bijective
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd] :
    Function.Bijective (superVectEps P).oddMap := by
  have : Subsingleton (𝟙_ SuperVect).odd :=
    (inferInstance : Subsingleton PUnit.{1})
  exact ⟨fun _ _ _ => Subsingleton.elim _ _,
    fun y => ⟨0, Subsingleton.elim _ y⟩⟩

/-- **The unit comparison is an isomorphism of super vector
spaces.** -/
noncomputable def superVectEpsIso
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd] :
    𝟙_ SuperVect ≅ toSuperVect P (S.unitMod : S.Mod.{u, u, u, u}) :=
  SuperVect.isoOfBijective (superVectEps P)
    (superVectEps_evenMap_bijective P)
    (superVectEps_oddMap_bijective P)

/-- **The unit comparison is invertible.** -/
instance isIso_superVectEps
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd] : IsIso (superVectEps P) :=
  (superVectEpsIso P).isIso_hom

end EpsIsoSuper

end EpsIso

/-! ## Unitality of the comparison -/

section SuperVectUnitality

open scoped TensorProduct

attribute [local irreducible] superVectMu

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)
  (M : S.Mod.{u, u, u, u})

/-- **Left unitality of the monoidal comparison.** -/
theorem superVectMu_left_unitality
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd]
    [FiniteDimensional ℂ (((S.unitMod : S.Mod.{u, u, u, u}).tensor M).tensor
      (pointMod P)).even]
    [FiniteDimensional ℂ (((S.unitMod : S.Mod.{u, u, u, u}).tensor M).tensor
      (pointMod P)).odd] :
    (λ_ (toSuperVect P M)).hom =
      (superVectEps P ▷ toSuperVect P M) ≫
        superVectMu P S.unitMod M ≫
        superVectHom P (λ_ M).hom := by
  have : Subsingleton (𝟙_ SuperVect).odd :=
    (inferInstance : Subsingleton PUnit.{1})
  refine SuperVect.hom_ext
    (superVectPairEven_ext (fun r x => ?_) (fun u y => ?_))
    (superVectPairOdd_ext (fun r y => ?_) (fun u x => ?_))
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_left_unitality P M))
      (tmulEE (S.unitMod : S.Mod.{u, u, u, u})
        (M.tensor (pointMod P)) (LinearMap.toSpanSingleton ℂ S.even S.one r)
        ((toSuperVectEvenEquiv P M).symm x))
    simp only [modComp_evenMap_apply] at key
    rw [modLeftUnitor_hom, leftUnitorHom_evenMap_tmulEE,
      whiskerRight_evenMap_tmulEE, actEE_span_one] at key
    simp only [svComp_evenMap_apply]
    rw [svLeftUnitor_evenMap_inl, svWhiskerRight_evenMap_inl,
      superVectEps_evenMap_apply, superVectMu_evenMap_ee,
      LinearEquiv.symm_apply_apply, superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply, superVectEpsRaw_apply, ← key,
      map_smul, LinearEquiv.apply_symm_apply]
  · rw [Subsingleton.elim u 0, TensorProduct.zero_tmul,
      svEvenInr_zero, map_zero, map_zero]
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_left_unitality P M))
      (tmulEO (S.unitMod : S.Mod.{u, u, u, u})
        (M.tensor (pointMod P)) (LinearMap.toSpanSingleton ℂ S.even S.one r)
        ((toSuperVectOddEquiv P M).symm y))
    simp only [modComp_oddMap_apply] at key
    rw [modLeftUnitor_hom, leftUnitorHom_oddMap_tmulEO,
      whiskerRight_oddMap_tmulEO, actEO_span_one] at key
    simp only [svComp_oddMap_apply]
    rw [svLeftUnitor_oddMap_inl, svWhiskerRight_oddMap_inl,
      superVectEps_evenMap_apply, superVectMu_oddMap_eo,
      LinearEquiv.symm_apply_apply, superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply, superVectEpsRaw_apply, ← key,
      map_smul, LinearEquiv.apply_symm_apply]
  · rw [Subsingleton.elim u 0, TensorProduct.zero_tmul,
      svOddInr_zero, map_zero, map_zero]

/-- **Right unitality of the monoidal comparison.** -/
theorem superVectMu_right_unitality
    [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).even]
    [FiniteDimensional ℂ ((S.unitMod : S.Mod.{u, u, u, u}).tensor (pointMod
      P)).odd]
    [FiniteDimensional ℂ ((M.tensor (S.unitMod : S.Mod.{u, u, u, u})).tensor
      (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor (S.unitMod : S.Mod.{u, u, u, u})).tensor
      (pointMod P)).odd] :
    (ρ_ (toSuperVect P M)).hom =
      (toSuperVect P M ◁ superVectEps P) ≫
        superVectMu P M S.unitMod ≫
        superVectHom P (ρ_ M).hom := by
  have : Subsingleton (𝟙_ SuperVect).odd :=
    (inferInstance : Subsingleton PUnit.{1})
  refine SuperVect.hom_ext
    (superVectPairEven_ext (fun x r => ?_) (fun y u => ?_))
    (superVectPairOdd_ext (fun x u => ?_) (fun y r => ?_))
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_right_unitality P M))
      (tmulEE (M.tensor (pointMod P))
        (S.unitMod : S.Mod.{u, u, u, u})
        ((toSuperVectEvenEquiv P M).symm x)
        (LinearMap.toSpanSingleton ℂ S.even S.one r))
    simp only [modComp_evenMap_apply] at key
    rw [modRightUnitor_hom, rightUnitorHom_evenMap_tmulEE,
      whiskerLeft_evenMap_tmulEE, actEE_span_one] at key
    simp only [svComp_evenMap_apply]
    rw [svRightUnitor_evenMap_inl, svWhiskerLeft_evenMap_inl,
      superVectEps_evenMap_apply, superVectMu_evenMap_ee,
      LinearEquiv.symm_apply_apply, superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply, superVectEpsRaw_apply, ← key,
      map_smul, LinearEquiv.apply_symm_apply]
  · rw [Subsingleton.elim u 0, TensorProduct.tmul_zero,
      svEvenInr_zero, map_zero, map_zero]
  · rw [Subsingleton.elim u 0, TensorProduct.tmul_zero,
      svOddInl_zero, map_zero, map_zero]
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap
      (pointBaseMu_right_unitality P M))
      (tmulOE (M.tensor (pointMod P))
        (S.unitMod : S.Mod.{u, u, u, u})
        ((toSuperVectOddEquiv P M).symm y)
        (LinearMap.toSpanSingleton ℂ S.even S.one r))
    simp only [modComp_oddMap_apply] at key
    rw [modRightUnitor_hom, rightUnitorHom_oddMap_tmulOE,
      whiskerLeft_oddMap_tmulOE, actEO_span_one] at key
    simp only [svComp_oddMap_apply]
    rw [svRightUnitor_oddMap_inr, svWhiskerLeft_oddMap_inr,
      superVectEps_evenMap_apply, superVectMu_oddMap_oe,
      LinearEquiv.symm_apply_apply, superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply, superVectEpsRaw_apply, ← key,
      map_smul, LinearEquiv.apply_symm_apply]

end SuperVectUnitality
/-! ## Naturality of the comparison -/

section RawNaturality

open scoped TensorProduct

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)
  {M M' N N' : S.Mod.{u, u, u, u}}

/-- **The raw comparison is natural** in both variables, in even
degree. -/
theorem superVectMuEvenRaw_naturality (f : M ⟶ M') (g : N ⟶ N') :
    (SuperCommAlgebra.Mod.tensorHom
        (SuperCommAlgebra.Mod.tensorHom f g)
        (𝟙 (pointMod P))).evenMap.comp
        (superVectMuEvenRaw P M N) =
      (superVectMuEvenRaw P M' N').comp
        (LinearMap.prodMap
          (TensorProduct.map (SuperCommAlgebra.Mod.tensorHom f
              (𝟙 (pointMod P))).evenMap
            (SuperCommAlgebra.Mod.tensorHom g
              (𝟙 (pointMod P))).evenMap)
          (TensorProduct.map (SuperCommAlgebra.Mod.tensorHom f
              (𝟙 (pointMod P))).oddMap
            (SuperCommAlgebra.Mod.tensorHom g
              (𝟙 (pointMod P))).oddMap)) := by
  refine LinearMap.ext fun z => Eq.trans
    (LinearMap.congr_fun (congrArg SuperCommAlgebra.Mod.Hom.evenMap
      (pointBaseMu_naturality P f g)) _).symm ?_
  exact congrArg (pointBaseMu P M' N').evenMap
    (LinearMap.congr_fun (gradedTensorEven_naturality
      (M.tensor (pointMod P)) (N.tensor (pointMod P))
      (SuperCommAlgebra.Mod.tensorHom f (𝟙 (pointMod P)))
      (SuperCommAlgebra.Mod.tensorHom g (𝟙 (pointMod P)))) z)

end RawNaturality

/-! ## The comparison intertwines the braidings -/

section SuperVectBraiding

open scoped TensorProduct

attribute [local irreducible] superVectMu

variable {S : SuperCommAlgebra.{u, u}} (P : SuperPoint S)
  (M N : S.Mod.{u, u, u, u})

/-- **The monoidal comparison intertwines the braidings**: the
Koszul sign of the super vector spaces is the sign of the braiding
of the super modules. -/
@[reassoc]
theorem superVectMu_braiding [FiniteDimensional ℂ (M.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (M.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).even]
    [FiniteDimensional ℂ (N.tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((M.tensor N).tensor (pointMod P)).odd]
    [FiniteDimensional ℂ ((N.tensor M).tensor (pointMod P)).even]
    [FiniteDimensional ℂ ((N.tensor M).tensor (pointMod P)).odd] :
    superVectMu P M N ≫ superVectHom P (β_ M N).hom =
      (β_ (toSuperVect P M) (toSuperVect P N)).hom ≫
        superVectMu P N M := by
  refine SuperVect.hom_ext
    (superVectPairEven_ext (fun x y => ?_) (fun x y => ?_))
    (superVectPairOdd_ext (fun x y => ?_) (fun x y => ?_))
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap (pointBaseMu_braiding P M N))
      (tmulEE (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectEvenEquiv P M).symm x)
        ((toSuperVectEvenEquiv P N).symm y))
    simp only [modComp_evenMap_apply] at key
    rw [modBraiding_hom (M ⊗ pointMod P) (N ⊗ pointMod P),
      braidingHom_evenMap_tmulEE] at key
    simp only [modTensorObj] at key
    simp only [svComp_evenMap_apply]
    rw [superVectMu_evenMap_ee, superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply, svBraiding_evenMap_inl,
      superVectMu_evenMap_ee, key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.evenMap (pointBaseMu_braiding P M N))
      (tmulOO (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectOddEquiv P M).symm x)
        ((toSuperVectOddEquiv P N).symm y))
    simp only [modComp_evenMap_apply] at key
    rw [modBraiding_hom (M ⊗ pointMod P) (N ⊗ pointMod P),
      braidingHom_evenMap_tmulOO, map_neg] at key
    simp only [modTensorObj] at key
    simp only [svComp_evenMap_apply]
    rw [superVectMu_evenMap_oo, superVectHom_evenMap_apply,
      LinearEquiv.symm_apply_apply, svBraiding_evenMap_inr, map_neg,
      superVectMu_evenMap_oo, key, map_neg]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap (pointBaseMu_braiding P M N))
      (tmulEO (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectEvenEquiv P M).symm x)
        ((toSuperVectOddEquiv P N).symm y))
    simp only [modComp_oddMap_apply] at key
    rw [modBraiding_hom (M ⊗ pointMod P) (N ⊗ pointMod P),
      braidingHom_oddMap_tmulEO] at key
    simp only [modTensorObj] at key
    simp only [svComp_oddMap_apply]
    rw [superVectMu_oddMap_eo, superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply, svBraiding_oddMap_inl,
      superVectMu_oddMap_oe, key]
    rfl
  · have key := LinearMap.congr_fun (congrArg
      SuperCommAlgebra.Mod.Hom.oddMap (pointBaseMu_braiding P M N))
      (tmulOE (M ⊗ pointMod P) (N ⊗ pointMod P)
        ((toSuperVectOddEquiv P M).symm x)
        ((toSuperVectEvenEquiv P N).symm y))
    simp only [modComp_oddMap_apply] at key
    rw [modBraiding_hom (M ⊗ pointMod P) (N ⊗ pointMod P),
      braidingHom_oddMap_tmulOE] at key
    simp only [modTensorObj] at key
    simp only [svComp_oddMap_apply]
    rw [superVectMu_oddMap_oe, superVectHom_oddMap_apply,
      LinearEquiv.symm_apply_apply, svBraiding_oddMap_inr,
      superVectMu_oddMap_eo, key]
    rfl

end SuperVectBraiding

end RS
