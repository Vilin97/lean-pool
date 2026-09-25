/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairNat
import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairAdd

/-!
# The comparison map on a family of retracts

If a module object is presented as a finite family of retracts
whose projectors sum to the identity, and the comparison map of
Deligne's (2.11.1) is invertible on each retract, then it is
invertible on the module object itself.  This is the additivity
step that reduces (2.11.1) on free modules to the two rank-one
cases; it needs no biproducts in the category of module objects,
only the retraction identities and the totality of the projectors.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

section

variable {D : Type u}

open SuperCommAlgebra.Mod

/-- A finite family of endomorphisms of a module object whose
underlying morphisms sum to the identity stays total after
tensoring with a second module object. -/
theorem sum_modTensorMapMod
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R]
    {ι : Type*} (s : Finset ι)
    {M N : Mod D R} (g : ι → (M ⟶ M))
    (h : ∑ i ∈ s, (g i).hom = 𝟙 M.X) :
    ∑ i ∈ s, (modTensorMapMod R (g i) (𝟙 N)).hom =
      𝟙 (modTensorMod R M N).X := by
  apply modTensor_hom_ext
  have hl : modTensorπ R M N ≫
      ∑ i ∈ s, (modTensorMapMod R (g i) (𝟙 N)).hom =
        ∑ i ∈ s, ((g i).hom ▷ N.X) ≫ modTensorπ R M N := by
    erw [Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Eq.trans (modTensorπ_map R (g i) (𝟙 N))
      (eq_whisker ?_ _)
    rw [Mod.id_hom']
    exact MonoidalCategory.tensorHom_id _ _
  refine hl.trans ?_
  refine Eq.trans (Preadditive.sum_comp _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (sum_whiskerRight s (fun i => (g i).hom) N.X).symm _) ?_
  rw [h, MonoidalCategory.id_whiskerRight, Category.id_comp]
  exact (Category.comp_id _).symm

/-- **The comparison map on a family of retracts.** -/
theorem isIso_gammaPairComparison_of_retracts
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {ι : Type*}
    [Fintype ι] {M : Mod D R} {M' : ι → Mod D R} (N : Mod D R)
    (s : ∀ i, M' i ⟶ M) (r : ∀ i, M ⟶ M' i)
    (htot : ∑ i : ι, (r i).hom ≫ (s i).hom = 𝟙 M.X)
    (h : ∀ i, IsIso (gammaPairComparison L R (M' i) N)) :
    IsIso (gammaPairComparison L R M N) := by
  classical
  have := h
  have hnat : ∀ (P P' : Mod D R) (f : P ⟶ P'),
      SuperCommAlgebra.Mod.tensorHom (gammaFunMap L R f)
          (𝟙 (gammaModule D L R N.X)) ≫
        gammaPairComparison L R P' N =
      gammaPairComparison L R P N ≫
        gammaFunMap L R (modTensorMapMod R f (𝟙 N)) := by
    intro P P' f
    have hx := gammaPairComparison_naturality_aux L R f (𝟙 N)
    rw [gammaFunMap_id] at hx
    exact hx
  have hcomp : ∑ i : ι, (r i ≫ s i).hom = 𝟙 M.X :=
    Eq.trans (Finset.sum_congr rfl fun i _ => Mod.comp_hom' (r i)
      (s i)) htot
  have hone : ∑ i : ι, gammaFunMap L R (r i ≫ s i) =
      𝟙 (gammaModule D L R M.X) :=
    sum_gammaModuleFunctor_map L R Finset.univ _ hcomp
  have hsrc : ∑ i : ι,
      (SuperCommAlgebra.Mod.tensorHom (gammaFunMap L R (r i))
          (𝟙 (gammaModule D L R N.X)) ≫
        SuperCommAlgebra.Mod.tensorHom (gammaFunMap L R (s i))
          (𝟙 (gammaModule D L R N.X))) =
      𝟙 ((gammaModule D L R M.X).tensor
        (gammaModule D L R N.X)) := by
    have hi : ∀ i : ι,
        SuperCommAlgebra.Mod.tensorHom (gammaFunMap L R (r i))
            (𝟙 (gammaModule D L R N.X)) ≫
          SuperCommAlgebra.Mod.tensorHom (gammaFunMap L R (s i))
            (𝟙 (gammaModule D L R N.X)) =
        SuperCommAlgebra.Mod.tensorHom
          (gammaFunMap L R (r i ≫ s i))
          (𝟙 (gammaModule D L R N.X)) := by
      intro i
      refine Eq.trans (SuperCommAlgebra.Mod.tensorHom_comp
        (gammaFunMap L R (r i)) (gammaFunMap L R (s i))
        (𝟙 (gammaModule D L R N.X))
        (𝟙 (gammaModule D L R N.X))).symm ?_
      rw [Category.comp_id]
      exact congrArg (fun t => SuperCommAlgebra.Mod.tensorHom t
          (𝟙 (gammaModule D L R N.X)))
        (CategoryTheory.Functor.map_comp (gammaModuleFunctor L R)
          (r i) (s i)).symm
    refine Eq.trans (Finset.sum_congr rfl fun i _ => hi i) ?_
    refine Eq.trans (SuperCommAlgebra.Mod.tensorHom_sum_left
      Finset.univ (fun i : ι => gammaFunMap L R (r i ≫ s i)) _).symm
      ?_
    rw [hone]
    exact SuperCommAlgebra.Mod.tensorHom_id _ _
  have htgt : ∑ i : ι,
      (gammaFunMap L R (modTensorMapMod R (r i) (𝟙 N)) ≫
        gammaFunMap L R (modTensorMapMod R (s i) (𝟙 N))) =
      𝟙 (gammaModule D L R (modTensorMod R M N).X) := by
    have hi : ∀ i : ι,
        gammaFunMap L R (modTensorMapMod R (r i) (𝟙 N)) ≫
          gammaFunMap L R (modTensorMapMod R (s i) (𝟙 N)) =
        gammaFunMap L R
          (modTensorMapMod R (r i ≫ s i) (𝟙 N)) := by
      intro i
      refine Eq.trans (CategoryTheory.Functor.map_comp
        (gammaModuleFunctor L R) _ _).symm ?_
      refine congrArg ((gammaModuleFunctor L R).map) ?_
      rw [← modTensorMapMod_comp', Category.comp_id]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => hi i) ?_
    refine sum_gammaModuleFunctor_map L R Finset.univ _ ?_
    exact sum_modTensorMapMod R Finset.univ (fun i => r i ≫ s i)
      hcomp
  refine ⟨∑ i : ι,
    gammaFunMap L R (modTensorMapMod R (r i) (𝟙 N)) ≫
      inv (gammaPairComparison L R (M' i) N) ≫
        SuperCommAlgebra.Mod.tensorHom (gammaFunMap L R (s i))
          (𝟙 (gammaModule D L R N.X)), ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsrc
    rw [← Category.assoc, ← hnat M (M' i) (r i), Category.assoc,
      IsIso.hom_inv_id_assoc]
  · rw [Preadditive.sum_comp]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) htgt
    rw [Category.assoc, Category.assoc, hnat (M' i) M (s i),
      IsIso.inv_hom_id_assoc]

end

end RS
