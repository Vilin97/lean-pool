/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPairRetract
import LeanPool.RegtsSevenster.RS.Classical.Deligne.FreeMixRetract

/-!
# The comparison map on a family of retracts, second variable

The mirror of `RS.isIso_gammaPairComparison_of_retracts`: a finite
family of retracts in the second module variable, total in the same
sense, transports invertibility of the comparison map of Deligne's
(2.11.1) in exactly the same way.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u}}
variable {M N P Q : S.Mod.{u, u, u, u}}

/-- **The tensor product of super modules is additive in the right
variable.** -/
theorem tensorHom_add_right (f : M ⟶ P) (g g' : N ⟶ Q) :
    tensorHom f (g + g') = tensorHom f g + tensorHom f g' := by
  refine hom_ext (fun m n => ?_) (fun m n => ?_) (fun m n => ?_)
    (fun m n => ?_)
  · rw [tensorHom_evenMap_tmulEE, add_evenMap, LinearMap.add_apply,
      map_add, add_evenMap, LinearMap.add_apply,
      tensorHom_evenMap_tmulEE, tensorHom_evenMap_tmulEE]
  · rw [tensorHom_evenMap_tmulOO, add_oddMap, LinearMap.add_apply,
      map_add, add_evenMap, LinearMap.add_apply,
      tensorHom_evenMap_tmulOO, tensorHom_evenMap_tmulOO]
  · rw [tensorHom_oddMap_tmulEO, add_oddMap, LinearMap.add_apply,
      map_add, add_oddMap, LinearMap.add_apply,
      tensorHom_oddMap_tmulEO, tensorHom_oddMap_tmulEO]
  · rw [tensorHom_oddMap_tmulOE, add_evenMap, LinearMap.add_apply,
      map_add, add_oddMap, LinearMap.add_apply,
      tensorHom_oddMap_tmulOE, tensorHom_oddMap_tmulOE]

/-- The tensor product of super modules kills the zero morphism in
the right variable. -/
theorem tensorHom_zero_right (f : M ⟶ P) :
    tensorHom f (0 : N ⟶ Q) = 0 := by
  refine hom_ext (fun m n => ?_) (fun m n => ?_) (fun m n => ?_)
    (fun m n => ?_)
  · rw [tensorHom_evenMap_tmulEE, zero_evenMap,
      LinearMap.zero_apply, map_zero, zero_evenMap,
      LinearMap.zero_apply]
  · rw [tensorHom_evenMap_tmulOO, zero_oddMap,
      LinearMap.zero_apply, map_zero, zero_evenMap,
      LinearMap.zero_apply]
  · rw [tensorHom_oddMap_tmulEO, zero_oddMap, LinearMap.zero_apply,
      map_zero, zero_oddMap, LinearMap.zero_apply]
  · rw [tensorHom_oddMap_tmulOE, zero_evenMap,
      LinearMap.zero_apply, map_zero, zero_oddMap,
      LinearMap.zero_apply]

/-- **The tensor product of super modules takes a finite sum in the
right variable to a finite sum.** -/
theorem tensorHom_sum_right {ι : Type*} (s : Finset ι)
    (f : M ⟶ P) (g : ι → (N ⟶ Q)) :
    tensorHom f (∑ i ∈ s, g i) = ∑ i ∈ s, tensorHom f (g i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, tensorHom_zero_right]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      tensorHom_add_right, ih]

end SuperCommAlgebra.Mod

section

variable {D : Type u}

open SuperCommAlgebra.Mod

/-- The mirror of `RS.sum_modTensorMapMod`, in the second
variable. -/
theorem sum_modTensorMapMod_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R]
    {ι : Type*} (s : Finset ι)
    {M N : Mod D R} (g : ι → (N ⟶ N))
    (h : ∑ i ∈ s, (g i).hom = 𝟙 N.X) :
    ∑ i ∈ s, (modTensorMapMod R (𝟙 M) (g i)).hom =
      𝟙 (modTensorMod R M N).X := by
  apply modTensor_hom_ext
  have hl : modTensorπ R M N ≫
      ∑ i ∈ s, (modTensorMapMod R (𝟙 M) (g i)).hom =
        ∑ i ∈ s, (M.X ◁ (g i).hom) ≫ modTensorπ R M N := by
    erw [Preadditive.comp_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Eq.trans (modTensorπ_map R (𝟙 M) (g i))
      (eq_whisker ?_ _)
    rw [Mod.id_hom']
    exact MonoidalCategory.id_tensorHom _ _
  refine hl.trans ?_
  refine Eq.trans (Preadditive.sum_comp _ _ _).symm ?_
  refine Eq.trans (eq_whisker
    (whiskerLeft_sum M.X s (fun i => (g i).hom)).symm _) ?_
  rw [h, MonoidalCategory.whiskerLeft_id, Category.id_comp]
  exact (Category.comp_id _).symm

/-- **The comparison map on a family of retracts in the second
variable.** -/
theorem isIso_gammaPairComparison_of_retracts_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {ι : Type*}
    [Fintype ι] (M : Mod D R) {N : Mod D R} {N' : ι → Mod D R}
    (s : ∀ i, N' i ⟶ N) (r : ∀ i, N ⟶ N' i)
    (htot : ∑ i : ι, (r i).hom ≫ (s i).hom = 𝟙 N.X)
    (h : ∀ i, IsIso (gammaPairComparison L R M (N' i))) :
    IsIso (gammaPairComparison L R M N) := by
  classical
  haveI := h
  have hnat : ∀ (P P' : Mod D R) (f : P ⟶ P'),
      SuperCommAlgebra.Mod.tensorHom
          (𝟙 (gammaModule D L R M.X)) (gammaFunMap L R f) ≫
        gammaPairComparison L R M P' =
      gammaPairComparison L R M P ≫
        gammaFunMap L R (modTensorMapMod R (𝟙 M) f) := by
    intro P P' f
    have hx := gammaPairComparison_naturality_aux L R (𝟙 M) f
    rw [gammaFunMap_id] at hx
    exact hx
  have hcomp : ∑ i : ι, (r i ≫ s i).hom = 𝟙 N.X :=
    Eq.trans (Finset.sum_congr rfl fun i _ => Mod.comp_hom' (r i)
      (s i)) htot
  have hone : ∑ i : ι, gammaFunMap L R (r i ≫ s i) =
      𝟙 (gammaModule D L R N.X) :=
    sum_gammaModuleFunctor_map L R Finset.univ _ hcomp
  have hsrc : ∑ i : ι,
      (SuperCommAlgebra.Mod.tensorHom
          (𝟙 (gammaModule D L R M.X)) (gammaFunMap L R (r i)) ≫
        SuperCommAlgebra.Mod.tensorHom
          (𝟙 (gammaModule D L R M.X)) (gammaFunMap L R (s i))) =
      𝟙 ((gammaModule D L R M.X).tensor
        (gammaModule D L R N.X)) := by
    have hi : ∀ i : ι,
        SuperCommAlgebra.Mod.tensorHom
            (𝟙 (gammaModule D L R M.X)) (gammaFunMap L R (r i)) ≫
          SuperCommAlgebra.Mod.tensorHom
            (𝟙 (gammaModule D L R M.X)) (gammaFunMap L R (s i)) =
        SuperCommAlgebra.Mod.tensorHom
          (𝟙 (gammaModule D L R M.X))
          (gammaFunMap L R (r i ≫ s i)) := by
      intro i
      refine Eq.trans (SuperCommAlgebra.Mod.tensorHom_comp
        (𝟙 (gammaModule D L R M.X)) (𝟙 (gammaModule D L R M.X))
        (gammaFunMap L R (r i)) (gammaFunMap L R (s i))).symm ?_
      rw [Category.comp_id]
      exact congrArg (fun t => SuperCommAlgebra.Mod.tensorHom
          (𝟙 (gammaModule D L R M.X)) t)
        (CategoryTheory.Functor.map_comp (gammaModuleFunctor L R)
          (r i) (s i)).symm
    refine Eq.trans (Finset.sum_congr rfl fun i _ => hi i) ?_
    refine Eq.trans (SuperCommAlgebra.Mod.tensorHom_sum_right
      Finset.univ _
      (fun i : ι => gammaFunMap L R (r i ≫ s i))).symm ?_
    rw [hone]
    exact SuperCommAlgebra.Mod.tensorHom_id _ _
  have htgt : ∑ i : ι,
      (gammaFunMap L R (modTensorMapMod R (𝟙 M) (r i)) ≫
        gammaFunMap L R (modTensorMapMod R (𝟙 M) (s i))) =
      𝟙 (gammaModule D L R (modTensorMod R M N).X) := by
    have hi : ∀ i : ι,
        gammaFunMap L R (modTensorMapMod R (𝟙 M) (r i)) ≫
          gammaFunMap L R (modTensorMapMod R (𝟙 M) (s i)) =
        gammaFunMap L R
          (modTensorMapMod R (𝟙 M) (r i ≫ s i)) := by
      intro i
      refine Eq.trans (CategoryTheory.Functor.map_comp
        (gammaModuleFunctor L R) _ _).symm ?_
      refine congrArg ((gammaModuleFunctor L R).map) ?_
      rw [← modTensorMapMod_comp', Category.comp_id]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => hi i) ?_
    refine sum_gammaModuleFunctor_map L R Finset.univ _ ?_
    exact sum_modTensorMapMod_right R Finset.univ
      (fun i => r i ≫ s i) hcomp
  refine ⟨∑ i : ι,
    gammaFunMap L R (modTensorMapMod R (𝟙 M) (r i)) ≫
      inv (gammaPairComparison L R M (N' i)) ≫
        SuperCommAlgebra.Mod.tensorHom
          (𝟙 (gammaModule D L R M.X))
          (gammaFunMap L R (s i)), ?_, ?_⟩
  · rw [Preadditive.comp_sum]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) hsrc
    rw [← Category.assoc, ← hnat N (N' i) (r i), Category.assoc,
      IsIso.hom_inv_id_assoc]
  · rw [Preadditive.sum_comp]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) htgt
    rw [Category.assoc, Category.assoc, hnat (N' i) N (s i),
      IsIso.inv_hom_id_assoc]

end

end RS
