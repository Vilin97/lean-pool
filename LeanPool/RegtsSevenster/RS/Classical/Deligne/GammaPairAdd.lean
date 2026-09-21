/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaModuleFunctor
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModMonoidal

/-!
# Additivity for the comparison map

The two constructions flanking the comparison map of Deligne's
(2.11.1) are additive: the tensor product of super modules is
additive in each variable, and realization turns a finite sum of
endomorphisms of a module object summing to the identity into a
finite sum of endomorphisms of its realization summing to the
identity.  These are what let a decomposition of a module object
into a finite family of retracts be pushed through the comparison.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra.{u, u}}
variable {M N P Q : S.Mod.{u, u, u, u}}

/-- The even component of a finite sum of morphisms, pointwise. -/
theorem sum_evenMap_apply {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) (m : M.even) :
    (∑ i ∈ s, f i).evenMap m = ∑ i ∈ s, (f i).evenMap m := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_evenMap,
      LinearMap.add_apply, ih]

/-- The odd component of a finite sum of morphisms, pointwise. -/
theorem sum_oddMap_apply {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ N)) (m : M.odd) :
    (∑ i ∈ s, f i).oddMap m = ∑ i ∈ s, (f i).oddMap m := by
  classical
  induction s using Finset.induction with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, add_oddMap,
      LinearMap.add_apply, ih]

/-- **The tensor product of super modules is additive in the left
variable.** -/
theorem tensorHom_add_left (f f' : M ⟶ P) (g : N ⟶ Q) :
    tensorHom (f + f') g = tensorHom f g + tensorHom f' g := by
  refine hom_ext (fun m n => ?_) (fun m n => ?_) (fun m n => ?_)
    (fun m n => ?_)
  · rw [tensorHom_evenMap_tmulEE, add_evenMap, LinearMap.add_apply,
      map_add, LinearMap.add_apply, add_evenMap,
      LinearMap.add_apply, tensorHom_evenMap_tmulEE,
      tensorHom_evenMap_tmulEE]
  · rw [tensorHom_evenMap_tmulOO, add_oddMap, LinearMap.add_apply,
      map_add, LinearMap.add_apply, add_evenMap,
      LinearMap.add_apply, tensorHom_evenMap_tmulOO,
      tensorHom_evenMap_tmulOO]
  · rw [tensorHom_oddMap_tmulEO, add_evenMap, LinearMap.add_apply,
      map_add, LinearMap.add_apply, add_oddMap,
      LinearMap.add_apply, tensorHom_oddMap_tmulEO,
      tensorHom_oddMap_tmulEO]
  · rw [tensorHom_oddMap_tmulOE, add_oddMap, LinearMap.add_apply,
      map_add, LinearMap.add_apply, add_oddMap,
      LinearMap.add_apply, tensorHom_oddMap_tmulOE,
      tensorHom_oddMap_tmulOE]

/-- The tensor product of super modules kills the zero morphism in
the left variable. -/
theorem tensorHom_zero_left (g : N ⟶ Q) :
    tensorHom (0 : M ⟶ P) g = 0 := by
  refine hom_ext (fun m n => ?_) (fun m n => ?_) (fun m n => ?_)
    (fun m n => ?_)
  · rw [tensorHom_evenMap_tmulEE, zero_evenMap, LinearMap.zero_apply,
      map_zero, LinearMap.zero_apply, zero_evenMap,
      LinearMap.zero_apply]
  · rw [tensorHom_evenMap_tmulOO, zero_oddMap, LinearMap.zero_apply,
      map_zero, LinearMap.zero_apply, zero_evenMap,
      LinearMap.zero_apply]
  · rw [tensorHom_oddMap_tmulEO, zero_evenMap, LinearMap.zero_apply,
      map_zero, LinearMap.zero_apply, zero_oddMap,
      LinearMap.zero_apply]
  · rw [tensorHom_oddMap_tmulOE, zero_oddMap, LinearMap.zero_apply,
      map_zero, LinearMap.zero_apply, zero_oddMap,
      LinearMap.zero_apply]

/-- **The tensor product of super modules takes a finite sum in the
left variable to a finite sum.** -/
theorem tensorHom_sum_left {ι : Type*} (s : Finset ι)
    (f : ι → (M ⟶ P)) (g : N ⟶ Q) :
    tensorHom (∑ i ∈ s, f i) g = ∑ i ∈ s, tensorHom (f i) g := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, tensorHom_zero_left]
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      tensorHom_add_left, ih]

end SuperCommAlgebra.Mod

/-! ## Additivity of realization -/

section Realize

variable {D : Type u}

/-- **Realization is additive on endomorphisms**: a finite family
of endomorphisms of a module object whose underlying morphisms sum
to the identity realizes to a family summing to the identity. -/
theorem sum_gammaModuleFunctor_map
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {P : Mod D R} {ι : Type*}
    (s : Finset ι) (g : ι → (P ⟶ P))
    (h : ∑ i ∈ s, (g i).hom = 𝟙 P.X) :
    ∑ i ∈ s, (gammaModuleFunctor L R).map (g i) =
      𝟙 ((gammaModuleFunctor L R).obj P) := by
  refine SuperCommAlgebra.Mod.Hom.ext ?_ ?_ <;>
    refine LinearMap.ext fun m => ?_
  · rw [SuperCommAlgebra.Mod.sum_evenMap_apply]
    show ∑ i ∈ s, m ≫ (g i).hom = m
    erw [← Preadditive.comp_sum, h, Category.comp_id]
  · rw [SuperCommAlgebra.Mod.sum_oddMap_apply]
    show ∑ i ∈ s, m ≫ (g i).hom = m
    erw [← Preadditive.comp_sum, h, Category.comp_id]

end Realize

end RS
