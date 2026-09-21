/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaModuleFunctor
import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaPair
import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModMonoidal

/-!
# Naturality of the comparison map

The comparison map `RS.gammaPairComparison` of Deligne's (2.11.1)
is natural in each of its two module variables: realization
`RS.gammaModuleFunctor` carries a morphism of module objects to a
morphism of Γ-modules, both sides of the comparison map are
functorial in that morphism, and the resulting square commutes.

Everything rests on one identity, `RS.gpair_naturality`: the
ungraded pairing `RS.gpair` of a morphism into `M` against a
morphism into `N` is natural, that is,
`gpair (m ≫ f.hom) (n ≫ g.hom) = gpair m n ≫ modTensorMap R f g`.
This is the defining equation of `RS.modTensorMap` against
`RS.modTensorπ`, read through the interchange law.  Transported
along a source identification it becomes
`RS.gpairLin_naturality`, and the four graded blocks of the
comparison map are four instances of that one statement, one for
each family of generators of the tensor product of super modules.
The extensionality principle `RS.SuperCommAlgebra.Mod.hom_ext`
reduces the naturality square to exactly those four instances.

## Contents

* `RS.gpair_naturality`, `RS.gpairLin_naturality`: naturality of
  the ungraded pairing, plain and transported.
* `RS.modTensorMapMod_id'`, `RS.modTensorMapMod_comp'`,
  `RS.modTensorMapModIso`: functoriality of the bundled relative
  tensor product, and the isomorphism it yields from a pair of
  isomorphisms.
* `RS.SuperCommAlgebra.Mod.tensorIso`: the tensor product of two
  isomorphisms of super modules.
* `RS.gammaPairComparison_naturality_left`,
  `RS.gammaPairComparison_naturality_right`,
  `RS.gammaPairComparison_naturality`: the naturality squares.
* `RS.gammaPairComparison_isIso_of_iso`: whether the comparison
  map is an isomorphism depends only on the isomorphism classes of
  the two module objects.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

/-! ## Naturality of the ungraded pairing -/

section Pairing

variable {D : Type u}

/-- **Naturality of the pairing**: pairing after postcomposition
with a pair of module morphisms is pairing followed by the
functorial map of the relative tensor product. -/
theorem gpair_naturality
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] (R : D) [MonObj R] {M : Mod D R} {M' : Mod D R}
    {N : Mod D R} {N' : Mod D R}
    {X Y : D} (f : M ⟶ M') (g : N ⟶ N')
    (m : X ⟶ M.X) (n : Y ⟶ N.X) :
    gpair (M := M') (N := N') (m ≫ f.hom) (n ≫ g.hom) =
      gpair (M := M) (N := N) m n ≫ modTensorMap R f g := by
  show ((m ≫ f.hom) ⊗ₘ (n ≫ g.hom)) ≫ modTensorπ R M' N' =
    ((m ⊗ₘ n) ≫ modTensorπ R M N) ≫ modTensorMap R f g
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [modTensorπ_map]

/-- **The transported naturality of the pairing**: the form taken
by `RS.gpair_naturality` at a source identification, that is, at
one graded block of the comparison map. -/
theorem gpairLin_naturality
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D] (R : D) [MonObj R] {M : Mod D R} {M' : Mod D R}
    {N : Mod D R} {N' : Mod D R}
    {W X Y : D} (s : W ⟶ X ⊗ Y)
    (f : M ⟶ M') (g : N ⟶ N') (m : X ⟶ M.X) (n : Y ⟶ N.X) :
    s ≫ gpair (M := M') (N := N') (m ≫ f.hom) (n ≫ g.hom) =
      (s ≫ gpair (M := M) (N := N) m n) ≫ modTensorMap R f g := by
  rw [gpair_naturality, Category.assoc]

end Pairing

/-! ## Functoriality of the bundled relative tensor product -/

section BundledFunctoriality

variable {D : Type u}

/-- The bundled functorial map preserves identities. -/
theorem modTensorMapMod_id'
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R]
    (M N : Mod D R) :
    modTensorMapMod R (𝟙 M) (𝟙 N) = 𝟙 (modTensorMod R M N) :=
  Mod.hom_ext _ _ (modTensorMap_id R (M := M) (N := N))

/-- The bundled functorial map preserves composition. -/
theorem modTensorMapMod_comp'
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R] {M : Mod D R} {M' : Mod D R}
    {M'' : Mod D R} {N : Mod D R} {N' : Mod D R} {N'' : Mod D R}
    (f : M ⟶ M') (f' : M' ⟶ M'')
    (g : N ⟶ N') (g' : N' ⟶ N'') :
    modTensorMapMod R (f ≫ f') (g ≫ g') =
      modTensorMapMod R f g ≫ modTensorMapMod R f' g' :=
  Mod.hom_ext _ _ (modTensorMap_comp R f f' g g')

/-- The relative tensor product of two isomorphisms of module
objects. -/
noncomputable def modTensorMapModIso
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (R : D) [MonObj R] [IsCommMonObj R] {M : Mod D R} {M' : Mod D R}
    {N : Mod D R} {N' : Mod D R}
    (e : M ≅ M') (e' : N ≅ N') :
    modTensorMod R M N ≅ modTensorMod R M' N' where
  hom := modTensorMapMod R e.hom e'.hom
  inv := modTensorMapMod R e.inv e'.inv
  hom_inv_id := by
    rw [← modTensorMapMod_comp', e.hom_inv_id, e'.hom_inv_id,
      modTensorMapMod_id']
  inv_hom_id := by
    rw [← modTensorMapMod_comp', e.inv_hom_id, e'.inv_hom_id,
      modTensorMapMod_id']

end BundledFunctoriality

/-! ## Two conveniences for super modules -/

section SuperConveniences

variable {S : SuperCommAlgebra.{v, v}}
variable {P P' Q Q' T : S.Mod.{v, v, v, v}}

/-- The even component of a composite, applied to an element. -/
theorem SuperCommAlgebra.Mod.comp_evenMap_apply (a : P ⟶ Q)
    (b : Q ⟶ T) (t : P.even) :
    (a ≫ b).evenMap t = b.evenMap (a.evenMap t) := rfl

/-- The odd component of a composite, applied to an element. -/
theorem SuperCommAlgebra.Mod.comp_oddMap_apply (a : P ⟶ Q)
    (b : Q ⟶ T) (t : P.odd) :
    (a ≫ b).oddMap t = b.oddMap (a.oddMap t) := rfl

/-- The tensor product of two isomorphisms of super modules. -/
noncomputable def SuperCommAlgebra.Mod.tensorIso (a : P ≅ P')
    (b : Q ≅ Q') : P.tensor Q ≅ P'.tensor Q' where
  hom := SuperCommAlgebra.Mod.tensorHom a.hom b.hom
  inv := SuperCommAlgebra.Mod.tensorHom a.inv b.inv
  hom_inv_id := by
    rw [← SuperCommAlgebra.Mod.tensorHom_comp, a.hom_inv_id,
      b.hom_inv_id, SuperCommAlgebra.Mod.tensorHom_id]
  inv_hom_id := by
    rw [← SuperCommAlgebra.Mod.tensorHom_comp, a.inv_hom_id,
      b.inv_hom_id, SuperCommAlgebra.Mod.tensorHom_id]

end SuperConveniences

/-! ## Naturality of the comparison map -/

section Naturality

variable {D : Type u}

open SuperCommAlgebra.Mod

/-- Realization of a morphism of module objects, with its type
written at the Γ-modules themselves.  This is
`RS.gammaModuleFunctor` on morphisms, and is reducibly equal to
it; naming it keeps the two ends of a naturality square typed by
the same expressions. -/
noncomputable abbrev gammaFunMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {M : Mod D R} {M' : Mod D R}
    (f : M ⟶ M') :
    gammaModule D L R M.X ⟶ gammaModule D L R M'.X :=
  (gammaModuleFunctor L R).map f

/-- Realization takes an identity to an identity. -/
theorem gammaFunMap_id
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (M : Mod D R) :
    gammaFunMap L R (𝟙 M) = 𝟙 (gammaModule D L R M.X) :=
  CategoryTheory.Functor.map_id _ _

@[simp]
theorem gammaPairComparison_evenMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (M N : Mod D R) :
    (gammaPairComparison L R M N).evenMap = gammaPairEven L R M N :=
  rfl

@[simp]
theorem gammaPairComparison_oddMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    (M N : Mod D R) :
    (gammaPairComparison L R M N).oddMap = gammaPairOdd L R M N :=
  rfl

/-- The naturality square, with the realized morphisms typed at
the Γ-modules.  This is `RS.gammaPairComparison_naturality` in the
form in which it is proved. -/
theorem gammaPairComparison_naturality_aux
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {M : Mod D R}
    {M' : Mod D R} {N : Mod D R} {N' : Mod D R}
    (f : M ⟶ M')
    (g : N ⟶ N') :
    SuperCommAlgebra.Mod.tensorHom (gammaFunMap L R f)
        (gammaFunMap L R g) ≫ gammaPairComparison L R M' N' =
      gammaPairComparison L R M N ≫
        gammaFunMap L R (modTensorMapMod R f g) := by
  refine hom_ext (fun m n => ?_) (fun m n => ?_) (fun m n => ?_)
    (fun m n => ?_)
  · simp only [comp_evenMap_apply, gammaPairComparison_evenMap,
      tensorHom_evenMap_tmulEE]
    erw [gammaPairEven_tmulEE, gammaPairEven_tmulEE]
    exact gpairLin_naturality R _ f g m n
  · simp only [comp_evenMap_apply, gammaPairComparison_evenMap,
      tensorHom_evenMap_tmulOO]
    erw [gammaPairEven_tmulOO, gammaPairEven_tmulOO]
    exact gpairLin_naturality R _ f g m n
  · simp only [comp_oddMap_apply, gammaPairComparison_oddMap,
      tensorHom_oddMap_tmulEO]
    erw [gammaPairOdd_tmulEO, gammaPairOdd_tmulEO]
    exact gpairLin_naturality R _ f g m n
  · simp only [comp_oddMap_apply, gammaPairComparison_oddMap,
      tensorHom_oddMap_tmulOE]
    erw [gammaPairOdd_tmulOE, gammaPairOdd_tmulOE]
    exact gpairLin_naturality R _ f g m n

/-- **The naturality square of the comparison map**, in both
module variables at once. -/
theorem gammaPairComparison_naturality
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {M : Mod D R}
    {M' : Mod D R} {N : Mod D R} {N' : Mod D R}
    (f : M ⟶ M') (g : N ⟶ N') :
    SuperCommAlgebra.Mod.tensorHom
        ((gammaModuleFunctor L R).map f)
        ((gammaModuleFunctor L R).map g) ≫
        gammaPairComparison L R M' N' =
      gammaPairComparison L R M N ≫
        (gammaModuleFunctor L R).map (modTensorMapMod R f g) :=
  gammaPairComparison_naturality_aux L R f g

/-- **The naturality square of the comparison map in the first
module variable**. -/
theorem gammaPairComparison_naturality_left
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {M : Mod D R}
    {M' : Mod D R}
    (f : M ⟶ M')
    (N : Mod D R) :
    SuperCommAlgebra.Mod.tensorHom
        ((gammaModuleFunctor L R).map f)
        (𝟙 (gammaModule D L R N.X)) ≫
        gammaPairComparison L R M' N =
      gammaPairComparison L R M N ≫
        (gammaModuleFunctor L R).map
          (modTensorMapMod R f (𝟙 N)) := by
  have h := gammaPairComparison_naturality_aux L R f (𝟙 N)
  rw [gammaFunMap_id] at h
  exact h

/-- **The naturality square of the comparison map in the second
module variable**. -/
theorem gammaPairComparison_naturality_right
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {N : Mod D R}
    {N' : Mod D R}
    (M : Mod D R)
    (g : N ⟶ N') :
    SuperCommAlgebra.Mod.tensorHom
        (𝟙 (gammaModule D L R M.X))
        ((gammaModuleFunctor L R).map g) ≫
        gammaPairComparison L R M N' =
      gammaPairComparison L R M N ≫
        (gammaModuleFunctor L R).map
          (modTensorMapMod R (𝟙 M) g) := by
  have h := gammaPairComparison_naturality_aux L R (𝟙 M) g
  rw [gammaFunMap_id] at h
  exact h

/-- **Invariance of the comparison map under isomorphism**:
whether the comparison map is an isomorphism depends only on the
isomorphism classes of the two module objects. -/
theorem gammaPairComparison_isIso_of_iso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [Linear ℂ D]
    [MonoidalLinear ℂ D] [HasCoequalizers D]
    [∀ X : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
    (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R] {M : Mod D R}
    {M' : Mod D R} {N : Mod D R} {N' : Mod D R}
    (e : M ≅ M') (e' : N ≅ N')
    (h : IsIso (gammaPairComparison L R M' N')) :
    IsIso (gammaPairComparison L R M N) := by
  haveI := h
  haveI : IsIso (gammaFunMap L R (modTensorMapMod R e.hom e'.hom)) :=
    ((gammaModuleFunctor L R).mapIso
      (modTensorMapModIso R e e')).isIso_hom
  haveI : IsIso (SuperCommAlgebra.Mod.tensorHom
      (gammaFunMap L R e.hom) (gammaFunMap L R e'.hom)) :=
    (SuperCommAlgebra.Mod.tensorIso
      ((gammaModuleFunctor L R).mapIso e)
      ((gammaModuleFunctor L R).mapIso e')).isIso_hom
  have key : SuperCommAlgebra.Mod.tensorHom (gammaFunMap L R e.hom)
        (gammaFunMap L R e'.hom) ≫
      gammaPairComparison L R M' N' ≫
        inv (gammaFunMap L R (modTensorMapMod R e.hom e'.hom)) =
      gammaPairComparison L R M N := by
    rw [← Category.assoc,
      gammaPairComparison_naturality_aux L R e.hom e'.hom,
      Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [← key]
  infer_instance

end Naturality

end RS
