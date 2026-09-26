/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModBiprod
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.SuperModIso
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModBiprod

/-!
# Realization of a biproduct of module objects

Morphisms out of the two generators into a biproduct are pairs of
morphisms, and the action on a biproduct is componentwise, so the
realization of a biproduct is the biproduct of the realizations.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

universe v u

variable {D : Type u}

/-- The comparison of the realization of a biproduct with the
biproduct of the realizations. -/
noncomputable def gammaBiprodMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D] [HasBinaryBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] [IsCommMonObj R] (M : Mod D R) (N : Mod D R) :
    gammaModule D L R (modBiprod R M N).X ⟶
      (gammaModule D L R M.X).biprod
        (gammaModule D L R N.X) := by
  haveI : IsModHom R (show (modBiprod R M N).X ⟶ M.X from
      biprod.fst) := (modBiprodFst R M N).isModHom
  haveI : IsModHom R (show (modBiprod R M N).X ⟶ N.X from
      biprod.snd) := (modBiprodSnd R M N).isModHom
  exact
    { evenMap := LinearMap.prod
        (Linear.rightComp ℂ _
          (show (modBiprod R M N).X ⟶ M.X from biprod.fst))
        (Linear.rightComp ℂ _
          (show (modBiprod R M N).X ⟶ N.X from biprod.snd))
      oddMap := LinearMap.prod
        (Linear.rightComp ℂ _
          (show (modBiprod R M N).X ⟶ M.X from biprod.fst))
        (Linear.rightComp ℂ _
          (show (modBiprod R M N).X ⟶ N.X from biprod.snd))
      map_actEE := fun x m => by
        refine Prod.ext ?_ ?_ <;>
          exact (Category.assoc _ _ _).trans
            (congrArg _ (gact_naturality R _ x m))
      map_actEO := fun x m => by
        refine Prod.ext ?_ ?_ <;>
          exact (Category.assoc _ _ _).trans
            (congrArg _ (gact_naturality R _ x m))
      map_actOE := fun u m => by
        refine Prod.ext ?_ ?_ <;>
          exact (Category.assoc _ _ _).trans
            (congrArg _ (gact_naturality R _ u m))
      map_actOO := fun u m => by
        refine Prod.ext ?_ ?_ <;>
          exact (Category.assoc _ _ _).trans
            (congrArg _ (gact_naturality R _ u m)) }

/-- Morphisms into a binary biproduct are pairs, ℂ-linearly. -/
theorem bijective_pair [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (R : D) [MonObj R] (M : Mod D R) (N : Mod D R)
    (P : D) :
    Function.Bijective
      (fun f : P ⟶ M.X ⊞ N.X =>
        ((f ≫ biprod.fst, f ≫ biprod.snd) :
          (P ⟶ M.X) × (P ⟶ N.X))) := by
  constructor
  · intro f g h
    refine biprod.hom_ext _ _ ?_ ?_
    · exact congrArg Prod.fst h
    · exact congrArg Prod.snd h
  · intro p
    refine ⟨biprod.lift p.1 p.2, ?_⟩
    refine Prod.ext ?_ ?_
    · exact biprod.lift_fst _ _
    · exact biprod.lift_snd _ _

/-- **The realization of a biproduct is the biproduct of the
realizations.** -/
noncomputable def gammaBiprodIso
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D] [HasBinaryBiproducts D] (L : OddLine D) (R : D)
    [MonObj R] [IsCommMonObj R] (M : Mod D R) (N : Mod D R) :
    gammaModule D L R (modBiprod R M N).X ≅
      (gammaModule D L R M.X).biprod
        (gammaModule D L R N.X) :=
  SuperCommAlgebra.Mod.isoOfComponents (gammaBiprodMap L R M N)
    (bijective_pair R M N (𝟙_ D)) (bijective_pair R M N L.obj)

end RS
