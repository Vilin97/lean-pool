/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.GammaModule

/-!
# Morphisms of super modules

A morphism of super modules over a super-commutative algebra is a
pair of ℂ-linear maps, one in each degree, commuting with the
four action blocks.  Postcomposition with a morphism of module
objects realizes one.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits

universe u u'

/-- **A morphism of super modules**: a degreewise ℂ-linear map
commuting with all four actions. -/
@[ext]
structure SuperCommAlgebra.Mod.Hom {S : SuperCommAlgebra}
    (M N : S.Mod) where
  /-- The even component. -/
  evenMap : M.even →ₗ[ℂ] N.even
  /-- The odd component. -/
  oddMap : M.odd →ₗ[ℂ] N.odd
  /-- Compatibility with the even-on-even action. -/
  map_actEE : ∀ x m, evenMap (M.actEE x m) = N.actEE x (evenMap m)
  /-- Compatibility with the even-on-odd action. -/
  map_actEO : ∀ x m, oddMap (M.actEO x m) = N.actEO x (oddMap m)
  /-- Compatibility with the odd-on-even action. -/
  map_actOE : ∀ u m, oddMap (M.actOE u m) = N.actOE u (evenMap m)
  /-- Compatibility with the odd-on-odd action. -/
  map_actOO : ∀ u m, evenMap (M.actOO u m) = N.actOO u (oddMap m)

namespace SuperCommAlgebra.Mod

variable {S : SuperCommAlgebra}

/-- The identity morphism of super modules. -/
def Hom.id (M : S.Mod) : Hom M M where
  evenMap := LinearMap.id
  oddMap := LinearMap.id
  map_actEE _ _ := rfl
  map_actEO _ _ := rfl
  map_actOE _ _ := rfl
  map_actOO _ _ := rfl

/-- Composition of morphisms of super modules. -/
def Hom.comp {M N P : S.Mod} (f : Hom M N) (g : Hom N P) :
    Hom M P where
  evenMap := g.evenMap.comp f.evenMap
  oddMap := g.oddMap.comp f.oddMap
  map_actEE x m := by
    show g.evenMap (f.evenMap _) = _
    rw [f.map_actEE, g.map_actEE]
    rfl
  map_actEO x m := by
    show g.oddMap (f.oddMap _) = _
    rw [f.map_actEO, g.map_actEO]
    rfl
  map_actOE u m := by
    show g.oddMap (f.oddMap _) = _
    rw [f.map_actOE, g.map_actOE]
    rfl
  map_actOO u m := by
    show g.evenMap (f.evenMap _) = _
    rw [f.map_actOO, g.map_actOO]
    rfl

/-- Super modules over a fixed algebra form a category. -/
instance instCategory : Category S.Mod where
  Hom := Hom
  id := Hom.id
  comp f g := Hom.comp f g
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The zero morphism of super modules. -/
instance homZero (M N : S.Mod) : Zero (M ⟶ N) :=
  ⟨{ evenMap := 0
     oddMap := 0
     map_actEE := fun _ _ => by simp
     map_actEO := fun _ _ => by simp
     map_actOE := fun _ _ => by simp
     map_actOO := fun _ _ => by simp }⟩

/-- Addition of morphisms of super modules. -/
instance homAdd (M N : S.Mod) : Add (M ⟶ N) :=
  ⟨fun f g =>
    { evenMap := f.evenMap + g.evenMap
      oddMap := f.oddMap + g.oddMap
      map_actEE := fun x m => by
        simp only [LinearMap.add_apply, map_add]
        rw [f.map_actEE, g.map_actEE]
      map_actEO := fun x m => by
        simp only [LinearMap.add_apply, map_add]
        rw [f.map_actEO, g.map_actEO]
      map_actOE := fun u m => by
        simp only [LinearMap.add_apply, map_add]
        rw [f.map_actOE, g.map_actOE]
      map_actOO := fun u m => by
        simp only [LinearMap.add_apply, map_add]
        rw [f.map_actOO, g.map_actOO] }⟩

/-- Negation of morphisms of super modules. -/
instance homNeg (M N : S.Mod) : Neg (M ⟶ N) :=
  ⟨fun f =>
    { evenMap := -f.evenMap
      oddMap := -f.oddMap
      map_actEE := fun x m => by
        simp only [LinearMap.neg_apply, map_neg]
        rw [f.map_actEE]
      map_actEO := fun x m => by
        simp only [LinearMap.neg_apply, map_neg]
        rw [f.map_actEO]
      map_actOE := fun u m => by
        simp only [LinearMap.neg_apply, map_neg]
        rw [f.map_actOE]
      map_actOO := fun u m => by
        simp only [LinearMap.neg_apply, map_neg]
        rw [f.map_actOO] }⟩

/-- Scaling of morphisms of super modules. -/
instance homSMul (M N : S.Mod) : SMul ℂ (M ⟶ N) :=
  ⟨fun c f =>
    { evenMap := c • f.evenMap
      oddMap := c • f.oddMap
      map_actEE := fun x m => by
        simp only [LinearMap.smul_apply, map_smul]
        rw [f.map_actEE]
      map_actEO := fun x m => by
        simp only [LinearMap.smul_apply, map_smul]
        rw [f.map_actEO]
      map_actOE := fun u m => by
        simp only [LinearMap.smul_apply, map_smul]
        rw [f.map_actOE]
      map_actOO := fun u m => by
        simp only [LinearMap.smul_apply, map_smul]
        rw [f.map_actOO] }⟩

@[simp] theorem add_evenMap {M N : S.Mod} (f g : M ⟶ N) :
    (f + g).evenMap = f.evenMap + g.evenMap := rfl

@[simp] theorem add_oddMap {M N : S.Mod} (f g : M ⟶ N) :
    (f + g).oddMap = f.oddMap + g.oddMap := rfl

@[simp] theorem zero_evenMap {M N : S.Mod} :
    (0 : M ⟶ N).evenMap = 0 := rfl

@[simp] theorem zero_oddMap {M N : S.Mod} :
    (0 : M ⟶ N).oddMap = 0 := rfl

@[simp] theorem neg_evenMap {M N : S.Mod} (f : M ⟶ N) :
    (-f).evenMap = -f.evenMap := rfl

@[simp] theorem neg_oddMap {M N : S.Mod} (f : M ⟶ N) :
    (-f).oddMap = -f.oddMap := rfl

@[simp] theorem smul_evenMap {M N : S.Mod} (c : ℂ) (f : M ⟶ N) :
    (c • f).evenMap = c • f.evenMap := rfl

@[simp] theorem smul_oddMap {M N : S.Mod} (c : ℂ) (f : M ⟶ N) :
    (c • f).oddMap = c • f.oddMap := rfl

/-- Morphisms of super modules form an additive group. -/
instance homAddCommGroup (M N : S.Mod) : AddCommGroup (M ⟶ N) where
  add_assoc f g h := Hom.ext (add_assoc _ _ _) (add_assoc _ _ _)
  zero_add f := Hom.ext (zero_add _) (zero_add _)
  add_zero f := Hom.ext (add_zero _) (add_zero _)
  add_comm f g := Hom.ext (add_comm _ _) (add_comm _ _)
  neg_add_cancel f :=
    Hom.ext (neg_add_cancel _) (neg_add_cancel _)
  nsmul := nsmulRec
  zsmul := zsmulRec

/-- Super modules form a preadditive category. -/
instance instPreadditive : Preadditive S.Mod where
  add_comp _ _ _ f f' g := by
    refine Hom.ext (LinearMap.ext fun x => ?_)
      (LinearMap.ext fun x => ?_)
    · show g.evenMap (f.evenMap x + f'.evenMap x) = _
      exact map_add _ _ _
    · show g.oddMap (f.oddMap x + f'.oddMap x) = _
      exact map_add _ _ _
  comp_add _ _ _ f g g' := Hom.ext rfl rfl

end SuperCommAlgebra.Mod

section Realize

universe v

variable {D : Type u}

/-- The convolution action is natural in the module object. -/
theorem gact_naturality [Category.{v} D] [MonoidalCategory D] (R : D) [MonObj R]
    {M N : D} [ModObj R M] [ModObj R N]
    (f : M ⟶ N) [IsModHom R f] {X Y : D} (a : X ⟶ R)
    (m : Y ⟶ M) :
    gact (R := R) a m ≫ f = gact (R := R) a (m ≫ f) := by
  have hf : actLeft R M ≫ f = (R ◁ f) ≫ actLeft R N :=
    IsModHom.smul_hom
  rw [gact_def, gact_def, Category.assoc, hf, ← Category.assoc,
    ← MonoidalCategory.id_tensorHom,
    MonoidalCategory.tensorHom_comp_tensorHom, Category.comp_id]

/-- **Postcomposition realizes a morphism of super modules.** -/
noncomputable def gammaModuleMap
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D] (L : OddLine D) (R : D) [MonObj R] [IsCommMonObj R]
    {M N : D} [ModObj R M]
    [ModObj R N] (f : M ⟶ N) [IsModHom R f] :
    gammaModule D L R M ⟶ gammaModule D L R N where
  evenMap := Linear.rightComp ℂ _ f
  oddMap := Linear.rightComp ℂ _ f
  map_actEE x m := by
    exact (Category.assoc _ _ _).trans
      (congrArg _ (gact_naturality R f x m))
  map_actEO x m := by
    exact (Category.assoc _ _ _).trans
      (congrArg _ (gact_naturality R f x m))
  map_actOE u m := by
    exact (Category.assoc _ _ _).trans
      (congrArg _ (gact_naturality R f u m))
  map_actOO u m := by
    exact (Category.assoc _ _ _).trans
      (congrArg _ (gact_naturality R f u m))

end Realize

end RS
