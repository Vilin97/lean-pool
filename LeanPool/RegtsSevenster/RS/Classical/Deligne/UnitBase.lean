/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModBiprod

/-!
# Modules over the tensor unit

Over the tensor unit as base algebra, relative module theory
collapses to the ambient category.

* `unitMod`: any object, as a module over the unit through the
  trivial action; the unit law forces the action of any module
  over the unit to be the left unitor (`modObj_unitBase_smul`).
* `modTensorUnitBase`: over the trivial base the two coequalizer
  legs agree, so the module tensor product collapses to the plain
  tensor product of the carriers.
* `freeModUnitBase`: the free module on `V` over the unit is `V`
  itself, via the left unitor.
* `modBiprodZeroLeft`: over any base, the biproduct with a module
  whose carrier is zero collapses to the other summand.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

section UnitModule

/-- Any object, as a module over the tensor unit through the
trivial action. -/
def unitMod [Category.{v} D] [MonoidalCategory D]
    (X : D) : Mod D (𝟙_ D) := ⟨X⟩

@[simp] lemma unitMod_X [Category.{v} D] [MonoidalCategory D]
    (X : D) : (unitMod X).X = X := rfl

/-- Any action of the tensor unit is the left unitor: the unit
law forces it, since the unit of the trivial base is the
identity.  The instance is quantified, so the lemma applies to
the action of any module over the unit, not only the trivial
one. -/
lemma modObj_unitBase_smul
    [Category.{v} D] [MonoidalCategory D] (X : D) [inst : ModObj (𝟙_ D) X] :
    γ[𝟙_ D, X] = (λ_ X).hom := by
  have h := ModObj.one_smul_self (𝟙_ D) X
  rw [MonObj.one_def, MonoidalCategory.id_whiskerRight,
    Category.id_comp] at h
  exact h

/-- The action of any module over the unit, in `actLeft` form. -/
lemma actLeft_unitBase
    [Category.{v} D] [MonoidalCategory D] (X : D) [inst : ModObj (𝟙_ D) X] :
    actLeft (𝟙_ D) X = (λ_ X).hom :=
  modObj_unitBase_smul X

end UnitModule

section TensorUnitBase

/-- The braided right action of any module over the unit is the
right unitor. -/
lemma actRight_unitBase
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (X : D) [inst : ModObj (𝟙_ D) X] :
    actRight (𝟙_ D) X = (ρ_ X).hom := by
  rw [actRight, actLeft_unitBase, braiding_tensorUnit_right]
  simp

/-- Over the trivial base the two coequalizer legs of the module
tensor product are equal morphisms. -/
lemma modTensorLegM_unitBase_eq
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (M : Mod D (𝟙_ D)) (N : Mod D (𝟙_ D)) :
    modTensorLegM (𝟙_ D) M N = modTensorLegN (𝟙_ D) M N := by
  rw [modTensorLegM, modTensorLegN,
    actRight_unitBase M.X (inst := M.mod),
    actLeft_unitBase N.X (inst := N.mod)]
  monoidal

/-- **Over the trivial base the module tensor product is the
plain tensor product**: the coequalizer of a pair of equal legs
is the target itself. -/
@[simps]
noncomputable def modTensorUnitBase
    [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
    (M : Mod D (𝟙_ D)) (N : Mod D (𝟙_ D)) [HasCoequalizers D] :
    modTensor (𝟙_ D) M N ≅ M.X ⊗ N.X where
  hom := modTensorDesc (𝟙_ D) M N (𝟙 (M.X ⊗ N.X))
    (by rw [modTensorLegM_unitBase_eq])
  inv := modTensorπ (𝟙_ D) M N
  hom_inv_id := by
    apply modTensor_hom_ext
    rw [modTensorπ_desc_assoc, Category.id_comp,
      Category.comp_id]
  inv_hom_id := modTensorπ_desc (𝟙_ D) M N _ _

end TensorUnitBase

section FreeUnitBase

/-- The left unitor intertwines the free action over the unit
with the trivial action. -/
theorem freeModUnitBase_linear [Category.{v} D] [MonoidalCategory D] (V : D) :
    ((α_ (𝟙_ D) (𝟙_ D) V).inv ≫ (λ_ (𝟙_ D)).hom ▷ V) ≫
        (λ_ V).hom =
      (𝟙_ D) ◁ (λ_ V).hom ≫ (λ_ V).hom := by
  monoidal

/-- The left unitor intertwines the trivial action with the free
action over the unit. -/
theorem freeModUnitBase_linear_inv
    [Category.{v} D] [MonoidalCategory D] (V : D) :
    (λ_ V).hom ≫ (λ_ V).inv =
      (𝟙_ D) ◁ (λ_ V).inv ≫
        ((α_ (𝟙_ D) (𝟙_ D) V).inv ≫ (λ_ (𝟙_ D)).hom ▷ V) := by
  monoidal

/-- **The free module over the trivial base is its generator**,
via the left unitor. -/
noncomputable def freeModUnitBase
    [Category.{v} D] [MonoidalCategory D] (V : D) :
    freeMod (𝟙_ D) V ≅ unitMod V where
  hom := Mod.Hom.mk' (λ_ V).hom (by
    change ((α_ (𝟙_ D) (𝟙_ D) V).inv ≫ (λ_ (𝟙_ D)).hom ▷ V) ≫
        (λ_ V).hom =
      (𝟙_ D) ◁ (λ_ V).hom ≫ (λ_ V).hom
    exact freeModUnitBase_linear V)
  inv := Mod.Hom.mk' (λ_ V).inv (by
    change (λ_ V).hom ≫ (λ_ V).inv =
      (𝟙_ D) ◁ (λ_ V).inv ≫
        ((α_ (𝟙_ D) (𝟙_ D) V).inv ≫ (λ_ (𝟙_ D)).hom ▷ V)
    exact freeModUnitBase_linear_inv V)
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (λ_ V).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (λ_ V).inv_hom_id

end FreeUnitBase

section BiprodZero

/-- **Collapse of a zero summand**: over any base, the module
biproduct with a module whose carrier is zero is the other
summand. -/
noncomputable def modBiprodZeroLeft
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (Z : Mod D A) (N : Mod D A)
    (hZ : IsZero Z.X) :
    modBiprod A Z N ≅ N where
  hom := modBiprodSnd A Z N
  inv := modBiprodInr A Z N
  hom_inv_id := by
    apply Mod.Hom.ext
    change (biprod.snd ≫ biprod.inr : Z.X ⊞ N.X ⟶ _) = 𝟙 _
    have hfst : (biprod.fst : Z.X ⊞ N.X ⟶ Z.X) = 0 :=
      hZ.eq_of_tgt _ _
    rw [← biprod.total, hfst, Limits.zero_comp, zero_add]
  inv_hom_id := by
    apply Mod.Hom.ext
    change (biprod.inr ≫ biprod.snd : N.X ⟶ _) = 𝟙 _
    rw [biprod.inr_snd]

end BiprodZero

end RS
