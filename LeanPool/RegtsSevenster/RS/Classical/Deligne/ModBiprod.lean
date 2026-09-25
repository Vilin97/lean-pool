/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModTensor

/-!
# Biproducts of internal modules

The biproduct of two modules over a monoid object carries the
componentwise action: the tensor distributes over the biproduct
in a monoidally preadditive category, and the two actions act in
each summand.  The injections and projections are module maps,
and morphisms out of the biproduct module are determined by the
two components.
-/

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-- The componentwise action on the biproduct of the carriers. -/
noncomputable def modBiprodAct
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    A ⊗ (M.X ⊞ N.X) ⟶ M.X ⊞ N.X :=
  biprod.lift ((A ◁ biprod.fst) ≫ actLeft A M.X)
    ((A ◁ biprod.snd) ≫ actLeft A N.X)

/-- The unit law of the componentwise action. -/
theorem modBiprodAct_one [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    (η[A] ▷ (M.X ⊞ N.X)) ≫ modBiprodAct A M N =
      (λ_ (M.X ⊞ N.X)).hom := by
  apply biprod.hom_ext
  · rw [Category.assoc, modBiprodAct, biprod.lift_fst,
      ← Category.assoc, ← whisker_exchange, Category.assoc,
      one_actLeft, leftUnitor_naturality]
  · rw [Category.assoc, modBiprodAct, biprod.lift_snd,
      ← Category.assoc, ← whisker_exchange, Category.assoc,
      one_actLeft, leftUnitor_naturality]

/-- The multiplication law of the componentwise action. -/
theorem modBiprodAct_mul [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    (μ[A] ▷ (M.X ⊞ N.X)) ≫ modBiprodAct A M N =
      (α_ A A (M.X ⊞ N.X)).hom ≫
        (A ◁ modBiprodAct A M N) ≫ modBiprodAct A M N := by
  apply biprod.hom_ext
  · rw [Category.assoc, modBiprodAct, biprod.lift_fst,
      Category.assoc, Category.assoc, biprod.lift_fst,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.lift_fst]
    rw [← Category.assoc, ← whisker_exchange,
      Category.assoc, mul_actLeft]
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      associator_naturality_right_assoc]
  · rw [Category.assoc, modBiprodAct, biprod.lift_snd,
      Category.assoc, Category.assoc, biprod.lift_snd,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.lift_snd]
    rw [← Category.assoc, ← whisker_exchange,
      Category.assoc, mul_actLeft]
    rw [MonoidalCategory.whiskerLeft_comp, Category.assoc,
      associator_naturality_right_assoc]

/-- The module structure on the biproduct of the carriers. -/
@[implicit_reducible]
noncomputable def modBiprodModObj
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    ModObj A (M.X ⊞ N.X) where
  smul := modBiprodAct A M N
  one_smul := modBiprodAct_one A M N
  mul_smul := modBiprodAct_mul A M N

/-- **The biproduct of modules**, bundled. -/
noncomputable def modBiprod
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    Mod D A :=
  letI := modBiprodModObj A M N
  ⟨M.X ⊞ N.X⟩

@[simp] lemma modBiprod_X [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    (modBiprod A M N).X = (M.X ⊞ N.X) := rfl

/-- The first injection intertwines the actions. -/
theorem actLeft_modBiprodInl
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) :
    actLeft A M.X ≫ (biprod.inl : M.X ⟶ M.X ⊞ N.X) =
      (A ◁ biprod.inl) ≫ modBiprodAct A M N := by
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc, modBiprodAct,
      biprod.lift_fst, biprod.inl_fst, Category.comp_id,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.inl_fst, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]
  · rw [Category.assoc, Category.assoc, modBiprodAct,
      biprod.lift_snd, biprod.inl_snd, Limits.comp_zero,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.inl_snd, MonoidalPreadditive.whiskerLeft_zero,
      Limits.zero_comp]

/-- The second injection intertwines the actions. -/
theorem actLeft_modBiprodInr
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) :
    actLeft A N.X ≫ (biprod.inr : N.X ⟶ M.X ⊞ N.X) =
      (A ◁ biprod.inr) ≫ modBiprodAct A M N := by
  apply biprod.hom_ext
  · rw [Category.assoc, Category.assoc, modBiprodAct,
      biprod.lift_fst, biprod.inr_fst, Limits.comp_zero,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.inr_fst, MonoidalPreadditive.whiskerLeft_zero,
      Limits.zero_comp]
  · rw [Category.assoc, Category.assoc, modBiprodAct,
      biprod.lift_snd, biprod.inr_snd, Category.comp_id,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.inr_snd, MonoidalCategory.whiskerLeft_id,
      Category.id_comp]

/-- The first projection intertwines the actions. -/
theorem modBiprodAct_fst [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    modBiprodAct A M N ≫ biprod.fst =
      (A ◁ (biprod.fst : M.X ⊞ N.X ⟶ M.X)) ≫
        actLeft A M.X := by
  rw [modBiprodAct, biprod.lift_fst]

/-- The second projection intertwines the actions. -/
theorem modBiprodAct_snd [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    modBiprodAct A M N ≫ biprod.snd =
      (A ◁ (biprod.snd : M.X ⊞ N.X ⟶ N.X)) ≫
        actLeft A N.X := by
  rw [modBiprodAct, biprod.lift_snd]

/-- The first injection is a module map. -/
noncomputable def modBiprodInl
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) : M ⟶ modBiprod A M N :=
  Mod.Hom.mk' (biprod.inl : M.X ⟶ M.X ⊞ N.X)
    (by exact actLeft_modBiprodInl A M N)

/-- The second injection is a module map. -/
noncomputable def modBiprodInr
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) : N ⟶ modBiprod A M N :=
  Mod.Hom.mk' (biprod.inr : N.X ⟶ M.X ⊞ N.X)
    (by exact actLeft_modBiprodInr A M N)

/-- The first projection is a module map. -/
noncomputable def modBiprodFst
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    modBiprod A M N ⟶ M :=
  Mod.Hom.mk' (biprod.fst : M.X ⊞ N.X ⟶ M.X)
    (by exact modBiprodAct_fst A M N)

/-- The second projection is a module map. -/
noncomputable def modBiprodSnd
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    modBiprod A M N ⟶ N :=
  Mod.Hom.mk' (biprod.snd : M.X ⊞ N.X ⟶ N.X)
    (by exact modBiprodAct_snd A M N)

@[simp] lemma modBiprodInl_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) :
    (modBiprodInl A M N).hom = biprod.inl := rfl

@[simp] lemma modBiprodInr_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (A : D) [MonObj A]
    (M : Mod D A) (N : Mod D A) :
    (modBiprodInr A M N).hom = biprod.inr := rfl

section Map

/-- Componentwise maps intertwine the biproduct actions. -/
theorem modBiprodAct_map [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    {M' : Mod D A} {N' : Mod D A}
    (f : M ⟶ M') (g : N ⟶ N') :
    modBiprodAct A M N ≫ biprod.map f.hom g.hom =
      (A ◁ biprod.map f.hom g.hom) ≫
        modBiprodAct A M' N' := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, ← Category.assoc,
      modBiprodAct_fst, Category.assoc, actLeft_natural,
      Category.assoc, modBiprodAct, biprod.lift_fst,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.map_fst]
  · rw [Category.assoc, biprod.map_snd, ← Category.assoc,
      modBiprodAct_snd, Category.assoc, actLeft_natural,
      Category.assoc, modBiprodAct, biprod.lift_snd,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.map_snd]

/-- **Functoriality of the module biproduct.** -/
noncomputable def modBiprodMap
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    {M' : Mod D A} {N' : Mod D A}
    (f : M ⟶ M') (g : N ⟶ N') :
    modBiprod A M N ⟶ modBiprod A M' N' :=
  Mod.Hom.mk' (biprod.map f.hom g.hom)
    (by exact modBiprodAct_map A M N f g)

@[simp] lemma modBiprodMap_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    {M' : Mod D A} {N' : Mod D A}
    (f : M ⟶ M') (g : N ⟶ N') :
    (modBiprodMap A M N f g).hom =
      biprod.map f.hom g.hom := rfl

/-- The module biproduct of two isomorphisms. -/
noncomputable def modBiprodMapIso
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    {M' : Mod D A} {N' : Mod D A}
    (e₁ : M ≅ M')
    (e₂ : N ≅ N') :
    modBiprod A M N ≅ modBiprod A M' N' where
  hom := modBiprodMap A M N e₁.hom e₂.hom
  inv := modBiprodMap A M' N' e₁.inv e₂.inv
  hom_inv_id := by
    apply Mod.Hom.ext
    change biprod.map e₁.hom.hom e₂.hom.hom ≫
        biprod.map e₁.inv.hom e₂.inv.hom =
      𝟙 (M.X ⊞ N.X)
    have h₁ : e₁.hom.hom ≫ e₁.inv.hom = 𝟙 M.X :=
      congrArg Mod.Hom.hom e₁.hom_inv_id
    have h₂ : e₂.hom.hom ≫ e₂.inv.hom = 𝟙 N.X :=
      congrArg Mod.Hom.hom e₂.hom_inv_id
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.map_fst, ← Category.assoc,
        biprod.map_fst, Category.assoc, h₁,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, biprod.map_snd, ← Category.assoc,
        biprod.map_snd, Category.assoc, h₂,
        Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply Mod.Hom.ext
    change biprod.map e₁.inv.hom e₂.inv.hom ≫
        biprod.map e₁.hom.hom e₂.hom.hom =
      𝟙 (M'.X ⊞ N'.X)
    have h₁ : e₁.inv.hom ≫ e₁.hom.hom = 𝟙 M'.X :=
      congrArg Mod.Hom.hom e₁.inv_hom_id
    have h₂ : e₂.inv.hom ≫ e₂.hom.hom = 𝟙 N'.X :=
      congrArg Mod.Hom.hom e₂.inv_hom_id
    apply biprod.hom_ext
    · rw [Category.assoc, biprod.map_fst, ← Category.assoc,
        biprod.map_fst, Category.assoc, h₁,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, biprod.map_snd, ← Category.assoc,
        biprod.map_snd, Category.assoc, h₂,
        Category.comp_id, Category.id_comp]

end Map

@[simp] lemma modBiprodFst_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    (modBiprodFst A M N).hom = biprod.fst := rfl

@[simp] lemma modBiprodSnd_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    (modBiprodSnd A M N).hom = biprod.snd := rfl

section Rearrange

/-- The braiding of a module biproduct is linear. -/
theorem modBiprodAct_braiding
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    modBiprodAct A M N ≫ (biprod.braiding M.X N.X).hom =
      (A ◁ (biprod.braiding M.X N.X).hom) ≫
        modBiprodAct A N M := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.braiding_hom, biprod.lift_fst,
      modBiprodAct_snd, Category.assoc, modBiprodAct,
      biprod.lift_fst,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.lift_fst]
  · rw [Category.assoc, biprod.braiding_hom, biprod.lift_snd,
      modBiprodAct_fst, Category.assoc, modBiprodAct,
      biprod.lift_snd,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.lift_snd]

/-- **The biproduct of modules is symmetric.** -/
noncomputable def modBiprodSymmIso
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A) :
    modBiprod A M N ≅ modBiprod A N M where
  hom := Mod.Hom.mk' (biprod.braiding M.X N.X).hom (by
    exact modBiprodAct_braiding A M N)
  inv := Mod.Hom.mk' (biprod.braiding N.X M.X).hom (by
    exact modBiprodAct_braiding A N M)
  hom_inv_id := by
    apply Mod.Hom.ext
    change (biprod.braiding M.X N.X).hom ≫
      (biprod.braiding N.X M.X).hom = 𝟙 (M.X ⊞ N.X)
    exact (biprod.braiding M.X N.X).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    change (biprod.braiding N.X M.X).hom ≫
      (biprod.braiding M.X N.X).hom = 𝟙 (N.X ⊞ M.X)
    exact (biprod.braiding N.X M.X).hom_inv_id

/-- The action on the left-nested triple biproduct, retyped. -/
noncomputable def actLeftNest
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    A ⊗ ((M.X ⊞ N.X) ⊞ P.X) ⟶ (M.X ⊞ N.X) ⊞ P.X :=
  modBiprodAct A (modBiprod A M N) P

/-- The action on the right-nested triple biproduct, retyped. -/
noncomputable def actRightNest
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    A ⊗ (M.X ⊞ (N.X ⊞ P.X)) ⟶ M.X ⊞ (N.X ⊞ P.X) :=
  modBiprodAct A M (modBiprod A N P)

/-- The associator of a module biproduct is linear. -/
theorem modBiprodAct_associator
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    actLeftNest A M N P ≫
        (biprod.associator M.X N.X P.X).hom =
      (A ◁ (biprod.associator M.X N.X P.X).hom) ≫
        actRightNest A M N P := by
  have h1 : actLeftNest A M N P ≫ biprod.fst =
      (A ◁ biprod.fst) ≫ modBiprodAct A M N :=
    modBiprodAct_fst A (modBiprod A M N) P
  have h2 : actLeftNest A M N P ≫ biprod.snd =
      (A ◁ biprod.snd) ≫ actLeft A P.X :=
    modBiprodAct_snd A (modBiprod A M N) P
  have h3 : actRightNest A M N P ≫ biprod.fst =
      (A ◁ biprod.fst) ≫ actLeft A M.X :=
    modBiprodAct_fst A M (modBiprod A N P)
  have h4 : actRightNest A M N P ≫ biprod.snd =
      (A ◁ biprod.snd) ≫ modBiprodAct A N P :=
    modBiprodAct_snd A M (modBiprod A N P)
  have h4' : ∀ {Z : D} (g : (N.X ⊞ P.X) ⟶ Z),
      actRightNest A M N P ≫ biprod.snd ≫ g =
      (A ◁ biprod.snd) ≫ modBiprodAct A N P ≫ g := by
    intro Z g
    rw [← Category.assoc, h4, Category.assoc]
  have h1' : ∀ {Z : D} (g : (M.X ⊞ N.X) ⟶ Z),
      actLeftNest A M N P ≫ biprod.fst ≫ g =
      (A ◁ biprod.fst) ≫ modBiprodAct A M N ≫ g := by
    intro Z g
    rw [← Category.assoc, h1, Category.assoc]
  change actLeftNest A M N P ≫
      biprod.lift (biprod.fst ≫ biprod.fst)
        (biprod.lift (biprod.fst ≫ biprod.snd)
          biprod.snd) =
    (A ◁ biprod.lift (biprod.fst ≫ biprod.fst)
      (biprod.lift (biprod.fst ≫ biprod.snd) biprod.snd)) ≫
      actRightNest A M N P
  apply biprod.hom_ext
  · simp only [Category.assoc, biprod.lift_fst]
    rw [h3, ← MonoidalCategory.whiskerLeft_comp_assoc,
      biprod.lift_fst,
      MonoidalCategory.whiskerLeft_comp_assoc]
    rw [← Category.assoc, h1, Category.assoc,
      modBiprodAct_fst]
  · apply biprod.hom_ext
    · simp only [Category.assoc, biprod.lift_fst,
        biprod.lift_snd]
      rw [h4' biprod.fst]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc,
        biprod.lift_snd]
      rw [modBiprodAct_fst]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc,
        biprod.lift_fst,
        MonoidalCategory.whiskerLeft_comp_assoc]
      rw [h1' biprod.snd, modBiprodAct_snd]
    · simp only [Category.assoc, biprod.lift_snd]
      rw [h4' biprod.snd]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc,
        biprod.lift_snd]
      rw [modBiprodAct_snd]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc,
        biprod.lift_snd]
      exact h2

/-- **The biproduct of modules is associative.** -/
noncomputable def modBiprodAssocIso
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (A : D) [MonObj A] (M : Mod D A) (N : Mod D A)
    (P : Mod D A) :
    modBiprod A (modBiprod A M N) P ≅
      modBiprod A M (modBiprod A N P) where
  hom := Mod.Hom.mk' (biprod.associator M.X N.X P.X).hom (by
    exact modBiprodAct_associator A M N P)
  inv := Mod.Hom.mk' (biprod.associator M.X N.X P.X).inv (by
    change actRightNest A M N P ≫
        (biprod.associator M.X N.X P.X).inv =
      (A ◁ (biprod.associator M.X N.X P.X).inv) ≫
        actLeftNest A M N P
    refine (cancel_mono
      (biprod.associator M.X N.X P.X).hom).mp ?_
    rw [Category.assoc,
      (biprod.associator M.X N.X P.X).inv_hom_id,
      Category.comp_id, Category.assoc]
    refine Eq.symm ?_
    refine Eq.trans (whisker_eq _
      (modBiprodAct_associator A M N P)) ?_
    rw [← Category.assoc,
      ← MonoidalCategory.whiskerLeft_comp,
      (biprod.associator M.X N.X P.X).inv_hom_id,
      MonoidalCategory.whiskerLeft_id, Category.id_comp])
  hom_inv_id := by
    apply Mod.Hom.ext
    exact (biprod.associator M.X N.X P.X).hom_inv_id
  inv_hom_id := by
    apply Mod.Hom.ext
    exact (biprod.associator M.X N.X P.X).inv_hom_id

end Rearrange

end RS
