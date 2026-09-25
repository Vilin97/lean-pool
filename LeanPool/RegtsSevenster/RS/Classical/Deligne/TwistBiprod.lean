/-
Copyright (c) 2026 William Whistler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: William Whistler
-/

module

public import LeanPool.RegtsSevenster.RS.Classical.Deligne.ModBiprod
public import LeanPool.RegtsSevenster.RS.Classical.Deligne.TwistShuffle

/-!
# Twisting distributes over the biproduct of modules

Tensoring on the left by a fixed object distributes over the
biproduct of two modules.  At the level of carriers this is the
standard distributivity of the tensor over a binary biproduct,
assembled from `biprod.lift` and `biprod.desc`; the two round-trips
use the totality relation of the biproduct together with the
additivity of the left whiskering.  The distributivity map
intertwines the action through the right tensor factor with the
componentwise action of the biproduct, because each biproduct
projection is a module map and the twist of a module map is again
a module map.
-/

@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits
open scoped MonObj

universe v u

variable {D : Type u}

/-! ## The carrier-level distributivity -/

section Carrier

/-- **Distributivity of the tensor over a binary biproduct**: the
comparison map assembled from the two whiskered projections. -/
noncomputable def tensorLeftBiprodHom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (V : D) (X : D) (Y : D) :
    V ⊗ (X ⊞ Y) ⟶ (V ⊗ X) ⊞ (V ⊗ Y) :=
  biprod.lift (V ◁ biprod.fst) (V ◁ biprod.snd)

/-- The inverse comparison map, assembled from the two whiskered
injections. -/
noncomputable def tensorLeftBiprodInv
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (V : D) (X : D) (Y : D) :
    (V ⊗ X) ⊞ (V ⊗ Y) ⟶ V ⊗ (X ⊞ Y) :=
  biprod.desc (V ◁ biprod.inl) (V ◁ biprod.inr)

@[simp] lemma tensorLeftBiprodHom_fst
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (V : D) (X : D) (Y : D) :
    tensorLeftBiprodHom V X Y ≫ biprod.fst = V ◁ biprod.fst :=
  biprod.lift_fst _ _

@[simp] lemma tensorLeftBiprodHom_snd
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (V : D) (X : D) (Y : D) :
    tensorLeftBiprodHom V X Y ≫ biprod.snd = V ◁ biprod.snd :=
  biprod.lift_snd _ _

@[simp] lemma inl_tensorLeftBiprodInv
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (V : D) (X : D) (Y : D) :
    biprod.inl ≫ tensorLeftBiprodInv V X Y = V ◁ biprod.inl :=
  biprod.inl_desc _ _

@[simp] lemma inr_tensorLeftBiprodInv
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] (V : D) (X : D) (Y : D) :
    biprod.inr ≫ tensorLeftBiprodInv V X Y = V ◁ biprod.inr :=
  biprod.inr_desc _ _

/-- The comparison map is split by its inverse: the totality
relation of the biproduct, whiskered. -/
@[simp] theorem tensorLeftBiprodHom_inv
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (V : D) (X : D) (Y : D) :
    tensorLeftBiprodHom V X Y ≫ tensorLeftBiprodInv V X Y =
      𝟙 (V ⊗ (X ⊞ Y)) := by
  rw [tensorLeftBiprodHom, tensorLeftBiprodInv, biprod.lift_desc,
    ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalCategory.whiskerLeft_comp,
    ← MonoidalPreadditive.whiskerLeft_add, biprod.total,
    MonoidalCategory.whiskerLeft_id]

/-- The inverse comparison map is split by the comparison map. -/
@[simp] theorem tensorLeftBiprodInv_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] (V : D) (X : D) (Y : D) :
    tensorLeftBiprodInv V X Y ≫ tensorLeftBiprodHom V X Y =
      𝟙 ((V ⊗ X) ⊞ (V ⊗ Y)) := by
  refine biprod.hom_ext' _ _ ?_ ?_
  · rw [← Category.assoc, inl_tensorLeftBiprodInv,
      Category.comp_id]
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, tensorLeftBiprodHom_fst,
        ← MonoidalCategory.whiskerLeft_comp, biprod.inl_fst,
        MonoidalCategory.whiskerLeft_id, biprod.inl_fst]
    · rw [Category.assoc, tensorLeftBiprodHom_snd,
        ← MonoidalCategory.whiskerLeft_comp, biprod.inl_snd,
        MonoidalPreadditive.whiskerLeft_zero, biprod.inl_snd]
  · rw [← Category.assoc, inr_tensorLeftBiprodInv,
      Category.comp_id]
    refine biprod.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, tensorLeftBiprodHom_fst,
        ← MonoidalCategory.whiskerLeft_comp, biprod.inr_fst,
        MonoidalPreadditive.whiskerLeft_zero, biprod.inr_fst]
    · rw [Category.assoc, tensorLeftBiprodHom_snd,
        ← MonoidalCategory.whiskerLeft_comp, biprod.inr_snd,
        MonoidalCategory.whiskerLeft_id, biprod.inr_snd]

end Carrier

/-! ## The distributivity as a module isomorphism -/

section ModuleMap

/-- **The twist of a module map is a module map**: a map
intertwining the actions still intertwines them after whiskering
by a fixed object on the left. -/
theorem actAcross_whiskerLeft_of
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D] (A : D)
    [MonObj A] (V : D)
    {X Y : D} [ModObj A X] [ModObj A Y]
    (g : X ⟶ Y)
    (hg : actLeft A X ≫ g = (A ◁ g) ≫ actLeft A Y) :
    actAcross A V X ≫ (V ◁ g) =
      (A ◁ (V ◁ g)) ≫ actAcross A V Y := by
  rw [actAcross_eq_braidPast, actAcross_eq_braidPast,
    Category.assoc, ← MonoidalCategory.whiskerLeft_comp, hg,
    MonoidalCategory.whiskerLeft_comp,
    braidPast_natural_tail_assoc]

/-- The action on the twist of the module biproduct, retyped. -/
noncomputable def twistBiprodActL
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] [SymmetricCategory D] (A : D) [MonObj A] (V : D)
    (P : Mod D A) (Q : Mod D A) :
    A ⊗ (V ⊗ (P.X ⊞ Q.X)) ⟶ V ⊗ (P.X ⊞ Q.X) :=
  actAcross A V (modBiprod A P Q).X

/-- The componentwise action on the biproduct of the twists,
retyped. -/
noncomputable def twistBiprodActR
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] [SymmetricCategory D] (A : D) [MonObj A] (V : D)
    (P : Mod D A) (Q : Mod D A) :
    A ⊗ ((V ⊗ P.X) ⊞ (V ⊗ Q.X)) ⟶ (V ⊗ P.X) ⊞ (V ⊗ Q.X) :=
  modBiprodAct A (tensorLeftMod A V P) (tensorLeftMod A V Q)

/-- The twisted first projection intertwines the actions. -/
theorem twistBiprodActL_fst
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] [SymmetricCategory D] (A : D) [MonObj A] (V : D)
    (P : Mod D A) (Q : Mod D A) :
    twistBiprodActL A V P Q ≫
        (V ◁ (biprod.fst : P.X ⊞ Q.X ⟶ P.X)) =
      (A ◁ (V ◁ (biprod.fst : P.X ⊞ Q.X ⟶ P.X))) ≫
        actAcross A V P.X := by
  let := modBiprodModObj A P Q
  exact actAcross_whiskerLeft_of A V biprod.fst
    (modBiprodAct_fst A P Q)

/-- The twisted second projection intertwines the actions. -/
theorem twistBiprodActL_snd
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] [SymmetricCategory D] (A : D) [MonObj A] (V : D)
    (P : Mod D A) (Q : Mod D A) :
    twistBiprodActL A V P Q ≫
        (V ◁ (biprod.snd : P.X ⊞ Q.X ⟶ Q.X)) =
      (A ◁ (V ◁ (biprod.snd : P.X ⊞ Q.X ⟶ Q.X))) ≫
        actAcross A V Q.X := by
  let := modBiprodModObj A P Q
  exact actAcross_whiskerLeft_of A V biprod.snd
    (modBiprodAct_snd A P Q)

/-- The first component of the componentwise action. -/
theorem twistBiprodActR_fst
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] [SymmetricCategory D] (A : D) [MonObj A] (V : D)
    (P : Mod D A) (Q : Mod D A) :
    twistBiprodActR A V P Q ≫ biprod.fst =
      (A ◁ biprod.fst) ≫ actAcross A V P.X :=
  modBiprodAct_fst A (tensorLeftMod A V P) (tensorLeftMod A V Q)

/-- The second component of the componentwise action. -/
theorem twistBiprodActR_snd
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] [SymmetricCategory D] (A : D) [MonObj A] (V : D)
    (P : Mod D A) (Q : Mod D A) :
    twistBiprodActR A V P Q ≫ biprod.snd =
      (A ◁ biprod.snd) ≫ actAcross A V Q.X :=
  modBiprodAct_snd A (tensorLeftMod A V P) (tensorLeftMod A V Q)

/-- **The distributivity map is linear**: it intertwines the action
through the right tensor factor with the componentwise action of
the biproduct. -/
theorem twistBiprodActL_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] [SymmetricCategory D] (A : D) [MonObj A] (V : D)
    (P : Mod D A) (Q : Mod D A) :
    twistBiprodActL A V P Q ≫ tensorLeftBiprodHom V P.X Q.X =
      (A ◁ tensorLeftBiprodHom V P.X Q.X) ≫
        twistBiprodActR A V P Q := by
  refine biprod.hom_ext _ _ ?_ ?_
  · rw [Category.assoc, tensorLeftBiprodHom_fst, Category.assoc,
      twistBiprodActR_fst,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      tensorLeftBiprodHom_fst]
    exact twistBiprodActL_fst A V P Q
  · rw [Category.assoc, tensorLeftBiprodHom_snd, Category.assoc,
      twistBiprodActR_snd,
      ← MonoidalCategory.whiskerLeft_comp_assoc,
      tensorLeftBiprodHom_snd]
    exact twistBiprodActL_snd A V P Q

/-- **The inverse distributivity map is linear.** -/
theorem twistBiprodActR_inv
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] [SymmetricCategory D]
    (A : D) [MonObj A] (V : D) (P : Mod D A) (Q : Mod D A) :
    twistBiprodActR A V P Q ≫ tensorLeftBiprodInv V P.X Q.X =
      (A ◁ tensorLeftBiprodInv V P.X Q.X) ≫
        twistBiprodActL A V P Q := by
  have : IsIso (tensorLeftBiprodHom V P.X Q.X) :=
    ⟨tensorLeftBiprodInv V P.X Q.X,
      tensorLeftBiprodHom_inv V P.X Q.X,
      tensorLeftBiprodInv_hom V P.X Q.X⟩
  rw [← cancel_mono (tensorLeftBiprodHom V P.X Q.X),
    Category.assoc, Category.assoc, tensorLeftBiprodInv_hom,
    Category.comp_id, twistBiprodActL_hom, ← Category.assoc,
    ← MonoidalCategory.whiskerLeft_comp, tensorLeftBiprodInv_hom,
    MonoidalCategory.whiskerLeft_id, Category.id_comp]

/-- The distributivity map, as a module map. -/
noncomputable def tensorLeftBiprodModHom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] [SymmetricCategory D] (A : D) [MonObj A] (V : D)
    (P : Mod D A) (Q : Mod D A) :
    tensorLeftMod A V (modBiprod A P Q) ⟶
      modBiprod A (tensorLeftMod A V P)
        (tensorLeftMod A V Q) :=
  Mod.Hom.mk' (tensorLeftBiprodHom V P.X Q.X)
    (by exact twistBiprodActL_hom A V P Q)

/-- The inverse distributivity map, as a module map. -/
noncomputable def tensorLeftBiprodModInv
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] [SymmetricCategory D]
    (A : D) [MonObj A] (V : D) (P : Mod D A) (Q : Mod D A) :
    modBiprod A (tensorLeftMod A V P) (tensorLeftMod A V Q) ⟶
      tensorLeftMod A V (modBiprod A P Q) :=
  Mod.Hom.mk' (tensorLeftBiprodInv V P.X Q.X)
    (by exact twistBiprodActR_inv A V P Q)

@[simp] lemma tensorLeftBiprodModHom_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [HasBinaryBiproducts D] [SymmetricCategory D] (A : D) [MonObj A] (V : D)
    (P : Mod D A) (Q : Mod D A) :
    (tensorLeftBiprodModHom A V P Q).hom =
      tensorLeftBiprodHom V P.X Q.X := rfl

@[simp] lemma tensorLeftBiprodModInv_hom
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] [SymmetricCategory D]
    (A : D) [MonObj A] (V : D) (P : Mod D A) (Q : Mod D A) :
    (tensorLeftBiprodModInv A V P Q).hom =
      tensorLeftBiprodInv V P.X Q.X := rfl

/-- **Twisting distributes over the biproduct of modules**: the
twist of a biproduct of modules is the biproduct of the twists. -/
noncomputable def tensorLeftBiprodIso
    [Category.{v} D] [MonoidalCategory D] [Preadditive D]
    [MonoidalPreadditive D] [HasBinaryBiproducts D] [SymmetricCategory D]
    (A : D) [MonObj A]
    (V : D) (P Q : Mod D A) :
    tensorLeftMod A V (modBiprod A P Q) ≅
      modBiprod A (tensorLeftMod A V P)
        (tensorLeftMod A V Q) where
  hom := tensorLeftBiprodModHom A V P Q
  inv := tensorLeftBiprodModInv A V P Q
  hom_inv_id :=
    Mod.hom_ext _ _ (tensorLeftBiprodHom_inv V P.X Q.X)
  inv_hom_id :=
    Mod.hom_ext _ _ (tensorLeftBiprodInv_hom V P.X Q.X)

end ModuleMap

end RS
