/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

import LeanPool.Circuitlib.Circuit.Category.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

/-! # Combinational circuit category

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- Category of combinational circuits. -/
structure CombinationalCircuitCategory (V : Type*) (G : Type*) where of (V) (G) ::
  /-- The number of wires of this object. -/
  obj : ℕ

attribute [inline, simp] CombinationalCircuitCategory.obj

@[simp]
instance : OfNat (CombinationalCircuitCategory V G) n where
  ofNat := .of V G n

namespace CombinationalCircuitCategory

universe u v

variable {V : Type v} {G : Type u}

/-- Homomorphism. -/
def Hom (V : Type v) [Preorder V] (I O : CombinationalCircuitCategory V G) :=
  { f : Wires V I.obj → Wires V O.obj // Monotone f }

/-- The underlying identity wire-function. -/
@[inline, simp]
def idVal : Wires V n → Wires V n := fun x => x

@[simp]
lemma id_monotone [Preorder V] : Monotone (idVal (V:=V) (n:=n)) := monotone_id

/-- The identity morphism. -/
@[inline, simp]
def id [Preorder V] : CombinationalCircuitCategory.Hom V X X := ⟨idVal, id_monotone⟩

open CategoryTheory

@[inline, simp]
instance [Preorder V] : Category.{v} (CombinationalCircuitCategory V G) where
  Hom := Hom V
  id _ := id
  comp f g := ⟨g.val ∘ f.val, Monotone.comp g.property f.property⟩
  id_comp _ := by rfl
  comp_id _ := by rfl
  assoc _ _ _ := by rfl

@[simp]
lemma id_coe_apply
    [Preorder V]
    (X : CombinationalCircuitCategory V G) (v : Wires V X.obj) :
    (𝟙 X : Hom V X X).val v = v := rfl

/-- The wire-function that duplicates its single input wire. -/
@[inline, simp]
def fork (w : Wires V 1) : Wires V 2 := #v[w.get 0, w.get 0]

@[simp]
lemma fork_monotone [Preorder V] : Monotone (fork (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> exact h 0

/-- The wire-function that joins two input wires by taking their supremum. -/
@[inline, simp]
def join [SemilatticeSup V] (w : Wires V 2) : Wires V 1 := #v[w.get 0 ⊔ w.get 1]

@[simp]
lemma join_monotone [SemilatticeSup V] : Monotone (join (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 := by omega
  subst this; exact sup_le_sup (h 0) (h 1)

/-- The monoidal product of two objects, adding their wire counts. -/
@[inline, simp]
abbrev tensorObj (X Y : CombinationalCircuitCategory V G) : CombinationalCircuitCategory V G :=
  .of V G (X.obj + Y.obj)

@[inline]
instance
    [SemilatticeSup V]
    [Gate V G]
    [Bot V] :
    CircuitCategory V G (CombinationalCircuitCategory V G) where
  gate g := ⟨Gate.gate g, Gate.gate_monotone g⟩
  stub := ⟨fun _ => #v[⊥], fun _ _ _ => le_refl _⟩
  drop := ⟨fun _ => #v[], fun _ _ _ => le_refl _⟩
  fork := ⟨fork, fork_monotone⟩
  join := ⟨join, join_monotone⟩

lemma tensorHom_val_add
    {X₁ X₂ : CombinationalCircuitCategory V G} :
    min X₁.obj (X₁.obj + X₂.obj) = X₁.obj :=
  by simp

lemma tensorHom_val_sub
    {X₁ X₂ : CombinationalCircuitCategory V G} :
    X₁.obj + X₂.obj - X₁.obj = X₂.obj :=
  by simp

variable [SemilatticeSup V]

/-- The underlying wire-function of the monoidal product of two morphisms. -/
@[inline, simp]
abbrev tensorHomVal
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (v : Wires V (X₁.obj + X₂.obj)) :
    Wires V (Y₁.obj + Y₂.obj) :=
  (f.val ((v.take X₁.obj).cast tensorHom_val_add)).append
    (g.val ((v.drop X₁.obj).cast tensorHom_val_sub))

lemma tensorHom_eq
    {X₁ Y₁ X₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (f : X₁ ⟶ Y₁) :
    (f.val (Vector.ofFn fun i ↦ Vector.get a (Fin.castAdd X₂.obj i))).toArray.size = Y₁.obj :=
  (f.val (Vector.ofFn (fun i => a.get (i.castAdd _)))).size_toArray

omit [SemilatticeSup V] in
lemma tensorHom_take
    {X₁ X₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj)) :
    (a.take X₁.obj).cast tensorHom_val_add =
    Vector.ofFn fun i => a.get (Fin.castAdd X₂.obj i) := by
  apply Wires.ext; intro i
  simp [Vector.get]

lemma tensorHom_eq_left
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₁.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (tensorHomVal f g a).get (Fin.castAdd Y₂.obj j) =
    Vector.get (f.val (Vector.ofFn fun i => Vector.get a (Fin.castAdd X₂.obj i))) j := by
  have htake := tensorHom_take a
  have hf := tensorHom_eq a f
  simp only [htake, Vector.get, Vector.append, Fin.val_cast, Fin.val_castAdd] at hf ⊢
  exact Array.getElem_append_left (by omega)

lemma tensorHom_eq_right
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₂.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (tensorHomVal f g a).get (Fin.natAdd Y₁.obj j) =
    Vector.get (g.val (Vector.ofFn fun i => Vector.get a (Fin.natAdd X₁.obj i))) j := by
  have htake := tensorHom_take a
  have hdrop : (a.drop X₁.obj).cast tensorHom_val_sub =
    Vector.ofFn fun i => a.get (Fin.natAdd X₁.obj i) := by
    apply Wires.ext; intro i
    simp [Vector.get, Vector.drop, Fin.val_natAdd]
  have hf := tensorHom_eq a f
  simp only [htake, hdrop, Vector.get, Vector.append,
    Fin.val_cast, Fin.val_castAdd, Fin.val_natAdd] at hf ⊢
  rw [Array.getElem_append_right (by omega)]
  congr 1; omega

lemma tensorHom_get
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (w : Wires V (X₁.obj + X₂.obj))
    (i : Fin (Y₁.obj + Y₂.obj)) :
    (tensorHomVal f g w).get i =
    if h : i.val < Y₁.obj
    then (f.val (Vector.ofFn fun k => w.get (Fin.castAdd X₂.obj k))).get ⟨i.val, h⟩
    else (g.val (Vector.ofFn fun k => w.get (Fin.natAdd X₁.obj k))).get
      ⟨i.val - Y₁.obj, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [tensorHom_eq_left, Fin.val_castAdd, dif_pos j.isLt]
  · simp only [tensorHom_eq_right, Fin.val_natAdd,
               dif_neg (show ¬(Y₁.obj + j.val < Y₁.obj) from by omega)]
    congr 1; exact Fin.ext (by simp)

@[simp]
lemma tensorHom_monotone
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    Monotone (tensorHomVal f g) := fun a b h i =>
  Fin.addCases
    (fun j => by
      have lhs_eq := tensorHom_eq_left a j f g
      have rhs_eq := tensorHom_eq_left b j f g
      rw [lhs_eq, rhs_eq]
      exact f.property (fun k => by
        simp only [Vector.get, Vector.toArray_ofFn, Fin.val_cast, Array.getElem_ofFn, Fin.eta]
        exact h (k.castAdd _)) j)
    (fun j => by
      have lhs_eq := tensorHom_eq_right a j f g
      have rhs_eq := tensorHom_eq_right b j f g
      rw [lhs_eq, rhs_eq]
      exact g.property (fun k => by
        simp only [Vector.get, Vector.toArray_ofFn, Fin.val_cast, Array.getElem_ofFn, Fin.eta]
        exact h (k.natAdd _)) j)
    i

/-- The monoidal product of two morphisms. -/
@[inline, simp]
abbrev tensorHom
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨tensorHomVal f g, tensorHom_monotone f g⟩

/-- The underlying wire-function of the forward direction of a wire-count isomorphism. -/
@[simp]
abbrev isoHomVal (h : n = m) : Wires V n → Wires V m := (·.cast h)

@[simp]
lemma iso_hom_monotone (h : n = m) : Monotone (isoHomVal (V:=V) h) :=
  fun _ _ hab i => hab (i.cast h.symm)

/-- The forward direction of a wire-count isomorphism. -/
@[simp]
abbrev isoHom (h : n = m) : { f : Wires V n → Wires V m // Monotone f } :=
  ⟨isoHomVal h, iso_hom_monotone h⟩

/-- The underlying wire-function of the inverse direction of a wire-count isomorphism. -/
@[simp]
abbrev isoInvVal (h : n = m) : Wires V m → Wires V n := (·.cast h.symm)

lemma iso_inv_monotone (h : n = m) : Monotone (isoInvVal (V:=V) h) :=
  fun _ _ hab i => hab (i.cast h)

/-- The inverse direction of a wire-count isomorphism. -/
@[simp]
abbrev isoInv (h : n = m) : { f : Wires V m → Wires V n // Monotone f } :=
  ⟨isoInvVal h, iso_inv_monotone h⟩

@[simp]
lemma iso_hom_inv_id
    (h : n = m) :
    isoHom h ≫ isoInv h = 𝟙 (OfNat.ofNat n : CombinationalCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl

lemma iso_inv_hom_id
    (h : n = m) :
    isoInv h ≫ isoHom h = 𝟙 (OfNat.ofNat m : CombinationalCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl

/-- The isomorphism between objects with equal wire counts. -/
@[inline, simp]
def iso
    (h : n = m) :
    CombinationalCircuitCategory.of V G n ≅ CombinationalCircuitCategory.of V G m :=
  { hom := isoHom h
    inv := isoInv h
    hom_inv_id := iso_hom_inv_id h
    inv_hom_id := iso_inv_hom_id h }

@[simp]
lemma whisker
    (X Y : CombinationalCircuitCategory V G) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (X.tensorObj Y) := by
  apply Subtype.ext; funext v
  change tensorHomVal (𝟙 X) (𝟙 Y) v = v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X) (𝟙 Y)]
    simp only [CategoryStruct.id, id]; rw [idVal, Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X) (𝟙 Y)]
    simp only [CategoryStruct.id, id]; rw [idVal, Wires.get_ofFn]

/-- Left whiskering of a morphism by a fixed object. -/
@[inline, simp]
abbrev whiskerLeft
    (X : CombinationalCircuitCategory V G)
    {Y₁ Y₂ : CombinationalCircuitCategory V G} :
    (Y₁ ⟶ Y₂) →
    (tensorObj X Y₁ ⟶ tensorObj X Y₂) :=
  tensorHom (𝟙 X)

/-- Right whiskering of a morphism by a fixed object. -/
@[inline, simp]
abbrev whiskerRight
    {X₁ X₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ X₂)
    (Y : CombinationalCircuitCategory V G) : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom f (𝟙 Y)

@[simp]
lemma tensorHom_def
    {W X Y Z : CombinationalCircuitCategory V G} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorHom f g = whiskerRight f Y ≫ whiskerLeft X g := by
  apply Subtype.ext; funext v
  change tensorHomVal f g v = tensorHomVal id g (tensorHomVal f id v)
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j f g, tensorHom_eq_left _ j id g]
    simp only [id]; rw [idVal, Wires.get_ofFn]
    exact (tensorHom_eq_left v j f id).symm
  · rw [tensorHom_eq_right v j f g, tensorHom_eq_right _ j id g]
    simp only [id]
    exact congrArg (fun x => (g.val x).get j)
      (Wires.ext (fun k => by
        conv_rhs => rw [Wires.get_ofFn]
        exact (tensorHom_eq_right v k f (𝟙 _)).symm))

@[simp]
lemma id_tensorHom_id
    (X₁ X₂ : CombinationalCircuitCategory V G) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (X₁.tensorObj X₂) := by
  apply Subtype.ext; funext v
  change tensorHomVal (𝟙 X₁) (𝟙 X₂) v = v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X₁) (𝟙 X₂)]
    simp only [CategoryStruct.id, id]; rw [idVal, Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X₁) (𝟙 X₂)]
    simp only [CategoryStruct.id, id]; rw [idVal, Wires.get_ofFn]

@[simp]
lemma tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CombinationalCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply Subtype.ext; funext v
  change tensorHomVal g₁ g₂ (tensorHomVal f₁ f₂ v) = tensorHomVal (f₁ ≫ g₁) (f₂ ≫ g₂) v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left _ j g₁ g₂, tensorHom_eq_left v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₁.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_left v k f₁ f₂))
  · rw [tensorHom_eq_right _ j g₁ g₂, tensorHom_eq_right v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₂.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_right v k f₁ f₂))

/-- The monoidal unit, the object with no wires. -/
@[inline, simp]
def tensorUnit : CombinationalCircuitCategory V G := .of V G 0

omit [SemilatticeSup V] in
@[simp]
lemma associator_eq
    (X Y Z : CombinationalCircuitCategory V G) :
    X.obj + Y.obj + Z.obj = X.obj + (Y.obj + Z.obj) :=
  Nat.add_assoc X.obj Y.obj Z.obj

/-- The associator isomorphism of the monoidal structure. -/
@[inline, simp]
def associator
    (X Y Z : CombinationalCircuitCategory V G) :
    (X.tensorObj Y).tensorObj Z ≅ X.tensorObj (Y.tensorObj Z) :=
  iso (associator_eq X Y Z)

lemma associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CombinationalCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (Y₁.associator Y₂ Y₃).hom =
      (X₁.associator X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp [CategoryStruct.comp, Function.comp, Vector.append, Vector.cast]

lemma pentagon
    (W X Y Z : CombinationalCircuitCategory V G) :
    whiskerRight (W.associator X Y).hom Z ≫
      (W.associator (X.tensorObj Y) Z).hom ≫
      whiskerLeft W (X.associator Y Z).hom =
    ((W.tensorObj X).associator Y Z).hom ≫ (W.associator X (Y.tensorObj Z)).hom := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [CategoryStruct.comp, Function.comp, Vector.append, Vector.cast]
  simp [show W.obj + (X.obj + (Y.obj + Z.obj)) =
    W.obj + (X.obj + Y.obj) + Z.obj from by omega,
    show min W.obj (W.obj + (X.obj + Y.obj) + Z.obj) = W.obj from by omega]

omit [SemilatticeSup V] in
lemma leftUnitor_eq
    (X : CombinationalCircuitCategory V G) :
    (tensorUnit (V:=V) (G:=G)).obj + X.obj = X.obj :=
  Nat.zero_add X.obj

omit [SemilatticeSup V] in
lemma rightUnitor_eq
    (X : CombinationalCircuitCategory V G) :
    X.obj + (tensorUnit (V:=V) (G:=G)).obj = X.obj :=
  Nat.add_zero X.obj

/-- The left unitor isomorphism of the monoidal structure. -/
@[simp]
abbrev leftUnitor (X : CombinationalCircuitCategory V G) : tensorObj tensorUnit X ≅ X :=
  iso (leftUnitor_eq X)

/-- The right unitor isomorphism of the monoidal structure. -/
@[simp]
abbrev rightUnitor (X : CombinationalCircuitCategory V G) : tensorObj X tensorUnit ≅ X :=
  iso (rightUnitor_eq X)

lemma leftUnitor_naturality
    {X Y : CombinationalCircuitCategory V G} (f : X ⟶ Y) :
    whiskerLeft tensorUnit f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp [iso, CategoryStruct.comp, Function.comp, Vector.append, Vector.cast]

lemma rightUnitor_naturality
    {X Y : CombinationalCircuitCategory V G}
    (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp only [CategoryStruct.comp, Function.comp, Vector.append, Vector.cast]
  congr 1
  simp

open MonoidalCategory

lemma triangle
    (X Y : CombinationalCircuitCategory V G) :
    (associator X tensorUnit Y).hom ≫ whiskerLeft X (leftUnitor Y).hom =
    whiskerRight (rightUnitor X).hom Y := by
  apply Subtype.ext; funext v; apply Vector.ext; intro i hi
  simp [CategoryStruct.comp, Vector.append, Function.comp]

@[inline, simp]
instance : MonoidalCategory.{v} (CombinationalCircuitCategory V G) where
  tensorObj
  tensorHom
  whiskerLeft
  whiskerRight
  tensorHom_def
  id_tensorHom_id
  tensorHom_comp_tensorHom
  whiskerLeft_id := whisker
  id_whiskerRight := whisker
  tensorUnit
  associator
  associator_naturality
  leftUnitor
  leftUnitor_naturality
  rightUnitor
  rightUnitor_naturality
  pentagon
  triangle

@[simp]
lemma monoidal_tensorObj_obj
    (X Y : CombinationalCircuitCategory V G) :
    (X ⊗ Y).obj = X.obj + Y.obj := rfl

@[simp]
lemma monoidal_tensorUnit_obj :
    (𝟙_ (CombinationalCircuitCategory V G)).obj = 0 := rfl

@[simp]
lemma id_hom_apply
    (X : CombinationalCircuitCategory V G) (v : Wires V X.obj) :
    (CategoryStruct.id X : Hom V X X).val v = v := rfl

omit [SemilatticeSup V] in
lemma sub_eq {X Y : CombinationalCircuitCategory V G} : X.obj + Y.obj - X.obj = Y.obj := by omega

@[simp]
lemma associator_hom_apply
    (X Y Z : CombinationalCircuitCategory V G)
    (v : Wires V ((X ⊗ Y) ⊗ Z).obj) :
    (α_ X Y Z).hom.val v = v.cast (associator_eq X Y Z) := rfl

@[simp]
lemma associator_inv_apply
    (X Y Z : CombinationalCircuitCategory V G)
    (v : Wires V (X ⊗ (Y ⊗ Z)).obj) :
    (α_ X Y Z).inv.val v = v.cast (associator_eq X Y Z).symm := rfl

lemma braiding_hom_eq
    {X Y : CombinationalCircuitCategory V G} :
    (X ⊗ Y).obj - X.obj + min X.obj (X ⊗ Y).obj = (Y ⊗ X).obj := by simp

/-- The underlying wire-function of the braiding, swapping two blocks of wires. -/
@[inline, simp]
abbrev braidingHomVal
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X ⊗ Y).obj) :
    Wires V (Y ⊗ X).obj :=
  ((v.drop X.obj).append (v.take X.obj)).cast braiding_hom_eq

lemma braiding_hom_lt
    {X Y : CombinationalCircuitCategory V G}
    {j : Fin Y.obj} :
    X.obj + ↑j < (X ⊗ Y).obj := by
  change X.obj + j.val < X.obj + Y.obj
  omega

lemma braiding_hom_ge
    {X Y : CombinationalCircuitCategory V G}
    {j : Fin X.obj} :
    ↑j < (X ⊗ Y).obj := by
  change j.val < X.obj + Y.obj
  omega

@[simp]
lemma braiding_hom_monotone
    {X Y : CombinationalCircuitCategory V G} :
    Monotone (X.braidingHomVal Y) := fun a b hab i => by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Vector.get, Vector.cast, Vector.append, Vector.drop, monoidal_tensorObj_obj,
               Vector.size_toArray, Fin.val_cast, Fin.val_castAdd, Array.size_extract, min_self,
               Nat.add_sub_cancel_left, Fin.is_lt, Array.getElem_append_left, Array.getElem_extract]
    exact hab ⟨X.obj + j.val, braiding_hom_lt⟩
  · simp only [braidingHomVal, monoidal_tensorObj_obj, Vector.get, Vector.cast, Vector.append,
               Vector.drop, Vector.take, Vector.size_toArray, Fin.val_cast, Fin.val_natAdd,
               Array.size_extract, min_self, Nat.add_sub_cancel_left, Nat.le_add_right,
               Array.getElem_append_right, Array.getElem_extract, Nat.zero_add]
    exact hab ⟨j.val, braiding_hom_ge⟩

/-- The braiding morphism, swapping two blocks of wires. -/
@[inline, simp]
def braidingHom (X Y : CombinationalCircuitCategory V G) : X ⊗ Y ⟶ Y ⊗ X :=
  ⟨braidingHomVal X Y, braiding_hom_monotone⟩

lemma braiding_hom_inv_id
    {X Y : CombinationalCircuitCategory V G} :
    X.braidingHom Y ≫ Y.braidingHom X = 𝟙 (X ⊗ Y) := by
  apply Subtype.ext; funext v
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [CategoryStruct.comp, Function.comp, braidingHom,
               braidingHomVal, monoidal_tensorObj_obj, id_coe_apply]
    simp [Vector.get, Vector.drop, Vector.take, Vector.append, Vector.cast]
  · simp only [CategoryStruct.comp, Function.comp, braidingHom,
               braidingHomVal, monoidal_tensorObj_obj, id_coe_apply]
    simp [Vector.get, Vector.drop, Vector.take, Vector.append, Vector.cast]

/-- The braiding isomorphism of the symmetric monoidal structure. -/
@[inline, simp]
def braiding (X Y : CombinationalCircuitCategory V G) : X ⊗ Y ≅ Y ⊗ X :=
  { hom := braidingHom X Y
    inv := braidingHom Y X
    hom_inv_id := braiding_hom_inv_id
    inv_hom_id := braiding_hom_inv_id }

lemma braiding_naturality_left
    {X Y : CombinationalCircuitCategory V G}
    (f : X ⟶ Y)
    (Z : CombinationalCircuitCategory V G) :
    f ▷ Z ≫ (Y.braiding Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
          MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.tensorObj, Vector.get,
          Vector.append]
  · simp only [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
               MonoidalCategoryStruct.whiskerRight, braiding, braidingHom,
               braidingHomVal, monoidal_tensorObj_obj, Function.comp_apply, Vector.get,
               Vector.cast, Vector.append, Vector.drop, Vector.take, Array.take_eq_extract,
               Array.drop_eq_extract, Vector.size_toArray, Array.size_append, Array.size_extract,
               min_self, Nat.add_sub_cancel_left, Array.extract_append, Nat.sub_self,
               Array.extract_extract, Nat.add_zero, Nat.zero_le, Nat.sub_eq_zero_of_le,
               Array.extract_zero, Array.append_empty, Array.append_assoc, Vector.take_eq_extract,
               Vector.toArray_extract,
               Nat.sub_zero, Fin.val_cast, Fin.val_natAdd, Nat.le_add_right, inf_of_le_right,
               Array.getElem_append_right, Array.getElem_extract, Nat.zero_add,
               Vector.getElem_toArray, inf_of_le_left, Nat.add_le_add_iff_left]
    congr 1
    exact congrArg f.val (Wires.ext (fun k => by
      simp [Vector.get]))

lemma braiding_eq
    {X Y Z : CombinationalCircuitCategory V G}
    {f : Y ⟶ Z}
    {v : Wires V (X ⊗ Y).obj}
    {j : Fin X.obj} :
    Vector.get ((X ◁ f ≫ (X.braiding Z).hom).val v) (Fin.natAdd Z.obj j) =
    Vector.get (((X.braiding Y).hom ≫ f ▷ X).val v) (Fin.natAdd Z.obj j) := by
  simp [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
        MonoidalCategoryStruct.whiskerRight, Vector.get, Vector.append]

lemma braiding_naturality_right
    (X : CombinationalCircuitCategory V G)
    {Y Z : CombinationalCircuitCategory V G}
    (f : Y ⟶ Z) :
    X ◁ f ≫ (X.braiding Z).hom = (braiding X Y).hom ≫ f ▷ X := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
          MonoidalCategoryStruct.whiskerRight, Vector.get, Vector.append]
    congr 1
  · simp [CategoryStruct.comp, MonoidalCategoryStruct.whiskerLeft,
          MonoidalCategoryStruct.whiskerRight, Vector.get, Vector.append]

omit [SemilatticeSup V] in
lemma braiding_add
    {X Y : CombinationalCircuitCategory V G}
    (h : ↑i < Y.obj) :
    X.obj + ↑i < X.obj + Y.obj := by omega

lemma braiding_sub
    {X Y : CombinationalCircuitCategory V G}
    {i : Fin (Y ⊗ X).obj} :
    ↑i - Y.obj < (X ⊗ Y).obj := by
  have : i.val < Y.obj + X.obj := i.isLt
  change i.val - Y.obj < X.obj + Y.obj
  omega

omit [SemilatticeSup V] in
lemma braiding_get_ge
    {X Y : CombinationalCircuitCategory V G}
    {j : Fin X.obj} :
    ¬Y.obj + ↑j < Y.obj := by omega

lemma braiding_get
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X ⊗ Y).obj)
    (i : Fin (Y ⊗ X).obj) :
    ((X.braiding Y).hom.val v).get i =
      if h : i.val < Y.obj
      then v.get ⟨X.obj + i.val, braiding_add h⟩
      else v.get ⟨i.val - Y.obj, braiding_sub⟩ := by
  unfold CombinationalCircuitCategory.braiding CombinationalCircuitCategory.braidingHom
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.val_castAdd, dif_pos j.isLt]; simp [Vector.get, Vector.append]
  · simp [Vector.get, Vector.append]

lemma braiding_get_castAdd
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin Y.obj) :
    ((braiding X Y).hom.val v).get (Fin.castAdd X.obj j) =
    v.get (Fin.natAdd X.obj j) := by
  simp only [braiding_get, Fin.val_castAdd, dif_pos j.isLt]
  exact congrArg v.get (Fin.ext (by simp))

lemma braiding_get_natAdd
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin X.obj) :
    ((braiding X Y).hom.val v).get (Fin.natAdd Y.obj j) =
    v.get (Fin.castAdd Y.obj j) := by
  simp only [braiding_get, braiding_get_ge, Fin.val_natAdd]
  exact congrArg v.get (Fin.ext (by simp))

lemma hexagon_forward
    (X Y Z : CombinationalCircuitCategory V G) :
    (α_ X Y Z).hom ≫ (X.braiding (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
    (X.braiding Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (X.braiding Z).hom := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
             MonoidalCategoryStruct.whiskerRight, associator_hom_apply, monoidal_tensorObj_obj]
  refine Fin.addCases (fun j => ?_)
    (fun jj => Fin.addCases (fun k => ?_) (fun k => ?_) jj) i
  all_goals simp only [Fin.val_castAdd, Fin.val_natAdd, Wires.get_cast, braiding_get,
                       monoidal_tensorObj_obj, tensorHom_get, Wires.get_ofFn, CategoryStruct.id,
                       id, idVal]
  all_goals split_ifs <;> (first
    | (refine congrArg v.get (Fin.ext ?_); simp at *; done)
    | (refine congrArg v.get (Fin.ext ?_); simp; omega))

lemma hexagon_reverse
    (X Y Z : CombinationalCircuitCategory V G) :
    (α_ X Y Z).inv ≫ ((X ⊗ Y).braiding Z).hom ≫ (α_ Z X Y).inv =
    X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp,
             MonoidalCategoryStruct.whiskerLeft,
             MonoidalCategoryStruct.whiskerRight,
             associator_inv_apply,
             monoidal_tensorObj_obj]
  refine Fin.addCases
    (fun jj => Fin.addCases (fun k => ?_) (fun k => ?_) jj)
    (fun j => ?_) i
  all_goals simp only [Fin.val_castAdd, Fin.val_natAdd, Wires.get_cast, braiding_get,
                       monoidal_tensorObj_obj, tensorHom_get, Wires.get_ofFn, CategoryStruct.id,
                       id, idVal]
  all_goals split_ifs <;> (first
    | (refine congrArg v.get (Fin.ext ?_); simp at *; done)
    | (refine congrArg v.get (Fin.ext ?_); simp []; omega))

lemma symmetry
    (X Y : CombinationalCircuitCategory V G) :
    (X.braiding Y).hom ≫ (Y.braiding X).hom = 𝟙 (X ⊗ Y) := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp, braiding_get]
  have htXY : (X ⊗ Y).obj = X.obj + Y.obj := rfl
  split <;> split <;>
  exact congrArg v.get (Fin.ext (by simp only []; omega))

@[inline, simp]
instance : SymmetricCategory (CombinationalCircuitCategory V G) where
  braiding
  braiding_naturality_left
  braiding_naturality_right
  hexagon_forward
  hexagon_reverse
  symmetry

end CombinationalCircuitCategory

end Circuit
