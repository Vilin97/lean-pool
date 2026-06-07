/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/

module

public import LeanPool.Circuitlib.Circuit.Category.Combinational
public import Mathlib.Data.Stream.Init

@[expose] public section

/-! # Sequential circuit category

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

namespace Circuit

/-- Category of sequential circuits. -/
structure SequentialCircuitCategory (V : Type*) (G : Type*) where of (V) (G) ::
  obj : ℕ

attribute [inline, simp] SequentialCircuitCategory.obj

@[simp]
instance : OfNat (SequentialCircuitCategory V G) n where
  ofNat := .of V G n

namespace SequentialCircuitCategory

@[inline]
def Stream := Stream'

instance [Preorder α] : Preorder (Stream α) where
  le xs ys := (xs.zip (fun x y => (x, y)) ys).All ((fun (x, y) => x <= y))
  le_refl _ _ := le_refl _
  le_trans _ _ _ h₁ h₂ i := le_trans (h₁ i) (h₂ i)

abbrev Stream.map.{u, v} {α : Type u} {β : Type v} : (α → β) → Stream α → Stream β := Stream'.map

@[simp]
lemma Stream'.map_apply (f : α → β) (s : Stream' α) (t : ℕ) :
    Stream'.map f s t = f (s t) := rfl

universe u v

variable {V : Type v} {G : Type u}

/-- A stream function is causal if the output at time `t` depends only on inputs up to time `t`. -/
def Causal (f : Stream α → Stream β) : Prop :=
  ∀ (x y : Stream α) (t : ℕ), (∀ s, s ≤ t → x s = y s) → f x t = f y t

/-- Homomorphism. -/
def Hom (V : Type v) [Preorder V] (I O : SequentialCircuitCategory V G) :=
  { f : Stream (Wires V I.obj) → Stream (Wires V O.obj) // Monotone f ∧ Causal f }

@[inline, simp]
def id_val : Stream (Wires V n) → Stream (Wires V n) := fun x => x

variable [Preorder V]

@[simp]
lemma id_monotone : Monotone (id_val (V:=V) (n:=n)) := monotone_id

omit [Preorder V] in
@[simp]
lemma id_causal : Causal (id_val (V:=V) (n:=n)) := fun _ _ t h => h t le_rfl

@[inline, simp]
def id : SequentialCircuitCategory.Hom V X X := ⟨id_val, ⟨id_monotone, id_causal⟩⟩

open CategoryTheory

@[inline, simp]
instance : Category.{v} (SequentialCircuitCategory V G) where
  Hom := Hom V
  id _ := id
  comp f g := ⟨g.val ∘ f.val,
    ⟨Monotone.comp g.property.1 f.property.1,
     fun x y t h => g.property.2 _ _ t
      fun s hs => f.property.2 x y s
        fun s' hs' => h s' (le_trans hs' hs)⟩⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[inline, simp]
abbrev tensorObj (X Y : SequentialCircuitCategory V G) : SequentialCircuitCategory V G :=
  .of V G (X.obj + Y.obj)

omit [Preorder V] in
@[simp]
lemma tensorHom_val_add
    {X₁ X₂ : SequentialCircuitCategory V G} :
    min X₁.obj (X₁.obj + X₂.obj) = X₁.obj := by simp

omit [Preorder V] in
@[simp]
lemma tensorHom_val_sub
    {X₁ X₂ : SequentialCircuitCategory V G} :
    X₁.obj + X₂.obj - X₁.obj = X₂.obj := by simp

@[inline, simp]
abbrev tensorHom_val
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (v : Stream (Wires V (X₁.obj + X₂.obj))) :
    Stream (Wires V (Y₁.obj + Y₂.obj)) :=
  Stream'.zip (fun a b => a.append b)
    (f.val (Stream'.map (fun w => (w.take X₁.obj).cast tensorHom_val_add) v))
    (g.val (Stream'.map (fun w => (w.drop X₁.obj).cast tensorHom_val_sub) v))

omit [Preorder V] in
@[simp]
lemma tensorHom_take
    {X₁ X₂ : SequentialCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj)) :
    (a.take X₁.obj).cast tensorHom_val_add =
    Vector.ofFn fun i => a.get (Fin.castAdd X₂.obj i) := by
  apply Wires.ext
  intro i
  simp [Vector.get]

@[inline, simp]
abbrev tensorHom_eq' {X₁ X₂ : SequentialCircuitCategory V G} (w : Vector V (X₁.obj + X₂.obj)) :=
  Vector.ofFn fun i ↦ Vector.get w (Fin.castAdd X₂.obj i)

@[simp]
lemma tensorHom_eq
    {X₁ Y₁ X₂ : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (f : X₁ ⟶ Y₁)
    (t : ℕ) :
    (f.val (Stream'.map tensorHom_eq' v) t).toArray.size = Y₁.obj :=
  (f.val _ t).size_toArray

@[simp]
lemma tensorHom_eq_left
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (t : ℕ) (j : Fin Y₁.obj)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    ((tensorHom_val f g v).get t).get (Fin.castAdd Y₂.obj j) =
    (f.val (Stream'.map tensorHom_eq' v) t).get j := by
  have hsz := (f.val (Stream'.map (fun w =>
    Vector.ofFn fun i ↦ w.get (Fin.castAdd X₂.obj i)) v) t).size_toArray
  simp only [tensorHom_take, tensorHom_val, Stream'.get_zip,
    Vector.get, Vector.append]
  exact Array.getElem_append_left (by simp)

@[simp]
lemma tensorHom_eq_right
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (t : ℕ) (j : Fin Y₂.obj)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    ((tensorHom_val f g v).get t).get (Fin.natAdd Y₁.obj j) =
    (g.val (Stream'.map (fun w =>
      Vector.ofFn fun i ↦ Vector.get w (Fin.natAdd X₁.obj i)) v) t).get j := by
  have hdrop : ∀ (a : Wires V (X₁.obj + X₂.obj)),
      (a.drop X₁.obj).cast tensorHom_val_sub =
      Vector.ofFn fun i => a.get (Fin.natAdd X₁.obj i) := fun a => by
    apply Wires.ext
    intro i
    simp [Vector.get, Vector.drop, Fin.val_natAdd]
  simp only [tensorHom_take, hdrop, tensorHom_val, Stream'.get_zip,
    Vector.get, Vector.append]
  rw [Array.getElem_append_right (by simp)]
  congr 1
  simp

@[simp]
lemma tensorHom_monotone
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    Monotone (tensorHom_val f g) := fun v₁ v₂ h t i =>
  Fin.addCases
    (fun j => by
      have lhs_eq := tensorHom_eq_left v₁ t j f g
      have rhs_eq := tensorHom_eq_left v₂ t j f g
      rw [lhs_eq, rhs_eq]
      exact f.property.1 (fun t' k => by
        simp only [Stream'.get_map, Wires.get_ofFn]
        exact h t' (k.castAdd _)) t j)
    (fun j => by
      have lhs_eq := tensorHom_eq_right v₁ t j f g
      have rhs_eq := tensorHom_eq_right v₂ t j f g
      rw [lhs_eq, rhs_eq]
      exact g.property.1 (fun t' k => by
        simp only [Stream'.get_map, Wires.get_ofFn]
        exact h t' (k.natAdd _)) t j)
    i

@[simp]
lemma tensorHom_causal
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    Causal (tensorHom_val f g) := fun x y t h => by
  simp only [tensorHom_val]
  have hf : f.val (Stream'.map (fun w => (w.take X₁.obj).cast tensorHom_val_add) x) t =
      f.val (Stream'.map (fun w => (w.take X₁.obj).cast tensorHom_val_add) y) t :=
    f.property.2 _ _ t fun s hs => by
      show (Stream'.map _ x) s = (Stream'.map _ y) s
      simp only [Stream'.map_apply, h s hs]
  have hg : g.val (Stream'.map (fun w => (w.drop X₁.obj).cast tensorHom_val_sub) x) t =
      g.val (Stream'.map (fun w => (w.drop X₁.obj).cast tensorHom_val_sub) y) t :=
    g.property.2 _ _ t fun s hs => by
      show (Stream'.map _ x) s = (Stream'.map _ y) s
      simp only [Stream'.map_apply, h s hs]
  unfold Stream'.zip Stream'.get
  rw [hf, hg]

@[inline, simp]
abbrev tensorHom
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨tensorHom_val f g, ⟨tensorHom_monotone f g, tensorHom_causal f g⟩⟩

@[simp]
abbrev iso_hom_val (h : n = m) : Stream (Wires V n) → Stream (Wires V m) :=
  Stream'.map (·.cast h)

@[simp]
lemma iso_hom_monotone (h : n = m) : Monotone (iso_hom_val (V:=V) h) :=
  fun _ _ hab t i => hab t (i.cast h.symm)

omit [Preorder V] in
@[simp]
lemma iso_hom_causal (h : n = m) : Causal (iso_hom_val (V:=V) h) :=
  fun _ _ t heq => congrArg (·.cast h) (heq t le_rfl)

@[simp]
abbrev iso_hom (h : n = m) :
    { f : Stream (Wires V n) → Stream (Wires V m) // Monotone f ∧ Causal f } :=
  ⟨iso_hom_val h, ⟨iso_hom_monotone h, iso_hom_causal h⟩⟩

@[simp]
abbrev iso_inv_val (h : n = m) : Stream (Wires V m) → Stream (Wires V n) :=
  Stream'.map (·.cast h.symm)

@[simp]
lemma iso_inv_monotone (h : n = m) : Monotone (iso_inv_val (V:=V) h) :=
  fun _ _ hab t i => hab t (i.cast h)

omit [Preorder V] in
@[simp]
lemma iso_inv_causal (h : n = m) : Causal (iso_inv_val (V:=V) h) :=
  fun _ _ t heq => congrArg (·.cast h.symm) (heq t le_rfl)

@[simp]
abbrev iso_inv (h : n = m) :
    { f : Stream (Wires V m) → Stream (Wires V n) // Monotone f ∧ Causal f } :=
  ⟨iso_inv_val h, ⟨iso_inv_monotone h, iso_inv_causal h⟩⟩

@[simp]
lemma iso_hom_inv_id
    (h : n = m) :
    iso_hom h ≫ iso_inv h = 𝟙 (OfNat.ofNat n : SequentialCircuitCategory V G) := by
  apply Subtype.ext
  funext v
  rfl

@[simp]
lemma iso_inv_hom_id
    (h : n = m) :
    iso_inv h ≫ iso_hom h = 𝟙 (OfNat.ofNat m : SequentialCircuitCategory V G) := by
  apply Subtype.ext
  funext v
  rfl

omit [Preorder V] in
@[simp]
lemma id_coe_apply
    [Preorder V]
    (X : SequentialCircuitCategory V G) (v : Stream (Wires V X.obj)) :
    (𝟙 X : Hom V X X).val v = v := rfl

@[inline, simp]
def iso
    (h : n = m) :
    SequentialCircuitCategory.of V G n ≅ SequentialCircuitCategory.of V G m :=
  { hom := iso_hom h
    inv := iso_inv h
    hom_inv_id := iso_hom_inv_id h
    inv_hom_id := iso_inv_hom_id h }


@[simp]
lemma whisker
    (X Y : SequentialCircuitCategory V G) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (X.tensorObj Y) := by
  apply Subtype.ext
  funext v t
  change (tensorHom_val (𝟙 X) (𝟙 Y) v).get t = v.get t
  apply Wires.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v t j (𝟙 X) (𝟙 Y)]
    simp [CategoryStruct.id, id, id_val, Stream'.map, Stream'.get, Wires.get_ofFn]
  · rw [tensorHom_eq_right v t j (𝟙 X) (𝟙 Y)]
    simp [CategoryStruct.id, id, id_val, Stream'.map, Stream'.get, Wires.get_ofFn]

@[inline, simp]
abbrev whiskerLeft
    (X : SequentialCircuitCategory V G)
    {Y₁ Y₂ : SequentialCircuitCategory V G} :
    (Y₁ ⟶ Y₂) →
    (tensorObj X Y₁ ⟶ tensorObj X Y₂) :=
  tensorHom (𝟙 X)

@[inline, simp]
abbrev whiskerRight
    {X₁ X₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ X₂)
    (Y : SequentialCircuitCategory V G) : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom f (𝟙 Y)

@[simp]
lemma tensorHom_def
    {W X Y Z : SequentialCircuitCategory V G} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorHom f g = whiskerRight f Y ≫ whiskerLeft X g := by
  apply Subtype.ext
  funext v t
  change (tensorHom_val f g v).get t =
    (tensorHom_val id g (tensorHom_val f id v)).get t
  apply Wires.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v t j f g, tensorHom_eq_left _ t j id g]
    simp only [id, Stream'.map, id_val, Wires.get_ofFn]
    exact (tensorHom_eq_left v t j f id).symm
  · rw [tensorHom_eq_right v t j f g, tensorHom_eq_right _ t j id g]
    simp only [id]
    have heq : (Stream'.map (fun w =>
        Vector.ofFn fun i ↦ w.get (Fin.natAdd W.obj i)) v) =
      (Stream'.map (fun w =>
        Vector.ofFn fun i ↦ w.get (Fin.natAdd X.obj i))
          (tensorHom_val f ⟨id_val, ⟨id_monotone, id_causal⟩⟩ v)) := by
      funext t'
      apply Wires.ext
      intro k
      simp only [Stream'.map, Wires.get_ofFn]
      have := (tensorHom_eq_right v t' k f (𝟙 Y)).symm
      simp only [CategoryStruct.id, id, id_val, Stream'.map,
        Wires.get_ofFn] at this
      exact this
    exact congrArg (fun s => (g.val s t).get j) heq

@[simp]
lemma id_tensorHom_id
    (X₁ X₂ : SequentialCircuitCategory V G) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (X₁.tensorObj X₂) := whisker X₁ X₂

@[simp]
lemma tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SequentialCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply Subtype.ext
  funext v t
  change (tensorHom_val g₁ g₂ (tensorHom_val f₁ f₂ v)).get t =
    (tensorHom_val (f₁ ≫ g₁) (f₂ ≫ g₂) v).get t
  apply Wires.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left _ t j g₁ g₂,
        tensorHom_eq_left v t j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp, Function.comp]
    exact congrArg (fun s => (g₁.val s t).get j)
      (funext fun t' => Wires.ext fun k => by
        simp only [Stream'.map, Wires.get_ofFn]
        exact tensorHom_eq_left v t' k f₁ f₂)
  · rw [tensorHom_eq_right _ t j g₁ g₂,
        tensorHom_eq_right v t j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp, Function.comp]
    exact congrArg (fun s => (g₂.val s t).get j)
      (funext fun t' => Wires.ext fun k => by
        simp only [Stream'.map, Wires.get_ofFn]
        exact tensorHom_eq_right v t' k f₁ f₂)

@[inline, simp]
def tensorUnit : SequentialCircuitCategory V G := .of V G 0

omit [Preorder V] in
@[simp]
lemma associator_eq
    (X Y Z : SequentialCircuitCategory V G) :
    X.obj + Y.obj + Z.obj = X.obj + (Y.obj + Z.obj) :=
  Nat.add_assoc X.obj Y.obj Z.obj

@[inline, simp]
def associator
    (X Y Z : SequentialCircuitCategory V G) :
    (X.tensorObj Y).tensorObj Z ≅ X.tensorObj (Y.tensorObj Z) :=
  iso (associator_eq X Y Z)

@[simp]
lemma associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SequentialCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (Y₁.associator Y₂ Y₃).hom =
      (X₁.associator X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply Subtype.ext
  funext v t
  apply Vector.ext
  intro i hi
  simp only [CategoryStruct.comp, Function.comp, tensorHom_val,
    associator, iso, iso_hom, iso_hom_val, Stream'.map_map,
    Stream'.map, Stream'.zip, Stream'.get, Vector.append,
    Vector.cast]
  simp only [Vector.getElem_mk, Array.append_assoc]
  congr 1
  congr 1
  · exact congrArg Vector.toArray (congrFun (congrArg f₁.val
      (funext fun t' => Wires.ext fun k => by
        simp [Stream'.map, Function.comp, Vector.get, Vector.take])) t)
  congr 1
  · exact congrArg Vector.toArray (congrFun (congrArg f₂.val
      (funext fun t' => Wires.ext fun k => by
        simp [Stream'.map, Function.comp, Vector.get, Vector.take, Vector.drop])) t)
  · exact congrArg Vector.toArray (congrFun (congrArg f₃.val
      (funext fun t' => Wires.ext fun k => by
        simp [Stream'.map, Function.comp, Vector.get, Vector.drop])) t)

@[simp]
lemma pentagon
    (W X Y Z : SequentialCircuitCategory V G) :
    whiskerRight (W.associator X Y).hom Z ≫
      (W.associator (X.tensorObj Y) Z).hom ≫
      whiskerLeft W (X.associator Y Z).hom =
    ((W.tensorObj X).associator Y Z).hom ≫ (W.associator X (Y.tensorObj Z)).hom := by
  apply Subtype.ext
  funext v t
  apply Vector.ext
  intro i hi
  simp only [CategoryStruct.comp, Function.comp, tensorHom_val,
    associator, iso, iso_hom, iso_hom_val,
    Vector.append, Vector.cast]
  unfold Stream'.map Stream'.zip Stream'.get
  simp [show W.obj + (X.obj + (Y.obj + Z.obj)) =
    W.obj + (X.obj + Y.obj) + Z.obj from by omega,
    show min W.obj (W.obj + (X.obj + Y.obj) + Z.obj) = W.obj from by omega]

omit [Preorder V] in
@[simp]
lemma leftUnitor_eq
    (X : SequentialCircuitCategory V G) :
    (tensorUnit (V:=V) (G:=G)).obj + X.obj = X.obj :=
  Nat.zero_add X.obj

omit [Preorder V] in
@[simp]
lemma rightUnitor_eq
    (X : SequentialCircuitCategory V G) :
    X.obj + (tensorUnit (V:=V) (G:=G)).obj = X.obj :=
  Nat.add_zero X.obj

@[simp]
abbrev leftUnitor (X : SequentialCircuitCategory V G) : tensorObj tensorUnit X ≅ X :=
  iso (leftUnitor_eq X)

@[simp]
abbrev rightUnitor (X : SequentialCircuitCategory V G) : tensorObj X tensorUnit ≅ X :=
  iso (rightUnitor_eq X)

@[simp]
lemma leftUnitor_naturality
    {X Y : SequentialCircuitCategory V G} (f : X ⟶ Y) :
    whiskerLeft tensorUnit f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  apply Subtype.ext
  funext v t
  apply Vector.ext
  intro i hi
  simp only [iso, CategoryStruct.comp, Function.comp,
    tensorHom_val, iso_hom_val, iso_hom]
  unfold Stream'.map Stream'.zip Stream'.get
  simp [Vector.append]

@[simp]
lemma rightUnitor_naturality
    {X Y : SequentialCircuitCategory V G}
    (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  apply Subtype.ext
  funext v t
  apply Vector.ext
  intro i hi
  simp only [CategoryStruct.comp, Function.comp,
    tensorHom_val, iso_hom_val, iso_hom, iso]
  unfold Stream'.map Stream'.zip Stream'.get
  have : (v t).toArray.extract X.obj X.obj = #[] := by grind
  simp [Vector.append, this]

open MonoidalCategory

@[simp]
lemma triangle
    (X Y : SequentialCircuitCategory V G) :
    (associator X tensorUnit Y).hom ≫ whiskerLeft X (leftUnitor Y).hom =
    whiskerRight (rightUnitor X).hom Y := by
  apply Subtype.ext
  funext v t
  apply Vector.ext
  intro i hi
  simp only [CategoryStruct.comp, Function.comp,
    tensorHom_val, iso_hom_val, iso_hom, iso]
  unfold Stream'.map Stream'.zip Stream'.get
  simp [Stream'.map, Stream'.get, Vector.cast]

@[inline, simp]
instance : MonoidalCategory.{v} (SequentialCircuitCategory V G) where
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
    (X Y : SequentialCircuitCategory V G) :
    (X ⊗ Y).obj = X.obj + Y.obj := rfl

@[simp]
lemma braiding_hom_eq
    {X Y : SequentialCircuitCategory V G} :
    (X ⊗ Y).obj - X.obj + min X.obj (X ⊗ Y).obj = (Y ⊗ X).obj :=
  by simp

@[inline, simp]
abbrev braiding_hom_val
    (X Y : SequentialCircuitCategory V G) :
    Stream (Wires V (X ⊗ Y).obj) →
    Stream (Wires V (Y ⊗ X).obj) :=
  Stream.map (fun v => ((v.drop X.obj).append (v.take X.obj)).cast braiding_hom_eq)

@[simp]
lemma braiding_hom_lt
    {X Y : SequentialCircuitCategory V G}
    {j : Fin Y.obj} :
    X.obj + ↑j < (X ⊗ Y).obj := by
  change X.obj + j.val < X.obj + Y.obj
  omega

@[simp]
lemma braiding_hom_ge
    {X Y : SequentialCircuitCategory V G}
    {j : Fin X.obj} :
    ↑j < (X ⊗ Y).obj := by
  change j.val < X.obj + Y.obj
  omega

@[simp]
lemma braiding_hom_monotone
    {X Y : SequentialCircuitCategory V G} :
    Monotone (X.braiding_hom_val Y) := fun a b hab t i => by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Stream'.map, Stream'.get, Vector.get, Vector.cast, Vector.append,
               Vector.drop, monoidal_tensorObj_obj, Vector.size_toArray, Fin.val_cast,
               Fin.val_castAdd, Array.size_extract, min_self, Nat.add_sub_cancel_left, Fin.is_lt,
               Array.getElem_append_left, Array.getElem_extract]
    exact hab t ⟨X.obj + j.val, braiding_hom_lt⟩
  · simp only [Stream.map, Stream'.map, Stream'.get, braiding_hom_val, monoidal_tensorObj_obj,
               Vector.get, Vector.cast, Vector.append, Vector.drop, Vector.take,
               Vector.size_toArray, Fin.val_cast, Fin.val_natAdd, Array.size_extract, min_self,
               Nat.add_sub_cancel_left, Nat.le_add_right, Array.getElem_append_right,
               Array.getElem_extract, Nat.zero_add]
    exact hab t ⟨j.val, braiding_hom_ge⟩

@[simp]
lemma braiding_hom_causal
    {X Y : SequentialCircuitCategory V G} :
    Causal (X.braiding_hom_val Y) := fun _ _ t h => by
  simp only [braiding_hom_val, Stream.map, Stream'.map_apply, h t le_rfl]

@[inline, simp]
def braiding_hom (X Y : SequentialCircuitCategory V G) : X ⊗ Y ⟶ Y ⊗ X :=
  ⟨braiding_hom_val X Y, ⟨braiding_hom_monotone, braiding_hom_causal⟩⟩

@[simp]
lemma braiding_hom_inv_id
    {X Y : SequentialCircuitCategory V G} :
    X.braiding_hom Y ≫ Y.braiding_hom X = 𝟙 (X ⊗ Y) := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [CategoryStruct.comp, Function.comp, braiding_hom, braiding_hom_val,
          monoidal_tensorObj_obj, id_coe_apply, monoidal_tensorObj_obj, Vector.get, Vector.append]
  · simp [CategoryStruct.comp, Function.comp, braiding_hom, braiding_hom_val,
          monoidal_tensorObj_obj, id_coe_apply, Vector.get, Vector.append]

@[inline, simp]
def braiding (X Y : SequentialCircuitCategory V G) : X ⊗ Y ≅ Y ⊗ X :=
  { hom := braiding_hom X Y
    inv := braiding_hom Y X
    hom_inv_id := braiding_hom_inv_id
    inv_hom_id := braiding_hom_inv_id }

@[simp]
lemma braiding_naturality_left
    {X Y : SequentialCircuitCategory V G}
    (f : X ⟶ Y)
    (Z : SequentialCircuitCategory V G) :
    f ▷ Z ≫ (Y.braiding Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  change (braiding_hom_val Y Z (tensorHom_val f (𝟙 Z) v) t).get i =
    (tensorHom_val (𝟙 Z) f (braiding_hom_val X Z v) t).get i
  simp only [braiding_hom_val, tensorHom_val]
  unfold Stream.map Stream'.map Stream'.zip Stream'.get
  dsimp only [Function.comp]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Vector.get, Vector.append]
  · simp only [Vector.get, monoidal_tensorObj_obj, Vector.cast, Vector.append, Vector.drop,
               Vector.take, Array.take_eq_extract, Array.drop_eq_extract, Vector.size_toArray,
               id_coe_apply, Array.size_append, Array.size_extract, min_self,
               Nat.add_sub_cancel_left, Array.extract_append, Nat.sub_self, Array.extract_extract,
               Nat.add_zero, Nat.zero_le, Nat.sub_eq_zero_of_le, Array.extract_zero,
               Array.append_empty, Array.append_assoc, Vector.take_eq_extract,
               Vector.toArray_extract, Vector.cast_mk, Vector.drop_mk, Vector.extract_mk,
               Nat.sub_zero, Fin.val_cast, Fin.val_natAdd, Nat.le_add_right, inf_of_le_right,
               Array.getElem_append_right, Array.getElem_extract, Nat.zero_add,
               Vector.getElem_toArray, inf_of_le_left, Nat.add_le_add_iff_left]
    congr 1
    exact congrFun (congrArg f.val (funext fun n =>
      Wires.ext (fun k => by simp [Vector.get]))) t

@[simp]
lemma braiding_naturality_right
    (X : SequentialCircuitCategory V G)
    {Y Z : SequentialCircuitCategory V G}
    (f : Y ⟶ Z) :
    X ◁ f ≫ (X.braiding Z).hom = (braiding X Y).hom ≫ f ▷ X := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  change (braiding_hom_val X Z (tensorHom_val (𝟙 X) f v) t).get i =
    (tensorHom_val f (𝟙 X) (braiding_hom_val X Y v) t).get i
  simp only [braiding_hom_val, tensorHom_val]
  unfold Stream.map Stream'.map Stream'.zip Stream'.get
  dsimp only [Function.comp]
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp [Vector.get, Vector.drop, Vector.take, Vector.append, Vector.cast]
  · simp [Vector.get, Vector.append]

omit [Preorder V] in
@[simp]
lemma braiding_add
    {X Y : SequentialCircuitCategory V G}
    (h : ↑i < Y.obj) :
    X.obj + ↑i < X.obj + Y.obj := by omega

@[simp]
lemma braiding_sub
    {X Y : SequentialCircuitCategory V G}
    {i : Fin (Y ⊗ X).obj} :
    ↑i - Y.obj < (X ⊗ Y).obj := by
  have : i.val < Y.obj + X.obj := i.isLt
  change i.val - Y.obj < X.obj + Y.obj
  omega

omit [Preorder V] in
@[simp]
lemma braiding_get_ge
    {X Y : SequentialCircuitCategory V G}
    {j : Fin X.obj} :
    ¬Y.obj + ↑j < Y.obj := by omega

omit [Preorder V] in
@[simp]
lemma iso_hom_get
    (h : n = m) (v : Stream (Wires V n)) (t : ℕ) (i : Fin m) :
    (iso_hom_val (V:=V) h v t).get i = (v t).get ⟨i.val, h ▸ i.isLt⟩ := by
  unfold iso_hom_val
  simp [Stream'.map, Stream'.get, Wires.get_cast]

@[simp]
lemma braiding_get
    (X Y : SequentialCircuitCategory V G)
    (v : Stream (Wires V (X ⊗ Y).obj))
    (t : ℕ)
    (i : Fin (Y ⊗ X).obj) :
    (X.braiding_hom_val Y v t).get i =
      if h : i.val < Y.obj
      then (v t).get ⟨X.obj + i.val, braiding_add h⟩
      else (v t).get ⟨i.val - Y.obj, braiding_sub⟩ := by
  unfold braiding_hom_val Stream.map Stream'.map Stream'.get
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.val_castAdd, dif_pos j.isLt]
    simp [Vector.get, Vector.append]
  · simp only [Fin.val_natAdd, dif_neg (show ¬(Y.obj + j.val < Y.obj) from by omega)]
    simp [Vector.get, Vector.append]

@[simp]
lemma tensorHom_get
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (t : ℕ)
    (i : Fin (Y₁.obj + Y₂.obj)) :
    (tensorHom_val f g v t).get i =
    if h : i.val < Y₁.obj
    then (f.val (Stream'.map tensorHom_eq' v) t).get ⟨i.val, h⟩
    else (g.val (Stream'.map (fun w =>
      Vector.ofFn fun k => w.get (Fin.natAdd X₁.obj k)) v) t).get
      ⟨i.val - Y₁.obj, by omega⟩ := by
  change ((tensorHom_val f g v).get t).get i = _
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left]
    simp only [Fin.val_castAdd, dif_pos j.isLt]
  · rw [tensorHom_eq_right]
    simp only [Fin.val_natAdd, dif_neg (show ¬(Y₁.obj + j.val < Y₁.obj) from by omega)]
    congr 1
    exact Fin.ext (by simp)

omit [Preorder V] in
@[simp]
lemma tensorObj_size_eq_forward
    {X Y Z : SequentialCircuitCategory V G}
    (v : Stream (Wires V ((X.tensorObj Y).tensorObj Z).obj)) :
    (v t).toArray.size = ((X.tensorObj Y).tensorObj Z).obj := (v t).size_toArray

@[simp]
lemma hexagon_forward
    (X Y Z : SequentialCircuitCategory V G) :
    (α_ X Y Z).hom ≫ (X.braiding (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
    (X.braiding Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (X.braiding Z).hom := by
  change (associator X Y Z).hom ≫ (X.braiding (tensorObj Y Z)).hom ≫ (associator Y Z X).hom =
    whiskerRight (X.braiding Y).hom Z ≫ (associator Y X Z).hom ≫ whiskerLeft Y (X.braiding Z).hom
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  simp only [CategoryStruct.comp, Function.comp, tensorHom_val, associator, iso, iso_hom,
             iso_hom_val, braiding, braiding_hom, braiding_hom_val, Vector.append, Vector.cast,
             CategoryStruct.id, id]
  unfold Stream.map Stream'.map Stream'.zip Stream'.get
  simp only [Vector.drop, Vector.take, id_val]
  unfold Array.take Array.drop
  have htXY : (X ⊗ Y).obj = X.obj + Y.obj := rfl
  have hm1 : min (X.obj + Y.obj) (X.obj + Y.obj + Z.obj) = X.obj + Y.obj :=
    min_eq_left (by omega)
  have hm2 : min X.obj (X.obj + Y.obj) = X.obj := min_eq_left (by omega)
  refine Fin.addCases (fun j => ?_) (fun jj => Fin.addCases (fun k => ?_) (fun k => ?_) jj) i
  all_goals simp only [Vector.get, Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast,
    Array.size_extract, Array.size_append, tensorObj_size_eq_forward, htXY, hm1, hm2, min_self,
    Nat.add_sub_cancel_left, Nat.sub_zero]
  · rw [Array.getElem_append_left (by simp [*]; omega), Array.getElem_extract,
        Array.getElem_append_left (by simp [*]), Array.getElem_extract,
        Array.getElem_append_left (by simp [*]; omega),
        Array.getElem_append_left (by simp [*]),
        Array.getElem_extract, Array.getElem_extract]
    congr 1
    omega
  · rw [Array.getElem_append_left (by simp [*]), Array.getElem_extract,
        Array.getElem_append_right (by simp [*])]
    simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_forward, hm1, hm2, min_self,
      Nat.add_sub_cancel_left, Nat.sub_zero]
    rw [Array.getElem_append_left (by simp [*]; omega),
        Array.getElem_extract, Array.getElem_extract,
        Array.getElem_append_right (by simp [*])]
    simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_forward, Nat.sub_zero]
    rw [Array.getElem_extract]
    congr 1
    omega
  · rw [Array.getElem_append_right (by simp [*])]
    simp only [Array.size_extract, tensorObj_size_eq_forward, min_self]
    rw [Array.getElem_extract,
        Array.getElem_append_right (by simp [*])]
    simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_forward, hm1, hm2, min_self,
      Nat.add_sub_cancel_left, Nat.sub_zero]
    rw [Array.getElem_append_right (by simp [*]; omega)]
    simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_forward, hm1, hm2, min_self,
      Nat.add_sub_cancel_left, Nat.sub_zero]
    rw [Array.getElem_extract, Array.getElem_extract,
        Array.getElem_append_left (by simp [*]),
        Array.getElem_append_right (by simp [*])]
    simp only [Array.size_extract, tensorObj_size_eq_forward, hm1, min_self,
               Nat.add_sub_cancel_left, Nat.sub_zero]
    rw [Array.getElem_extract, Array.getElem_extract]
    congr 1
    omega

omit [Preorder V] in
@[simp]
lemma tensorObj_size_eq_reverse
    {X Y Z : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X.tensorObj (Y.tensorObj Z)).obj)) :
    (v t).toArray.size = (X.tensorObj (Y.tensorObj Z)).obj := (v t).size_toArray

@[simp]
lemma hexagon_reverse
    (X Y Z : SequentialCircuitCategory V G) :
    (α_ X Y Z).inv ≫ ((X ⊗ Y).braiding Z).hom ≫ (α_ Z X Y).inv =
    X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  change (associator X Y Z).inv ≫ ((tensorObj X Y).braiding Z).hom ≫ (associator Z X Y).inv =
    whiskerLeft X (Y.braiding Z).hom ≫ (associator X Z Y).inv ≫ whiskerRight (X.braiding Z).hom Y
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  simp only [CategoryStruct.comp, Function.comp, tensorHom_val, associator, iso, iso_inv,
             iso_inv_val, braiding, braiding_hom, braiding_hom_val, Vector.append, Vector.cast,
             CategoryStruct.id, id]
  unfold Stream.map Stream'.map Stream'.zip Stream'.get
  simp only [Vector.drop, Vector.take, id_val]
  unfold Array.take Array.drop
  have htXZ : (X ⊗ Z).obj = X.obj + Z.obj := rfl
  have hm9 : min Y.obj (Y.obj + Z.obj) = Y.obj := min_eq_left (by omega)
  have hm3' : min X.obj (X.obj + (Y.obj + Z.obj)) = X.obj := min_eq_left (by omega)
  have hm7' : min (X.obj + Z.obj) (X.obj + (Z.obj + Y.obj)) = X.obj + Z.obj :=
    min_eq_left (by omega)
  have hsub1 : X.obj + (Y.obj + Z.obj) - (X.obj + Y.obj) = Z.obj := by omega
  refine Fin.addCases
    (fun jj => Fin.addCases (fun j => ?_) (fun k => ?_) jj)
    (fun k => ?_) i
  all_goals simp only [Vector.get, Fin.val_castAdd, Fin.val_natAdd, Fin.val_cast,
    Array.size_extract, Array.size_append, tensorObj_size_eq_reverse, htXZ, hm9,
    hm3', hm7', min_self, Nat.add_sub_cancel_left, Nat.sub_zero]
  all_goals
    first
    | rw [Array.getElem_append_right
            (by simp only [Array.size_extract, tensorObj_size_eq_reverse, min_self, hsub1]; omega)]
      simp only [Array.size_extract, tensorObj_size_eq_reverse, min_self, hsub1]
      rw [Array.getElem_extract,
           Array.getElem_append_right
             (by
                simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_reverse,
                           min_self, hm3', Nat.add_sub_cancel_left, Nat.sub_zero]
                omega)]
      simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_reverse, hm3', min_self,
                 Nat.add_sub_cancel_left, Nat.sub_zero]
      rw [Array.getElem_extract,
          Array.getElem_append_right
            (by
               simp only [Array.size_extract, tensorObj_size_eq_reverse, hm3', Nat.sub_zero]
               omega)]
      simp only [Array.size_extract, tensorObj_size_eq_reverse, hm3', Nat.sub_zero]
      rw [Array.getElem_append_right
            (by
               simp only [Array.size_extract, tensorObj_size_eq_reverse, min_self,
                          Nat.add_sub_cancel_left]
               omega)]
      simp only [Array.size_extract, tensorObj_size_eq_reverse, min_self, Nat.add_sub_cancel_left]
      rw [Array.getElem_extract, Array.getElem_extract]
      congr 1
      omega
    | rw [Array.getElem_append_left
            (by simp only [Array.size_extract, tensorObj_size_eq_reverse, min_self, hsub1]; omega),
          Array.getElem_extract,
          Array.getElem_append_left
            (by
               simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_reverse,
                          min_self, hm3', Nat.add_sub_cancel_left, Nat.sub_zero]
               omega),
          Array.getElem_append_left
            (by
               simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_reverse,
                           min_self, hm3', Nat.add_sub_cancel_left, Nat.sub_zero]
               omega),
          Array.getElem_extract, Array.getElem_extract,
          Array.getElem_append_right
             (by
                simp only [Array.size_extract, tensorObj_size_eq_reverse, hm3', Nat.sub_zero]
                omega)]
      simp only [Array.size_extract, tensorObj_size_eq_reverse, hm3', Nat.sub_zero]
      rw [Array.getElem_append_left
            (by
               simp only [Array.size_extract, tensorObj_size_eq_reverse, min_self,
                          Nat.add_sub_cancel_left]
               omega),
          Array.getElem_extract, Array.getElem_extract]
      congr 1
      omega
    | rw [Array.getElem_append_right
            (by simp only [Array.size_extract, tensorObj_size_eq_reverse, min_self, hsub1]; omega)]
      simp only [Array.size_extract, tensorObj_size_eq_reverse, min_self, hsub1]
      rw [Array.getElem_extract,
          Array.getElem_append_left
            (by
               simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_reverse,
                          min_self, Nat.add_sub_cancel_left, Nat.sub_zero]
               omega),
          Array.getElem_append_right
            (by
              simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_reverse, min_self,
                         hm3', Nat.add_sub_cancel_left, Nat.sub_zero]
              omega)]
      simp only [Array.size_extract, Array.size_append, tensorObj_size_eq_reverse, hm3', min_self,
                 Nat.add_sub_cancel_left, Nat.sub_zero]
      rw [Array.getElem_extract, Array.getElem_extract,
          Array.getElem_append_left
            (by
               simp only [Array.size_extract, tensorObj_size_eq_reverse, hm3', hm9, Nat.sub_zero]
               omega),
          Array.getElem_extract]
      congr 1
      omega

@[simp]
lemma symmetry
    (X Y : SequentialCircuitCategory V G) :
    (X.braiding Y).hom ≫ (Y.braiding X).hom = 𝟙 (X ⊗ Y) := by
  change (X.braiding_hom Y) ≫ (Y.braiding_hom X) = 𝟙 (tensorObj X Y)
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  simp only [CategoryStruct.comp, Function.comp, braiding_hom, braiding_get]
  have htXY : (X ⊗ Y).obj = X.obj + Y.obj := rfl
  split <;> split <;>
  exact congrArg (v t).get (Fin.ext (by simp only []; omega))

@[inline, simp]
instance : SymmetricCategory (SequentialCircuitCategory V G) where
  braiding
  braiding_naturality_left
  braiding_naturality_right
  hexagon_forward
  hexagon_reverse
  symmetry

end SequentialCircuitCategory

end Circuit
