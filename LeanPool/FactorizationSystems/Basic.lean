/-
Copyright (c) 2026 Ivan Kobe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Kobe
-/

import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.MorphismProperty.Composition

namespace CategoryTheory
universe u v u' v'
variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- The predicate that a class of morphism contains the isomorphisms -/
def contains_isos (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y : C⦄ (f : X ≅ Y) , W f.hom

/-- The predicate of a class of morphisms being closed under compositin -/
class is_closed_comp (W : MorphismProperty C) extends W.Respects W where

/-- The structure of a factorization system on a category C with specified classes of morphisms -/
structure FactorizationSystem {C : Type u} [Category.{v} C] (L R : MorphismProperty C) where
  /-- The left class contains isomorphism -/
  contains_isos_left_class : contains_isos L
  /-- The right class contains isomorphism -/
  contains_isos_right_class : contains_isos R
  /-- The left class is closed under composition -/
  is_closed_comp_left_class : is_closed_comp L
  /-- The right class is closed under composition -/
  is_closed_comp_right_class : is_closed_comp R
  /-- The midpoint/image of the factorization -/
  image : {X Y : C} → (f : X ⟶ Y) → C
  /-- The left map of the factorization -/
  left_map : {X Y : C} → (f : X ⟶ Y) → X ⟶ image f
  /-- The left map of the factorization is contained in the left class -/
  left_map_in_left_class : {X Y : C} → (f : X ⟶ Y) → L (left_map f)
  /-- The right map of the factorization -/
  right_map : {X Y : C} → (f : X ⟶ Y) → image f ⟶ Y
  /-- The left map of the factorization is contained in the left class -/
  right_map_in_right_class : {X Y : C} → (f : X ⟶ Y) → R (right_map f)
  /-- The factorization -/
  factorization : {X Y : C} → (f : X ⟶ Y) → left_map f ≫ right_map f = f := by aesop_cat
  /-- The factorization is unique up to isomorphism -/
  factorization_iso :
    {X Y : C} → (f : X ⟶ Y) → (im : C) → (left : X ⟶ im) → L left→ (right : im ⟶ Y) → R right →
    (fact : left ≫ right = f) →
    Σ' i : image f ≅ im, left_map f ≫ i.hom = left ∧ i.hom ≫ right = right_map f
  /-- The factorization is unique up toa unique isomorphism -/
  factorization_iso_is_unique :
    {X Y : C} → (f : X ⟶ Y) → (im : C) → (left : X ⟶ im)→ (p : L left) → (right : im ⟶ Y) →
    (q : R right) → (fact : left ≫ right = f) → (i : image f ≅ im) →
    (comm₁ : left_map f ≫ i.hom = left) → (comm₂ : i.hom ≫ right = right_map f) →
    i = (factorization_iso f im left p right q fact).fst

/-- A useful characterization of the uniqueness of the factorization iso -/
lemma factorization_iso_is_unique' {L R : MorphismProperty C} (F : FactorizationSystem L R)
  {X Y : C} (f : X ⟶ Y) (E E' : C) (s : X ⟶ E) (hs : L s) (p : E ⟶ Y) (hp : R p) (fact : s ≫ p = f)
  (s' : X ⟶ E') (hs' : L s') (p' : E' ⟶ Y) (hp' : R p') (fact' : s' ≫ p' = f)
  (i i' : E ≅ E') (comm₁ : s ≫ i.hom = s') (comm₂ : i.hom ≫ p' = p) (comm₁' : s ≫ i'.hom = s')
  (comm₂' : i'.hom ≫ p' = p) : i = i' := by
  let α := F.factorization_iso f E' s' hs' p' hp' fact'
  let c₁ : F.left_map f ≫ (α.fst ≪≫ i.symm).hom = s := by calc
      F.left_map f ≫ (α.fst ≪≫ i.symm).hom =
        F.left_map f ≫ (α.fst.hom ≫ i.symm.hom) := by aesop_cat
      _ = (F.left_map f ≫ α.fst.hom) ≫ i.symm.hom := by simp
      _ = s' ≫ i.symm.hom := by rw [α.snd.left]
      _ = (s ≫ i.hom) ≫ i.symm.hom := by rw [← comm₁]
      _ = (s ≫ i.hom) ≫ i.inv := by aesop_cat
      _ = s ≫ i.hom ≫ i.inv := by simp
      _ = s := by rw [i.hom_inv_id]; simp
  let c₂ : (α.fst ≪≫ i.symm).hom ≫ p = F.right_map f := by calc
      (α.fst ≪≫ i.symm).hom ≫ p =
        (α.fst.hom ≫ i.symm.hom) ≫ p := by aesop_cat
      _ = (α.fst.hom ≫ i.symm.hom) ≫ (i.hom ≫ p') := by rw [← comm₂]
      _ = α.fst.hom ≫ (i.symm.hom ≫ i.hom) ≫ p' := by simp
      _ = α.fst.hom ≫ (i.inv ≫ i.hom) ≫ p' := by aesop_cat
      _ = α.fst.hom ≫ p' := by rw [i.inv_hom_id]; simp
      _ = F.right_map f := α.snd.right
  let φ := F.factorization_iso_is_unique f E s hs p hp fact (α.fst ≪≫ Iso.symm i) c₁ c₂
  let c₁' : F.left_map f ≫ (α.fst ≪≫ i'.symm).hom = s := by calc
      F.left_map f ≫ (α.fst ≪≫ i'.symm).hom =
        F.left_map f ≫ (α.fst.hom ≫ i'.symm.hom) := by aesop_cat
      _ = (F.left_map f ≫ α.fst.hom) ≫ i'.symm.hom := by simp
      _ = s' ≫ i'.symm.hom := by rw [α.snd.left]
      _ = (s ≫ i'.hom) ≫ i'.symm.hom := by rw [← comm₁']
      _ = (s ≫ i'.hom) ≫ i'.inv := by aesop_cat
      _ = s ≫ i'.hom ≫ i'.inv := by simp
      _ = s := by rw [i'.hom_inv_id]; simp
  let c₂' : (α.fst ≪≫ i'.symm).hom ≫ p = F.right_map f := by calc
      (α.fst ≪≫ i'.symm).hom ≫ p =
        (α.fst.hom ≫ i'.symm.hom) ≫ p := by aesop_cat
      _ = (α.fst.hom ≫ i'.symm.hom) ≫ (i'.hom ≫ p') := by rw [← comm₂']
      _ = α.fst.hom ≫ (i'.symm.hom ≫ i'.hom) ≫ p' := by simp
      _ = α.fst.hom ≫ (i'.inv ≫ i'.hom) ≫ p' := by aesop_cat
      _ = α.fst.hom ≫ p' := by rw [i'.inv_hom_id]; simp
      _ = F.right_map f := α.snd.right
  let ψ := F.factorization_iso_is_unique f E s hs p hp fact (α.fst ≪≫ Iso.symm i') c₁' c₂'
  let χ : α.fst ≪≫ i.symm = α.fst ≪≫ i'.symm := by calc
    α.fst ≪≫ i.symm = (F.factorization_iso f E s hs p hp fact).fst := φ
    _ = α.fst ≪≫ i'.symm := by rw [← ψ ]
  let ξ : Iso.symm i' = Iso.symm i := by calc
    Iso.symm i' = (α.fst.symm ≪≫ α.fst) ≪≫ Iso.symm i' := by simp
    _ = α.fst.symm ≪≫ (α.fst ≪≫ Iso.symm i') := by simp
    _ = α.fst.symm ≪≫ (α.fst ≪≫ Iso.symm i) := by rw [ χ ]
    _ = (α.fst.symm ≪≫ α.fst) ≪≫ Iso.symm i := by simp
    _ = Iso.symm i := by simp
  exact Iso.symm_eq_iff.mp (Eq.symm ξ)

/-- A class of morphisms in C defines a class of morphism in the slice C/X for every X ∈ C -/
def MorphismPropertySlice (W : MorphismProperty C) (X : C) : MorphismProperty (Over X) := by
  rintro _ _ f
  exact W ((Over.forget X).map f)

/-- If a class of morphisms contains isomorphisms,
then so does the class of morphisms in the slice -/
lemma contains_isos_slice : {W : MorphismProperty C} → {X : C} →  contains_isos W →
    contains_isos (MorphismPropertySlice W X) := by
  intro _ X h _ _ i
  exact h (asIso ((Over.forget X).map i.hom))

/-- If a class of morphisms is closed under composition,
then so does the class of morphisms in the slice -/
lemma is_closed_comp_slice {W : MorphismProperty C} {X : C} (h : is_closed_comp W) :
    is_closed_comp (MorphismPropertySlice W X) where
  precomp f hf g hg := by
    unfold MorphismPropertySlice
    rw [(Over.forget X).map_comp]
    exact h.precomp _ hf _ hg
  postcomp f hf g hg := by
    unfold MorphismPropertySlice
    rw [(Over.forget X).map_comp]
    exact h.postcomp _ hf _ hg

namespace Over

/-- If a triangle commutes in the slice C/X, then it commutes in C -/
lemma forget_map_comp :
    {X : C} → {p q r : Over X} → (F : p ⟶ q) → (G : q ⟶ r) → (H : p ⟶ r) →
    (hyp : F ≫ G = H) → (F.left ≫ G.left = H.left) := by
  intro X p q r F G H hyp
  simpa using congrArg (fun K : p ⟶ r => K.left) hyp

/-- The forgetful functor C/X ⟶ X preserves isomorphisms -/
def forget_preserves_isos : {X : C} → {f g : Over X} → (i : f ≅ g) → f.left ≅ g.left := by
  rintro X _ _ i
  exact
  {
    hom := by exact i.hom.left,
    inv := by exact i.inv.left,
    hom_inv_id := by exact forget_map_comp _ _ _ i.hom_inv_id,
    inv_hom_id := by exact forget_map_comp _ _ _ i.inv_hom_id
  }

end Over

/-- Imported FactorizationSystems declaration. -/
def image_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → Over X := by
  rintro _ _ _ F _ ⟨_,_,g⟩ ⟨φ,_,_⟩
  apply Over.mk ((F.right_map φ) ≫ g)

/-- Imported FactorizationSystems declaration. -/
def left_map_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → (f ⟶ image_slice F φ) := by
  rintro _ _ _ F ⟨_,_,f⟩ ⟨_,_,g⟩ ⟨φ,_,w⟩
  have comm : F.left_map φ ≫ F.right_map φ ≫ g = f := by
    calc
      F.left_map φ ≫ F.right_map φ ≫ g =  (F.left_map φ ≫ F.right_map φ) ≫ g := by simp
      _ = φ ≫ g := by exact (F.factorization φ) =≫ g
      _ = f := by simpa using w
  exact Over.homMk (F.left_map φ) comm

lemma left_map_in_left_class_slice : {X : C} → {L R : MorphismProperty C} →
    (F : FactorizationSystem L R) → {f g : Over X} → (φ : f ⟶ g) →
    (MorphismPropertySlice L X) (left_map_slice F φ) := by
  rintro _ _ _ F _ _ ⟨φ,_,_⟩
  have el := F.left_map_in_left_class φ
  aesop_cat

/-- Imported FactorizationSystems declaration. -/
def right_map_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → (image_slice F φ ⟶ g) := by
  rintro _ _ _ F _ _ ⟨φ,_,_⟩
  exact Over.homMk (F.right_map φ) (by aesop_cat)

lemma right_map_in_right_class_slice : {X : C} → {L R : MorphismProperty C} →
    (F : FactorizationSystem L R) → {f g : Over X} → (φ : f ⟶ g) →
    (MorphismPropertySlice R X) (right_map_slice F φ) := by
  rintro _ _ _ F _ _ ⟨φ,_,_⟩
  have el := F.right_map_in_right_class φ
  aesop_cat

lemma factorization_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → left_map_slice F φ ≫ right_map_slice F φ = φ := by
  rintro _ _ _ F _ _ ⟨φ,_,_⟩
  have fact := F.factorization φ
  aesop_cat

/-- Imported FactorizationSystems declaration. -/
def factorization_iso_slice : {X : C} → {L R : MorphismProperty C} → (F : FactorizationSystem L R) →
    {f g : Over X} → (φ : f ⟶ g) → (im : Over X) → (left : f ⟶ im) →
    (p : (MorphismPropertySlice L X) left) → (right : im ⟶ g) →
    (q : (MorphismPropertySlice R X) right) → (fact : left ≫ right = φ) →
      Σ' i : image_slice F φ ≅ im,
        left_map_slice F φ ≫ i.hom = left ∧ i.hom ≫ right = right_map_slice F φ := by
  rintro _ _ _ F _ ⟨_,_,g⟩ ⟨φ,_,_⟩ ⟨_,_,h⟩ ⟨l,_,_⟩ _ ⟨r,_,w⟩ _ fact
  have ⟨i,⟨P,Q⟩⟩ :=
    F.factorization_iso φ _ l (by aesop_cat) r (by aesop_cat) (Over.forget_map_comp _ _ _ fact)
  exact {
    fst := by
      have comm : i.hom ≫ h = (F.right_map φ) ≫ g := by
        have h_eq : h = r ≫ g := by
          simpa using w.symm
        calc
          i.hom ≫ h = (i.hom ≫ r) ≫ g := by
            rw [h_eq]
            exact (Category.assoc i.hom r g).symm
          _ = (F.right_map φ) ≫ g := by rw [Q]
      exact Over.isoMk i comm
    snd := by aesop_cat
  }

lemma factorization_iso_is_unique_slice : {X : C} → {L R : MorphismProperty C} →
    (F : FactorizationSystem L R) → {f g : Over X} → (φ : f ⟶ g) → (im : Over X) → (left : f ⟶ im) →
    (p : (MorphismPropertySlice L X) left) → (right : im ⟶ g) →
    (q : (MorphismPropertySlice R X) right) → (fact : left ≫ right = φ) →
    (i : image_slice F φ ≅ im) → (comm₁ : left_map_slice F φ ≫ i.hom = left) →
    (comm₂ : i.hom ≫ right = right_map_slice F φ) →
    i = (factorization_iso_slice F φ im left p right q fact).fst := by
  rintro _ _ _ F ⟨A,_,f⟩ ⟨B,_,g⟩ ⟨φ,_,u⟩ ⟨C,_,h⟩ ⟨l,_,v⟩ p ⟨r,_,w⟩ q fact i comm₁ comm₂
  have uniqueness := F.factorization_iso_is_unique φ C l p r q
    (Over.forget_map_comp _ _ _ fact)
    (Over.forget_preserves_isos i)
    (Over.forget_map_comp _ _ _ comm₁)
    (Over.forget_map_comp _ _ _ comm₂)
  ext
  have coh : (Over.forget_preserves_isos i).hom = i.hom.left := by rfl
  rw [←coh]
  have coh' : (F.factorization_iso φ C l p r q (Over.forget_map_comp _ _ _ fact)).fst.hom =
    (factorization_iso_slice F ⟨φ,_,u⟩ ⟨C,_,h⟩ ⟨l,_,v⟩ p ⟨r,_,w⟩ q fact).fst.hom.left := by
    unfold factorization_iso_slice
    aesop_cat
  rw [←coh']
  aesop_cat

/-- A factorization system in C descends to a factorization system in the slice -/
def FactorizationSystemSlice : {X : C} → {L R : MorphismProperty C} →
    (F : FactorizationSystem L R) →
    FactorizationSystem (MorphismPropertySlice L X) (MorphismPropertySlice R X) := by
  intro X L R F
  exact
  {
    contains_isos_left_class := contains_isos_slice F.contains_isos_left_class
    contains_isos_right_class := contains_isos_slice F.contains_isos_right_class
    is_closed_comp_left_class := is_closed_comp_slice F.is_closed_comp_left_class
    is_closed_comp_right_class := is_closed_comp_slice F.is_closed_comp_right_class
    image := image_slice F
    left_map := left_map_slice F
    left_map_in_left_class := left_map_in_left_class_slice F
    right_map := right_map_slice F
    right_map_in_right_class := right_map_in_right_class_slice F
    factorization := factorization_slice F
    factorization_iso := factorization_iso_slice F
    factorization_iso_is_unique := factorization_iso_is_unique_slice F
  }

/-
  We now prove that in any factorization system (L,R), the intersection of the left and the right
  class is precisely the class of isos, i.e. L∩R=Iso
-/

variable {L R : MorphismProperty C}

/- Given two (L,R)-factorizations of a map f, we construct an isomorphisms between their midpoints-/
/-- Imported FactorizationSystems declaration. -/
def fact_fact_iso : (F : FactorizationSystem L R) → {X Y : C} →  (f : X ⟶ Y) →
    (E : C) → (l : X ⟶ E) → (p : L l) → (r : E ⟶ Y) → (q : R r) → (fact : l ≫ r = f) →
    (E' : C) → (l' : X ⟶ E') → (p' : L l') → (r' : E' ⟶ Y) → (q' : R r') → (fact' : l' ≫ r' = f) →
    E ≅ E' := by
  intro F X Y f E l p r q fact E' l' p' r' q' fact'
  apply Iso.trans
  · exact Iso.symm (F.factorization_iso f E l p r q fact).fst
  · exact (F.factorization_iso f E' l' p' r' q' fact').fst

/- the isomorphisms commutes with left maps -/
lemma fact_fact_iso_comm_left : (F : FactorizationSystem L R) → {X Y : C} →  (f : X ⟶ Y) →
    (E : C) → (l : X ⟶ E) → (p : L l) → (r : E ⟶ Y) → (q : R r) → (fact : l ≫ r = f) →
    (E' : C) → (l' : X ⟶ E') → (p' : L l') → (r' : E' ⟶ Y) → (q' : R r') → (fact' : l' ≫ r' = f) →
    l ≫ (fact_fact_iso F f E l p r q fact E' l' p' r' q' fact').hom = l' := by
  intro F X Y f E l p r q fact E' l' p' r' q' fact'
  let comm_left := (F.factorization_iso f E l p r q fact).snd.left
  let comm_right := (F.factorization_iso f E l p r q fact).snd.right
  let comm_left' := (F.factorization_iso f E' l' p' r' q' fact').snd.left
  let comm_right' := (F.factorization_iso f E' l' p' r' q' fact').snd.right
  let inv := (F.factorization_iso f E l p r q fact).fst.inv
  let hom := (F.factorization_iso f E l p r q fact).fst.hom
  let hom' := (F.factorization_iso f E' l' p' r' q' fact').fst.hom
  have duh : l = F.left_map f ≫ hom := by aesop_cat
  calc
    l ≫ inv ≫ hom' = F.left_map f ≫ hom' := by rw [duh]; simp; aesop
    _ = l' := comm_left'

/- the isomorphisms commutes with right maps -/
lemma fact_fact_iso_comm_right : (F : FactorizationSystem L R) → {X Y : C} →  (f : X ⟶ Y) →
    (E : C) → (l : X ⟶ E) → (p : L l) → (r : E ⟶ Y) → (q : R r) → (fact : l ≫ r = f) →
    (E' : C) → (l' : X ⟶ E') → (p' : L l') → (r' : E' ⟶ Y) → (q' : R r') → (fact' : l' ≫ r' = f) →
    (fact_fact_iso F f E l p r q fact E' l' p' r' q' fact').hom ≫ r' = r := by
  intro F X Y f E l p r q fact E' l' p' r' q' fact'
  let comm_left := (F.factorization_iso f E l p r q fact).snd.left
  let comm_right := (F.factorization_iso f E l p r q fact).snd.right
  let comm_left' := (F.factorization_iso f E' l' p' r' q' fact').snd.left
  let comm_right' := (F.factorization_iso f E' l' p' r' q' fact').snd.right
  unfold fact_fact_iso
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
  let inv := (F.factorization_iso f E l p r q fact).fst.inv
  let hom := (F.factorization_iso f E l p r q fact).fst.hom
  let hom' := (F.factorization_iso f E' l' p' r' q' fact').fst.hom
  calc
    inv ≫ hom' ≫ r' = inv ≫ F.right_map f := by rw [comm_right']
    _ = inv ≫ hom ≫ r := by rw [comm_right]
    _ = (inv ≫ hom) ≫ r := by simp
    _ = (𝟙 _) ≫ r := by rw [(F.factorization_iso f E l p r q fact).fst.inv_hom_id]
    _ = r := by simp

namespace MorphismProperty

/- Notation for intersection of morphism properties -/
/-- Imported FactorizationSystems declaration. -/
instance Inter : Inter (MorphismProperty C) where
  inter : (L R : MorphismProperty C) → MorphismProperty C := by
      intro L R X Y f
      exact L f ∧ R f

end MorphismProperty

/- The intersection of the left and the right class are precisely the isomorphisms -/
lemma left_right_intersection_iso :
    FactorizationSystem L R → L ∩ R = MorphismProperty.isomorphisms C := by
  intro F
  ext X Y f
  constructor
  · intro ⟨Lf,Rf⟩
    let inv_f := (fact_fact_iso F f
      Y f Lf (𝟙 Y) (F.contains_isos_right_class (Iso.refl Y)) (by aesop_cat)
      X (𝟙 X) (F.contains_isos_left_class (Iso.refl X)) f Rf (by aesop_cat)).hom
    simp only [MorphismProperty.isomorphisms.iff]
    use inv_f
    constructor
    · exact fact_fact_iso_comm_left F f
        Y f Lf (𝟙 Y) (F.contains_isos_right_class (Iso.refl Y)) (by aesop_cat)
        X (𝟙 X) (F.contains_isos_left_class (Iso.refl X)) f Rf (by aesop_cat)
    · exact fact_fact_iso_comm_right F f
        Y f Lf (𝟙 Y) (F.contains_isos_right_class (Iso.refl Y)) (by aesop_cat)
        X (𝟙 X) (F.contains_isos_left_class (Iso.refl X)) f Rf (by aesop_cat)
  · intro iso_f
    simp at iso_f
    let f_as_iso := asIso f
    constructor
    · exact (F.contains_isos_left_class f_as_iso)
    · exact (F.contains_isos_right_class f_as_iso)

/-
  The left class of a factorization system has the right cancellation property and, dually,
  the right class of a factorization system has the left cancellation property.
-/

namespace MorphismProperty

/-- Imported FactorizationSystems declaration. -/
def left_cancellation (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z : C⦄ (u : X ⟶ Y) (v : Y ⟶ Z) (_ : W (u ≫ v)) (_ : W v) , W u

/-- Imported FactorizationSystems declaration. -/
def right_cancellation (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y Z : C⦄ (u : X ⟶ Y) (v : Y ⟶ Z) (_ : W (u ≫ v)) (_ : W u) , W v

end MorphismProperty

lemma right_cancellation_left_class :
    (F : FactorizationSystem L R) → MorphismProperty.right_cancellation L := by
  intro F X Y Z u v Lw Lu
  let w := u ≫ v
  let E := F.image v
  let s := F.left_map v
  let p := F.right_map v
  let fact := F.factorization v
  let i := (
    fact_fact_iso F w E (u ≫ s)
    (F.is_closed_comp_left_class.precomp _ Lu _ (F.left_map_in_left_class v)) p
    (F.right_map_in_right_class v) (by aesop_cat) Z w Lw (𝟙 Z)
    (F.contains_isos_right_class (Iso.refl Z)) (by aesop_cat)
  )
  have fact': i.hom ≫ (𝟙 Z) = p := by exact (
    fact_fact_iso_comm_right F w E (u ≫ s)
    (F.is_closed_comp_left_class.precomp _ Lu _ (F.left_map_in_left_class v)) p
    (F.right_map_in_right_class v) (by aesop_cat) Z w Lw (𝟙 Z)
    (F.contains_isos_right_class (Iso.refl Z)) (by aesop_cat)
  )
  have Lp' : L (i.hom ≫ (𝟙 Z)) := F.is_closed_comp_left_class.postcomp
    (𝟙 Z) (F.contains_isos_left_class (Iso.refl Z))
    i.hom (F.contains_isos_left_class _)
  have Lp : L p := by rw [←fact']; exact Lp'
  have Lsp := F.is_closed_comp_left_class.precomp s (F.left_map_in_left_class v) p Lp
  rw [←fact]
  exact Lsp

lemma left_cancellation_right_class :
    (F : FactorizationSystem L R) → MorphismProperty.left_cancellation R := by
  intro F X Y Z u v Rw Rv
  let w := u ≫ v
  let E := F.image u
  let t := F.left_map u
  let q := F.right_map u
  let fact := F.factorization u
  let comm : t ≫ q ≫ v = w := by
    calc
      t ≫ q ≫ v = (t ≫ q) ≫ v := by simp
      _ = u ≫ v := by rw [fact]
      _ = w := by rfl
  let i := (
    fact_fact_iso F w E t (F.left_map_in_left_class u) (q ≫ v)
    (F.is_closed_comp_right_class.precomp _ (F.right_map_in_right_class u) _ Rv) comm X (𝟙 X)
    (F.contains_isos_left_class (Iso.refl X)) w Rw (by aesop_cat)
  )
  have fact' : t ≫ i.hom = 𝟙 X := by exact (
    fact_fact_iso_comm_left F w E t (F.left_map_in_left_class u) (q ≫ v)
    (F.is_closed_comp_right_class.precomp _ (F.right_map_in_right_class u) _ Rv) comm X (𝟙 X)
    (F.contains_isos_left_class (Iso.refl X)) w Rw (by aesop_cat)
  )
  have eq : t = i.inv := by
    calc
      t = t ≫ 𝟙 E := by rw [Category.comp_id]
      _ = t ≫ i.hom ≫ i.inv := by rw [i.hom_inv_id]
      _ = (t ≫ i.hom) ≫ i.inv := by simp
      _ = i.inv := by rw [fact']; simp
  have Riinv : R i.inv := F.contains_isos_right_class (asIso i.inv)
  have Rt : R t := by rw [eq]; exact Riinv
  have Rqt : R (t ≫ q) := by
    exact F.is_closed_comp_right_class.precomp t Rt q (F.right_map_in_right_class u)
  rw [←fact]
  exact Rqt

end CategoryTheory
