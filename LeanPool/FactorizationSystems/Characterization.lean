/-
Copyright (c) 2026 Ivan Kobe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Kobe
-/

import Mathlib.CategoryTheory.MorphismProperty.Basic
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Comma

import LeanPool.FactorizationSystems.Basic
import LeanPool.FactorizationSystems.Orthogonality
import LeanPool.FactorizationSystems.OrthogonalComplements

/-!
# LeanPool.FactorizationSystems.Characterization
-/

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]

/- The predicate of a class of morphisms being replete -/
/-- Imported FactorizationSystems declaration. -/
def isReplete (W : MorphismProperty C) : Prop :=
  ∀ ⦃X Y X' Y' : C⦄ (l : X ⟶ Y) (l' : X' ⟶ Y') (i : X ≅ X') (j : Y ≅ Y')
    (_ : i.hom ≫ l' = l ≫ j.hom) (_: W l) , W l'

/- The left class of a factorization system is replete -/
lemma is_replete_left_class
  (L R : MorphismProperty C) (F : FactorizationSystem L R) : isReplete L := by
  intro X Y X' Y' l l' i j c p
  let i' := i.symm
  have eq : l' = i'.hom ≫ l ≫ j.hom := by calc
    l' = i.inv ≫ i.hom ≫ l' := by simp
    _ = i'.hom ≫ i.hom ≫ l' := by rfl
    _ = i'.hom ≫ l ≫ j.hom := by rw [c]
  rw [ eq ]
  apply  F.is_closed_comp_left_class.precomp
  · apply F.contains_isos_left_class
  · apply  F.is_closed_comp_left_class.precomp
    · exact p
    · apply F.contains_isos_left_class

/- The right class of a factorization system is replete -/
lemma is_replete_right_class
  (L R : MorphismProperty C) (F : FactorizationSystem L R) : isReplete R := by
  intro X Y X' Y' r r' i j c p
  let i' := i.symm
  have eq : r' = i'.hom ≫ r ≫ j.hom := by calc
    r' = i.inv ≫ i.hom ≫ r' := by simp
    _ = i'.hom ≫ i.hom ≫ r' := by rfl
    _ = i'.hom ≫ r ≫ j.hom := by rw [c]
  rw [ eq ]
  apply  F.is_closed_comp_right_class.precomp
  · apply F.contains_isos_right_class
  · apply  F.is_closed_comp_right_class.precomp
    · exact p
    · apply F.contains_isos_right_class

/- The type of weak factorization systems (NB : the terminology here isn't completely standard) -/
/-- Imported FactorizationSystems declaration. -/
structure WeakFactorizationSystem (L R : MorphismProperty C) where
  /-- The midpoint object of the weak factorization. -/
  image : {X Y : C} → (f : X ⟶ Y) → C
  /-- The left morphism of the weak factorization. -/
  leftMap : {X Y : C} → (f : X ⟶ Y) → X ⟶ image f
  /-- The left morphism lies in the left class. -/
  left_map_in_left_class : {X Y : C} → (f : X ⟶ Y) → L (leftMap f)
  /-- The right morphism of the weak factorization. -/
  rightMap : {X Y : C} → (f : X ⟶ Y) → image f ⟶ Y
  /-- The right morphism lies in the right class. -/
  right_map_in_right_class : {X Y : C} → (f : X ⟶ Y) → R (rightMap f)
  /-- The two maps compose to the original morphism. -/
  factorization : {X Y : C} → (f : X ⟶ Y) → leftMap f ≫ rightMap f = f := by aesop_cat

/- A factorization system determines a weak factorization system -/
/-- Imported FactorizationSystems declaration. -/
def WFSOfFS (L R : MorphismProperty C) (F : FactorizationSystem L R) :
  WeakFactorizationSystem L R := {
    image := F.image
    leftMap := F.leftMap
    left_map_in_left_class := F.left_map_in_left_class
    rightMap := F.rightMap
    right_map_in_right_class := F.right_map_in_right_class
    factorization := F.factorization }

/- The predicate of classes of morphisms being orthogonal -/
/-- Imported FactorizationSystems declaration. -/
def orthogonalClass (L R : MorphismProperty C) :=
  ∀ ⦃A B X Y : C⦄ (l : A ⟶ B) (_ : L l) (r : X ⟶ Y) (_ : R r) , orthogonal l r

/- Towards the proof that the two classes of a factorization system are orthogonal -/

/- If (L,R) is a factorization system, then every (L,R)-square has a diagonal filler -/
/-- Imported FactorizationSystems declaration. -/
def FactorizationSystemDiagonal
  {L R : MorphismProperty C} (F : FactorizationSystem L R) {A B X Y : C} (l : A ⟶ B) (hl : L l)
  (r : X ⟶ Y) (hr : R r) (S : l □ r) : diagonalFiller S := by
  let s := F.leftMap S.top
  let p := F.rightMap S.top
  let s' := F.leftMap S.bot
  let p' := F.rightMap S.bot
  let I := F.factorizationIso (l ≫ S.bot) (F.image S.bot) (l ≫ (F.leftMap S.bot))
    (F.is_closed_comp_left_class.precomp l hl (F.leftMap S.bot) (F.left_map_in_left_class S.bot))
    (F.rightMap S.bot) ( F.right_map_in_right_class S.bot)
    (by have fact := F.factorization S.bot; aesop_cat)
  let fact : F.leftMap S.top ≫ F.rightMap S.top ≫ r = l ≫ S.bot := by calc
    F.leftMap S.top ≫ F.rightMap S.top ≫ r = (F.leftMap S.top ≫ F.rightMap S.top) ≫ r := by
      simp
    _ = S.top ≫ r := by rw [F.factorization S.top]
    _ = l ≫ S.bot := by rw [← S.comm]
  let J := F.factorizationIso (l ≫ S.bot) (F.image S.top) (F.leftMap S.top)
    (F.left_map_in_left_class S.top) ((F.rightMap S.top) ≫ r)
    (F.is_closed_comp_right_class.precomp
      (F.rightMap S.top) (F.right_map_in_right_class S.top) r hr) fact
  exact {
    map := s' ≫ I.fst.inv ≫ J.fst.hom ≫ p
    comm_top := by calc
      l ≫ s' ≫ I.fst.inv ≫ J.fst.hom ≫ p = (l ≫ s') ≫ I.fst.inv ≫ J.fst.hom ≫ p := by simp
      _ = (F.leftMap (l ≫ S.bot) ≫ I.fst.hom) ≫ I.fst.inv ≫ J.fst.hom ≫ p := by rw [I.snd.left]
      _ = F.leftMap (l ≫ S.bot) ≫ (I.fst.hom ≫ I.fst.inv) ≫ J.fst.hom ≫ p := by simp
      _ = F.leftMap (l ≫ S.bot) ≫ J.fst.hom ≫ p := by rw [I.fst.hom_inv_id]; simp
      _ = (F.leftMap (l ≫ S.bot) ≫ J.fst.hom) ≫ p := by simp
      _ = s ≫ p := by rw [J.snd.left]
      _ = S.top := F.factorization S.top
    comm_bot := by calc
      (s' ≫ I.fst.inv ≫ J.fst.hom ≫ p) ≫ r = s' ≫ I.fst.inv ≫ (J.fst.hom ≫ p ≫ r) := by simp
      _ = s' ≫ I.fst.inv ≫ F.rightMap (l ≫ S.bot) := by rw [J.snd.right]
      _ = s' ≫ I.fst.inv ≫ I.fst.hom ≫ p' := by rw [I.snd.right]
      _ = s' ≫ (I.fst.inv ≫ I.fst.hom) ≫ p' := by simp
      _ = s' ≫ p' := by rw [I.fst.inv_hom_id]; simp
      _ = S.bot := F.factorization S.bot}

/- An auxiliary lemma for uniqueness of diagonal fillers -/
lemma FactorizationSystem_diagonal_canonicity
  {L R : MorphismProperty C} (F : FactorizationSystem L R) {A B X Y : C} (l : A ⟶ B) (hl : L l)
  (r : X ⟶ Y) (hr : R r) (S : l □ r) (d : diagonalFiller S) :
  d.map = (FactorizationSystemDiagonal F l hl r hr S).map := by
  let comm : (l ≫ F.leftMap d.map) ≫ F.rightMap d.map = S.top := by calc
    (l ≫ F.leftMap d.map) ≫ F.rightMap d.map = l ≫ F.leftMap d.map ≫ F.rightMap d.map :=
      by simp
    _ = l ≫ d.map := by rw [F.factorization d.map]
    _ = S.top := d.comm_top
  let K := F.factorizationIso S.top (F.image d.map) (l ≫ F.leftMap d.map)
    (F.is_closed_comp_left_class.precomp l hl (F.leftMap d.map) (F.left_map_in_left_class d.map))
    (F.rightMap d.map) (F.right_map_in_right_class d.map) comm
  let comm' : F.leftMap d.map ≫ F.rightMap d.map ≫ r = S.bot := by calc
    F.leftMap d.map ≫ F.rightMap d.map ≫ r = (F.leftMap d.map ≫ F.rightMap d.map) ≫ r :=
      by simp
    _ = d.map ≫ r := by rw [F.factorization d.map]
    _ = S.bot := d.comm_bot
  let K' := F.factorizationIso S.bot (F.image d.map) (F.leftMap d.map)
    (F.left_map_in_left_class d.map) ((F.rightMap d.map) ≫ r)
    (F.is_closed_comp_right_class.precomp
      (F.rightMap d.map) (F.right_map_in_right_class d.map) r hr) comm'
  let I := F.factorizationIso (l ≫ S.bot) (F.image S.bot) (l ≫ (F.leftMap S.bot))
    (F.is_closed_comp_left_class.precomp l hl (F.leftMap S.bot) (F.left_map_in_left_class S.bot))
    (F.rightMap S.bot) ( F.right_map_in_right_class S.bot)
    (by have fact := F.factorization S.bot; aesop_cat)
  let fact : F.leftMap S.top ≫ F.rightMap S.top ≫ r = l ≫ S.bot := by calc
    F.leftMap S.top ≫ F.rightMap S.top ≫ r = (F.leftMap S.top ≫ F.rightMap S.top) ≫ r := by
      simp
    _ = S.top ≫ r := by rw [F.factorization S.top]
    _ = l ≫ S.bot := by rw [← S.comm]
  let I' := F.factorizationIso (l ≫ S.bot) (F.image S.top) (F.leftMap S.top)
    (F.left_map_in_left_class S.top) ((F.rightMap S.top) ≫ r)
    (F.is_closed_comp_right_class.precomp
      (F.rightMap S.top) (F.right_map_in_right_class S.top) r hr) fact
  let kk := K'.fst ≪≫ K.fst.symm
  let ii := I.fst.symm ≪≫ I'.fst
  let fact' : (l ≫ F.leftMap S.bot) ≫ F.rightMap S.bot = l ≫ S.bot := by calc
    (l ≫ F.leftMap S.bot) ≫ F.rightMap S.bot = l ≫ (F.leftMap S.bot ≫ F.rightMap S.bot) := by
      simp
    _ = l ≫ S.bot := by rw [F.factorization S.bot]
  let fact'' : F.leftMap S.top ≫ F.rightMap S.top ≫ r = l ≫ S.bot := by calc
    F.leftMap S.top ≫ F.rightMap S.top ≫ r = (F.leftMap S.top ≫ F.rightMap S.top) ≫ r := by
      simp
    _ = S.top ≫ r := by rw [F.factorization S.top]
    _ = l ≫ S.bot := by rw [← S.comm]
  let comm₀ : (l ≫ F.leftMap S.bot) ≫ ii.hom = F.leftMap S.top := by calc
    (l ≫ F.leftMap S.bot) ≫ ii.hom =
      (l ≫ F.leftMap S.bot ≫ I.fst.inv) ≫ I'.fst.hom := by simp; rfl
    _ = F.leftMap (l ≫ S.bot) ≫ I'.fst.hom := by
      have c : l ≫ F.leftMap S.bot ≫ I.fst.inv = F.leftMap (l ≫ S.bot) := by calc
        l ≫ F.leftMap S.bot ≫ I.fst.inv = (l ≫ F.leftMap S.bot) ≫ I.fst.inv := by simp
        _ = (F.leftMap (l ≫ S.bot) ≫ I.fst.hom) ≫ I.fst.inv := by rw [I.snd.left]
        _ = F.leftMap (l ≫ S.bot) ≫ (I.fst.hom ≫ I.fst.inv) := by simp
        _ = F.leftMap (l ≫ S.bot) := by rw [I.fst.hom_inv_id]; simp
      rw [ c ]
    _ = F.leftMap S.top := I'.snd.left
  let comm₁ : ii.hom ≫ F.rightMap S.top ≫ r = F.rightMap S.bot := by calc
    ii.hom ≫ F.rightMap S.top ≫ r = (I.fst.inv ≫ I'.fst.hom) ≫ F.rightMap S.top ≫ r := by
      simp only [Category.assoc]; aesop_cat
    _ = I.fst.inv ≫ (I'.fst.hom ≫ F.rightMap S.top ≫ r) := by simp
    _ = I.fst.inv ≫ F.rightMap (l ≫ S.bot) := by rw [I'.snd.right]
    _ = I.fst.inv ≫ (I.fst.hom ≫ F.rightMap S.bot) := by rw [I.snd.right]
    _ = (I.fst.inv ≫ I.fst.hom) ≫ F.rightMap S.bot := by simp
    _ = F.rightMap S.bot := by rw [I.fst.inv_hom_id]; simp
  let comm₀' : (l ≫ F.leftMap S.bot) ≫ kk.hom = F.leftMap S.top := by calc
    (l ≫ F.leftMap S.bot) ≫ kk.hom = l ≫ (F.leftMap S.bot ≫ K'.fst.hom) ≫ K.fst.inv := by
      simp; rfl
    _ = l ≫ F.leftMap d.map ≫ K.fst.inv := by rw [K'.snd.left]
    _ = (l ≫ F.leftMap d.map) ≫ K.fst.inv := by simp
    _ = (F.leftMap S.top ≫ K.fst.hom) ≫ K.fst.inv := by rw [K.snd.left]
    _ = F.leftMap S.top ≫ (K.fst.hom ≫ K.fst.inv) := by simp
    _ = F.leftMap S.top := by rw [K.fst.hom_inv_id]; simp
  let comm₁' : kk.hom ≫ F.rightMap S.top ≫ r = F.rightMap S.bot := by calc
    kk.hom ≫ F.rightMap S.top ≫ r = K'.fst.hom ≫ K.fst.inv ≫ F.rightMap S.top ≫ r := by
      aesop_cat
    _ = K'.fst.hom ≫ K.fst.inv ≫ (K.fst.hom ≫ F.rightMap d.map) ≫ r := by rw [K.snd.right]
    _ = K'.fst.hom ≫ (K.fst.inv ≫ K.fst.hom) ≫ F.rightMap d.map ≫ r := by simp
    _ = K'.fst.hom ≫ F.rightMap d.map ≫ r := by rw [K.fst.inv_hom_id]; simp
    _ = F.rightMap S.bot := K'.snd.right
  let uniq := factorization_iso_is_unique' F (l ≫ S.bot) (F.image S.bot) (F.image S.top)
    (l ≫ F.leftMap S.bot) (F.is_closed_comp_left_class.precomp l hl (F.leftMap S.bot)
    (F.left_map_in_left_class S.bot)) (F.rightMap S.bot) (F.right_map_in_right_class S.bot)
    fact' (F.leftMap S.top) (F.left_map_in_left_class S.top) (F.rightMap S.top ≫ r)
    (F.is_closed_comp_right_class.precomp (F.rightMap S.top) (F.right_map_in_right_class S.top)
    r hr) fact'' ii kk comm₀ comm₁ comm₀' comm₁'
  calc
    d.map = F.leftMap d.map ≫ F.rightMap d.map := by rw [F.factorization d.map]
    _ = (F.leftMap S.bot ≫ K'.fst.hom) ≫ (K.fst.inv ≫ F.rightMap S.top) := by
      rw [K'.snd.left]; congr; calc
      F.rightMap d.map = (K.fst.inv ≫ K.fst.hom) ≫ F.rightMap d.map := by
        rw [K.fst.inv_hom_id]; simp
      _ = K.fst.inv ≫ (K.fst.hom ≫ F.rightMap d.map) := by simp
      _ = K.fst.inv ≫ F.rightMap S.top := by rw [K.snd.right]
    _ = F.leftMap S.bot ≫ (K'.fst ≪≫ K.fst.symm).hom ≫ F.rightMap S.top := by simp
    _ = F.leftMap S.bot ≫ kk.hom ≫ F.rightMap S.top := by rfl
    _ = F.leftMap S.bot ≫ ii.hom ≫ F.rightMap S.top := by rw [ uniq ]
    _ = (FactorizationSystemDiagonal F l hl r hr S).map := by aesop_cat

/- The two classes of a factorization system are orthogonal -/
/-- Imported FactorizationSystems declaration. -/
def FactorizationSystemOrthogonal
  (L R : MorphismProperty C) (F : FactorizationSystem L R) : orthogonalClass L R := by
  intro A B X Y l hl r hr
  exact {
    diagonal := fun S => FactorizationSystemDiagonal F l hl r hr S
    diagonal_unique := fun S d d' => by calc
      d.map = (FactorizationSystemDiagonal F l hl r hr S).map :=
        FactorizationSystem_diagonal_canonicity F l hl r hr S d
      _ = d'.map := Eq.symm (FactorizationSystem_diagonal_canonicity F l hl r hr S d') }

/- If (L,R) is a weak factorization system, R is replete and L⊥R,
then R is the right orthogonal complement of L-/
lemma left_determinacy (L R : MorphismProperty C) (H₁R : isReplete R)
  (H₂ : WeakFactorizationSystem L R) (H₃ : orthogonalClass L R) :
  R = rightOrthogonalComplement L := by
  ext X Y r
  apply Iff.intro
  · intro Rr A B l Ll
    exact orthogonal_implies_hom_orthogonal l r (H₃ l Ll r Rr)
  · intro L_orthogonal_r
    let S : H₂.leftMap r □ r :=
      { top := 𝟙 X , bot := H₂.rightMap r , comm := by have f := H₂.factorization r; aesop_cat }
    let d : diagonalFiller S :=
      ( homOrthogonalImpliesOrthogonal
        ( L_orthogonal_r (H₂.leftMap r) (H₂.left_map_in_left_class r))).diagonal S
    let S' : H₂.leftMap r □ H₂.rightMap r := { top := H₂.leftMap r , bot := H₂.rightMap r }
    let δ : diagonalFiller S' := {
      map := d.map ≫ H₂.leftMap r
      comm_top := by calc
        H₂.leftMap r ≫ d.map ≫ H₂.leftMap r =
          (H₂.leftMap r ≫ d.map) ≫ H₂.leftMap r := by simp
        _ = H₂.leftMap r := by rw [d.comm_top]; simp [S]
      comm_bot := by calc
        (d.map ≫ H₂.leftMap r) ≫ H₂.rightMap r =
          d.map ≫ (H₂.leftMap r ≫ H₂.rightMap r) := by simp
        _ = d.map ≫ r := by rw [H₂.factorization r]
        _ = S'.bot := d.comm_bot }
    let δ' : diagonalFiller S' := { map := 𝟙 (H₂.image r) }
    let u : X ≅ H₂.image r := {
      hom := H₂.leftMap r
      inv := d.map
      hom_inv_id := d.comm_top
      inv_hom_id := (H₃ (H₂.leftMap r) (H₂.left_map_in_left_class r) (H₂.rightMap r)
        (H₂.right_map_in_right_class r)).diagonal_unique S' δ δ' }
    exact H₁R (H₂.rightMap r) r u.symm (Iso.refl _)
      (by
        simpa only [Iso.symm_hom, Iso.refl_hom, Category.comp_id] using d.comm_bot)
      (H₂.right_map_in_right_class r)

/- If (L,R) is a weak factorization system, L is replete and L⊥R,
then L is the right orthogonal complement of R-/
lemma right_determinacy (L R : MorphismProperty C) (H₁L : isReplete L)
  (H₂ : WeakFactorizationSystem L R) (H₃ : orthogonalClass L R) :
  L = leftOrthogonalComplement R := by
  ext A B l
  constructor
  case mp =>
    intro Ll X Y r Rr
    exact orthogonal_implies_hom_orthogonal l r (H₃ l Ll r Rr)
  case mpr =>
    intro l_orthogonal_R
    let S : l □ H₂.rightMap l :=
      { top := H₂.leftMap l , bot := 𝟙 B , comm := by have f := H₂.factorization l; aesop_cat }
    let d : diagonalFiller S :=
      ( homOrthogonalImpliesOrthogonal
        ( l_orthogonal_R (H₂.rightMap l) (H₂.right_map_in_right_class l))).diagonal S
    let S' : H₂.leftMap l □ H₂.rightMap l := { top := H₂.leftMap l , bot := H₂.rightMap l }
    let δ : diagonalFiller S' := {
      map := H₂.rightMap l ≫ d.map
      comm_top := by calc
        H₂.leftMap l ≫ H₂.rightMap l ≫ d.map =
          (H₂.leftMap l ≫ H₂.rightMap l) ≫ d.map := by simp
        _ = l ≫ d.map := by rw [H₂.factorization l]
        _ = H₂.leftMap l := d.comm_top
      comm_bot := by have cb := d.comm_bot; aesop_cat }
    let δ' : diagonalFiller S' := { map := 𝟙 _ }
    let p : H₂.image l ≅ B := {
      hom := H₂.rightMap l
      inv := d.map
      hom_inv_id := (H₃ (H₂.leftMap l) (H₂.left_map_in_left_class l) (H₂.rightMap l)
        (H₂.right_map_in_right_class l)).diagonal_unique S' δ δ'
      inv_hom_id := d.comm_bot }
    exact H₁L (H₂.leftMap l) l (Iso.refl _) p (by have f := H₂.factorization l; aesop_cat)
      (H₂.left_map_in_left_class l)

/- Constructs a factorization system from replete left and right classes, a weak
factorization system, and orthogonality. -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def FactorizationSystemCharacterization (L R : MorphismProperty C) (H₁L : isReplete L)
  (H₁R : isReplete R) (H₂ : WeakFactorizationSystem L R) (H₃ : orthogonalClass L R) :
  FactorizationSystem L R := {
    image := H₂.image
    leftMap := H₂.leftMap
    left_map_in_left_class := H₂.left_map_in_left_class
    rightMap := H₂.rightMap
    right_map_in_right_class := H₂.right_map_in_right_class
    factorization := H₂.factorization
    contains_isos_left_class := by
      rw [ right_determinacy L R H₁L H₂ H₃ ]
      exact Arrow.contains_isos_left_ort_complement R
    contains_isos_right_class := by
      rw [ left_determinacy L R H₁R H₂ H₃ ]
      exact Arrow.contains_isos_right_ort_complement L
    is_closed_comp_left_class := {
      precomp := fun l Ll l' Ll' => (Eq.symm (right_determinacy L R H₁L H₂ H₃)) ▸
        Arrow.is_closed_under_comp_l_ort_complement
          R l ((right_determinacy L R H₁L H₂ H₃) ▸ Ll) l' ((right_determinacy L R H₁L H₂ H₃) ▸ Ll')
      postcomp := fun l' Ll' l Ll => (Eq.symm (right_determinacy L R H₁L H₂ H₃)) ▸
        Arrow.is_closed_under_comp_l_ort_complement
          R l ((right_determinacy L R H₁L H₂ H₃) ▸ Ll) l' ((right_determinacy L R H₁L H₂ H₃) ▸ Ll')}
    is_closed_comp_right_class := {
      precomp := fun r Rr r' Rr' => (Eq.symm (left_determinacy L R H₁R H₂ H₃)) ▸
        Arrow.is_closed_under_comp_r_ort_complement
          L r ((left_determinacy L R H₁R H₂ H₃) ▸ Rr) r' ((left_determinacy L R H₁R H₂ H₃) ▸ Rr')
      postcomp := fun r' Rr' r Rr => (Eq.symm (left_determinacy L R H₁R H₂ H₃)) ▸
        Arrow.is_closed_under_comp_r_ort_complement
          L r ((left_determinacy L R H₁R H₂ H₃) ▸ Rr) r' ((left_determinacy L R H₁R H₂ H₃) ▸ Rr') }
    factorizationIso := fun f E u Lu p Rp fact => by
      have orth₀' : leftOrthogonalComplement R (H₂.leftMap f) :=
        (right_determinacy L R H₁L H₂ H₃) ▸ (H₂.left_map_in_left_class f)
      let orth₀ : orthogonal (H₂.leftMap f) p := homOrthogonalImpliesOrthogonal (orth₀' p Rp)
      let S₀ : (H₂.leftMap f) □ p := {
        top := u
        bot := H₂.rightMap f
        comm := by have c₀ := H₂.factorization f; have c₁ := fact; aesop_cat }
      let d : H₂.image f ⟶ E := (orth₀.diagonal S₀).map
      let orth₁' : leftOrthogonalComplement R u := (right_determinacy L R H₁L H₂ H₃) ▸ Lu
      let orth₁ : orthogonal u (H₂.rightMap f) :=
        homOrthogonalImpliesOrthogonal (orth₁' (H₂.rightMap f) (H₂.right_map_in_right_class f))
      let S₁ : u □ (H₂.rightMap f) :=
        { top := H₂.leftMap f , bot := p , comm := have c := S₀.comm; by aesop_cat}
      let r : E ⟶ H₂.image f := (orth₁.diagonal S₁).map
      let I : H₂.image f ≅ E := {
        hom := d
        inv := r
        hom_inv_id := by
          let T : H₂.leftMap f □  H₂.rightMap f := {top := H₂.leftMap f , bot := H₂.rightMap f}
          let δ : diagonalFiller T := {
            map := d ≫ r
            comm_top := by calc
              H₂.leftMap f ≫ d ≫ r = (H₂.leftMap f ≫ d) ≫ r := by simp
              _ = u ≫ r := by rw [ (orth₀.diagonal S₀).comm_top ]
              _ = H₂.leftMap f := by rw [ (orth₁.diagonal S₁).comm_top ]
            comm_bot := by calc
              (d ≫ r) ≫ H₂.rightMap f = d ≫ r ≫ H₂.rightMap f := by simp
              _ = d ≫ p := by rw [ (orth₁.diagonal S₁).comm_bot ]
              _ = H₂.rightMap f := by rw [ (orth₀.diagonal S₀).comm_bot ] }
          let δ' : diagonalFiller T := { map := 𝟙 _ }
          exact (H₃ (H₂.leftMap f) (H₂.left_map_in_left_class f) (H₂.rightMap f)
            (H₂.right_map_in_right_class f)).diagonal_unique T δ δ'
        inv_hom_id := by
          let T : u □ p := {top := u , bot := p}
          let δ : diagonalFiller T := {
            map := r ≫ d
            comm_top := by calc
              u ≫ r ≫ d = (u ≫ r) ≫ d := by simp
              _ = H₂.leftMap f ≫ d := by rw [ (orth₁.diagonal S₁).comm_top ]
              _ = u := by rw [ (orth₀.diagonal S₀).comm_top ]
            comm_bot := by calc
              (r ≫ d) ≫ p = r ≫ d ≫ p := by simp
              _ = r ≫ H₂.rightMap f := by rw [ (orth₀.diagonal S₀).comm_bot ]
              _ = p := by rw [ (orth₁.diagonal S₁).comm_bot ] }
          let δ' : diagonalFiller T := { map := 𝟙 _ }
          exact (H₃ u Lu p Rp).diagonal_unique T δ δ' }
      apply PSigma.mk I
      apply And.intro
      · exact (orth₀.diagonal S₀).comm_top
      · exact (orth₀.diagonal S₀).comm_bot
    factorization_iso_is_unique := fun f E u Lu p Rp fact I c c' => by
      ext
      have orth₀' : leftOrthogonalComplement R (H₂.leftMap f) :=
        (right_determinacy L R H₁L H₂ H₃) ▸ (H₂.left_map_in_left_class f)
      let orth₀ : orthogonal (H₂.leftMap f) p := homOrthogonalImpliesOrthogonal (orth₀' p Rp)
      let S₀ : (H₂.leftMap f) □ p := {
        top := u
        bot := H₂.rightMap f
        comm := by have c₀ := H₂.factorization f; have c₁ := fact; aesop_cat }
      let δ : diagonalFiller S₀ := orth₀.diagonal S₀
      let δ' : diagonalFiller S₀ := { map := I.hom , comm_top := c , comm_bot := c' }
      have eq := (H₃ (H₂.leftMap f) (H₂.left_map_in_left_class f) p Rp).diagonal_unique S₀ δ δ'
      aesop_cat }

end CategoryTheory
