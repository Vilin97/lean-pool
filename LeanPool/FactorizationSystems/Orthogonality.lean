/-
Copyright (c) 2026 Ivan Kobe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ivan Kobe
-/

import LeanPool.FactorizationSystems.Examples
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.IsLimit
import Mathlib.CategoryTheory.Iso
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-
Given two morphisms l: A ⟶ B and r: X ⟶ Y in a category C, we say that l is left orthogonal to r
or that r is right orthogonal to l, if for every commuting square of the form

    A ----f----> X
    |            |
  l |            |
    |            |
    v            v
    B ----g----> Y,

there exists a unique diagonal filler d: B ⟶ X making both triangles commute.
-/

namespace CategoryTheory
universe u v
variable {C : Type u} [Category.{v} C]
variable [HasPullbacks : Limits.HasPullbacks C]


/- The sort of commuting squares in a category C -/
/-- Imported FactorizationSystems declaration. -/
structure square (A B X Y : C) where
  /-- The left vertical morphism. -/
  left : A ⟶ B
  /-- The right vertical morphism. -/
  right : X ⟶ Y
  /-- The top horizontal morphism. -/
  top : A ⟶ X
  /-- The bottom horizontal morphism. -/
  bot : B ⟶ Y
  /-- The square commutes. -/
  comm : left ≫ bot = top ≫ right := by aesop_cat

/- The sort of commuting squares in a category C with specified vertical maps -/
/-- Imported FactorizationSystems declaration. -/
structure square_completion {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) where
  /-- The top horizontal morphism. -/
  top : A ⟶ X
  /-- The bottom horizontal morphism. -/
  bot : B ⟶ Y
  /-- The square commutes. -/
  comm : l ≫ bot = top ≫ r := by aesop_cat

/-- Imported FactorizationSystems declaration. -/
infixl:75 " □ " => square_completion

/- Forgetting the specification of vertical maps -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def square_of_square_completion
    {A B X Y : C} {l : A ⟶ B} {r : X ⟶ Y} (S' : l □ r) :
    square A B X Y where
  left := l
  right := r
  top := S'.top
  bot := S'.bot
  comm := S'.comm

variable {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y)

/- The sort of diagonal fillers of a square with specified vertical maps -/
/-- Imported FactorizationSystems declaration. -/
structure diagonal_filler
    {A B X Y : C} {f : A ⟶ B} {g : X ⟶ Y} (S : f □ g) where
  /-- The diagonal morphism. -/
  map : B ⟶ X
  /-- The top triangle commutes. -/
  comm_top : f ≫ map = S.top := by aesop_cat
  /-- The bottom triangle commutes. -/
  comm_bot : map ≫ g = S.bot := by aesop_cat

/- The sort of proofs that morphisms f and g are orthogonal -/
/-- Imported FactorizationSystems declaration. -/
structure orthogonal {A B X Y : C} (f : A ⟶ B) (g : X ⟶ Y) where
  /-- A chosen diagonal filler for every square. -/
  diagonal : (S : f □ g) → diagonal_filler S
  /-- The chosen diagonal filler is unique. -/
  diagonal_unique :
    (S : f □ g) → (d : diagonal_filler S) → (d' : diagonal_filler S) → d.map = d'.map

/- We now start working towards an alternative characterization of orthogonality: morphisms l and r
are orthogonal iff the commuting square
                l^*
    Hom(B,X)--------->Hom(A,X)
      |                 |
  r_* |                 |r_*
      |                 |
      v                 V
    Hom(B,Y)--------->Hom(A,Y)  is a pullback square in Set.
                l^*
-/

/- We first construct this commuting square in Set-/

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def hom_square_left : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((B ⟶ X) ⟶ (A ⟶ X)) :=
  fun l r =>
    let _keep := r
    TypeCat.ofHom fun f => l ≫ f

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def hom_square_right : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((B ⟶ Y) ⟶ (A ⟶ Y)) :=
  fun l r =>
    let _keep := r
    TypeCat.ofHom fun f => l ≫ f

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def hom_square_top : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((B ⟶ X) ⟶ (B ⟶ Y)) :=
  fun l r =>
    let _keep := l
    TypeCat.ofHom fun f => f ≫ r

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def hom_square_bot : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((A ⟶ X) ⟶ (A ⟶ Y)) :=
  fun l r =>
    let _keep := l
    TypeCat.ofHom fun f => f ≫ r

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def hom_square : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) →
    square (B ⟶ X) (A ⟶ X) (B ⟶ Y) (A ⟶ Y) := fun l r =>
  {
    left := hom_square_left l r
    right := hom_square_right l r
    top := hom_square_top l r
    bot := hom_square_bot l r
    comm := by
      ext f
      exact Category.assoc l f r
  }

/- The canonical pullback of the cospan given by the right and bottom maps in the hom square -/
/-- Imported FactorizationSystems declaration. -/
def hom_cospan_pullback : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → Type v := by
  intro A B X Y l r
  exact Limits.pullback (hom_square_right l r) (hom_square_bot l r)

/- The associated pullback cone -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_cospan_pullback_cone : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) →
    Limits.PullbackCone (hom_square_right l r) (hom_square_bot l r) := by
  intro A B X Y l r
  exact Limits.pullback.cone (hom_square_right l r) (hom_square_bot l r)


/- The first projection of the hom pullback -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def hom_cospan_pullback_fst {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (hom_cospan_pullback l r) ⟶ (B ⟶ Y) :=
  Limits.pullback.fst (hom_square_right l r) (hom_square_bot l r)

/- The second projection of the hom pullback -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def hom_cospan_pullback_snd {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (hom_cospan_pullback l r) ⟶ (A ⟶ X) :=
  Limits.pullback.snd (hom_square_right l r) (hom_square_bot l r)

/- The universal property of the hom pullback -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def hom_cospan_pullback_lift {W : Type v} {A B X Y : C}
    (l : A ⟶ B) (r : X ⟶ Y) (φ : W ⟶ (B ⟶ Y)) (ψ : W ⟶ (A ⟶ X))
    (comm : φ ≫ (hom_square_right l r) = ψ ≫ (hom_square_bot l r) := by aesop_cat) :
    W ⟶ hom_cospan_pullback l r :=
  Limits.pullback.lift φ ψ comm

omit HasPullbacks in
lemma hom_cospan_pullback_lift_fst {W : Type v} {A B X Y : C}
    (l : A ⟶ B) (r : X ⟶ Y) (φ : W ⟶ (B ⟶ Y)) (ψ : W ⟶ (A ⟶ X))
    (comm : φ ≫ (hom_square_right l r) = ψ ≫ (hom_square_bot l r) := by aesop_cat) :
    hom_cospan_pullback_lift l r φ ψ comm ≫ hom_cospan_pullback_fst l r = φ :=
  Limits.pullback.lift_fst φ ψ comm

omit HasPullbacks in
lemma hom_cospan_pullback_lift_snd {W : Type v} {A B X Y : C}
    (l : A ⟶ B) (r : X ⟶ Y) (φ : W ⟶ (B ⟶ Y)) (ψ : W ⟶ (A ⟶ X))
    (comm : φ ≫ (hom_square_right l r) = ψ ≫ (hom_square_bot l r) := by aesop_cat) :
    hom_cospan_pullback_lift l r φ ψ comm ≫ hom_cospan_pullback_snd l r = ψ :=
  Limits.pullback.lift_snd φ ψ comm

/- The hom pullback square is in particular commutative -/
omit HasPullbacks in
lemma hom_cospan_pullback_condition {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (hom_cospan_pullback_fst l r) ≫ (hom_square_right l r) =
    (hom_cospan_pullback_snd l r) ≫ (hom_square_bot l r) :=
  Limits.pullback.condition

/- The property of a commuting square being Cartesian -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def is_cartesian_square {A B X Y : C} (S : square A B X Y) : Prop :=
  IsIso (Limits.pullback.lift S.top S.left (by rw [S.comm]))

/- The second characterization of orthogonality via the hom square in Set -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def hom_orthogonal {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Prop :=
  is_cartesian_square (hom_square l r)

/- We construct a map from Hom(B,X) into the pullback
of the hom square via the universal mapping property -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonals_hom_cospan_pullback_top {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (B ⟶ X) ⟶ (A ⟶ X) :=
  let _keep := r
  TypeCat.ofHom fun f => l ≫ f

/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonals_hom_cospan_pullback_bot {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (B ⟶ X) ⟶ (B ⟶ Y) :=
  let _keep := l
  TypeCat.ofHom fun f => f ≫ r

omit HasPullbacks in
lemma diagonals_hom_cospan_pullback_lift_comm {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (diagonals_hom_cospan_pullback_bot l r) ≫ (hom_square_right l r) =
    (diagonals_hom_cospan_pullback_top l r) ≫ (hom_square_bot l r) := by
  ext d
  calc
    (diagonals_hom_cospan_pullback_bot l r ≫ hom_square_right l r) d = l ≫ (d ≫ r) := rfl
    _ = (l ≫ d) ≫ r := (Category.assoc l d r).symm
    _ = (diagonals_hom_cospan_pullback_top l r ≫ hom_square_bot l r) d := rfl

/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonals_hom_cospan_pullback_lift {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (B ⟶ X) ⟶ hom_cospan_pullback l r :=
  hom_cospan_pullback_lift l r
    (diagonals_hom_cospan_pullback_bot l r)
    (diagonals_hom_cospan_pullback_top l r)
    (diagonals_hom_cospan_pullback_lift_comm l r)

omit HasPullbacks in
lemma diagonals_hom_cospan_pullback_lift_fst {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_hom_cospan_pullback_lift l r ≫ hom_cospan_pullback_fst l r =
    (diagonals_hom_cospan_pullback_bot l r) :=
  Limits.pullback.lift_fst
    (diagonals_hom_cospan_pullback_bot l r)
    (diagonals_hom_cospan_pullback_top l r)
    (diagonals_hom_cospan_pullback_lift_comm l r)

omit HasPullbacks in
lemma diagonals_hom_cospan_pullback_lift_snd {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_hom_cospan_pullback_lift l r ≫ hom_cospan_pullback_snd l r =
    (diagonals_hom_cospan_pullback_top l r) :=
  Limits.pullback.lift_snd
    (diagonals_hom_cospan_pullback_bot l r)
    (diagonals_hom_cospan_pullback_top l r)
    (diagonals_hom_cospan_pullback_lift_comm l r)

/- Given an element in the pullback of the hom
square in Set, we construct a commuting square in C -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_cospan_pullback_to_square_completion
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (x : hom_cospan_pullback l r) :
    l □ r := by
  let x'  := (hom_cospan_pullback_fst l r) x
  let x'' := (hom_cospan_pullback_snd l r)  x
  have S : l □ r := {
      top := x''
      bot := x'
      comm := by
        simpa [x', x''] using congrArg
          (fun h : hom_cospan_pullback l r ⟶ (A ⟶ Y) => h x)
          (hom_cospan_pullback_condition l r)
  }
  exact S

/- With the assumption that l and r are orthognal, we can construct from an
element in the pullback of the hom square a diagonal filler of this square -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_cospan_pullback_to_diagonal_filler
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r)
    (x : Limits.pullback (hom_square_right l r) (hom_square_bot l r)) :
    diagonal_filler (hom_cospan_pullback_to_square_completion l r x) := by
  let ⟨d,S⟩ := h
  exact d (hom_cospan_pullback_to_square_completion l r x)

/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_cospan_pullback_to_diagonal_filler_map
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r) :
    (Limits.pullback (hom_square_right l r) (hom_square_bot l r)) ⟶ (B ⟶ X) :=
  TypeCat.ofHom fun x => (hom_cospan_pullback_to_diagonal_filler l r h x).map

omit HasPullbacks in
lemma hom_cospan_pullback_to_diagonal_filler_map_comm_top
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r)
    (x : Limits.pullback (hom_square_right l r) (hom_square_bot l r)) :
    l ≫ (hom_cospan_pullback_to_diagonal_filler_map l r h x) =
    (hom_cospan_pullback_to_square_completion l r x).top :=
  (hom_cospan_pullback_to_diagonal_filler l r h x).comm_top

omit HasPullbacks in
lemma hom_cospan_pullback_to_diagonal_filler_map_comm_bot
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r)
    (x : Limits.pullback (hom_square_right l r) (hom_square_bot l r)) :
    (hom_cospan_pullback_to_diagonal_filler_map l r h x) ≫ r =
    (hom_cospan_pullback_to_square_completion l r x).bot :=
  (hom_cospan_pullback_to_diagonal_filler l r h x).comm_bot

omit HasPullbacks

/- If morphisms l and r in C are orthogonal, then the hom square is cartesian -/
omit HasPullbacks in
lemma orthogonal_implies_hom_orthogonal :
    {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → (orthogonal l r) → (hom_orthogonal l r) := by
  intro A B X Y l r ⟨d,u⟩
  unfold hom_orthogonal
  unfold is_cartesian_square
  use hom_cospan_pullback_to_diagonal_filler_map l r ⟨d,u⟩
  constructor
  · ext δ
    simp only [TypeCat.Fun.toFun_apply, comp_apply, id_apply]
    let i := hom_cospan_pullback_to_diagonal_filler_map l r ⟨d,u⟩
    let homSquareComm :
        (hom_square l r).top ≫ (hom_square l r).right =
          (hom_square l r).left ≫ (hom_square l r).bot := by
      rw [(hom_square l r).comm]
    let j := Limits.pullback.lift
      (hom_square l r).top (hom_square l r).left homSquareComm
    let S : l □ r := { top := l ≫ δ , bot := δ ≫ r }
    let Δ : diagonal_filler S := {
      map := δ
      comm_top := by aesop_cat
      comm_bot := by aesop_cat
    }
    let comm_snd :=  Limits.pullback.lift_snd
      (hom_square l r).top (hom_square l r).left homSquareComm
    let comm_fst :=  Limits.pullback.lift_fst
      (hom_square l r).top (hom_square l r).left homSquareComm
    let Δ' : diagonal_filler S := {
      map := i (j δ)
      comm_top := by calc
        l ≫ i (j δ) = (hom_cospan_pullback_to_square_completion l r (j δ)).top :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_top l r ⟨d,u⟩ (j δ)
        _ = Limits.pullback.snd (hom_square_right l r) (hom_square_bot l r) (j δ) := by aesop_cat
        _ = (Limits.pullback.lift (hom_square l r).top (hom_square l r).left
            homSquareComm ≫
            Limits.pullback.snd (hom_square l r).right (hom_square l r).bot) δ := by rfl
        _ = (hom_square l r).left δ := by rw [comm_snd]
      comm_bot := by calc
        i (j δ) ≫ r = (hom_cospan_pullback_to_square_completion l r (j δ)).bot :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_bot l r ⟨d,u⟩ (j δ)
        _ = Limits.pullback.fst (hom_square_right l r) (hom_square_bot l r) (j δ) := by aesop_cat
        _ = (Limits.pullback.lift (hom_square l r).top (hom_square l r).left
            homSquareComm ≫
            Limits.pullback.fst (hom_square l r).right (hom_square l r).bot) δ := by rfl
        _ = (hom_square l r).top δ := by rw [comm_fst]
      }
    calc
      i (j δ) = Δ'.map := by rfl
      _ = Δ.map := by rw [← u _ Δ Δ']
      _ = δ := by rfl
  · apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst]
      ext x
      let g := Limits.pullback.fst (hom_square l r).right (hom_square l r).bot x
      let δ := hom_cospan_pullback_to_diagonal_filler_map l r ⟨d,u⟩
      calc
        (δ ≫ (hom_square l r).top) x = (δ x) ≫ r := rfl
        _ = (hom_cospan_pullback_to_square_completion l r x).bot :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_bot l r ⟨d,u⟩ x
        _ = g := by rfl
    · rw [Category.assoc, Limits.pullback.lift_snd]
      ext x
      let f := Limits.pullback.snd (hom_square l r).right (hom_square l r).bot x
      let δ := hom_cospan_pullback_to_diagonal_filler_map l r ⟨d,u⟩
      calc
        (δ ≫ (hom_square l r).left) x = l ≫ (δ x) := rfl
        _ = (hom_cospan_pullback_to_square_completion l r x).top :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_top l r ⟨d,u⟩ x
        _ = f := by rfl

/- We now start working towards the proof of the implication in the other direction -/

/- The cone associated to the pullback of the hom square -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_pullback_cone
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    Limits.PullbackCone (hom_square l r).right (hom_square l r).bot :=
  Limits.pullback.cone (hom_square l r).right (hom_square l r).bot

/- The proof that this cone is a limit cone-/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_pullback_cone_isLimit
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    Limits.IsLimit (hom_pullback_cone l r) :=
  Limits.pullback.isLimit (hom_square l r).right (hom_square l r).bot

/- The components of this limit cone-/

/-- Imported FactorizationSystems declaration. -/
def hom_pullback_cone_point {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Type v :=
  (hom_pullback_cone l r).pt

/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_pullback_fst
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : hom_pullback_cone_point l r ⟶ (B ⟶ Y) :=
  Limits.pullback.fst (hom_square l r).right (hom_square l r).bot

/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_pullback_snd
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : hom_pullback_cone_point l r ⟶ (A ⟶ X) :=
  Limits.pullback.snd (hom_square l r).right (hom_square l r).bot

/- We construct a cone over the same cospan with apex Hom(B,X) -/

omit HasPullbacks in
lemma diagonals_comm {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (hom_square l r).top ≫ (hom_square l r).right = (hom_square l r).left ≫ (hom_square l r).bot
    := by rw [(hom_square l r).comm]

/-- Imported FactorizationSystems declaration. -/
def diagonals_cone
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    Limits.PullbackCone (hom_square l r).right (hom_square l r).bot :=
  Limits.PullbackCone.mk (hom_square l r).top (hom_square l r).left (diagonals_comm l r)

/-- Imported FactorizationSystems declaration. -/
def diagonals_cone_point
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Type v :=
  (diagonals_cone l r).pt

/-- Imported FactorizationSystems declaration. -/
def diagonals_cone_fst
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_cone_point l r ⟶ (B ⟶ Y) :=
  Limits.PullbackCone.fst (diagonals_cone l r)

/-- Imported FactorizationSystems declaration. -/
def diagonals_cone_snd
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_cone_point l r ⟶ (A ⟶ X) :=
  Limits.PullbackCone.snd (diagonals_cone l r)

/- The map from Hom(B,X) into the canonical pullback -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonals_hom_cospan_lift
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_cone_point l r ⟶ hom_pullback_cone_point l r :=
  (hom_pullback_cone_isLimit l r).lift (diagonals_cone l r)

omit HasPullbacks in
lemma diagonals_hom_cospan_lift_fst
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_hom_cospan_lift l r ≫ hom_pullback_fst l r = (hom_square l r).top :=
  (hom_pullback_cone_isLimit l r).fac (diagonals_cone l r) Limits.WalkingCospan.left

omit HasPullbacks in
lemma diagonals_hom_cospan_lift_snd
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonals_hom_cospan_lift l r ≫ hom_pullback_snd l r = (hom_square l r).left :=
  (hom_pullback_cone_isLimit l r).fac (diagonals_cone l r) Limits.WalkingCospan.right

/- An auxiliary definition of orthogonality that behaves much better -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def hom_orthogonal_aux {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Prop :=
  IsIso (diagonals_hom_cospan_lift l r)

omit HasPullbacks in
lemma hom_orthogonal_implies_hom_orthogonal_aux
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal l r) :
    hom_orthogonal l r := h

omit HasPullbacks in
lemma hom_orthogonal_aux_implies_hom_orthogonal
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    hom_orthogonal l r := h

/- The isomorphism from Hom(B,X) into the canonical pullback -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_orthogonal_aux_hom {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
      (B ⟶ X) ⟶ (hom_cospan_pullback l r) :=
  (asIso (diagonals_hom_cospan_lift l r)).hom

/-The inverse of the isomorphism from Hom(B,X) into the canonical pullback -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_orthogonal_aux_inv {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    (hom_cospan_pullback l r) ⟶ (B ⟶ X) :=
  (asIso (diagonals_hom_cospan_lift l r)).inv

omit HasPullbacks in
lemma hom_orthogonal_aux_hom_inv_id
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    (hom_orthogonal_aux_hom l r h) ≫ (hom_orthogonal_aux_inv l r h) = 𝟙 (B ⟶ X) :=
  (asIso (diagonals_hom_cospan_lift l r)).hom_inv_id

omit HasPullbacks in
lemma hom_orthogonal_aux_inv_hom_id
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    (hom_orthogonal_aux_inv l r h) ≫ (hom_orthogonal_aux_hom l r h) =
    𝟙 (hom_cospan_pullback l r) :=
  (asIso (diagonals_hom_cospan_lift l r)).inv_hom_id

/- We now prove that the cone with apex Hom(B,X) is a limit cone -/

/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def hom_orthogonal_aux_lift
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    ∀ s : Limits.PullbackCone (hom_square l r).right (hom_square l r).bot,
    s.pt ⟶ diagonals_cone_point l r := by
  intro s
  let lift : s.pt ⟶ hom_pullback_cone_point l r
    := (Limits.pullback.isLimit (hom_square l r).right (hom_square l r).bot).lift s
  exact lift ≫ hom_orthogonal_aux_inv l r h

lemma hom_orthogonal_aux_fac_left
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    ∀ s : Limits.PullbackCone (hom_square l r).right (hom_square l r).bot,
    hom_orthogonal_aux_lift l r h s ≫ diagonals_cone_fst l r = s.fst := by
  intro s
  let lift : s.pt ⟶ hom_pullback_cone_point l r :=
    (Limits.pullback.isLimit (hom_square l r).right (hom_square l r).bot).lift s
  calc
    hom_orthogonal_aux_lift l r h s ≫ diagonals_cone_fst l r =
    lift ≫ (hom_orthogonal_aux_inv l r h ≫ diagonals_cone_fst l r) := by rfl
    _ = lift ≫ hom_cospan_pullback_fst l r := by
      have triangle_comm :
        (diagonals_hom_cospan_pullback_lift l r) ≫ hom_cospan_pullback_fst l r =
        (hom_square l r).top := diagonals_hom_cospan_pullback_lift_fst l r
      apply whisker_eq lift
      calc
        hom_orthogonal_aux_inv l r h ≫ (hom_square l r).top =
        hom_orthogonal_aux_inv l r h ≫
          ((diagonals_hom_cospan_pullback_lift l r) ≫ hom_cospan_pullback_fst l r) :=
          by rw [triangle_comm]
        _ = (hom_orthogonal_aux_inv l r h ≫ diagonals_hom_cospan_pullback_lift l r) ≫
          hom_cospan_pullback_fst l r := by aesop_cat
        _ = (hom_orthogonal_aux_inv l r h ≫ hom_orthogonal_aux_hom l r h) ≫
          hom_cospan_pullback_fst l r := by rfl
        _ = hom_cospan_pullback_fst l r := by rw [hom_orthogonal_aux_inv_hom_id l r h]; simp
    _ = s.fst := (hom_pullback_cone_isLimit l r).fac s Limits.WalkingCospan.left

lemma hom_orthogonal_aux_fac_right
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    ∀ s : Limits.PullbackCone (hom_square l r).right (hom_square l r).bot,
    hom_orthogonal_aux_lift l r h s ≫ diagonals_cone_snd l r = s.snd := by
  intro s
  let lift : s.pt ⟶ (hom_cospan_pullback l r) :=
    (Limits.pullback.isLimit (hom_square l r).right (hom_square l r).bot).lift s
  calc
    hom_orthogonal_aux_lift l r h s ≫ diagonals_cone_snd l r =
    lift ≫ (hom_orthogonal_aux_inv l r h ≫ diagonals_cone_snd l r) := by rfl
    _ = lift ≫ hom_cospan_pullback_snd l r := by
      have triangle_comm :
        (diagonals_hom_cospan_pullback_lift l r) ≫ hom_cospan_pullback_snd l r =
        (hom_square l r).left := diagonals_hom_cospan_pullback_lift_snd l r
      apply whisker_eq lift
      calc
        hom_orthogonal_aux_inv l r h ≫ (hom_square l r).left =
        hom_orthogonal_aux_inv l r h ≫
          (diagonals_hom_cospan_pullback_lift l r ≫ hom_cospan_pullback_snd l r) :=
          by rw [triangle_comm]
        _ = (hom_orthogonal_aux_inv l r h ≫ hom_orthogonal_aux_hom l r h) ≫
          hom_cospan_pullback_snd l r := by rfl
        _ = hom_cospan_pullback_snd l r := by rw [hom_orthogonal_aux_inv_hom_id l r]; simp
    _ = s.snd := (hom_pullback_cone_isLimit l r).fac s Limits.WalkingCospan.right

lemma hom_orthogonal_aux_uniq
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    (∀ (s : Limits.PullbackCone (hom_square l r).right (hom_square l r).bot) (m : s.pt ⟶ B ⟶ X),
      m ≫ (hom_square l r).top = s.fst →
      m ≫ (hom_square l r).left = s.snd →
      m = hom_orthogonal_aux_lift l r h s) := by
  intro s m comm₁ comm₂
  unfold hom_orthogonal_aux_lift
  let lift : s.pt ⟶ hom_pullback_cone_point l r :=
    (hom_pullback_cone_isLimit l r).lift s
  have comm₁' :
      (m ≫ hom_orthogonal_aux_hom l r h) ≫ hom_pullback_fst l r =
      lift ≫ hom_pullback_fst l r := by
    calc
      (m ≫ hom_orthogonal_aux_hom l r h) ≫ hom_pullback_fst l r =
          m ≫ (hom_orthogonal_aux_hom l r h ≫ hom_pullback_fst l r) := by
        rw [Category.assoc]
      _ = m ≫ (hom_square l r).top := by
        apply whisker_eq m
        exact diagonals_hom_cospan_lift_fst l r
      _ = s.fst := comm₁
      _ = lift ≫ hom_pullback_fst l r := by
        simpa [lift, hom_pullback_fst] using
          ((hom_pullback_cone_isLimit l r).fac s Limits.WalkingCospan.left).symm
  have comm₂' :
      (m ≫ hom_orthogonal_aux_hom l r h) ≫ hom_pullback_snd l r =
      lift ≫ hom_pullback_snd l r := by
    calc
      (m ≫ hom_orthogonal_aux_hom l r h) ≫ hom_pullback_snd l r =
          m ≫ (hom_orthogonal_aux_hom l r h ≫ hom_pullback_snd l r) := by
        rw [Category.assoc]
      _ = m ≫ (hom_square l r).left := by
        apply whisker_eq m
        exact diagonals_hom_cospan_lift_snd l r
      _ = s.snd := comm₂
      _ = lift ≫ hom_pullback_snd l r := by
        simpa [lift, hom_pullback_snd] using
          ((hom_pullback_cone_isLimit l r).fac s Limits.WalkingCospan.right).symm
  have whee : m ≫ hom_orthogonal_aux_hom l r h = (hom_pullback_cone_isLimit l r).lift s :=
    Limits.pullback.hom_ext comm₁' comm₂'
  calc
    m = m ≫ (hom_orthogonal_aux_hom l r h ≫ hom_orthogonal_aux_inv l r h) := by
      rw [hom_orthogonal_aux_hom_inv_id l r h, Category.comp_id]
    _ = (m ≫ hom_orthogonal_aux_hom l r h) ≫ hom_orthogonal_aux_inv l r h := by rfl
    _ = (hom_pullback_cone_isLimit l r).lift s ≫ hom_orthogonal_aux_inv l r h := by
      exact congrArg (fun q => q ≫ hom_orthogonal_aux_inv l r h) whee

/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_orthogonal_aux_implies_is_pullback_diagonals
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) :
    Limits.IsLimit (diagonals_cone l r) :=
  Limits.PullbackCone.IsLimit.mk
    (diagonals_comm l r)
    (hom_orthogonal_aux_lift l r h)
    (hom_orthogonal_aux_fac_left l r h)
    (hom_orthogonal_aux_fac_right l r h)
    (hom_orthogonal_aux_uniq l r h)

/- Given a commuting square in C with vertical morphisms l and r, we construct a cone over the
hom-cospan in Set with apex the terminal object -/

/-- Imported FactorizationSystems declaration. -/
def square_completion_cone_snd {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r)
    : PUnit ⟶ (A ⟶ X) :=
  TypeCat.ofHom fun _ => S.top

/-- Imported FactorizationSystems declaration. -/
def square_completion_cone_fst {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r)
    : PUnit ⟶ (B ⟶ Y) :=
  TypeCat.ofHom fun _ => S.bot

omit HasPullbacks in
lemma square_completion_cone_comm {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r) :
    square_completion_cone_fst l r S ≫ (hom_square l r).right =
    square_completion_cone_snd l r S ≫ (hom_square l r).bot := by
  ext _
  exact S.comm

/-- Imported FactorizationSystems declaration. -/
def square_completion_cone {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r) :
    Limits.PullbackCone (hom_square l r).right (hom_square l r).bot :=
  Limits.PullbackCone.mk
    (square_completion_cone_fst l r S)
    (square_completion_cone_snd l r S)
    (square_completion_cone_comm l r S)

/- Given a diagonal filler of a square S, we construct a map in Set
from the terminal object into the apex Hom(B,X) of the pullback cone -/
/-- Imported FactorizationSystems declaration. -/
def diagonal_filler_to_pullback
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r) (δ : diagonal_filler S) :
    PUnit ⟶ diagonals_cone_point l r :=
  TypeCat.ofHom fun _ => δ.map

/- If the hom square is cartesian, then l and r are orthogonal -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def is_hom_orthogonal_aux_implies_is_orthogonal
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : hom_orthogonal_aux l r) : orthogonal l r where
  diagonal := by
    intro S
    exact {
      map := (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
        (square_completion_cone l r S) PUnit.unit
      comm_top := by
        have comm : (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
            (square_completion_cone l r S) ≫
            (hom_square l r).left =
            square_completion_cone_snd l r S :=
          (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).fac
          (square_completion_cone l r S) Limits.WalkingCospan.right
        calc
          l ≫ ((hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
          (square_completion_cone l r S) PUnit.unit) =
          ((hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
          (square_completion_cone l r S) ≫ (hom_square l r).left) PUnit.unit := by rfl
          _ = square_completion_cone_snd l r S PUnit.unit := by
            exact congrArg (fun f : PUnit ⟶ (A ⟶ X) => f PUnit.unit) comm
          _ = S.top := by rfl
      comm_bot := by
        have comm : (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
            (square_completion_cone l r S) ≫
            (hom_square l r).top =
            square_completion_cone_fst l r S :=
          (hom_orthogonal_aux_implies_is_pullback_diagonals l r h).fac
          (square_completion_cone l r S) Limits.WalkingCospan.left
        calc
          ((hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
          (square_completion_cone l r S) PUnit.unit) ≫ r =
          ((hom_orthogonal_aux_implies_is_pullback_diagonals l r h).lift
          (square_completion_cone l r S) ≫ (hom_square l r).top) PUnit.unit := by rfl
          _ = square_completion_cone_fst l r S PUnit.unit := by
            exact congrArg (fun f : PUnit ⟶ (B ⟶ Y) => f PUnit.unit) comm
          _ = S.bot := by rfl
    }
  diagonal_unique := by
    intro S d d'
    have comm₁ :
        (diagonal_filler_to_pullback l r S d) ≫ diagonals_cone_fst l r =
        (diagonal_filler_to_pullback l r S d') ≫ diagonals_cone_fst l r:= by
      apply (homOfElement_eq_iff
        ((diagonal_filler_to_pullback l r S d ≫ diagonals_cone_fst l r) PUnit.unit)
        ((diagonal_filler_to_pullback l r S d' ≫ diagonals_cone_fst l r) PUnit.unit)).mpr
      calc
        (diagonal_filler_to_pullback l r S d ≫ diagonals_cone_fst l r) PUnit.unit =
        d.map ≫ r:= by rfl
        _ = S.bot := by rw [d.comm_bot]
        _ = d'.map ≫ r := by rw [d'.comm_bot]
        _ = (diagonal_filler_to_pullback l r S d' ≫ diagonals_cone_fst l r) PUnit.unit := by rfl
    have comm₂ :
        (diagonal_filler_to_pullback l r S d) ≫ diagonals_cone_snd l r =
        (diagonal_filler_to_pullback l r S d') ≫ diagonals_cone_snd l r:= by
      apply (homOfElement_eq_iff
        ((diagonal_filler_to_pullback l r S d ≫ diagonals_cone_snd l r) PUnit.unit)
        ((diagonal_filler_to_pullback l r S d' ≫ diagonals_cone_snd l r) PUnit.unit)).mpr
      calc
        (diagonal_filler_to_pullback l r S d ≫ diagonals_cone_snd l r) PUnit.unit =
        l ≫ d.map:= by rfl
        _ = S.top := by rw [d.comm_top]
        _ = l ≫ d'.map := by rw [d'.comm_top]
        _ = (diagonal_filler_to_pullback l r S d' ≫ diagonals_cone_snd l r) PUnit.unit := by rfl
    have unique := Limits.PullbackCone.IsLimit.hom_ext
      (hom_orthogonal_aux_implies_is_pullback_diagonals l r h) comm₁ comm₂
    simpa [diagonal_filler_to_pullback] using
      congrArg (fun f : PUnit ⟶ diagonals_cone_point l r => f PUnit.unit) unique

/-- Imported FactorizationSystems declaration. -/
noncomputable
def hom_orthogonal_implies_orthogonal
    {A B X Y : C} {l : A ⟶ B} {r : X ⟶ Y} (h : hom_orthogonal l r) : orthogonal l r :=
    is_hom_orthogonal_aux_implies_is_orthogonal l r
      ( hom_orthogonal_implies_hom_orthogonal_aux l r h)

end CategoryTheory
