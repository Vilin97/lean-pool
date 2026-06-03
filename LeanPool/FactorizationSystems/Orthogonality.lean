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

/-!
# LeanPool.FactorizationSystems.Orthogonality
-/

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
structure squareCompletion {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) where
  /-- The top horizontal morphism. -/
  top : A ⟶ X
  /-- The bottom horizontal morphism. -/
  bot : B ⟶ Y
  /-- The square commutes. -/
  comm : l ≫ bot = top ≫ r := by aesop_cat

/-- Imported FactorizationSystems declaration. -/
infixl:75 " □ " => squareCompletion

/- Forgetting the specification of vertical maps -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def squareOfSquareCompletion
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
structure diagonalFiller
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
  diagonal : (S : f □ g) → diagonalFiller S
  /-- The chosen diagonal filler is unique. -/
  diagonal_unique :
    (S : f □ g) → (d : diagonalFiller S) → (d' : diagonalFiller S) → d.map = d'.map

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
def homSquareLeft : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((B ⟶ X) ⟶ (A ⟶ X)) :=
  fun l r =>
    let _keep := r
    TypeCat.ofHom fun f => l ≫ f

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def homSquareRight : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((B ⟶ Y) ⟶ (A ⟶ Y)) :=
  fun l r =>
    let _keep := r
    TypeCat.ofHom fun f => l ≫ f

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def homSquareTop : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((B ⟶ X) ⟶ (B ⟶ Y)) :=
  fun l r =>
    let _keep := l
    TypeCat.ofHom fun f => f ≫ r

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def homSquareBot : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → ((A ⟶ X) ⟶ (A ⟶ Y)) :=
  fun l r =>
    let _keep := l
    TypeCat.ofHom fun f => f ≫ r

/-- Imported FactorizationSystems declaration. -/
@[reducible]
def homSquare : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) →
    square (B ⟶ X) (A ⟶ X) (B ⟶ Y) (A ⟶ Y) := fun l r =>
  {
    left := homSquareLeft l r
    right := homSquareRight l r
    top := homSquareTop l r
    bot := homSquareBot l r
    comm := by
      ext f
      exact Category.assoc l f r
  }

/- The canonical pullback of the cospan given by the right and bottom maps in the hom square -/
/-- Imported FactorizationSystems declaration. -/
def homCospanPullback : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → Type v := by
  intro A B X Y l r
  exact Limits.pullback (homSquareRight l r) (homSquareBot l r)

/- The associated pullback cone -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def homCospanPullbackCone : {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) →
    Limits.PullbackCone (homSquareRight l r) (homSquareBot l r) := by
  intro A B X Y l r
  exact Limits.pullback.cone (homSquareRight l r) (homSquareBot l r)


/- The first projection of the hom pullback -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def homCospanPullbackFst {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (homCospanPullback l r) ⟶ (B ⟶ Y) :=
  Limits.pullback.fst (homSquareRight l r) (homSquareBot l r)

/- The second projection of the hom pullback -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def homCospanPullbackSnd {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (homCospanPullback l r) ⟶ (A ⟶ X) :=
  Limits.pullback.snd (homSquareRight l r) (homSquareBot l r)

/- The universal property of the hom pullback -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def homCospanPullbackLift {W : Type v} {A B X Y : C}
    (l : A ⟶ B) (r : X ⟶ Y) (φ : W ⟶ (B ⟶ Y)) (ψ : W ⟶ (A ⟶ X))
    (comm : φ ≫ (homSquareRight l r) = ψ ≫ (homSquareBot l r) := by aesop_cat) :
    W ⟶ homCospanPullback l r :=
  Limits.pullback.lift φ ψ comm

omit HasPullbacks in
lemma hom_cospan_pullback_lift_fst {W : Type v} {A B X Y : C}
    (l : A ⟶ B) (r : X ⟶ Y) (φ : W ⟶ (B ⟶ Y)) (ψ : W ⟶ (A ⟶ X))
    (comm : φ ≫ (homSquareRight l r) = ψ ≫ (homSquareBot l r) := by aesop_cat) :
    homCospanPullbackLift l r φ ψ comm ≫ homCospanPullbackFst l r = φ :=
  Limits.pullback.lift_fst φ ψ comm

omit HasPullbacks in
lemma hom_cospan_pullback_lift_snd {W : Type v} {A B X Y : C}
    (l : A ⟶ B) (r : X ⟶ Y) (φ : W ⟶ (B ⟶ Y)) (ψ : W ⟶ (A ⟶ X))
    (comm : φ ≫ (homSquareRight l r) = ψ ≫ (homSquareBot l r) := by aesop_cat) :
    homCospanPullbackLift l r φ ψ comm ≫ homCospanPullbackSnd l r = ψ :=
  Limits.pullback.lift_snd φ ψ comm

/- The hom pullback square is in particular commutative -/
omit HasPullbacks in
lemma hom_cospan_pullback_condition {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (homCospanPullbackFst l r) ≫ (homSquareRight l r) =
    (homCospanPullbackSnd l r) ≫ (homSquareBot l r) :=
  Limits.pullback.condition

/- The property of a commuting square being Cartesian -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def isCartesianSquare {A B X Y : C} (S : square A B X Y) : Prop :=
  IsIso (Limits.pullback.lift S.top S.left (by rw [S.comm]))

/- The second characterization of orthogonality via the hom square in Set -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def homOrthogonal {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Prop :=
  isCartesianSquare (homSquare l r)

/- We construct a map from Hom(B,X) into the pullback
of the hom square via the universal mapping property -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonalsHomCospanPullbackTop {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (B ⟶ X) ⟶ (A ⟶ X) :=
  let _keep := r
  TypeCat.ofHom fun f => l ≫ f

/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonalsHomCospanPullbackBot {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (B ⟶ X) ⟶ (B ⟶ Y) :=
  let _keep := l
  TypeCat.ofHom fun f => f ≫ r

omit HasPullbacks in
lemma diagonals_hom_cospan_pullback_lift_comm {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (diagonalsHomCospanPullbackBot l r) ≫ (homSquareRight l r) =
    (diagonalsHomCospanPullbackTop l r) ≫ (homSquareBot l r) := by
  ext d
  calc
    (diagonalsHomCospanPullbackBot l r ≫ homSquareRight l r) d = l ≫ (d ≫ r) := rfl
    _ = (l ≫ d) ≫ r := (Category.assoc l d r).symm
    _ = (diagonalsHomCospanPullbackTop l r ≫ homSquareBot l r) d := rfl

/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonalsHomCospanPullbackLift {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (B ⟶ X) ⟶ homCospanPullback l r :=
  homCospanPullbackLift l r
    (diagonalsHomCospanPullbackBot l r)
    (diagonalsHomCospanPullbackTop l r)
    (diagonals_hom_cospan_pullback_lift_comm l r)

omit HasPullbacks in
lemma diagonals_hom_cospan_pullback_lift_fst {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonalsHomCospanPullbackLift l r ≫ homCospanPullbackFst l r =
    (diagonalsHomCospanPullbackBot l r) :=
  Limits.pullback.lift_fst
    (diagonalsHomCospanPullbackBot l r)
    (diagonalsHomCospanPullbackTop l r)
    (diagonals_hom_cospan_pullback_lift_comm l r)

omit HasPullbacks in
lemma diagonals_hom_cospan_pullback_lift_snd {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonalsHomCospanPullbackLift l r ≫ homCospanPullbackSnd l r =
    (diagonalsHomCospanPullbackTop l r) :=
  Limits.pullback.lift_snd
    (diagonalsHomCospanPullbackBot l r)
    (diagonalsHomCospanPullbackTop l r)
    (diagonals_hom_cospan_pullback_lift_comm l r)

/- Given an element in the pullback of the hom
square in Set, we construct a commuting square in C -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def homCospanPullbackToSquareCompletion
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (x : homCospanPullback l r) :
    l □ r := by
  let x'  := (homCospanPullbackFst l r) x
  let x'' := (homCospanPullbackSnd l r)  x
  have S : l □ r := {
      top := x''
      bot := x'
      comm := by
        simpa [x', x''] using congrArg
          (fun h : homCospanPullback l r ⟶ (A ⟶ Y) => h x)
          (hom_cospan_pullback_condition l r)
  }
  exact S

/- With the assumption that l and r are orthognal, we can construct from an
element in the pullback of the hom square a diagonal filler of this square -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def homCospanPullbackToDiagonalFiller
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r)
    (x : Limits.pullback (homSquareRight l r) (homSquareBot l r)) :
    diagonalFiller (homCospanPullbackToSquareCompletion l r x) := by
  let ⟨d,S⟩ := h
  exact d (homCospanPullbackToSquareCompletion l r x)

/-- Imported FactorizationSystems declaration. -/
noncomputable
def homCospanPullbackToDiagonalFillerMap
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r) :
    (Limits.pullback (homSquareRight l r) (homSquareBot l r)) ⟶ (B ⟶ X) :=
  TypeCat.ofHom fun x => (homCospanPullbackToDiagonalFiller l r h x).map

omit HasPullbacks in
lemma hom_cospan_pullback_to_diagonal_filler_map_comm_top
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r)
    (x : Limits.pullback (homSquareRight l r) (homSquareBot l r)) :
    l ≫ (homCospanPullbackToDiagonalFillerMap l r h x) =
    (homCospanPullbackToSquareCompletion l r x).top :=
  (homCospanPullbackToDiagonalFiller l r h x).comm_top

omit HasPullbacks in
lemma hom_cospan_pullback_to_diagonal_filler_map_comm_bot
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : orthogonal l r)
    (x : Limits.pullback (homSquareRight l r) (homSquareBot l r)) :
    (homCospanPullbackToDiagonalFillerMap l r h x) ≫ r =
    (homCospanPullbackToSquareCompletion l r x).bot :=
  (homCospanPullbackToDiagonalFiller l r h x).comm_bot

omit HasPullbacks

/- If morphisms l and r in C are orthogonal, then the hom square is cartesian -/
omit HasPullbacks in
lemma orthogonal_implies_hom_orthogonal :
    {A B X Y : C} → (l : A ⟶ B) → (r : X ⟶ Y) → (orthogonal l r) → (homOrthogonal l r) := by
  intro A B X Y l r ⟨d,u⟩
  unfold homOrthogonal
  unfold isCartesianSquare
  use homCospanPullbackToDiagonalFillerMap l r ⟨d,u⟩
  constructor
  · ext δ
    simp only [TypeCat.Fun.toFun_apply, comp_apply, id_apply]
    let i := homCospanPullbackToDiagonalFillerMap l r ⟨d,u⟩
    let homSquareComm :
        (homSquare l r).top ≫ (homSquare l r).right =
          (homSquare l r).left ≫ (homSquare l r).bot := by
      rw [(homSquare l r).comm]
    let j := Limits.pullback.lift
      (homSquare l r).top (homSquare l r).left homSquareComm
    let S : l □ r := { top := l ≫ δ , bot := δ ≫ r }
    let Δ : diagonalFiller S := {
      map := δ
      comm_top := by aesop_cat
      comm_bot := by aesop_cat
    }
    let comm_snd :=  Limits.pullback.lift_snd
      (homSquare l r).top (homSquare l r).left homSquareComm
    let comm_fst :=  Limits.pullback.lift_fst
      (homSquare l r).top (homSquare l r).left homSquareComm
    let Δ' : diagonalFiller S := {
      map := i (j δ)
      comm_top := by calc
        l ≫ i (j δ) = (homCospanPullbackToSquareCompletion l r (j δ)).top :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_top l r ⟨d,u⟩ (j δ)
        _ = Limits.pullback.snd (homSquareRight l r) (homSquareBot l r) (j δ) := by aesop_cat
        _ = (Limits.pullback.lift (homSquare l r).top (homSquare l r).left
            homSquareComm ≫
            Limits.pullback.snd (homSquare l r).right (homSquare l r).bot) δ := by rfl
        _ = (homSquare l r).left δ := by rw [comm_snd]
      comm_bot := by calc
        i (j δ) ≫ r = (homCospanPullbackToSquareCompletion l r (j δ)).bot :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_bot l r ⟨d,u⟩ (j δ)
        _ = Limits.pullback.fst (homSquareRight l r) (homSquareBot l r) (j δ) := by aesop_cat
        _ = (Limits.pullback.lift (homSquare l r).top (homSquare l r).left
            homSquareComm ≫
            Limits.pullback.fst (homSquare l r).right (homSquare l r).bot) δ := by rfl
        _ = (homSquare l r).top δ := by rw [comm_fst]
      }
    calc
      i (j δ) = Δ'.map := by rfl
      _ = Δ.map := by rw [← u _ Δ Δ']
      _ = δ := by rfl
  · apply Limits.pullback.hom_ext
    · rw [Category.assoc, Limits.pullback.lift_fst]
      ext x
      let g := Limits.pullback.fst (homSquare l r).right (homSquare l r).bot x
      let δ := homCospanPullbackToDiagonalFillerMap l r ⟨d,u⟩
      calc
        (δ ≫ (homSquare l r).top) x = (δ x) ≫ r := rfl
        _ = (homCospanPullbackToSquareCompletion l r x).bot :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_bot l r ⟨d,u⟩ x
        _ = g := by rfl
    · rw [Category.assoc, Limits.pullback.lift_snd]
      ext x
      let f := Limits.pullback.snd (homSquare l r).right (homSquare l r).bot x
      let δ := homCospanPullbackToDiagonalFillerMap l r ⟨d,u⟩
      calc
        (δ ≫ (homSquare l r).left) x = l ≫ (δ x) := rfl
        _ = (homCospanPullbackToSquareCompletion l r x).top :=
          hom_cospan_pullback_to_diagonal_filler_map_comm_top l r ⟨d,u⟩ x
        _ = f := by rfl

/- We now start working towards the proof of the implication in the other direction -/

/- The cone associated to the pullback of the hom square -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def homPullbackCone
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    Limits.PullbackCone (homSquare l r).right (homSquare l r).bot :=
  Limits.pullback.cone (homSquare l r).right (homSquare l r).bot

/- The proof that this cone is a limit cone-/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def homPullbackConeIsLimit
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    Limits.IsLimit (homPullbackCone l r) :=
  Limits.pullback.isLimit (homSquare l r).right (homSquare l r).bot

/- The components of this limit cone-/

/-- Imported FactorizationSystems declaration. -/
def homPullbackConePoint {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Type v :=
  (homPullbackCone l r).pt

/-- Imported FactorizationSystems declaration. -/
noncomputable
def homPullbackFst
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : homPullbackConePoint l r ⟶ (B ⟶ Y) :=
  Limits.pullback.fst (homSquare l r).right (homSquare l r).bot

/-- Imported FactorizationSystems declaration. -/
noncomputable
def homPullbackSnd
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : homPullbackConePoint l r ⟶ (A ⟶ X) :=
  Limits.pullback.snd (homSquare l r).right (homSquare l r).bot

/- We construct a cone over the same cospan with apex Hom(B,X) -/

omit HasPullbacks in
lemma diagonals_comm {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    (homSquare l r).top ≫ (homSquare l r).right = (homSquare l r).left ≫ (homSquare l r).bot
    := by rw [(homSquare l r).comm]

/-- Imported FactorizationSystems declaration. -/
def diagonalsCone
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    Limits.PullbackCone (homSquare l r).right (homSquare l r).bot :=
  Limits.PullbackCone.mk (homSquare l r).top (homSquare l r).left (diagonals_comm l r)

/-- Imported FactorizationSystems declaration. -/
def diagonalsConePoint
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Type v :=
  (diagonalsCone l r).pt

/-- Imported FactorizationSystems declaration. -/
def diagonalsConeFst
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonalsConePoint l r ⟶ (B ⟶ Y) :=
  Limits.PullbackCone.fst (diagonalsCone l r)

/-- Imported FactorizationSystems declaration. -/
def diagonalsConeSnd
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonalsConePoint l r ⟶ (A ⟶ X) :=
  Limits.PullbackCone.snd (diagonalsCone l r)

/- The map from Hom(B,X) into the canonical pullback -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def diagonalsHomCospanLift
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonalsConePoint l r ⟶ homPullbackConePoint l r :=
  (homPullbackConeIsLimit l r).lift (diagonalsCone l r)

omit HasPullbacks in
lemma diagonals_hom_cospan_lift_fst
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonalsHomCospanLift l r ≫ homPullbackFst l r = (homSquare l r).top :=
  (homPullbackConeIsLimit l r).fac (diagonalsCone l r) Limits.WalkingCospan.left

omit HasPullbacks in
lemma diagonals_hom_cospan_lift_snd
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) :
    diagonalsHomCospanLift l r ≫ homPullbackSnd l r = (homSquare l r).left :=
  (homPullbackConeIsLimit l r).fac (diagonalsCone l r) Limits.WalkingCospan.right

/- An auxiliary definition of orthogonality that behaves much better -/
/-- Imported FactorizationSystems declaration. -/
@[reducible]
def homOrthogonalAux {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) : Prop :=
  IsIso (diagonalsHomCospanLift l r)

omit HasPullbacks in
lemma hom_orthogonal_implies_hom_orthogonal_aux
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonal l r) :
    homOrthogonal l r := h

omit HasPullbacks in
lemma hom_orthogonal_aux_implies_hom_orthogonal
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
    homOrthogonal l r := h

/- The isomorphism from Hom(B,X) into the canonical pullback -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def homOrthogonalAuxHom {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
      (B ⟶ X) ⟶ (homCospanPullback l r) :=
  (asIso (diagonalsHomCospanLift l r)).hom

/-The inverse of the isomorphism from Hom(B,X) into the canonical pullback -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def homOrthogonalAuxInv {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
    (homCospanPullback l r) ⟶ (B ⟶ X) :=
  (asIso (diagonalsHomCospanLift l r)).inv

omit HasPullbacks in
lemma hom_orthogonal_aux_hom_inv_id
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
    (homOrthogonalAuxHom l r h) ≫ (homOrthogonalAuxInv l r h) = 𝟙 (B ⟶ X) :=
  (asIso (diagonalsHomCospanLift l r)).hom_inv_id

omit HasPullbacks in
lemma hom_orthogonal_aux_inv_hom_id
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
    (homOrthogonalAuxInv l r h) ≫ (homOrthogonalAuxHom l r h) =
    𝟙 (homCospanPullback l r) :=
  (asIso (diagonalsHomCospanLift l r)).inv_hom_id

/- We now prove that the cone with apex Hom(B,X) is a limit cone -/

/-- Imported FactorizationSystems declaration. -/
@[reducible]
noncomputable
def homOrthogonalAuxLift
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
    ∀ s : Limits.PullbackCone (homSquare l r).right (homSquare l r).bot,
    s.pt ⟶ diagonalsConePoint l r := by
  intro s
  let lift : s.pt ⟶ homPullbackConePoint l r
    := (Limits.pullback.isLimit (homSquare l r).right (homSquare l r).bot).lift s
  exact lift ≫ homOrthogonalAuxInv l r h

lemma hom_orthogonal_aux_fac_left
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
    ∀ s : Limits.PullbackCone (homSquare l r).right (homSquare l r).bot,
    homOrthogonalAuxLift l r h s ≫ diagonalsConeFst l r = s.fst := by
  intro s
  let lift : s.pt ⟶ homPullbackConePoint l r :=
    (Limits.pullback.isLimit (homSquare l r).right (homSquare l r).bot).lift s
  calc
    homOrthogonalAuxLift l r h s ≫ diagonalsConeFst l r =
    lift ≫ (homOrthogonalAuxInv l r h ≫ diagonalsConeFst l r) := by rfl
    _ = lift ≫ homCospanPullbackFst l r := by
      have triangle_comm :
        (diagonalsHomCospanPullbackLift l r) ≫ homCospanPullbackFst l r =
        (homSquare l r).top := diagonals_hom_cospan_pullback_lift_fst l r
      apply whisker_eq lift
      calc
        homOrthogonalAuxInv l r h ≫ (homSquare l r).top =
        homOrthogonalAuxInv l r h ≫
          ((diagonalsHomCospanPullbackLift l r) ≫ homCospanPullbackFst l r) :=
          by rw [triangle_comm]
        _ = (homOrthogonalAuxInv l r h ≫ diagonalsHomCospanPullbackLift l r) ≫
          homCospanPullbackFst l r := by aesop_cat
        _ = (homOrthogonalAuxInv l r h ≫ homOrthogonalAuxHom l r h) ≫
          homCospanPullbackFst l r := by rfl
        _ = homCospanPullbackFst l r := by rw [hom_orthogonal_aux_inv_hom_id l r h]; simp
    _ = s.fst := (homPullbackConeIsLimit l r).fac s Limits.WalkingCospan.left

lemma hom_orthogonal_aux_fac_right
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
    ∀ s : Limits.PullbackCone (homSquare l r).right (homSquare l r).bot,
    homOrthogonalAuxLift l r h s ≫ diagonalsConeSnd l r = s.snd := by
  intro s
  let lift : s.pt ⟶ (homCospanPullback l r) :=
    (Limits.pullback.isLimit (homSquare l r).right (homSquare l r).bot).lift s
  calc
    homOrthogonalAuxLift l r h s ≫ diagonalsConeSnd l r =
    lift ≫ (homOrthogonalAuxInv l r h ≫ diagonalsConeSnd l r) := by rfl
    _ = lift ≫ homCospanPullbackSnd l r := by
      have triangle_comm :
        (diagonalsHomCospanPullbackLift l r) ≫ homCospanPullbackSnd l r =
        (homSquare l r).left := diagonals_hom_cospan_pullback_lift_snd l r
      apply whisker_eq lift
      calc
        homOrthogonalAuxInv l r h ≫ (homSquare l r).left =
        homOrthogonalAuxInv l r h ≫
          (diagonalsHomCospanPullbackLift l r ≫ homCospanPullbackSnd l r) :=
          by rw [triangle_comm]
        _ = (homOrthogonalAuxInv l r h ≫ homOrthogonalAuxHom l r h) ≫
          homCospanPullbackSnd l r := by rfl
        _ = homCospanPullbackSnd l r := by rw [hom_orthogonal_aux_inv_hom_id l r]; simp
    _ = s.snd := (homPullbackConeIsLimit l r).fac s Limits.WalkingCospan.right

lemma hom_orthogonal_aux_uniq
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
    (∀ (s : Limits.PullbackCone (homSquare l r).right (homSquare l r).bot) (m : s.pt ⟶ B ⟶ X),
      m ≫ (homSquare l r).top = s.fst →
      m ≫ (homSquare l r).left = s.snd →
      m = homOrthogonalAuxLift l r h s) := by
  intro s m comm₁ comm₂
  unfold homOrthogonalAuxLift
  let lift : s.pt ⟶ homPullbackConePoint l r :=
    (homPullbackConeIsLimit l r).lift s
  have comm₁' :
      (m ≫ homOrthogonalAuxHom l r h) ≫ homPullbackFst l r =
      lift ≫ homPullbackFst l r := by
    calc
      (m ≫ homOrthogonalAuxHom l r h) ≫ homPullbackFst l r =
          m ≫ (homOrthogonalAuxHom l r h ≫ homPullbackFst l r) := by
        rw [Category.assoc]
      _ = m ≫ (homSquare l r).top := by
        apply whisker_eq m
        exact diagonals_hom_cospan_lift_fst l r
      _ = s.fst := comm₁
      _ = lift ≫ homPullbackFst l r := by
        convert
          ((homPullbackConeIsLimit l r).fac s Limits.WalkingCospan.left).symm
  have comm₂' :
      (m ≫ homOrthogonalAuxHom l r h) ≫ homPullbackSnd l r =
      lift ≫ homPullbackSnd l r := by
    calc
      (m ≫ homOrthogonalAuxHom l r h) ≫ homPullbackSnd l r =
          m ≫ (homOrthogonalAuxHom l r h ≫ homPullbackSnd l r) := by
        rw [Category.assoc]
      _ = m ≫ (homSquare l r).left := by
        apply whisker_eq m
        exact diagonals_hom_cospan_lift_snd l r
      _ = s.snd := comm₂
      _ = lift ≫ homPullbackSnd l r := by
        convert
          ((homPullbackConeIsLimit l r).fac s Limits.WalkingCospan.right).symm
  have whee : m ≫ homOrthogonalAuxHom l r h = (homPullbackConeIsLimit l r).lift s :=
    Limits.pullback.hom_ext comm₁' comm₂'
  calc
    m = m ≫ (homOrthogonalAuxHom l r h ≫ homOrthogonalAuxInv l r h) := by
      rw [hom_orthogonal_aux_hom_inv_id l r h, Category.comp_id]
    _ = (m ≫ homOrthogonalAuxHom l r h) ≫ homOrthogonalAuxInv l r h := by rfl
    _ = (homPullbackConeIsLimit l r).lift s ≫ homOrthogonalAuxInv l r h := by
      exact congrArg (fun q => q ≫ homOrthogonalAuxInv l r h) whee

/-- Imported FactorizationSystems declaration. -/
noncomputable
def homOrthogonalAuxImpliesIsPullbackDiagonals
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) :
    Limits.IsLimit (diagonalsCone l r) :=
  Limits.PullbackCone.IsLimit.mk
    (diagonals_comm l r)
    (homOrthogonalAuxLift l r h)
    (hom_orthogonal_aux_fac_left l r h)
    (hom_orthogonal_aux_fac_right l r h)
    (hom_orthogonal_aux_uniq l r h)

/- Given a commuting square in C with vertical morphisms l and r, we construct a cone over the
hom-cospan in Set with apex the terminal object -/

/-- Imported FactorizationSystems declaration. -/
def squareCompletionConeSnd {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r)
    : PUnit ⟶ (A ⟶ X) :=
  TypeCat.ofHom fun _ => S.top

/-- Imported FactorizationSystems declaration. -/
def squareCompletionConeFst {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r)
    : PUnit ⟶ (B ⟶ Y) :=
  TypeCat.ofHom fun _ => S.bot

omit HasPullbacks in
lemma square_completion_cone_comm {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r) :
    squareCompletionConeFst l r S ≫ (homSquare l r).right =
    squareCompletionConeSnd l r S ≫ (homSquare l r).bot := by
  ext _
  exact S.comm

/-- Imported FactorizationSystems declaration. -/
def squareCompletionCone {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r) :
    Limits.PullbackCone (homSquare l r).right (homSquare l r).bot :=
  Limits.PullbackCone.mk
    (squareCompletionConeFst l r S)
    (squareCompletionConeSnd l r S)
    (square_completion_cone_comm l r S)

/- Given a diagonal filler of a square S, we construct a map in Set
from the terminal object into the apex Hom(B,X) of the pullback cone -/
/-- Imported FactorizationSystems declaration. -/
def diagonalFillerToPullback
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (S : l □ r) (δ : diagonalFiller S) :
    PUnit ⟶ diagonalsConePoint l r :=
  TypeCat.ofHom fun _ => δ.map

/- If the hom square is cartesian, then l and r are orthogonal -/
/-- Imported FactorizationSystems declaration. -/
noncomputable
def isHomOrthogonalAuxImpliesIsOrthogonal
    {A B X Y : C} (l : A ⟶ B) (r : X ⟶ Y) (h : homOrthogonalAux l r) : orthogonal l r where
  diagonal := by
    intro S
    exact {
      map := (homOrthogonalAuxImpliesIsPullbackDiagonals l r h).lift
        (squareCompletionCone l r S) PUnit.unit
      comm_top := by
        have comm : (homOrthogonalAuxImpliesIsPullbackDiagonals l r h).lift
            (squareCompletionCone l r S) ≫
            (homSquare l r).left =
            squareCompletionConeSnd l r S :=
          (homOrthogonalAuxImpliesIsPullbackDiagonals l r h).fac
          (squareCompletionCone l r S) Limits.WalkingCospan.right
        calc
          l ≫ ((homOrthogonalAuxImpliesIsPullbackDiagonals l r h).lift
          (squareCompletionCone l r S) PUnit.unit) =
          ((homOrthogonalAuxImpliesIsPullbackDiagonals l r h).lift
          (squareCompletionCone l r S) ≫ (homSquare l r).left) PUnit.unit := by rfl
          _ = squareCompletionConeSnd l r S PUnit.unit := by
            exact congrArg (fun f : PUnit ⟶ (A ⟶ X) => f PUnit.unit) comm
          _ = S.top := by rfl
      comm_bot := by
        have comm : (homOrthogonalAuxImpliesIsPullbackDiagonals l r h).lift
            (squareCompletionCone l r S) ≫
            (homSquare l r).top =
            squareCompletionConeFst l r S :=
          (homOrthogonalAuxImpliesIsPullbackDiagonals l r h).fac
          (squareCompletionCone l r S) Limits.WalkingCospan.left
        calc
          ((homOrthogonalAuxImpliesIsPullbackDiagonals l r h).lift
          (squareCompletionCone l r S) PUnit.unit) ≫ r =
          ((homOrthogonalAuxImpliesIsPullbackDiagonals l r h).lift
          (squareCompletionCone l r S) ≫ (homSquare l r).top) PUnit.unit := by rfl
          _ = squareCompletionConeFst l r S PUnit.unit := by
            exact congrArg (fun f : PUnit ⟶ (B ⟶ Y) => f PUnit.unit) comm
          _ = S.bot := by rfl
    }
  diagonal_unique := by
    intro S d d'
    have comm₁ :
        (diagonalFillerToPullback l r S d) ≫ diagonalsConeFst l r =
        (diagonalFillerToPullback l r S d') ≫ diagonalsConeFst l r:= by
      apply (homOfElement_eq_iff
        ((diagonalFillerToPullback l r S d ≫ diagonalsConeFst l r) PUnit.unit)
        ((diagonalFillerToPullback l r S d' ≫ diagonalsConeFst l r) PUnit.unit)).mpr
      calc
        (diagonalFillerToPullback l r S d ≫ diagonalsConeFst l r) PUnit.unit =
        d.map ≫ r:= by rfl
        _ = S.bot := by rw [d.comm_bot]
        _ = d'.map ≫ r := by rw [d'.comm_bot]
        _ = (diagonalFillerToPullback l r S d' ≫ diagonalsConeFst l r) PUnit.unit := by rfl
    have comm₂ :
        (diagonalFillerToPullback l r S d) ≫ diagonalsConeSnd l r =
        (diagonalFillerToPullback l r S d') ≫ diagonalsConeSnd l r:= by
      apply (homOfElement_eq_iff
        ((diagonalFillerToPullback l r S d ≫ diagonalsConeSnd l r) PUnit.unit)
        ((diagonalFillerToPullback l r S d' ≫ diagonalsConeSnd l r) PUnit.unit)).mpr
      calc
        (diagonalFillerToPullback l r S d ≫ diagonalsConeSnd l r) PUnit.unit =
        l ≫ d.map:= by rfl
        _ = S.top := by rw [d.comm_top]
        _ = l ≫ d'.map := by rw [d'.comm_top]
        _ = (diagonalFillerToPullback l r S d' ≫ diagonalsConeSnd l r) PUnit.unit := by rfl
    have unique := Limits.PullbackCone.IsLimit.hom_ext
      (homOrthogonalAuxImpliesIsPullbackDiagonals l r h) comm₁ comm₂
    have unique' :
        (diagonalFillerToPullback l r S d : PUnit ⟶ (B ⟶ X)) =
          diagonalFillerToPullback l r S d' := by
      simpa [diagonalFillerToPullback, diagonalsConePoint, diagonalsCone] using unique
    exact congrArg (fun f : PUnit ⟶ (B ⟶ X) => f PUnit.unit) unique'

/-- Imported FactorizationSystems declaration. -/
noncomputable
def homOrthogonalImpliesOrthogonal
    {A B X Y : C} {l : A ⟶ B} {r : X ⟶ Y} (h : homOrthogonal l r) : orthogonal l r :=
    isHomOrthogonalAuxImpliesIsOrthogonal l r
      ( hom_orthogonal_implies_hom_orthogonal_aux l r h)

end CategoryTheory
