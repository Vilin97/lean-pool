/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Copyright (c) 2025 Aaron Liu. All rights reserved.
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Copyright (c) 2025 Yuyang Zhao. All rights reserved.
Copyright (c) 2024 Theodore Hwa. All rights reserved.
Copyright (c) 2019 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov, Aaron Liu, Apurva Nakade, Fox Thomson, František Silváši,
Isabel Longbottom, Junyan Xu, Kim Morrison, Mario Carneiro, Reid Barton, Theodore Hwa,
Violeta Hernández Palacios, Yuyang Zhao
-/
/-
Adapted and modified from the Apache-2.0-licensed CombinatorialGames construction:
https://github.com/vihdzp/combinatorial-games
-/
module

public import Mathlib.Order.GameAdd

/-!
# Conway's refinement conjecture from first principles

This file gives, in order, the complete definitions needed to read Conway's refinement conjecture:

1. a well-founded game with small left and right option families;
2. Conway recursion for negation, addition, multiplication, and order;
3. numeric games and equality of games;
4. surreal-number representatives and Conway's omnific-integer cut;
5. Conway's eight-variable refinement statement.

Surreals are presented by numeric games. `Game.Equivalent` is equality in their quotient, so the
four displayed product equations below are exactly the corresponding quotient equations.
`InlineConwayRefinementProof` proves that the recursive operations preserve numericity and
equivalence and then proves the final proposition.
-/

public noncomputable section

universe u

namespace ConwayRefinement.Standalone.InlineConwayRefinement

/-- A well-founded Conway game, built from small left and right option families. -/
inductive Game : Type (u + 1) where
  | mk (Left Right : Type u) (left : Left → Game) (right : Right → Game)

namespace Game

/-- A direct move selects either a left or a right option. -/
inductive Move : Game → Game → Prop
  | left {Left Right : Type u} {left : Left → Game} {right : Right → Game}
      (i : Left) : Move (left i) (.mk Left Right left right)
  | right {Left Right : Type u} {left : Left → Game} {right : Right → Game}
      (i : Right) : Move (right i) (.mk Left Right left right)

/-- Direct descent through options is well founded. -/
theorem move_wf : WellFounded Move := by
  constructor
  intro x
  induction x with
  | mk Left Right left right ihLeft ihRight =>
      constructor
      intro y hy
      cases hy with
      | left i => exact ihLeft i
      | right i => exact ihRight i

/-- Well-founded recursion on an ordered pair of games. -/
noncomputable def pairRec {C : Game → Game → Sort*}
    (step : ∀ x y,
      (∀ x' y', Prod.Lex Move Move (x', y') (x, y) → C x' y') → C x y)
    (x y : Game) : C x y :=
  @WellFounded.fix (Game × Game) (fun p ↦ C p.1 p.2) _ (move_wf.prod_lex move_wf)
    (fun p rec ↦ step p.1 p.2 (fun x' y' h ↦ rec (x', y') h)) (x, y)

/-- The characteristic equation for recursion on a pair of games. -/
theorem pairRec_eq {C : Game → Game → Sort*}
    (step : ∀ x y,
      (∀ x' y', Prod.Lex Move Move (x', y') (x, y) → C x' y') → C x y)
    (x y : Game) :
    pairRec step x y = step x y fun x' y' _ ↦ pairRec step x' y' :=
  WellFounded.fix_eq ..

/-- Negation interchanges the players and negates every option. -/
@[expose] def neg : Game → Game
  | .mk Left Right left right =>
      .mk Right Left (fun i ↦ neg (right i)) (fun i ↦ neg (left i))

/-- The defining option equation for negation. -/
theorem neg_mk (Left Right : Type u) (left : Left → Game) (right : Right → Game) :
    neg (.mk Left Right left right) =
      .mk Right Left (fun i ↦ neg (right i)) (fun i ↦ neg (left i)) :=
  (rfl)

/-- Conway addition: either player moves in exactly one summand. -/
@[expose] noncomputable def add : Game → Game → Game :=
  pairRec fun x y rec ↦
    match x, y with
    | .mk Lx Rx lx rx, .mk Ly Ry ly ry =>
        let x := Game.mk Lx Rx lx rx
        let y := Game.mk Ly Ry ly ry
        .mk (Lx ⊕ Ly) (Rx ⊕ Ry)
          (Sum.elim
            (fun i ↦ rec (lx i) y (Prod.Lex.left y y (Move.left i)))
            (fun j ↦ rec x (ly j) (Prod.Lex.right x (Move.left j))))
          (Sum.elim
            (fun i ↦ rec (rx i) y (Prod.Lex.left y y (Move.right i)))
            (fun j ↦ rec x (ry j) (Prod.Lex.right x (Move.right j))))

/-- The defining option equation for Conway addition. -/
theorem add_mk (Lx Rx Ly Ry : Type u) (lx : Lx → Game) (rx : Rx → Game)
    (ly : Ly → Game) (ry : Ry → Game) :
    add (.mk Lx Rx lx rx) (.mk Ly Ry ly ry) =
      .mk (Lx ⊕ Ly) (Rx ⊕ Ry)
        (Sum.elim (fun i ↦ add (lx i) (.mk Ly Ry ly ry))
          (fun j ↦ add (.mk Lx Rx lx rx) (ly j)))
        (Sum.elim (fun i ↦ add (rx i) (.mk Ly Ry ly ry))
          (fun j ↦ add (.mk Lx Rx lx rx) (ry j))) := by
  rw [add, pairRec_eq]

/-- The zero game `{ | }`. -/
@[expose] def zero : Game.{u} := .mk (ULift.{u} Empty) (ULift.{u} Empty) nofun nofun

/-- The zero game has no options. -/
theorem zero_eq : zero =
    .mk (ULift.{u} Empty) (ULift.{u} Empty) nofun nofun := (rfl)

/-- The unit game `{0 | }`. -/
@[expose] def one : Game.{u} :=
  .mk PUnit.{u + 1} (ULift.{u} Empty) (fun _ ↦ zero) nofun

/-- The unit game has zero as its sole left option. -/
theorem one_eq : one =
    .mk PUnit.{u + 1} (ULift.{u} Empty) (fun _ ↦ zero) nofun := (rfl)

/-- Conway multiplication. Its option from options `a` of `x` and `b` of `y` is
`a * y + x * b - a * b`; equal-side moves are left options and opposite-side moves are right
options. -/
@[expose] noncomputable def mul : Game → Game → Game :=
  pairRec fun x y rec ↦
    match x, y with
    | .mk Lx Rx lx rx, .mk Ly Ry ly ry =>
      let x := Game.mk Lx Rx lx rx
      let y := Game.mk Ly Ry ly ry
      let option (a b : Game) (ha : Move a x) (hb : Move b y) :=
        add (add (rec a y (Prod.Lex.left y y ha))
          (rec x b (Prod.Lex.right x hb)))
          (neg (rec a b (Prod.Lex.left b y ha)))
      .mk ((Lx × Ly) ⊕ (Rx × Ry)) ((Lx × Ry) ⊕ (Rx × Ly))
        (Sum.elim
          (fun ij ↦ option (lx ij.1) (ly ij.2) (Move.left ij.1) (Move.left ij.2))
          (fun ij ↦ option (rx ij.1) (ry ij.2) (Move.right ij.1) (Move.right ij.2)))
        (Sum.elim
          (fun ij ↦ option (lx ij.1) (ry ij.2) (Move.left ij.1) (Move.right ij.2))
          (fun ij ↦ option (rx ij.1) (ly ij.2) (Move.right ij.1) (Move.left ij.2)))

/-- The defining option equation for Conway multiplication. -/
theorem mul_mk (Lx Rx Ly Ry : Type u) (lx : Lx → Game) (rx : Rx → Game)
    (ly : Ly → Game) (ry : Ry → Game) :
    mul (.mk Lx Rx lx rx) (.mk Ly Ry ly ry) =
      let x := Game.mk Lx Rx lx rx
      let y := Game.mk Ly Ry ly ry
      let option (a b : Game) := add (add (mul a y) (mul x b)) (neg (mul a b))
      .mk ((Lx × Ly) ⊕ (Rx × Ry)) ((Lx × Ry) ⊕ (Rx × Ly))
        (Sum.elim (fun ij ↦ option (lx ij.1) (ly ij.2))
          (fun ij ↦ option (rx ij.1) (ry ij.2)))
        (Sum.elim (fun ij ↦ option (lx ij.1) (ry ij.2))
          (fun ij ↦ option (rx ij.1) (ly ij.2))) := by
  rw [mul, pairRec_eq]

/-- Conway's recursive order: `x ≤ y` when no left option of `x` is at least `y`, and no right
option of `y` is at most `x`. -/
@[expose] noncomputable def Le : Game → Game → Prop :=
  Sym2.GameAdd.recursion move_wf fun x y rec ↦
    match x, y with
    | .mk Lx Rx lx rx, .mk Ly Ry ly ry =>
        let x := Game.mk Lx Rx lx rx
        let y := Game.mk Ly Ry ly ry
        (∀ i : Lx, ¬rec y (lx i) (Sym2.GameAdd.snd_fst (Move.left i))) ∧
        (∀ j : Ry, ¬rec (ry j) x (Sym2.GameAdd.fst_snd (Move.right j)))

/-- The defining option equation for Conway's order. -/
theorem le_mk (Lx Rx Ly Ry : Type u) (lx : Lx → Game) (rx : Rx → Game)
    (ly : Ly → Game) (ry : Ry → Game) :
    Le (.mk Lx Rx lx rx) (.mk Ly Ry ly ry) ↔
      (∀ i, ¬Le (.mk Ly Ry ly ry) (lx i)) ∧
      (∀ j, ¬Le (ry j) (.mk Lx Rx lx rx)) := by
  exact propext_iff.1 <| Sym2.GameAdd.recursion_eq ..

/-- Conway equivalence, the equality relation on games. -/
def Equivalent (x y : Game) : Prop := Le x y ∧ Le y x

/-- Conway equivalence unfolds to the two order inequalities. -/
theorem equivalent_iff (x y : Game) : Equivalent x y ↔ Le x y ∧ Le y x := (Iff.rfl)

/-- Conway's strict order on numeric games. -/
def Less (x y : Game) : Prop := Le x y ∧ ¬Le y x

/-- Conway's strict order unfolds to an inequality and failure of its reverse. -/
theorem less_iff (x y : Game) : Less x y ↔ Le x y ∧ ¬Le y x := (Iff.rfl)

/-- A game is numeric when all its options are numeric and every left option is strictly below
every right option. -/
inductive Numeric : Game → Prop where
  | mk {Left Right : Type u} {left : Left → Game} {right : Right → Game} :
      (∀ i j, Less (left i) (right j)) →
      (∀ i, Numeric (left i)) →
      (∀ j, Numeric (right j)) →
      Numeric (.mk Left Right left right)

end Game

/-- A surreal-number representative is a numeric well-founded Conway game. Two representatives
denote the same surreal number precisely when their games are `Game.Equivalent`. -/
structure Surreal : Type (u + 1) where
  game : Game.{u}
  numeric : Game.Numeric game

namespace Surreal

/-- The singleton Conway cut `{x - 1 | x + 1}` at game level. -/
noncomputable def singletonIntegerCut (x : Game.{u}) : Game.{u} :=
  .mk PUnit PUnit (fun _ ↦ Game.add x (Game.neg Game.one))
    (fun _ ↦ Game.add x Game.one)

/-- The singleton-cut construction unfolds to its two displayed options. -/
theorem singletonIntegerCut_eq (x : Game.{u}) :
    singletonIntegerCut x =
      .mk PUnit PUnit (fun _ ↦ Game.add x (Game.neg Game.one))
        (fun _ ↦ Game.add x Game.one) := (rfl)

/-- Conway's cut equation defining an omnific integer. -/
def IsConwayOmnificInteger (x : Surreal.{u}) : Prop :=
  Game.Equivalent x.game (singletonIntegerCut x.game)

/-- Membership unfolds to Conway's defining cut equation. -/
theorem isConwayOmnificInteger_iff (x : Surreal.{u}) :
    IsConwayOmnificInteger x ↔ Game.Equivalent x.game (singletonIntegerCut x.game) :=
  (Iff.rfl)

/-- Conway's four-factor statement. Every equation `a * b = c * d` of omnific integers has
omnific integers `e`, `f`, `g`, `h` with
`a = e * f`, `b = g * h`, `c = e * g`, and `d = f * h`. All equations are equality in the
quotient of numeric games, written directly as `Game.Equivalent`. -/
abbrev ConwayConjecture : Prop :=
  ∀ a b c d : Surreal.{u},
    IsConwayOmnificInteger a → IsConwayOmnificInteger b →
    IsConwayOmnificInteger c → IsConwayOmnificInteger d →
    Game.Equivalent (Game.mul a.game b.game) (Game.mul c.game d.game) →
    ∃ e f g h : Surreal.{u},
      IsConwayOmnificInteger e ∧ IsConwayOmnificInteger f ∧
      IsConwayOmnificInteger g ∧ IsConwayOmnificInteger h ∧
      Game.Equivalent a.game (Game.mul e.game f.game) ∧
      Game.Equivalent b.game (Game.mul g.game h.game) ∧
      Game.Equivalent c.game (Game.mul e.game g.game) ∧
      Game.Equivalent d.game (Game.mul f.game h.game)

end Surreal

end ConwayRefinement.Standalone.InlineConwayRefinement

/-!
## Formal proof

Proof module: `InlineConwayRefinementProof`.

* `ConwayConjecture` → `ConwayConjecture.proof`
-/
