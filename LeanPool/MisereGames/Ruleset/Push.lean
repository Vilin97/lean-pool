/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Ruleset.Strip

/-!
Misere combinatorial games.
-/

namespace MisereGames

open GameForm
open Form

public section

/-!
# Push

Push is played on the same horizontal strip of squares as `Shove` (see
`Strip.Piece`), and a move again consists of choosing one of your pieces and
sliding it one square to the left. The difference is that in Push *only the
adjacent run of pieces moves*: the movement stops at the first empty square to
the left of the chosen piece, which gets filled. If there is no empty square to
the left, the leftmost piece falls off the board, exactly as in `Shove`.

In terms of the shared `Strip` primitive `shiftDown`, the Push move pushing the
piece at position `n` is `shiftDown b g n`, where `g` is the position of the
first empty square to the left of `n` (`Push.startPos`), or `0` if there is
none. So `Push` is the `Strip` ruleset whose shift anchor `start` is the
rightmost gap below `n`.
-/

/--
A `Push` position is a strip board (a function from positions to pieces with
finite support).
-/
structure Push where
  /-- The underlying strip board. -/
  toBoard : Strip.Board

namespace Push

open Strip

/--
The anchor of a Push move at position `n`: the position of the rightmost empty
square strictly to the left of `n` (the "gap" the adjacent block slides into),
or `0` if there is no empty square to the left.
-/
def startPos (b : Strip.Board) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun j => b.board j = .none ∧ j < n) n

theorem startPos_le (b : Strip.Board) (n : ℕ) : startPos b n ≤ n :=
  Nat.findGreatest_le _

theorem startPos_lt (b : Strip.Board) {n : ℕ} (hn : 0 < n) : startPos b n < n := by
  refine lt_of_le_of_ne (Nat.findGreatest_le _) ?_
  intro heq
  obtain ⟨-, h2⟩ := (Nat.findGreatest_eq_iff.mp heq).2.1 (by omega)
  exact absurd h2 (lt_irrefl n)

/--
`Push` is the `Strip` ruleset whose shift starts at the rightmost gap below
`n`: pushing the piece at position `n` slides only the contiguous block of
pieces adjacent to `n` into the first empty square to its left (or drops the
leftmost piece when there is no gap).
-/
instance : Strip Push where
  toBoard := Push.toBoard
  ofBoard := Push.mk
  toBoard_ofBoard _ := rfl
  push s n := ⟨s.toBoard.shiftDownB (startPos s.toBoard n) n⟩
  start s n := startPos s.toBoard n
  start_le s n := startPos_le s.toBoard n
  start_lt := by intro s _ hn; exact startPos_lt s.toBoard hn
  push_eq _ _ := rfl

/--
When there is an empty square to the left of `n`, the Push anchor is itself an
empty square: the adjacent block slides into it. This is what makes Push "stop
at the first empty tile".
-/
theorem board_startPos_eq_none (b : Strip.Board) {n : ℕ}
    (h : ∃ j, j < n ∧ b.board j = .none) :
    b.board (startPos b n) = .none := by
  obtain ⟨j, hj, hjb⟩ := h
  have hspec : (fun j => b.board j = .none ∧ j < n) (startPos b n) :=
    Nat.findGreatest_spec (P := fun j => b.board j = .none ∧ j < n) (le_of_lt hj) ⟨hjb, hj⟩
  exact hspec.1

/-- The `GameForm` of a Push position. -/
protected noncomputable def toGameForm : Push → GameForm := Strip.toGameForm

/-- The misère quotient of `Push` is isomorphic to `ℤ`. -/
protected noncomputable def equivInt :
    MisereQuotient (ClosedUnderAdd.closure (Ruleset.Forms Push)) ≃ ℤ :=
  Strip.equivInt Push

protected theorem le_iff_equiv_ge
    (a b : MisereQuotient (ClosedUnderAdd.closure (Ruleset.Forms Push))) :
    a ≤ b ↔ MisereQuotient.stridedEquivInt a ≥ MisereQuotient.stridedEquivInt b :=
  Strip.le_iff_equiv_ge Push a b

end Push

end

end MisereGames
