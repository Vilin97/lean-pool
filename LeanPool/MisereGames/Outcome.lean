/-
Copyright (c) 2025 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.Player
public import Mathlib.Order.Defs.PartialOrder

/-!
Misere combinatorial games.
-/

namespace MisereGames

public section

/--
The four outcome classes of a short partizan game.
-/
inductive Outcome where
  /--
  Left always wins, regardless of who starts.
  -/
  | L
  /--
  The Next (first) player wins.
  -/
  | N
  /--
  The Previous (second) player wins.
  -/
  | P
  /--
  Right always wins, regardless of who starts.
  -/
  | R
deriving DecidableEq

namespace Outcome

/--
Game outcomes are partially ordered in favour of Left, as illustrated in the
following Hasse diagram:
```
  L
 / \
N   P
 \ /
  R
```
-/
instance : LT Outcome where
  lt lhs rhs :=
    (lhs ≠ Outcome.L ∧ rhs = Outcome.L) ∨
    (lhs = Outcome.R ∧ rhs = Outcome.N) ∨
    (lhs = Outcome.R ∧ rhs = Outcome.P)

instance : DecidableLT Outcome := by
  simp only [DecidableLT, DecidableRel, LT.lt]
  infer_instance

instance instLE : LE Outcome where
  le lhs rhs := (lhs = rhs) ∨ (lhs < rhs)

instance : DecidableLE Outcome := by
  simp only [DecidableLE, DecidableRel, LE.le]
  infer_instance

instance : Preorder Outcome where
  le_refl _ := Or.inl rfl
  le_trans a b c _ _ := by
    cases a
    all_goals cases b
    all_goals cases c
    all_goals simp [LE.le, LT.lt] at *
  lt_iff_le_not_ge a b := by
    cases a
    all_goals cases b
    all_goals simp [LE.le, LT.lt] at *

instance : PartialOrder Outcome where
  le_antisymm a b _ _ := by
    cases a
    all_goals cases b
    all_goals simp [LE.le, LT.lt] at *

@[simp]
theorem ge_R (o : Outcome) : o ≥ Outcome.R := by
  simp only [ge_iff_le]
  unfold LE.le
  cases o
  all_goals simp [instLE, LT.lt]

@[simp]
theorem le_R_iff (o : Outcome) : o ≤ Outcome.R ↔ o = .R := by
  constructor <;> intro h1
  · exact le_antisymm h1 (ge_R o)
  · rw [h1]

@[simp]
theorem L_ge (o : Outcome) : Outcome.L ≥ o := by
  simp only [ge_iff_le]
  unfold LE.le
  cases o
  all_goals simp [instLE, LT.lt]

theorem ge_P_ge_N_eq_L {o : Outcome} (hp : o ≥ Outcome.P) (hn : o ≥ Outcome.N)
    : o = Outcome.L := by
  cases o
  all_goals simp [LE.le, LT.lt, LE.le] at *

@[simp]
theorem le_N_eq_N_or_R {o : Outcome} (hp : o ≤ Outcome.N)
    : o = Outcome.N ∨ o = Outcome.R := by
  cases o
  all_goals simp [LE.le, LT.lt, LE.le] at *

/-- Conjugate an outcome by swapping the players. -/
@[expose]
def Conjugate : Outcome → Outcome
  | .L => .R
  | .R => .L
  | .P => .P
  | .N => .N

theorem conjugate_conjugate_eq_self {o : Outcome} : o.Conjugate.Conjugate = o := by
  cases o <;> rfl

theorem outcome_ge_conjugate_le {x y : Outcome} (h1 : x ≥ y) :
    x.Conjugate ≤ y.Conjugate := by
  cases h2 : x
    <;> cases h3 : y
    <;> unfold Outcome.Conjugate
    <;> simp only [LE.le, LT.lt, and_false, and_self, and_true, ne_eq, not_false_eq_true,
                   not_true_eq_false, or_self, reduceCtorEq, or_false, or_true]
    <;> simp only [h2, h3, ge_iff_le] at h1
    <;> absurd h1
    <;> simp only [LE.le, LT.lt, and_false, and_self, and_true, ne_eq, not_false_eq_true,
                   not_true_eq_false, or_self, reduceCtorEq]

/-- The outcome determined by the winners when Left and Right start. -/
@[expose]
def ofPlayers : Player → Player → Outcome
  | .left, .left => Outcome.L
  | .right, .right => Outcome.R
  | .right, .left => Outcome.P
  | .left, .right => Outcome.N

/-- The outcome where the given player wins no matter who starts. -/
@[expose]
def ofPlayer : Player → Outcome
  | .left => Outcome.L
  | .right => Outcome.R

@[simp]
theorem ofPlayer_left : ofPlayer .left = .L := by rfl

@[simp]
theorem ofPlayer_right : ofPlayer .right = .R := by rfl

end Outcome

end

end MisereGames
