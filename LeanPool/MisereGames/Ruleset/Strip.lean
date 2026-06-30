/-
Copyright (c) 2026 Tomasz Maciosowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tomasz Maciosowski
-/
module

public import LeanPool.MisereGames.GameGraph
public import LeanPool.MisereGames.Misere.Stride
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Cases
import Mathlib.Tactic.Linarith

/-!
Misere combinatorial games.
-/

namespace MisereGames

open GameForm

public section

universe u

/-!
# Strips: shared board theory for `Shove` and `Push`

Both `Shove` and `Push` are played on a horizontal strip of squares, each
square either empty or occupied by a `Left` or `Right` piece (see
`Strip.Piece`). In both games a move consists of choosing one of your pieces
and shifting a contiguous "block" of pieces one square to the left.

The two rulesets differ only in *which* block of pieces is moved:

* In `Shove`, choosing the piece at position `n` shifts everything at positions
`0 .. n` one square to the left, regardless of gaps. The piece at position `0`
falls off the strip.
* In `Push`, only the *adjacent* run of pieces moves: the block stops at the
first empty square to the left of `n` (which gets filled). If there is no empty
square the leftmost piece falls off, just like `Shove`.

This module factors out everything that both rulesets have in common. The
single shared primitive is `Strip.shiftDown b start n`, which shifts the
squares `(start, n]` one place to the left into `[start, n)`. Both rulesets are
special cases:

* `Shove`'s move is `shiftDown b 0 n`.
* `Push`'s move is `shiftDown b g n`, where `g` is the position of the first
empty square left of `n` (or `0` if there is none).

The crucial fact about either game is its *stride*: the distance to the
rightmost tile of a given colour. Since the stride only ever depends on the
rightmost tile, and since pushing the rightmost tile behaves identically in
`Shove` and `Push`, the entire stride theory — culminating in the proof that
the misère quotient is isomorphic to `ℤ` — is developed once here, generically,
in terms of a `Strip` typeclass.
-/

namespace Strip

/-- A single square of a strip: empty, or occupied by a Left/Right piece. -/
inductive Piece
  | none
  | left
  | right
  deriving DecidableEq

/-- The piece belonging to a given player. -/
def Piece.ofPlayer : Player → Piece
  | .left => .left
  | .right => .right

@[simp]
theorem Piece.ofPlayer_ne_none (p : Player) : Piece.ofPlayer p ≠ Piece.none := by
  cases p <;> simp only [Piece.ofPlayer, ne_eq, reduceCtorEq, not_false_eq_true]

@[simp]
theorem Piece.none_ne_ofPlayer (p : Player) : Piece.none ≠ Piece.ofPlayer p := by
  cases p <;> simp only [Piece.ofPlayer, ne_eq, reduceCtorEq, not_false_eq_true]

theorem Piece.ofPlayer_injective : Function.Injective Piece.ofPlayer := by
  intro p q h
  cases p <;> cases q <;> simp_all only [Piece.ofPlayer, reduceCtorEq]

theorem Piece.eq_none_of_ne_ofPlayer {x : Piece} (hl : x ≠ .ofPlayer .left)
    (hr : x ≠ .ofPlayer .right) : x = .none := by
  cases x <;>
    simp_all only [Piece.ofPlayer, ne_eq, reduceCtorEq, not_false_eq_true, not_true_eq_false]

theorem Piece.ne_none_of_ofPlayer {p : Player} {x : Piece} (h : x = Piece.ofPlayer p) :
    x ≠ .none := by
  rw [h]; exact ofPlayer_ne_none p

/--
A strip board: a function from positions on the strip (leftmost being `0`) to
the piece at that position, with finite support (only finitely many occupied
squares).
-/
structure Board where
  /-- The piece at each board position. -/
  board : ℕ → Piece
  finite_support : ∃ N, ∀ n, N ≤ n → board n = .none

namespace Board

@[ext]
theorem ext {s t : Board} (h : ∀ n, s.board n = t.board n) : s = t := by
  cases s; cases t; simp only [mk.injEq]; funext n; exact h n

/-- The empty board. -/
@[expose] protected def zero : Board :=
  { board := fun _ => .none, finite_support := ⟨0, fun _ _ => rfl⟩ }

@[simp]
theorem zero_board (n : ℕ) : Board.zero.board n = .none := rfl

/-!
### `shiftDown`: the shared move primitive
-/

/--
`shiftDown b start n` shifts the squares in `(start, n]` one place to the left,
into `[start, n)`. Concretely: squares strictly below `start` are unchanged;
squares `start ≤ i < n` receive the piece from `i + 1`; square `n` becomes
empty; squares above `n` are unchanged.

When `start = 0` this is the `Shove` move (the piece at `0` falls off). When
`start` is the position of the first empty square below `n`, the empty square
is filled and this is the `Push` move.
-/
@[expose] def shiftDown (b : ℕ → Piece) (start n : ℕ) : ℕ → Piece := fun i =>
  if i < start then b i
  else if i < n then b (i + 1)
  else if i = n then Piece.none
  else b i

@[simp]
theorem shiftDown_lt_start (b : ℕ → Piece) {start n i : ℕ} (h : i < start) :
    shiftDown b start n i = b i := by
  simp only [shiftDown, h, ↓reduceIte]

@[simp]
theorem shiftDown_mid (b : ℕ → Piece) {start n i : ℕ} (h1 : start ≤ i) (h2 : i < n) :
    shiftDown b start n i = b (i + 1) := by
  simp only [shiftDown, Nat.not_lt.mpr h1, ↓reduceIte, h2]

@[simp]
theorem shiftDown_eq (b : ℕ → Piece) {start n : ℕ} (h : start ≤ n) :
    shiftDown b start n n = Piece.none := by
  rcases Nat.lt_or_ge start n with h' | h'
  · simp only [shiftDown, Nat.not_lt.mpr h, lt_self_iff_false, ↓reduceIte]
  · have : start = n := le_antisymm h h'
    subst this
    simp only [shiftDown, lt_self_iff_false, ↓reduceIte]

@[simp]
theorem shiftDown_gt (b : ℕ → Piece) {start n i : ℕ} (h : n < i) :
    shiftDown b start n i = b i := by
  have h1 : ¬ i < n := by omega
  have h2 : i ≠ n := by omega
  by_cases h3 : i < start
  · simp only [shiftDown, h3, ↓reduceIte]
  · simp only [shiftDown, h3, ↓reduceIte, h1, h2]

/-- `shiftDown` applied to a board with finite support. -/
@[expose] def shiftDownB (s : Board) (start n : ℕ) : Board where
  board := shiftDown s.board start n
  finite_support := by
    obtain ⟨N, hN⟩ := s.finite_support
    refine ⟨max N (n + 1), fun m hm => ?_⟩
    unfold shiftDown
    split_ifs with h1 h2 h3
    · exact hN _ (by omega)
    · exact hN _ (by omega)
    · rfl
    · exact hN _ (by omega)

@[simp]
theorem shiftDownB_board (s : Board) (start n : ℕ) :
    (s.shiftDownB start n).board = shiftDown s.board start n := rfl

/-!
### Weight measure for well-foundedness
-/

/--
The weight of a board is the sum of `i + 1` over each non-empty position `i`.
This is finite by finite support, and strictly decreases with each `shiftDown`
(as long as the pushed square `n` was occupied).
-/
noncomputable def weight (s : Board) : ℕ :=
  ∑ i ∈ Finset.range s.finite_support.choose,
    if s.board i = .none then 0 else i + 1

theorem weight_eq_of_bound {s : Board} (N : ℕ) (hN : ∀ n, N ≤ n → s.board n = .none) :
    s.weight = ∑ i ∈ Finset.range N, if s.board i = .none then 0 else i + 1 := by
  have h_weight_def :
      s.weight =
      ∑ i ∈ Finset.range (max (s.finite_support.choose) N),
      (if s.board i = .none then 0 else i + 1) := by
    refine Finset.sum_subset ?_ ?_
      <;> intro i hi <;> simp_all only [Finset.mem_range, lt_sup_iff, true_or]
    grind only [Exists.choose_spec]
  cases max_cases (s.finite_support.choose) N
    <;> simp_all only [sup_of_le_left, sup_eq_left, and_self]
  rw [←Finset.sum_range_add_sum_Ico _ ‹_›]
  simpa using fun i hi₁ hi₂ => hN i hi₁

/-
`shiftDown` strictly decreases the weight, provided `start ≤ n` and the pushed
square `n` is occupied. This single lemma serves both `Shove` (`start = 0`) and
`Push`.
-/
theorem weight_shiftDownB_lt {s : Board} {start n : ℕ} (hsn : start ≤ n)
    (hn : s.board n ≠ .none) : (s.shiftDownB start n).weight < s.weight := by
  rw [weight_eq_of_bound]
  case N => exact n + 1 + s.finite_support.choose
  · have h_split : ∑ i ∈ Finset.range (n + 1 + s.finite_support.choose),
    (if (s.shiftDownB start n).board i = .none then 0 else i + 1) = (∑ i ∈ Finset.range start,
      (if s.board i = .none then 0 else i + 1)) + (∑ i ∈ Finset.Ico start n,
        (if s.board (i + 1) = .none then 0 else i + 1)) +
          (∑ i ∈ Finset.Ico (n + 1) (n + 1 + s.finite_support.choose),
            (if s.board i = .none then 0 else i + 1)) := by
      have h_range :
          Finset.range (n + 1 + s.finite_support.choose) =
            Finset.range start ∪ Finset.Ico start n ∪ {n} ∪
              Finset.Ico (n + 1) (n + 1 + s.finite_support.choose) := by
        grind only [usr Exists.choose_spec, = Finset.union_singleton, = Finset.insert_union,
          = Finset.mem_union, = Finset.mem_range, = Finset.mem_insert, = Finset.mem_Ico,
          = Finset.mem_singleton]
      rw [h_range, Finset.sum_union, Finset.sum_union, Finset.sum_union] <;> norm_num
      · simp +decide only [shiftDown, lt_self_iff_false, ↓reduceIte, ite_eq_right_iff,
          isEmpty_Prop, not_lt, hsn, IsEmpty.forall_iff, add_zero]
        congr! 2
        · exact Finset.sum_congr rfl fun x hx => by aesop
        · refine Finset.sum_congr rfl fun x hx => ?_
          have := Finset.mem_Ico.mp hx
          split_ifs <;> omega
        · grind only [= Finset.mem_Ico]
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
          have := Finset.mem_range.mp hx₁; have := Finset.mem_Ico.mp hx₂; omega
      · grind only
      · exact ⟨Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
          have := Finset.mem_range.mp hx₁; have := Finset.mem_Ico.mp hx₂; omega,
          Finset.disjoint_left.mpr fun x hx₁ hx₂ => by
          have := Finset.mem_Ico.mp hx₁; have := Finset.mem_Ico.mp hx₂; omega⟩
    rw [weight_eq_of_bound]
    case N => exact n + 1 + s.finite_support.choose
    · have h_split2 : ∑ i ∈ Finset.range (n + 1 + s.finite_support.choose),
      (if s.board i = .none then 0 else i + 1) = (∑ i ∈ Finset.range start,
        (if s.board i = .none then 0 else i + 1)) + (∑ i ∈ Finset.Ico start (n + 1),
          (if s.board i = .none then 0 else i + 1)) +
            (∑ i ∈ Finset.Ico (n + 1) (n + 1 + s.finite_support.choose),
              (if s.board i = .none then 0 else i + 1)) := by
        rw [Finset.sum_range_add_sum_Ico _ (by omega), Finset.sum_range_add_sum_Ico _ (by omega)]
      simp_all +decide only [ne_eq, shiftDownB_board, Finset.sum_Ico_eq_sum_range,
        add_tsub_cancel_left, add_lt_add_iff_right, add_lt_add_iff_left, gt_iff_lt]
      rw [Nat.succ_sub hsn, Finset.sum_range_succ']
      split_ifs <;> simp_all +decide only [add_assoc, add_zero, Nat.reduceAdd]
      · apply Finset.sum_lt_sum
        · grind only
        · use n - start - 1
          grind only [= Finset.mem_range]
      · exact
          lt_add_of_le_of_pos
            (Finset.sum_le_sum fun _ _ => by split_ifs <;> omega)
            (Nat.succ_pos _)
    · grind only [usr Exists.choose_spec]
  · intro m hm
    simp_all +decide only [shiftDownB_board]
    rw [shiftDown]
    grind only [usr Exists.choose_spec]

/-!
### The rightmost occupied position
-/

/--
The position of the rightmost occupied square (or `0` if the board is empty).
-/
noncomputable def rightmostPos (s : Board) : ℕ :=
  Nat.findGreatest (fun n => s.board n ≠ .none) s.finite_support.choose

theorem rightmostPos_le (s : Board) : s.rightmostPos ≤ s.finite_support.choose :=
  Nat.findGreatest_le _

theorem rightmostPos_spec (s : Board) {k : ℕ} (hk : k ≤ s.finite_support.choose)
    (hne : s.board k ≠ .none) : s.board s.rightmostPos ≠ .none := by
  unfold rightmostPos
  exact Nat.findGreatest_spec (P := fun n => s.board n ≠ .none) hk hne

theorem board_eq_none_of_gt_rightmostPos {s : Board} {k : ℕ}
    (hk : s.rightmostPos < k) : s.board k = .none := by
  unfold rightmostPos at hk
  by_cases hk2 : k ≤ s.finite_support.choose
  · by_contra h
    exact absurd (Nat.le_findGreatest hk2 h) (not_le.mpr hk)
  · simp at hk2
    grind only [Exists.choose_spec]

theorem rightmostPos_greatest {s : Board} {k : ℕ} (hk : s.board k ≠ .none) :
    k ≤ s.rightmostPos := by
  by_contra h
  push Not at h
  have hk2 : k ≤ s.finite_support.choose := by
    by_contra h2; push Not at h2
    exact hk (s.finite_support.choose_spec k (by omega))
  exact hk (board_eq_none_of_gt_rightmostPos h)

/-- A nonzero `rightmostPos` is always occupied. -/
theorem board_rightmostPos_ne_none {s : Board} (h : 0 < s.rightmostPos) :
    s.board s.rightmostPos ≠ .none :=
  (Nat.findGreatest_eq_iff.mp (rfl :
    Nat.findGreatest (fun n => s.board n ≠ .none) s.finite_support.choose = s.rightmostPos)).2.1
    h.ne'

/-!
### The stride
-/

/--
The `p`-stride of a board: the distance to the rightmost tile when it is of
colour `p`, and `0` otherwise. This is the same definition for `Shove` and
`Push`.
-/
noncomputable def stride (s : Board) (p : Player) : ℕ :=
  if s.board s.rightmostPos = .ofPlayer p then s.rightmostPos + 1
  else 0

theorem stride_neg_eq_zero {s : Board} (p : Player)
    (hp : s.board s.rightmostPos = .ofPlayer p) :
    s.stride (-p) = 0 := by
  cases p <;> simp_all +decide only [Strip.Board.stride, Player.le_left, Player.right_le,
    Player.neg_left, Player.neg_right, Player.le_right_eq, Player.le_left_eq, ↓reduceIte]

theorem rightmost_of_stride_pos {p : Player} {s : Board}
    (hs : s.stride p ≠ 0) :
    s.board s.rightmostPos = .ofPlayer p ∧ s.rightmostPos + 1 = s.stride p := by
  unfold Strip.Board.stride at ⊢ hs
  simp only [ne_eq, ite_eq_right_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false, imp_false,
             not_not] at hs
  simp only [hs, ↓reduceIte, and_self]

theorem neg_push_below_rightmost {s : Board} {p : Player} {m : ℕ}
    (hrm : s.board s.rightmostPos = .ofPlayer p)
    (hm : s.board m = .ofPlayer (-p)) :
    m < s.rightmostPos := by
  apply lt_of_le_of_ne (rightmostPos_greatest (Piece.ne_none_of_ofPlayer hm))
  rintro rfl
  rw [hm] at hrm
  absurd Piece.ofPlayer_injective hrm
  simp only [Player.ne_iff_eq_neg]

end Board

end Strip

/-!
## The `Strip` typeclass

A `Strip` is a type `R` of game positions whose underlying data is a `Board`,
equipped with a move `push r n` (push the piece at position `n`). Both `Shove`
and `Push` are instances. The move is required to be a `shiftDown` of the
board, anchored at a position `start r n ≤ n` (with `start r n < n` whenever `n
> 0`). This single description captures both rulesets.
-/

/-- A strip ruleset with positions backed by a finite-support board. -/
class Strip (R : Type u) where
  /-- The underlying board of a position. -/
  toBoard : R → Strip.Board
  /--
  Construct a position from a board (used to realise prescribed strides).
  -/
  ofBoard : Strip.Board → R
  toBoard_ofBoard (b : Strip.Board) : toBoard (ofBoard b) = b
  /-- The move: push the piece at position `n`. -/
  push : R → ℕ → R
  /-- The anchor position of the shift. -/
  start : R → ℕ → ℕ
  start_le (r : R) (n : ℕ) : start r n ≤ n
  start_lt (r : R) {n : ℕ} (hn : 0 < n) : start r n < n
  /-- The move is a `shiftDown` of the board anchored at `start`. -/
  push_eq (r : R) (n : ℕ) : toBoard (push r n) = (toBoard r).shiftDownB (start r n) n

namespace Strip

variable {R : Type u} [Strip R]

/-- The piece at position `n` of `r`. -/
@[expose] def board (r : R) (n : ℕ) : Piece := (toBoard r).board n

@[simp]
theorem board_def (r : R) (n : ℕ) : board r n = (toBoard r).board n := rfl


/-- Weight of a position. -/
@[expose] noncomputable def weight (r : R) : ℕ := (toBoard r).weight

/-- Rightmost occupied position. -/
@[expose] noncomputable def rightmostPos (r : R) : ℕ := (toBoard r).rightmostPos

/-- The `p`-stride of a position. -/
@[expose] noncomputable def stride (r : R) (p : Player) : ℕ := (toBoard r).stride p

theorem weight_def (r : R) : weight r = (toBoard r).weight := rfl
theorem rightmostPos_def (r : R) : rightmostPos r = (toBoard r).rightmostPos := rfl
theorem stride_def (r : R) (p : Player) : stride r p = (toBoard r).stride p := rfl

/-!
### Structural lemmas for `push`
-/

theorem board_push_above (r : R) {n i : ℕ} (h : n < i) :
    board (push r n) i = board r i := by
  simp only [board_def, push_eq, Board.shiftDownB_board, Board.shiftDown_gt _ h]

theorem board_push_eq (r : R) (n : ℕ) : board (push r n) n = .none := by
  simp only [board_def, push_eq, Board.shiftDownB_board, Board.shiftDown_eq _ (start_le r n)]

theorem board_push_below (r : R) {n i : ℕ} (h : i < start r n) :
    board (push r n) i = board r i := by
  simp only [board_def, push_eq, Board.shiftDownB_board, Board.shiftDown_lt_start _ h]

theorem board_push_shift (r : R) {n : ℕ} (hn : 0 < n) :
    board (push r n) (n - 1) = board r n := by
  have h1 : start r n ≤ n - 1 := by have := start_lt r hn; omega
  have h2 : n - 1 < n := by omega
  have h3 : n - 1 + 1 = n := by omega
  simp only [board_def, push_eq, Board.shiftDownB_board, Board.shiftDown_mid _ h1 h2, h3]

theorem weight_push_lt (r : R) {n : ℕ} (hn : board r n ≠ .none) :
    weight (push r n) < weight r := by
  rw [weight, weight, push_eq]
  exact Board.weight_shiftDownB_lt (start_le r n) hn

/-!
### Moves and the associated `GameForm`
-/

/-- Legal moves in a strip ruleset. -/
protected def moves : Player → R → Set R :=
  fun p s ↦ push s '' {n : ℕ | board s n = Piece.ofPlayer p}

theorem mem_moves_iff (p : Player) (s s' : R) :
    s' ∈ Strip.moves p s ↔ ∃ n, board s n = Piece.ofPlayer p ∧ s' = push s n := by
  simp only [Strip.moves, Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩
  · rintro ⟨n, hn, rfl⟩; exact ⟨n, hn, rfl⟩

/-- The game graph of a strip ruleset. -/
def graph (R : Type u) [Strip R] : GameGraph R where
  moves := Strip.moves

theorem weight_lt_of_mem_move {p : Player} {s s' : R}
    (h_mem : s' ∈ (graph R).moves p s) : weight s' < weight s := by
  obtain ⟨n, hn₁, hn₂⟩ := (Strip.mem_moves_iff p s s').mp h_mem
  subst hn₂
  exact weight_push_lt s (by rw [hn₁]; exact Piece.ofPlayer_ne_none p)

instance : (graph R).IsWellFounded where
  wf := by
    refine { wf := WellFounded.intro ?_ }
    intro s
    induction n : weight s using Nat.strong_induction_on generalizing s with
    | h n ih =>
      refine ⟨?_, fun s' hs' => ?_⟩
      refine ih _ ?_ _ rfl
      obtain ⟨p, hp⟩ := hs'
      have := Strip.weight_lt_of_mem_move (p := p) hp
      omega

/-- The `GameForm` of a strip position. -/
protected noncomputable def toGameForm : R → GameForm := GameGraph.toForm (g := graph R)

@[simp]
theorem moves_toGameForm (p : Player) (s : R) :
    Form.moves p (Strip.toGameForm s) = Strip.toGameForm '' (Strip.moves p s) := by
  simp only [Strip.toGameForm, graph, GameGraph.moves_toForm]

theorem toGameForm_zero_iff (g : R) :
    (Strip.toGameForm g = 0) ↔ (∀ n, board g n = .none) := by
  rw [ ← not_iff_not ]
  constructor <;> intro h <;> contrapose! h <;>
    simp_all +decide only [board_def, GameForm.ext_iff, moves_toGameForm, Form.moves_zero,
      Set.image_eq_empty, Player.forall]
  · unfold Strip.moves; aesop
  · unfold Strip.moves at h
    simp_all +decide only [board_def, Set.ext_iff, Set.mem_image, Set.mem_setOf_eq,
      Set.mem_empty_iff_false, iff_false, not_exists, not_and, forall_apply_eq_imp_iff₂,
      imp_false]
    exact fun n => Piece.eq_none_of_ne_ofPlayer ( h.1 n ) ( h.2 n )

theorem toGameForm_push_mem_moves {s : R} (p : Player) {m : ℕ}
    (hm : board s m = .ofPlayer p) :
    Strip.toGameForm (push s m) ∈ Form.moves p (Strip.toGameForm s) := by
  rw [moves_toGameForm]
  refine ⟨push s m, ?_, rfl⟩
  rw [mem_moves_iff p s _]
  exact ⟨m, hm, rfl⟩

theorem mem_moves_toGameForm_iff (s : R) (p : Player) (g' : GameForm) :
    g' ∈ Form.moves p (Strip.toGameForm s) ↔
    ∃ m, board s m = .ofPlayer p ∧ g' = Strip.toGameForm (push s m) := by
  rw [moves_toGameForm]
  simp only [Set.mem_image]
  constructor
  · rintro ⟨s', hs', rfl⟩
    obtain ⟨m, hm, rfl⟩ := (mem_moves_iff p s s').mp hs'
    exact ⟨m, hm, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨push s m, (mem_moves_iff p s _).mpr ⟨m, hm, rfl⟩, rfl⟩

/-!
### `rightmostPos` and `stride` under `push`
-/

theorem rightmostPos_push_below {s : R} {m : ℕ}
    (hm : m < rightmostPos s) :
    rightmostPos (push s m) = rightmostPos s := by
  have hpos : 0 < rightmostPos s := by omega
  have hb : board (push s m) (rightmostPos s) = board s (rightmostPos s) := board_push_above s hm
  apply Nat.le_antisymm
  · -- Every square strictly above `rightmostPos s` agrees with `s` (by
  -- `board_push_above`) and is therefore empty, so the rightmost square of
  -- `push s m` cannot exceed `rightmostPos s`.
    by_contra hcon
    push Not at hcon
    have hpush_pos : 0 < rightmostPos (push s m) := by omega
    have hgt : m < rightmostPos (push s m) := lt_trans hm hcon
    have hocc : board (push s m) (rightmostPos (push s m)) ≠ .none :=
      Board.board_rightmostPos_ne_none hpush_pos
    rw [board_push_above s hgt] at hocc
    exact hocc (Board.board_eq_none_of_gt_rightmostPos hcon)
  · refine Board.rightmostPos_greatest ?_
    rw [← board_def, hb]
    exact Board.board_rightmostPos_ne_none hpos

theorem rightmostPos_push_at {s : R} {k : ℕ}
    (hk : rightmostPos s = k) (hpos : 0 < k) (hne : board s k ≠ .none) :
    rightmostPos (push s k) = k - 1 := by
  -- By definition of `rightmostPos`, we know that for any `j > k - 1`, `board
  -- (push s k) j = .none`.
  have h_rightmost_le : ∀ j, j > k - 1 → (‹Strip R›.board (‹Strip R›.push s k)) j = .none := by
    intro j hj
    by_cases hjk : j = k
    · rw [hjk]
      exact ‹Strip R›.board_push_eq s k
    · have hj_gt : j > k := by
        exact lt_of_le_of_ne ( Nat.le_of_pred_lt hj ) ( Ne.symm hjk )
      have hs_empty : (‹Strip R›.board s) j = .none := by
        rw [board_def]
        exact Strip.Board.board_eq_none_of_gt_rightmostPos (by
          rw [← rightmostPos_def, hk]
          exact hj_gt)
      exact (board_push_above s hj_gt).trans hs_empty
  -- By definition of `rightmostPos`, we know that `board (push s k) (k - 1) ≠
  -- .none`.
  have h_rightmost_ge : (‹Strip R›.board (‹Strip R›.push s k)) (k - 1) ≠ .none
  := by
    have := ‹Strip R›.board_push_shift s hpos; aesop
  apply Nat.le_antisymm
  · by_contra hcon
    push Not at hcon
    have hpos_rightmost : 0 < rightmostPos (push s k) := by omega
    have hoccupied : board (push s k) (rightmostPos (push s k)) ≠ .none :=
      Board.board_rightmostPos_ne_none hpos_rightmost
    exact hoccupied (h_rightmost_le _ hcon)
  · exact Board.rightmostPos_greatest h_rightmost_ge

theorem stride_push_below {s : R} (p : Player) {m : ℕ}
    (hm : m < rightmostPos s) :
    stride (push s m) p = stride s p := by
  rw [stride_def, stride_def, Strip.Board.stride, Strip.Board.stride,
      ← rightmostPos_def, ← rightmostPos_def, rightmostPos_push_below hm]
  rw [← board_def, ← board_def, board_push_above s hm]

theorem stride_push_at_rightmost {s : R} (p : Player) {k : ℕ}
    (hk : rightmostPos s = k) (hpos : 0 < k)
    (hp : board s k = .ofPlayer p) :
    stride (push s k) p = k := by
  convert Nat.findGreatest_eq_iff.mpr _
  · convert rfl
    · convert Nat.findGreatest_eq_iff.mpr _
      · exact k
      · exact fun n => n = k
      · infer_instance
      · unfold stride; simp_all +decide only [ne_eq]
        unfold Board.stride; simp_all +decide
        have := ‹Strip R›.board_push_shift s hpos; simp_all +decide
        have h_rightmost : (‹Strip R›.toBoard (‹Strip R›.push s k)).rightmostPos = k - 1 := by
          have := ‹Strip R›.rightmostPos_push_at ( hk := hk ) ( hpos := hpos ) ( by aesop )
          aesop
        lia
  · exact ⟨ le_rfl, fun _ => rfl, fun n hn₁ hn₂ => by omega ⟩

theorem stride_neg_push_at_rightmost {s : R} (p : Player) {k : ℕ}
    (hk : rightmostPos s = k)
    (hp : board s k = .ofPlayer p) (hpos : 0 < k) :
    stride (push s k) (-p) = 0 := by
  unfold stride
  unfold Board.stride; have :=
      ‹Strip R›.rightmostPos_push_at ( hk := hk ) ( hpos := hpos ) ( by aesop ); simp_all +decide
  have := ‹Strip R›.board_push_shift s hpos; simp_all +decide
  cases p <;> simp_all +decide only [rightmostPos, Player.le_left, Player.right_le,
    Player.neg_left, Player.neg_right, Player.le_right_eq, Player.le_left_eq, not_false_eq_true]

theorem push_rightmost_zero_empty {s : R}
    (h0 : rightmostPos s = 0) (n : ℕ) :
    board (push s 0) n = .none := by
  by_cases hn : n = 0
  · rw [hn]
    exact ‹Strip R›.board_push_eq s 0
  · -- Since $n \neq 0$, we have $n > 0$.
    have hn_pos : 0 < n := by
      exact Nat.pos_of_ne_zero hn
    have hs_empty : board s n = .none := by
      rw [board_def]
      exact Board.board_eq_none_of_gt_rightmostPos (by
        rw [← rightmostPos_def, h0]
        exact hn_pos)
    exact (board_push_above s hn_pos).trans hs_empty

theorem stride_neg_zero_of_p_move {s : R} (p : Player) {m : ℕ}
    (hrm : board s (rightmostPos s) = .ofPlayer p)
    (hm : board s m = .ofPlayer p) :
    stride (push s m) (-p) = 0 := by
  have h_rightmost : m ≤ (‹Strip R›.rightmostPos s) := by
    rw [rightmostPos_def]
    refine Board.rightmostPos_greatest ?_
    rw [← board_def, hm]
    exact Piece.ofPlayer_ne_none p
  cases lt_or_eq_of_le h_rightmost <;> simp_all +decide only [board_def]
  · apply Board.stride_neg_eq_zero
    have h_rightmost :
        (‹Strip R›.toBoard (‹Strip R›.push s m)).rightmostPos =
          (‹Strip R›.toBoard s).rightmostPos := by
      rw [← rightmostPos_def, ← rightmostPos_def]
      exact ‹Strip R›.rightmostPos_push_below ‹_›
    rw [h_rightmost, ← rightmostPos_def s]
    have hpush : board (push s m) (rightmostPos s) = Piece.ofPlayer p := by
      exact (board_push_above s ‹m < rightmostPos s›).trans
        ((board_def s (rightmostPos s)).trans hrm)
    exact (board_def (push s m) (rightmostPos s)).symm.trans hpush
  · by_cases hpos : 0 < (‹Strip R›.rightmostPos s)
    · exact ‹Strip R›.stride_neg_push_at_rightmost p (by aesop) (by aesop) hpos
    · have h_empty : ∀ n,
      (‹Strip R›.board (‹Strip R›.push s (‹Strip R›.rightmostPos s))) n = .none := by
        have := ‹Strip R›.push_rightmost_zero_empty (s := s) ( by omega ); aesop
      unfold stride
      simp_all +decide only [Std.le_refl, not_lt, nonpos_iff_eq_zero, board_def]
      unfold Board.stride; simp_all +decide only [Piece.none_ne_ofPlayer, ↓reduceIte]

theorem stride_push_eq_rightmostPos {s : R} (p : Player) {m : ℕ}
    (hm1 : board s m ≠ .none) (hm2 : m = rightmostPos s) :
    stride (push s m) p = stride s p - 1 := by
  have h_rightmost : m = (‹Strip R›.toBoard s).rightmostPos := by
    exact hm2
  by_cases hpos : 0 < (‹Strip R›.toBoard s).rightmostPos <;>
    simp_all +decide only [board_def, ne_eq, not_lt, nonpos_iff_eq_zero, stride]
  · unfold Board.stride; simp_all +decide
    have h_rightmost_push :
        (‹Strip R›.toBoard (‹Strip R›.push s (‹Strip R›.rightmostPos s))).rightmostPos =
          (‹Strip R›.rightmostPos s) - 1 := by
      exact ‹Strip R›.rightmostPos_push_at ( hk := rfl ) ( hpos := hpos ) ( by aesop )
    have h_board_push :
        (‹Strip R›.board (‹Strip R›.push s (‹Strip R›.rightmostPos s))
            (‹Strip R›.rightmostPos s - 1)) =
          (‹Strip R›.board s (‹Strip R›.rightmostPos s)) := by
      exact ‹Strip R›.board_push_shift s hpos
    split_ifs <;> simp_all +decide only [Piece.ofPlayer_ne_none, not_false_eq_true, board_def,
      Nat.sub_add_cancel hpos, add_tsub_cancel_right, not_true_eq_false]
  · have := ‹Strip R›.push_rightmost_zero_empty hpos; simp_all +decide only [board_def]
    unfold Board.stride
    simp_all +decide only [Piece.none_ne_ofPlayer, ↓reduceIte]
    unfold rightmostPos at *; aesop

theorem stride_push_le {s : R} (p : Player) {m : ℕ}
    (hm : board s m ≠ .none) :
    stride (push s m) p ≤ stride s p := by
  obtain h_lt | h_eq | h_gt := Nat.lt_trichotomy m (rightmostPos s)
  · exact Nat.le_of_eq (stride_push_below p h_lt)
  · rw [stride_push_eq_rightmostPos p hm h_eq]
    exact Nat.sub_le (stride s p) 1
  · absurd h_gt
    rw [not_lt]
    exact Board.rightmostPos_greatest (show (toBoard s).board m ≠ Piece.none from hm)

theorem stride_zero_of_push {s : R} {p : Player} {m : ℕ}
    (hs : stride s p = 0) (hm : board s m ≠ .none) :
    stride (push s m) p = 0 := by
  have := stride_push_le p hm
  rw [hs] at this
  exact Nat.le_zero.mp this

theorem push_to_empty_is_neg {s : R} {p : Player} {m : ℕ}
    (hs : stride s p = 0)
    (hm_piece : board s m ≠ .none)
    (h_empty : ∀ n, board (push s m) n = .none) :
    board s m = .ofPlayer (-p) := by
  have h_m_eq : m = rightmostPos s := by
    refine le_antisymm (Board.rightmostPos_greatest hm_piece) ?_
    by_contra h
    rw [not_le] at h
    have hkey : board (push s m) (rightmostPos s) ≠ .none := by
      rw [board_push_above s h]
      have hle : m ≤ (toBoard s).finite_support.choose := by
        have := Board.rightmostPos_greatest hm_piece
        have := Board.rightmostPos_le (toBoard s)
        rw [rightmostPos_def] at h
        omega
      exact Board.rightmostPos_spec (toBoard s) hle hm_piece
    exact hkey (h_empty _)
  rw [h_m_eq] at hm_piece ⊢
  rw [stride_def, Strip.Board.stride, ← rightmostPos_def] at hs
  rw [board_def] at hm_piece ⊢
  cases p <;> cases h : (toBoard s).board (rightmostPos s) <;>
    simp_all +decide only [ne_eq, board_def, Strip.Piece.ofPlayer, reduceCtorEq, ↓reduceIte,
      Nat.add_eq_zero_iff, and_false]

theorem isSolved_of_stride_zero {p : Player} {s : R}
    (hs : stride s p = 0) :
    GameForm.IsSolved p (Strip.toGameForm s) := by
  induction n : weight s using Nat.strong_induction_on generalizing s with
  | h n ih =>
    by_cases h_empty : ∀ n, board s n = .none
    · rw [← toGameForm_zero_iff] at h_empty
      rw [h_empty]
      exact GameForm.isSolved_zero p
    · obtain ⟨k, hk⟩ : ∃ k, board s k = .ofPlayer (-p) ∧ k = rightmostPos s := by
        have h_rightmost : board s (rightmostPos s) ≠ .none := by
          obtain ⟨j, hj⟩ : ∃ j, board s j ≠ .none := not_forall.mp h_empty
          refine Board.rightmostPos_spec (toBoard s) (le_of_not_gt ?_) hj
          intro h
          exact hj ((toBoard s).finite_support.choose_spec j h.le)
        refine ⟨rightmostPos s, ?_, rfl⟩
        rw [stride_def, Strip.Board.stride, ← rightmostPos_def] at hs
        rw [board_def] at h_rightmost ⊢
        cases p <;> cases h : (toBoard s).board (rightmostPos s) <;>
          simp_all +decide only [board_def, not_forall, ne_eq, Strip.Piece.ofPlayer, reduceCtorEq,
            ↓reduceIte, Nat.add_eq_zero_iff, and_false]
      rw [GameForm.isSolved_def]
      refine ⟨?_, ?_, ?_⟩
      · intro h₁
        obtain ⟨m, hm₁, hm₂⟩ := (mem_moves_toGameForm_iff s p 0).mp h₁
        have h_piece_neg : board s m = .ofPlayer (-p) := by
          apply push_to_empty_is_neg hs
          · exact hm₁.symm ▸ (by cases p <;> tauto)
          · exact fun j => by simpa using (toGameForm_zero_iff (push s m)).1 hm₂.symm j
        cases p <;> cases h : board s m <;>
          simp_all +decide only [board_def, not_forall, Player.le_left, Player.right_le,
            Player.neg_left, Player.neg_right, Player.le_right_eq, Player.le_left_eq,
            moves_toGameForm, Set.mem_image]
      · intro h_nonzero
        exact Form.not_isEnd_of_mem_moves (toGameForm_push_mem_moves (-p) hk.1)
      · intro gp hgp
        obtain ⟨q, m, hm⟩ :
            ∃ q m, gp = Strip.toGameForm (push s m) ∧ board s m = .ofPlayer q := by
          obtain ⟨q, ⟨⟨q, rfl⟩, hq⟩⟩ := hgp
          exact Exists.elim ((mem_moves_toGameForm_iff s q gp).1 hq)
            fun m hm => ⟨q, m, hm.2, hm.1⟩
        grind only [Piece.ofPlayer_ne_none, stride_zero_of_push, weight_push_lt]

theorem rightmostPos_greatest {s : R} {k : ℕ} (hk : board s k ≠ .none) :
    k ≤ rightmostPos s :=
  Board.rightmostPos_greatest hk

theorem rightmost_of_stride_pos {p : Player} {s : R} (hs : stride s p ≠ 0) :
    board s (rightmostPos s) = .ofPlayer p ∧ rightmostPos s + 1 = stride s p :=
  Board.rightmost_of_stride_pos hs

theorem neg_push_below_rightmost {s : R} {p : Player} {m : ℕ}
    (hrm : board s (rightmostPos s) = .ofPlayer p)
    (hm : board s m = .ofPlayer (-p)) :
    m < rightmostPos s :=
  Board.neg_push_below_rightmost hrm hm

/--
Every strip position has a stride: `HasStride p (toGameForm s) (stride s p)`.
This is the heart of the shared theory.
-/
theorem toGameForm_hasStride (s : R) (p : Player) :
    GameForm.HasStride p (Strip.toGameForm s) (stride s p) := by
  induction w : weight s using Nat.strong_induction_on generalizing s p with
  | _ w ih =>
  have ih_push : ∀ (m : ℕ) (q : Player), board s m ≠ .none →
      GameForm.HasStride q (Strip.toGameForm (push s m)) (stride (push s m) q) := by
    intro m q hm
    exact ih _ (by rw [← w]; exact weight_push_lt s hm) _ _ rfl
  by_cases hs : stride s p = 0
  · rw [hs]; exact hasStride_eq_zero_iff.mpr (isSolved_of_stride_zero hs)
  · obtain ⟨hrm, hrm_eq⟩ := rightmost_of_stride_pos hs
    set k := rightmostPos s with hk_def
    have hstride_eq : stride s p = k + 1 := by omega
    rw [hstride_eq]
    have hk_ne : board s k ≠ .none := by rw [hrm]; exact Piece.ofPlayer_ne_none p
    rw [GameForm.hasStride_succ_iff]
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro H
      have h_push_k_mem : Strip.toGameForm (push s k) ∈ Form.moves p (Strip.toGameForm s) :=
        toGameForm_push_mem_moves p hrm
      have h_push_k_opt : Form.IsOption (Strip.toGameForm (push s k)) (Strip.toGameForm s) :=
        Form.IsOption.of_mem_moves h_push_k_mem
      have h_push_k_solved := GameForm.isSolved_of_isOption H h_push_k_opt
      by_cases hk_pos : 0 < k
      · have h_stride_k : stride (push s k) p = k := stride_push_at_rightmost p rfl hk_pos hrm
        have h_hs_k := ih_push k p hk_ne
        rw [h_stride_k] at h_hs_k
        have := (GameForm.hasStride_isSolved_iff_zero h_hs_k).mp h_push_k_solved
        omega
      · have hk_zero : (k : ℕ) = 0 := by omega
        have h_empty : ∀ n, board (push s 0) n = .none :=
          push_rightmost_zero_empty (by rw [← hk_def]; exact hk_zero)
        have h_zero : Strip.toGameForm (push s k) = 0 := by
          rw [hk_zero]; exact (toGameForm_zero_iff _).mpr (fun n => h_empty n)
        rw [h_zero] at h_push_k_mem
        exact GameForm.isSolved_zero_not_mem H h_push_k_mem
    · intro g' hg'
      obtain ⟨m, hm_p, rfl⟩ := (mem_moves_toGameForm_iff s p g').mp hg'
      have hm_ne : board s m ≠ .none := by rw [hm_p]; exact Piece.ofPlayer_ne_none p
      have h_stride_ge : k ≤ stride (push s m) p := by
        by_cases hm_lt : m < rightmostPos s
        · rw [stride_push_below p hm_lt, hstride_eq]
          omega
        · have hm_eq : m = rightmostPos s := by
            refine le_antisymm ?_ (Nat.not_lt.mp hm_lt)
            apply rightmostPos_greatest
            rw [hm_p]
            exact Piece.ofPlayer_ne_none p
          have := stride_push_eq_rightmostPos p hm_ne hm_eq
          omega
      exact ⟨stride (push s m) p, h_stride_ge, ih_push m p hm_ne⟩
    · refine ⟨Strip.toGameForm (push s k), toGameForm_push_mem_moves p hrm, ?_, ?_⟩
      · by_cases hk_pos : 0 < k
        · have h_str := stride_push_at_rightmost p rfl hk_pos hrm
          have h_hs := ih_push k p hk_ne
          rwa [h_str] at h_hs
        · have hk_zero : (k : ℕ) = 0 := by omega
          have h_empty : ∀ n, board (push s 0) n = .none :=
            push_rightmost_zero_empty (by rw [← hk_def]; exact hk_zero)
          have h_zero : Strip.toGameForm (push s k) = 0 := by
            rw [hk_zero]; exact (toGameForm_zero_iff _).mpr (fun n => h_empty n)
          rw [h_zero, hk_zero]
          exact hasStride_eq_zero_iff.mpr (GameForm.isSolved_zero p)
      · intro g'' hg'' m_val hm_val
        obtain ⟨m', hm'_p, rfl⟩ := (mem_moves_toGameForm_iff s p g'').mp hg''
        have h_m_zero : m_val = 0 := by
          apply GameForm.hasStride_unique hm_val
          rw [← stride_neg_zero_of_p_move p hrm hm'_p]
          exact ih_push m' (-p) (Piece.ne_none_of_ofPlayer hm'_p)
        subst h_m_zero
        have h_neg_good : stride (push s k) (-p) = 0 := stride_neg_zero_of_p_move p hrm hrm
        exact ⟨0, le_refl _, by rw [← h_neg_good]; exact ih_push k (-p) hk_ne⟩
    · intro g' hg'
      obtain ⟨m, hm_neg, rfl⟩ := (mem_moves_toGameForm_iff s (-p) g').mp hg'
      have hm_lt : m < k := neg_push_below_rightmost hrm hm_neg
      have hm_ne : board s m ≠ .none := by rw [hm_neg]; exact Piece.ofPlayer_ne_none (-p)
      have h_stride_eq : stride (push s m) p = k + 1 := by
        rw [stride_push_below p (by rw [← hk_def]; exact hm_lt), hstride_eq]
      use k + 1
      refine ⟨le_refl _, ?_⟩
      rw [← h_stride_eq]
      exact ih_push m p hm_ne
    · intro hne
      have ⟨g', hg'⟩ := Set.nonempty_iff_ne_empty.mpr hne
      obtain ⟨m, hm_neg, rfl⟩ := (mem_moves_toGameForm_iff s (-p) g').mp hg'
      have hm_lt : m < k := neg_push_below_rightmost hrm hm_neg
      have hm_ne : board s m ≠ .none := by rw [hm_neg]; exact Piece.ofPlayer_ne_none (-p)
      have h_stride_eq : stride (push s m) p = k + 1 := by
        rw [stride_push_below p (by rw [← hk_def]; exact hm_lt), hstride_eq]
      use Strip.toGameForm (push s m)
      use (mem_moves_toGameForm_iff s (-p) _).mpr ⟨m, hm_neg, rfl⟩
      rw [← h_stride_eq]
      exact ih_push m p hm_ne

/-!
### Building the `Strided` structure and the equivalence with `ℤ`
-/

/--
For every player `p` and every `n`, there is a strip position with `p`-stride
`n` and `(-p)`-stride `0`: namely a single piece of colour `p` at position `n -
1`.
-/
theorem mk_with_stride (p : Player) (n : ℕ) :
    ∃ r : R, HasStride p (Strip.toGameForm r) n ∧ HasStride (-p) (Strip.toGameForm r) 0 := by
  rcases n with _ | n
  · have h_empty : ∀ k, board (ofBoard (R := R) Board.zero) k = .none := by
      intro k; rw [board_def, toBoard_ofBoard]; rfl
    refine ⟨ofBoard Board.zero, ?_, ?_⟩
    · rw [(toGameForm_zero_iff _).mpr h_empty]
      exact hasStride_eq_zero_iff.mpr (GameForm.isSolved_zero p)
    · rw [(toGameForm_zero_iff _).mpr h_empty]
      exact hasStride_eq_zero_iff.mpr (GameForm.isSolved_zero (-p))
  · set b : Board :=
      { board := fun m => if m = n then Piece.ofPlayer p else Piece.none,
        finite_support := ⟨n + 1, by
          intro m hm
          show (if m = n then Piece.ofPlayer p else Piece.none) = Piece.none
          rw [if_neg (show m ≠ n by omega)]⟩ }
      with hb_def
    have hbn : b.board n = .ofPlayer p := by rw [hb_def]; simp only [↓reduceIte]
    have hb_other : ∀ m, m ≠ n → b.board m = .none := by
      intro m hm; rw [hb_def]; simp only [if_neg hm]
    have h_rm : b.rightmostPos = n := by
      rw [Board.rightmostPos, Nat.findGreatest_eq_iff]
      refine ⟨?_, ?_, ?_⟩
      · by_contra h; push Not at h
        have := b.finite_support.choose_spec n (le_of_lt h)
        rw [hbn] at this
        exact Piece.ofPlayer_ne_none p this
      · intro _; rw [hbn]; exact Piece.ofPlayer_ne_none p
      · intro j hj _ hcontra; exact hcontra (hb_other j (by omega))
    have h_stride_p : stride (ofBoard (R := R) b) p = n + 1 := by
      rw [stride_def, toBoard_ofBoard, Board.stride, h_rm, hbn]
      simp only [↓reduceIte]
    have h_stride_np : stride (ofBoard (R := R) b) (-p) = 0 := by
      rw [stride_def, toBoard_ofBoard, Board.stride, h_rm, hbn, if_neg]
      intro hcontra
      exact absurd (Piece.ofPlayer_injective hcontra) (by simp only [Player.ne_iff_eq_neg, neg_neg])
    refine ⟨ofBoard b, ?_, ?_⟩
    · rw [← h_stride_p]; exact toGameForm_hasStride (ofBoard b) p
    · rw [← h_stride_np]; exact toGameForm_hasStride (ofBoard b) (-p)

/-- Every `Strip` ruleset is a `Ruleset`, with the shared `toGameForm`. -/
noncomputable instance ruleset (R : Type u) [Strip R] : Ruleset R where
  toGameForm := Strip.toGameForm
  moves_toGameForm p r g' h_g' := by
    rw [moves_toGameForm] at h_g'
    obtain ⟨r', _, rfl⟩ := h_g'
    exact ⟨r', rfl⟩

/--
The `Strided` structure on the additive closure of any `Strip` ruleset.
-/
noncomputable instance strided (R : Type u) [Strip R] :
    Strided (Form.ClosedUnderAdd.closure (Ruleset.Forms R)) where
  mk_with_strides :=
    ClosedUnderAdd.closure_mk_with_strides_aux (fun p n => by
      obtain ⟨r, h1, h2⟩ := mk_with_stride (R := R) p n
      exact ⟨Strip.toGameForm r, Ruleset.Forms.position_mem r, h1, h2⟩)
  has_stride p :=
    ClosedUnderAdd.closure_has_stride_aux p Strip.stride Strip.toGameForm_hasStride

/--
The misère quotient of any `Strip` ruleset is isomorphic to `ℤ`.
-/
protected noncomputable def equivInt (R : Type u) [Strip R] :
    MisereQuotient (Form.ClosedUnderAdd.closure (Ruleset.Forms R)) ≃ ℤ :=
  GameForm.MisereQuotient.stridedEquivInt

protected theorem le_iff_equiv_ge (R : Type u) [Strip R]
    (a b : MisereQuotient (Form.ClosedUnderAdd.closure (Ruleset.Forms R))) :
    a ≤ b ↔
    GameForm.MisereQuotient.stridedEquivInt a ≥ GameForm.MisereQuotient.stridedEquivInt b :=
  GameForm.MisereQuotient.le_iff_equiv_ge a b

end Strip

end

end MisereGames
