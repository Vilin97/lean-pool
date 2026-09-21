/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Kim Morrison, Fox Thomson
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Game.IGame
public meta import LeanPool.ConwayRefinement.CombinatorialGames.Tactic.AddInstances

import Mathlib.Data.Finite.Prod
import Mathlib.Data.Set.Finite.Lattice

/-!
# Classes of games

This file collects multiple basic classes of games, so as to make them available on most files. We
develop their theory elsewhere.

## Dicotic games

A game is dicotic when every non-zero subposition has both left and right moves. The Lawnmower
theorem (proven in `CombinatorialGames.Game.Small`) shows that every dicotic game is small.

## Impartial games

We define an impartial game as one where every subposition is equivalent to its negative. This is a
weaker definition than that found in the literature (which requires equality, rather than
equivalence), but this is still strong enough to prove the Sprague--Grundy theorem, as well as
closure under the basic arithmetic operations of multiplication and division.

## Numeric games

A game is `Numeric` if all the Left options are strictly smaller than all the Right options, and all
those options are themselves numeric. In terms of combinatorial games, the numeric games have
"frozen"; you can only make your position worse by playing, and Left is some definite "number" of
moves ahead (or behind) Right.

## Short games

A combinatorial game is `Short` if it has only finitely many subpositions. In particular, this means
there is a finite set of moves at every point.

We historically defined `Short x` as data, which we then used to enable some degree of computation
on combinatorial games. This functionality is now implemented through the `game_cmp` tactic instead.
-/

universe u

@[expose] public section

namespace IGame

/-! ### Dicotic games -/

/-- A game `x` is dicotic if both players can move from every nonempty subposition of `x`. -/
@[mk_iff dicotic_def']
class inductive Dicotic : IGame → Prop where
  | mk {x : IGame} : (xᴸ = ∅ ↔ xᴿ = ∅) → (∀ p, ∀ y ∈ x.moves p, Dicotic y) → Dicotic x

theorem dicotic_def {x : IGame} : Dicotic x ↔ (xᴸ = ∅ ↔ xᴿ = ∅) ∧ ∀ p, ∀ l ∈ x.moves p, Dicotic l :=
  dicotic_def' x

namespace Dicotic
variable {x y z : IGame}

theorem eq_zero_iff [hx : Dicotic x] : x = 0 ↔ ∃ p, x.moves p = ∅ := by
  rw [dicotic_def] at hx
  simp_all [Player.exists, IGame.ext_iff]

theorem ne_zero_iff [Dicotic x] : x ≠ 0 ↔ ∀ p, x.moves p ≠ ∅ := by
  simpa using eq_zero_iff.not

theorem moves_eq_empty_iff [hx : Dicotic x] : ∀ p q, x.moves p = ∅ ↔ x.moves q = ∅ :=
  Player.const_of_left_eq_right' (dicotic_def.1 hx).1

protected theorem of_mem_moves {p : Player} [hx : Dicotic x] (h : y ∈ x.moves p) : Dicotic y :=
  (dicotic_def.1 hx).2 p y h

/-- `dicotic` eagerly adds all possible `Dicotic` hypotheses. -/
elab "dicotic" : tactic =>
  addInstances <| .mk [`IGame.Dicotic.of_mem_moves]

@[simp]
protected instance zero : Dicotic 0 := by
  apply mk <;> simp

protected instance neg (x) [Dicotic x] : Dicotic (-x) := by
  apply mk
  · simp [moves_eq_empty_iff .left .right]
  · simp_rw [moves_neg, Set.mem_neg]
    intro p y hy
    dicotic
    rw [← neg_neg y]
    exact .neg _
termination_by x
decreasing_by igame_wf

@[simp]
theorem neg_iff {x : IGame} : Dicotic (-x) ↔ Dicotic x :=
  ⟨fun _ ↦ by simpa using Dicotic.neg (-x), fun _ ↦ .neg x⟩

end Dicotic

/-! ### Impartial games -/

/-- An impartial game is one that's equivalent to its negative, such that each left and right move
is also impartial.

Note that this is a slightly more general definition than the one that's usually in the literature,
as we don't require `x = -x`. Despite this, the Sprague-Grundy theorem still holds: see
`IGame.equiv_nim_grundyValue`.

In such a game, both players have the same payoffs at any subposition. -/
@[mk_iff impartial_def']
class inductive Impartial : IGame → Prop where
  | mk {x : IGame} : -x ≈ x → (∀ p, ∀ y ∈ x.moves p, Impartial y) → Impartial x

theorem impartial_def {x : IGame} : x.Impartial ↔ -x ≈ x ∧ ∀ p, ∀ y ∈ x.moves p, Impartial y :=
  impartial_def' x

namespace Impartial
variable (x y : IGame) [hx : Impartial x] [hy : Impartial y]

@[simp] theorem neg_equiv : -x ≈ x := (impartial_def.1 hx).1
@[simp] theorem equiv_neg : x ≈ -x := (neg_equiv _).symm

omit hx in
theorem sub_equiv : x - y ≈ x + y := add_congr_right (neg_equiv y)

@[aesop unsafe 50% apply]
protected theorem of_mem_moves {p} {x y : IGame} [h : Impartial x] :
    y ∈ x.moves p → Impartial y :=
  (impartial_def.1 h).2 p y

/-- `impartial` eagerly adds all possible `Impartial` hypotheses. -/
elab "impartial" : tactic =>
  addInstances <| .mk [`IGame.Impartial.of_mem_moves]

@[simp] protected instance zero : Impartial 0 := by rw [impartial_def]; simp

protected instance neg (x : IGame) [Impartial x] : Impartial (-x) := by
  apply mk
  · simp
  · simp_rw [moves_neg, Set.mem_neg]
    intro p y hy
    impartial
    rw [← neg_neg y]
    exact .neg _
termination_by x
decreasing_by igame_wf

protected instance add (x y : IGame) [Impartial x] [Impartial y] : Impartial (x + y) := by
  apply mk
  · rw [neg_add]
    exact add_congr (neg_equiv x) (neg_equiv y)
  · simp_rw [forall_moves_add]
    intro p
    constructor
    all_goals intro z hz; impartial; exact .add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Impartial x] [Impartial y] : Impartial (x - y) :=
  .add x (-y)

/-- The product instance is proven in `Game.Impartial.Grundy`. -/
theorem le_comm {x y} [Impartial x] [Impartial y] : x ≤ y ↔ y ≤ x := by
  rw [← IGame.neg_le_neg_iff, (neg_equiv y).le_congr (neg_equiv x)]

@[simp]
theorem not_lt : ¬x < y := by
  apply (lt_asymm · ?_)
  rwa [← IGame.neg_lt_neg_iff, (neg_equiv x).lt_congr (neg_equiv y)]

/-- By setting `y = 0`, we find that in an impartial game, either the first player always wins, or
the second player always wins. -/
theorem equiv_or_fuzzy : x ≈ y ∨ x ‖ y := by
  obtain (h | h | h | h) := lt_or_antisymmRel_or_gt_or_incompRel x y
  · cases not_lt x y h
  · exact .inl h
  · cases not_lt y x h
  · exact .inr h

variable {x y}

@[simp]
theorem not_equiv_iff : ¬ x ≈ y ↔ x ‖ y :=
   ⟨(equiv_or_fuzzy x y).resolve_left, IncompRel.not_antisymmRel⟩

@[simp]
theorem not_fuzzy_iff : ¬ x ‖ y ↔ x ≈ y :=
  not_iff_comm.1 not_equiv_iff

@[simp]
theorem le_iff_equiv : x ≤ y ↔ x ≈ y :=
  ⟨fun h ↦ ⟨h, le_comm.1 h⟩, And.left⟩

theorem ge_iff_equiv : y ≤ x ↔ x ≈ y :=
  ⟨fun h ↦ ⟨le_comm.2 h, h⟩, And.right⟩

theorem lf_iff_fuzzy : x ⧏ y ↔ x ‖ y := by simp [comm]
theorem gf_iff_fuzzy : y ⧏ x ↔ x ‖ y := by simp

theorem fuzzy_of_mem_moves {y : IGame} {p : Player} (hy : y ∈ x.moves p) : y ‖ x := by
  have := hx.of_mem_moves hy
  cases p with
  | left => symm; simpa using left_lf hy
  | right => simpa using lf_right hy

private theorem equiv_iff_forall_fuzzy' :
    x ≈ y ↔ (∀ z ∈ xᴸ, z ‖ y) ∧ (∀ z ∈ yᴿ, x ‖ z) := by
  rw [← le_iff_equiv, le_iff_forall_lf]
  congr! with z hz z hz
  all_goals impartial; simp [incompRel_comm]

theorem equiv_iff_forall_fuzzy (p : Player) :
    x ≈ y ↔ (∀ z ∈ x.moves p, z ‖ y) ∧ (∀ z ∈ y.moves (-p), x ‖ z) := by
  cases p with
  | left => exact equiv_iff_forall_fuzzy'
  | right =>
    rw [antisymmRel_comm, equiv_iff_forall_fuzzy', and_comm]
    simp_rw [incompRel_comm]
    rfl

theorem fuzzy_iff_exists_equiv (p : Player) :
    x ‖ y ↔ (∃ z ∈ x.moves p, z ≈ y) ∨ (∃ z ∈ y.moves (-p), x ≈ z) := by
  rw [← not_equiv_iff, equiv_iff_forall_fuzzy p, not_and_or]
  simp_rw [not_forall, ← exists_prop]
  congr! with _ h _ h
  all_goals impartial; exact not_fuzzy_iff

theorem equiv_zero (p : Player) : x ≈ 0 ↔ ∀ y ∈ x.moves p, y ‖ 0 := by
  rw [equiv_iff_forall_fuzzy p]; simp

theorem fuzzy_zero (p : Player) : x ‖ 0 ↔ ∃ y ∈ x.moves p, y ≈ 0 := by
  rw [fuzzy_iff_exists_equiv p]; simp

/-- A **strategy stealing** argument. If there's a move in `x`, such that any immediate move could
have also been reached in the first turn, then `x` is won by the first player. -/
theorem fuzzy_zero_of_forall_exists {p : Player} {y} (hy : y ∈ x.moves p)
    (H : ∀ z ∈ y.moves p, ∃ w ∈ x.moves p, z ≈ w) : x ‖ 0 := by
  apply (equiv_or_fuzzy _ _).resolve_left fun hx ↦ ?_
  impartial
  rw [equiv_zero] at hx
  obtain ⟨z, hz, hz'⟩ := (fuzzy_zero _).1 (hx y hy)
  obtain ⟨w, hw, hw'⟩ := H z hz
  exact (hx w hw).not_antisymmRel (hw'.symm.trans hz')

end Impartial

/-! ### Numeric games -/

/-- A game `!{s | t}` is numeric if everything in `s` is less than everything in `t`, and all the
elements of these sets are also numeric.

The `Surreal` numbers are built as the quotient of numeric games under equivalence. -/
@[mk_iff numeric_def']
class inductive Numeric : IGame → Prop where
  | mk {x : IGame} : (∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y < z) → (∀ p, ∀ y ∈ x.moves p, Numeric y) → Numeric x

theorem numeric_def {x : IGame} : Numeric x ↔
    (∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y < z) ∧ (∀ p, ∀ y ∈ x.moves p, Numeric y) :=
  numeric_def' x

namespace Numeric
variable {x y z : IGame}

theorem left_lt_right [h : Numeric x] (hy : y ∈ xᴸ) (hz : z ∈ xᴿ) : y < z :=
  (numeric_def.1 h).1 y hy z hz

protected theorem of_mem_moves {p : Player} [h : Numeric x] (hy : y ∈ x.moves p) : Numeric y :=
  (numeric_def.1 h).2 p y hy

/-- `numeric` eagerly adds all possible `Numeric` hypotheses. -/
elab "numeric" : tactic =>
  addInstances <| .mk [`IGame.Numeric.of_mem_moves]

protected theorem subposition [Numeric x] (h : Subposition y x) : Numeric y := by
  induction x using IGame.moveRecOn generalizing ‹x.Numeric› with | ind x ih
  obtain ⟨p, z, hz, hy⟩ := subposition_iff_exists.1 h
  obtain rfl | hy := wsubposition_iff_eq_or_subposition.1 hy
  · exact .of_mem_moves hz
  · exact @ih p z hz (.of_mem_moves hz) hy

@[simp]
protected instance zero : Numeric 0 := by
  rw [numeric_def]; simp

@[simp]
protected instance one : Numeric 1 := by
  rw [numeric_def]; simp

protected instance subtype (x : Subtype Numeric) : Numeric x.1 := x.2
protected instance moves {x : IGame} [Numeric x] {p : Player} (y : x.moves p) : Numeric y :=
  .of_mem_moves y.2

protected theorem le_of_not_le {x y : IGame} [Numeric x] [Numeric y] : ¬ x ≤ y → y ≤ x := by
  rw [lf_iff_exists_le, le_iff_forall_lf]
  rintro (⟨z, hz, h⟩ | ⟨z, hz, h⟩) <;> constructor <;> intro a ha h'
  · numeric
    exact left_lf_of_le h' hz (Numeric.le_of_not_le (left_lf_of_le h ha))
  · exact (left_lt_right hz ha).not_ge (h'.trans h)
  · exact (left_lt_right ha hz).not_ge (h.trans h')
  · numeric
    exact lf_right_of_le h' hz (Numeric.le_of_not_le (lf_right_of_le h ha))
termination_by x
decreasing_by igame_wf

protected theorem le_total (x y : IGame) [Numeric x] [Numeric y] : x ≤ y ∨ y ≤ x := by
  rw [or_iff_not_imp_left]
  exact Numeric.le_of_not_le

protected theorem lt_of_not_ge [Numeric x] [Numeric y] (h : ¬ x ≤ y) : y < x :=
  (Numeric.le_of_not_le h).lt_of_not_ge h

@[simp]
protected theorem not_le [Numeric x] [Numeric y] : ¬ x ≤ y ↔ y < x :=
  ⟨Numeric.lt_of_not_ge, not_le_of_gt⟩

@[simp]
protected theorem not_lt [Numeric x] [Numeric y] : ¬ x < y ↔ y ≤ x :=
  not_iff_comm.1 Numeric.not_le

protected theorem le_or_gt (x y : IGame) [Numeric x] [Numeric y] : x ≤ y ∨ y < x := by
  rw [← Numeric.not_le]
  exact em _

protected theorem lt_or_ge (x y : IGame) [Numeric x] [Numeric y] : x < y ∨ y ≤ x := by
  rw [← Numeric.not_lt]
  exact em _

theorem not_fuzzy (x y : IGame) [Numeric x] [Numeric y] : ¬ x ‖ y := by
  simpa [not_incompRel_iff_symmGen, Relation.SymmGen] using Numeric.le_total x y

theorem lt_or_equiv_or_gt (x y : IGame) [Numeric x] [Numeric y] : x < y ∨ x ≈ y ∨ y < x := by
  simp_rw [← Numeric.not_le]; tauto

/-- To prove a game is numeric, it suffices to show the left options are less or fuzzy
to the right options. -/
theorem mk_of_lf (h₁ : ∀ y ∈ xᴸ, ∀ z ∈ xᴿ, y ⧏ z) (h₂ : ∀ p, ∀ y ∈ x.moves p, Numeric y) :
    Numeric x :=
  mk (fun y hy z hz ↦ (@Numeric.not_le z y (h₂ _ z hz) (h₂ _ y hy)).1 (h₁ y hy z hz)) h₂

theorem le_iff_forall_lt [Numeric x] [Numeric y] :
    x ≤ y ↔ (∀ z ∈ xᴸ, z < y) ∧ (∀ z ∈ yᴿ, x < z) := by
  rw [le_iff_forall_lf]
  congr! with z hz z hz <;> numeric <;> rw [Numeric.not_le]

theorem lt_iff_exists_le [Numeric x] [Numeric y] :
    x < y ↔ (∃ z ∈ yᴸ, x ≤ z) ∨ (∃ z ∈ xᴿ, z ≤ y) := by
  rw [← Numeric.not_le, lf_iff_exists_le]

theorem left_lt [Numeric x] (h : y ∈ xᴸ) : y < x := by
  numeric; simpa using left_lf h

theorem lt_right [Numeric x] (h : y ∈ xᴿ) : x < y := by
  numeric; simpa using lf_right h

protected instance neg (x : IGame) [Numeric x] : Numeric (-x) := by
  refine mk (fun y hy z hz ↦ ?_) ?_
  · rw [← IGame.neg_lt_neg_iff]
    apply @left_lt_right x <;> simp_all
  · simp_rw [forall_moves_neg]
    intro p y hy
    numeric
    simpa using Numeric.neg y
termination_by x
decreasing_by igame_wf

@[simp]
theorem neg_iff {x : IGame} : Numeric (-x) ↔ Numeric x :=
  ⟨fun _ ↦ by simpa using Numeric.neg (-x), fun _ ↦ Numeric.neg x⟩

protected instance add (x y : IGame) [Numeric x] [Numeric y] : Numeric (x + y) := by
  apply mk <;> simp only [moves_add, Set.mem_union, Set.mem_image]
  · rintro _ (⟨a, ha, rfl⟩ | ⟨a, ha, rfl⟩) _ (⟨b, hb, rfl⟩ | ⟨b, hb, rfl⟩)
    any_goals simpa using left_lt_right ha hb
    all_goals
      trans (x + y)
      · simpa using left_lt ha
      · simpa using lt_right hb
  · rintro p _ (⟨z, hz, rfl⟩ | ⟨z, hz, rfl⟩)
    all_goals numeric; exact Numeric.add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Numeric x] [Numeric y] : Numeric (x - y) :=
  inferInstanceAs (Numeric (x + -y))

protected instance natCast : ∀ n : ℕ, Numeric n
  | 0 => inferInstanceAs (Numeric 0)
  | n + 1 => have := Numeric.natCast n; inferInstanceAs (Numeric (n + 1))

protected instance ofNat (n : ℕ) [n.AtLeastTwo] : Numeric ofNat(n) :=
  inferInstanceAs (Numeric n)

protected instance intCast : ∀ n : ℤ, Numeric n
  | .ofNat n => inferInstanceAs (Numeric n)
  | .negSucc n => inferInstanceAs (Numeric (-(n + 1)))

end Numeric

/-! ### Short games -/

/-- A short game is one with finitely many subpositions. That is, the left and right sets are
finite, and all of the games in them are short as well. -/
@[mk_iff short_def']
class inductive Short : IGame → Prop where
  | mk' (x : IGame) : (∀ p, (x.moves p).Finite) → (∀ p, ∀ y ∈ x.moves p, Short y) → Short x

theorem short_def {x : IGame} : Short x ↔ ∀ p, (x.moves p).Finite ∧ ∀ y ∈ x.moves p, Short y := by
  rw [short_def', ← forall_and]

alias ⟨_, Short.mk⟩ := short_def

namespace Short
variable {x y : IGame}

theorem finite_moves (p : Player) (x : IGame) [h : Short x] : (x.moves p).Finite :=
  (short_def.1 h p).1

instance (p : Player) (x : IGame) [Short x] : Finite (x.moves p) :=
  (Short.finite_moves _ x).to_subtype

protected theorem of_mem_moves [h : Short x] {p} (hy : y ∈ x.moves p) : Short y :=
  (short_def.1 h p).2 y hy

/-- `short` eagerly adds all possible `Short` hypotheses. -/
elab "short" : tactic =>
  addInstances <| .mk [`IGame.Short.of_mem_moves]

protected theorem subposition {x : IGame} [Short x] (h : Subposition y x) : Short y := by
  induction x using IGame.moveRecOn generalizing ‹x.Short› with | ind x ih
  obtain ⟨p, z, hz, hy⟩ := subposition_iff_exists.1 h
  obtain rfl | hy := wsubposition_iff_eq_or_subposition.1 hy
  · exact .of_mem_moves hz
  · exact @ih p z hz (.of_mem_moves hz) hy

theorem finite_setOf_subposition (x : IGame) [Short x] : {y | Subposition y x}.Finite := by
  induction x using IGame.moveRecOn generalizing ‹x.Short› with | ind x ih
  convert Set.finite_iUnion fun p => (finite_moves p x).biUnion fun y hy ↦
    (@ih p y hy (.of_mem_moves hy)).insert y
  ext
  rw [Set.mem_setOf, subposition_iff_exists]
  simp [wsubposition_iff_eq_or_subposition]

instance (x : IGame) [Short x] : Finite {y // Subposition y x} :=
  (Short.finite_setOf_subposition x).to_subtype

theorem _root_.IGame.short_iff_finite_setOf_subposition {x : IGame} :
    Short x ↔ {y | Subposition y x}.Finite := by
  refine ⟨@finite_setOf_subposition x, fun h ↦ mk fun p ↦ ⟨?_, ?_⟩⟩
  on_goal 1 => refine h.subset fun y hy ↦ ?_
  on_goal 2 => refine fun y hy ↦ short_iff_finite_setOf_subposition.2 <| h.subset fun z hz ↦ ?_
  all_goals igame_wf
termination_by x
decreasing_by igame_wf

@[simp]
protected instance zero : Short 0 := by
  rw [short_def]; simp

@[simp]
protected instance one : Short 1 := by
  rw [short_def]; simp

protected instance neg (x : IGame) [Short x] : Short (-x) := by
  refine mk fun p ↦ ⟨?_, ?_⟩
  · simpa [← Set.image_neg_eq_neg] using (finite_moves _ x).image _
  · rw [forall_moves_neg]
    intro y hy
    simpa using (Short.of_mem_moves hy).neg
termination_by x
decreasing_by igame_wf

@[simp]
theorem neg_iff {x : IGame} : Short (-x) ↔ Short x :=
  ⟨fun _ ↦ by simpa using Short.neg (-x), fun _ ↦ Short.neg x⟩

protected instance add (x y : IGame) [Short x] [Short y] : Short (x + y) := by
  refine mk fun p ↦ ⟨?_, ?_⟩
  · simpa using ⟨(finite_moves _ x).image _, (finite_moves _ y).image _⟩
  · rw [forall_moves_add]
    constructor
    all_goals intro z hz; short; exact Short.add ..
termination_by (x, y)
decreasing_by igame_wf

protected instance sub (x y : IGame) [Short x] [Short y] : Short (x - y) :=
  .add ..

protected instance natCast : ∀ n : ℕ, Short n
  | 0 => inferInstanceAs (Short 0)
  | n + 1 => have := Short.natCast n; inferInstanceAs (Short (n + 1))

protected instance ofNat (n : ℕ) [n.AtLeastTwo] : Short ofNat(n) :=
  inferInstanceAs (Short n)

protected instance intCast : ∀ n : ℤ, Short n
  | .ofNat n => inferInstanceAs (Short n)
  | .negSucc n => inferInstanceAs (Short (-(n + 1)))

protected instance mul (x y : IGame) [Short x] [Short y] : Short (x * y) := by
  refine mk fun p ↦ ⟨?_, ?_⟩
  · simpa [Set.image_union] using
      ⟨(finite_moves _ x).image2 _ (finite_moves _ y),
        (finite_moves _ x).image2 _ (finite_moves _ y)⟩
  · rw [forall_moves_mul]
    intro p' a ha b hb
    replace ha := Short.of_mem_moves ha
    replace hb := Short.of_mem_moves hb
    have := Short.mul a y; have := Short.mul x b; have := Short.mul a b
    rw [mulOption]
    infer_instance
termination_by (x, y)
decreasing_by igame_wf

protected instance mulOption (x y a b : IGame) [Short x] [Short y] [Short a] [Short b] :
    Short (mulOption x y a b) :=
  .sub ..

end Short
end IGame
