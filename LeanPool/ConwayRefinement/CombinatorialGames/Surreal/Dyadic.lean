/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Game.Classes
public import LeanPool.ConwayRefinement.CombinatorialGames.Mathlib.Dyadic
public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Division

import Mathlib.Data.Finset.DenselyOrdered

/-!
# Dyadic games

A combinatorial game that is both `Short` and `Numeric` is called dyadic. We show that the dyadic
games are in correspondence with the `Dyadic` rationals, in the sense that there exists a map
`Dyadic.toIGame` such that:

- `Dyadic.toIGame x` is always a dyadic game.
- For any dyadic game `y`, there exists `x` with `Dyadic.toIGame x ≈ y`.
- The game `Dyadic.toGame x` is equivalent to the `RatCast` of `x`.

## Future projects

Since dyadic rationals are easy to do computations with, there are some projects we could pursue in
the future:

- Define the birthday of a dyadic number computably, prove that `x.birthday = x.toIGame.birthday`.
- Define the simplest dyadic number between two others computably, use that to define
  `IGame.toDyadic`.
-/

universe u
open IGame

@[expose] public section

namespace Dyadic

/-! ### Upper and lower dyadic fractions -/

/-- For a dyadic number `m / n`, returns `(m - 1) / n`. -/
def lower (x : Dyadic) : Dyadic :=
  .mkRat (x.num - 1) x.den_mem_powers

/-- For a dyadic number `m / n`, returns `(m + 1) / n`. -/
def upper (x : Dyadic) : Dyadic :=
  .mkRat (x.num + 1) x.den_mem_powers

theorem den_lower_lt {x : Dyadic} (h : x.den ≠ 1) : (lower x).den < x.den := by
  rw [den, lower, coe_mkRat]
  exact den_mkRat_lt ((odd_num h).sub_odd odd_one).two_dvd h

theorem den_upper_lt {x : Dyadic} (h : x.den ≠ 1) : (upper x).den < x.den := by
  rw [den, upper, coe_mkRat]
  exact den_mkRat_lt ((odd_num h).add_odd odd_one).two_dvd h

/-- An auxiliary tactic for inducting on the denominator of a `Dyadic`. -/
macro "dyadic_wf" : tactic =>
  `(tactic| all_goals first | solve_by_elim
    [Prod.Lex.left, Prod.Lex.right, den_lower_lt, den_upper_lt] | decreasing_tactic)

@[simp]
theorem lower_neg (x : Dyadic) : lower (-x) = -upper x := by
  unfold lower upper
  ext
  simp [Rat.neg_mkRat, ← sub_eq_neg_add]

@[simp]
theorem upper_neg (x : Dyadic) : upper (-x) = -lower x := by
  unfold lower upper
  ext
  simp [Rat.neg_mkRat, ← sub_eq_neg_add]

theorem le_lower_of_lt {x y : Dyadic} (hd : x.den ≤ y.den) (h : x < y) : x ≤ y.lower := by
  obtain ⟨m, rfl⟩ := eq_mkRat_of_den_le hd y.den_mem_powers
  conv_rhs at h => rw [← y.mkRat_self]
  rw [mkRat_lt_mkRat] at h
  rwa [lower, mkRat_le_mkRat, Int.le_sub_one_iff]

theorem upper_le_of_lt {x y : Dyadic} (hd : y.den ≤ x.den) (h : x < y) : x.upper ≤ y := by
  have hd' : (-y).den ≤ (-x).den := by simpa using hd
  simpa using le_lower_of_lt hd' (neg_lt_neg h)

theorem lower_eq_of_den_eq_one {x : Dyadic} (h : x.den = 1) : lower x = x.num - 1 := by
  simp [lower, h]

theorem upper_eq_of_den_eq_one {x : Dyadic} (h : x.den = 1) : upper x = x.num + 1 := by
  simp [upper, h]

@[simp]
theorem lower_lt (x : Dyadic) : lower x < x := by
  conv_rhs => rw [← x.mkRat_self]
  rw [lower, mkRat_lt_mkRat]
  exact sub_one_lt x.num

@[simp]
theorem lt_upper (x : Dyadic) : x < upper x := by
  simpa using lower_lt (-x)

theorem lower_lt_upper (x : Dyadic) : lower x < upper x :=
  (lower_lt x).trans (lt_upper x)

theorem coe_lower (x : Dyadic) : lower x = x - (x.den : ℚ)⁻¹ := by
  simp [lower, Rat.mkRat_eq_div, sub_div, Rat.num_div_den]

theorem coe_upper (x : Dyadic) : upper x = x + (x.den : ℚ)⁻¹ := by
  simp [upper, Rat.mkRat_eq_div, add_div, Rat.num_div_den]

theorem lower_add_le_of_den_le {x y : Dyadic} (h : x.den ≤ y.den) :
    lower (x + y) ≤ x + lower y := by
  rw [← Dyadic.coe_le_coe]
  suffices (y.den : ℚ)⁻¹ ≤ ((x + y).den : ℚ)⁻¹ by simpa [coe_lower, Rat.add_assoc, sub_eq_add_neg]
  rw [inv_le_inv₀ (mod_cast y.den_pos) (mod_cast den_pos _)]
  exact_mod_cast den_add_le_den_right h

theorem lower_add_le_of_den_ge {x y : Dyadic} (h : y.den ≤ x.den) :
    lower (x + y) ≤ lower x + y := by
  simpa [add_comm] using lower_add_le_of_den_le h

theorem le_upper_add_of_den_le {x y : Dyadic} (h : x.den ≤ y.den) :
    x + upper y ≤ upper (x + y) := by
  simpa only [← neg_add, lower_neg, neg_le_neg_iff] using
    @lower_add_le_of_den_le (-x) (-y) (by simpa using h)

theorem le_upper_add_of_den_ge {x y : Dyadic} (h : y.den ≤ x.den) :
    upper x + y ≤ upper (x + y) := by
  simpa [add_comm] using le_upper_add_of_den_le h

/-! ### Dyadic numbers to games -/

/-- Converts a dyadic rational into an `IGame`. This map is defined so that:

* If `x : ℤ`, then `toIGame x = ↑x`.
* Otherwise, if `x = m / n` with `n` even, then `toIGame x = !{(m - 1) / n | (m + 1) / n}`. Note
  that both options will have smaller denominators. -/
@[coe]
noncomputable def toIGame (x : Dyadic) : IGame :=
  if _ : x.den = 1 then x.num else !{{toIGame (lower x)} | {toIGame (upper x)}}
termination_by x.den
decreasing_by dyadic_wf

noncomputable instance : Coe Dyadic IGame := ⟨toIGame⟩

theorem toIGame_of_den_eq_one {x : Dyadic} (hx : x.den = 1) : (x : IGame) = x.num := by
  rw [toIGame, dite_eq_left hx]

@[simp] theorem toIGame_intCast (n : ℤ) : ((n : Dyadic) : IGame) = n := by
  simpa using toIGame_of_den_eq_one (Dyadic.den_intCast n)
@[simp] theorem toIGame_natCast (n : ℕ) : ((n : Dyadic) : IGame) = n := toIGame_intCast n

@[simp] theorem toIGame_zero : ((0 : Dyadic) : IGame) = 0 := toIGame_natCast 0
@[simp] theorem toIGame_one :  ((1 : Dyadic) : IGame) = 1 := by simpa using toIGame_natCast 1

theorem toIGame_of_den_ne_one {x : Dyadic} (hx : x.den ≠ 1) :
    x = !{{(lower x : IGame)} | {(upper x : IGame)}} :=
  by rw [toIGame, dite_eq_right hx]

@[simp]
theorem toIGame_half : half = ½ := by
  rw [toIGame_of_den_ne_one (by decide)]
  suffices uh : upper half = 1 by
    rw [show lower half = 0 from rfl, uh]; ext p; cases p <;> simp
  rw [← Dyadic.coe_inj, upper, Dyadic.coe_mkRat]
  rfl

@[simp]
theorem toIGame_neg (x : Dyadic) : (-x : Dyadic) = -(x : IGame) := by
  unfold toIGame
  rw [den_neg]
  split_ifs with h
  · simp
  · simpa using ⟨toIGame_neg _, toIGame_neg _⟩
termination_by x.den
decreasing_by dyadic_wf

theorem eq_lower_of_mem_leftMoves_toIGame {x : Dyadic} {y : IGame} (h : y ∈ xᴸ) :
    y = lower x := by
  by_cases hx : x.den = 1
  · rw [toIGame_of_den_eq_one hx] at h
    rw [lower_eq_of_den_eq_one hx, eq_sub_one_of_mem_leftMoves_intCast h,
      ← Int.cast_one (R := Dyadic), ← Int.cast_sub, toIGame_intCast]
  · simpa [toIGame_of_den_ne_one hx] using h

theorem eq_upper_of_mem_rightMoves_toIGame {x : Dyadic} {y : IGame} (h : y ∈ xᴿ) :
    y = upper x := by
  have : -y ∈ (-x : Dyadic)ᴸ := by simpa
  simpa using eq_lower_of_mem_leftMoves_toIGame this

/-- A dyadic number `x` is always equivalent to `!{lower x | upper x}`, though this may not
necessarily be the canonical form. -/
theorem toIGame_equiv_lower_upper (x : Dyadic) :
    (x : IGame) ≈ !{{(lower x : IGame)} | {(upper x : IGame)}} := by
  rw [toIGame]
  split_ifs with h
  · unfold lower upper
    simp only [h, mkRat_one, toIGame_intCast]
    apply Fits.equiv_of_forall_moves
    · simp [Fits]
    · intro m hm
      obtain ⟨m, hm', rfl⟩ := eq_sub_one_of_mem_leftMoves_intCast hm
      simp
    · intro m hm
      obtain ⟨m, hm', rfl⟩ := eq_add_one_of_mem_rightMoves_intCast hm
      simp
  · rfl

instance _root_.IGame.Short.dyadic (x : Dyadic) : Short x := by
  rw [toIGame]
  split_ifs with h
  · exact .intCast _
  · rw [short_def]
    simpa using ⟨.dyadic _, .dyadic _⟩
termination_by x.den
decreasing_by dyadic_wf

private theorem numeric_lower (x : Dyadic) [hx : Numeric (x : IGame.{u})] :
    Numeric (lower x : IGame.{u}) := by
  by_cases h : x.den = 1
  · rw [lower_eq_of_den_eq_one h, ← Int.cast_one, ← Int.cast_sub, toIGame_intCast]
    infer_instance
  · apply hx.of_mem_moves (p := left)
    simp [toIGame_of_den_ne_one h]

private theorem numeric_upper (x : Dyadic) [hx : Numeric (x : IGame.{u})] :
    Numeric (toIGame.{u} (upper x)) := by
  have : Numeric (-x : Dyadic) := by simpa
  simpa using numeric_lower (-x)

private theorem lower_lt_aux (x : Dyadic) [hx : Numeric (x : IGame.{u})] :
    (lower x : IGame.{u}) < x := by
  by_cases h : x.den = 1
  · rw [lower_eq_of_den_eq_one h, ← Int.cast_one, ← Int.cast_sub, toIGame_intCast,
      toIGame_of_den_eq_one h]
    simp
  · apply hx.left_lt
    simp [toIGame_of_den_ne_one h]

private theorem lt_upper_aux (x : Dyadic) [hx : Numeric (x : IGame.{u})] :
    x < (upper x : IGame.{u}) := by
  have : Numeric (-x : Dyadic) := by simpa
  simpa using lower_lt_aux (-x)

private theorem toIGame_lt_toIGame_aux {x y : Dyadic}
    [Numeric (x : IGame.{u})] [Numeric (toIGame.{u} y)] (h : x < y) : (x : IGame.{u}) < y := by
  by_cases H : x.den = 1 ∧ y.den = 1
  · rwa [toIGame_of_den_eq_one H.1, toIGame_of_den_eq_one H.2, intCast_lt,
      ← Int.cast_lt (R := Dyadic), intCast_num_eq_self_of_den_eq_one H.1,
      intCast_num_eq_self_of_den_eq_one H.2]
  · obtain hd | hd := le_total x.den y.den
    · have := numeric_lower y
      have hy := lower_lt_aux y
      by_cases hy' : y.den = 1
      · rw [hy', den_le_one_iff_eq_one] at hd
        exact (H ⟨hd, hy'⟩).elim
      · exact (le_of_le_of_lt_of_lt toIGame_lt_toIGame_aux (le_lower_of_lt hd h)).trans_lt hy
    · have := numeric_upper x
      have hx := lt_upper_aux x
      by_cases hx' : x.den = 1
      · rw [hx', den_le_one_iff_eq_one] at hd
        exact (H ⟨hx', hd⟩).elim
      · exact hx.trans_le (le_of_le_of_lt_of_lt toIGame_lt_toIGame_aux (upper_le_of_lt hd h))
termination_by (x.den, y.den)
decreasing_by dyadic_wf

instance _root_.IGame.Numeric.dyadic (x : Dyadic) : Numeric x := by
  by_cases h : x.den = 1
  · rw [toIGame_of_den_eq_one h]
    infer_instance
  · rw [numeric_def, toIGame_of_den_ne_one h]
    have := IGame.Numeric.dyadic (lower x)
    have := IGame.Numeric.dyadic (upper x)
    have := toIGame_lt_toIGame_aux (lower_lt_upper x)
    simp_all
termination_by x.den
decreasing_by dyadic_wf

/-- `Dyadic.toIGame` as an `OrderEmbedding`. -/
@[simps!]
noncomputable def toIGameEmbedding : Dyadic ↪o IGame :=
  .ofStrictMono toIGame fun _ _ ↦ by exact toIGame_lt_toIGame_aux

@[simp, norm_cast]
theorem toIGame_le_toIGame {x y : Dyadic} : (x : IGame) ≤ y ↔ x ≤ y :=
  toIGameEmbedding.le_iff_le

@[simp, norm_cast]
theorem toIGame_lt_toIGame {x y : Dyadic} : (x : IGame) < y ↔ x < y :=
  toIGameEmbedding.lt_iff_lt

@[simp, norm_cast]
theorem toIGame_equiv_toIGame {x y : Dyadic} :  (x : IGame) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp, norm_cast]
theorem toIGame_inj {x y : Dyadic} : (x : IGame) = y ↔ x = y :=
  toIGameEmbedding.inj

theorem toIGame_add_equiv (x y : Dyadic) : ((x + y : Dyadic) : IGame.{u}) ≈ x + y := by
  by_cases H : x.den = 1 ∧ y.den = 1
  · rw [← intCast_num_eq_self_of_den_eq_one H.1, ← intCast_num_eq_self_of_den_eq_one H.2]
    simpa [← Int.cast_add] using intCast_add_equiv ..
  apply Fits.equiv_of_forall_moves ?_ (fun z hz ↦ ?_) (fun z hz ↦ ?_)
  · rw [Fits, forall_moves_add, forall_moves_add]
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    all_goals
      intro z hz
      first
        | obtain rfl := eq_lower_of_mem_leftMoves_toIGame hz
        | obtain rfl := eq_upper_of_mem_rightMoves_toIGame hz
      grw [← toIGame_add_equiv]
      simp
  · obtain rfl := eq_lower_of_mem_leftMoves_toIGame hz
    obtain h | h := le_or_gt x.den y.den
    · by_cases hy : y.den = 1; · simp_all
      use x + lower y
      have hy := toIGame_of_den_ne_one hy
      have : (lower y : IGame) ∈ yᴸ := by rw [hy]; simp
      rw [← (toIGame_add_equiv ..).le_congr_right, hy]
      simpa using lower_add_le_of_den_le h
    · use lower x + y
      have hx := toIGame_of_den_ne_one (den_ne_one_of_den_lt h)
      have : (lower x : IGame) ∈ xᴸ := by rw [hx]; simp
      rw [← (toIGame_add_equiv ..).le_congr_right, hx]
      simpa using lower_add_le_of_den_ge h.le
  · obtain rfl := eq_upper_of_mem_rightMoves_toIGame hz
    obtain h | h := le_or_gt x.den y.den
    · by_cases hy : y.den = 1; · simp_all
      use x + upper y
      have hy := toIGame_of_den_ne_one hy
      have : (upper y : IGame) ∈ yᴿ := by rw [hy]; simp
      grw [← (toIGame_add_equiv ..).le_congr_left, hy]
      simpa using le_upper_add_of_den_le h
    · use upper x + y
      have hx := toIGame_of_den_ne_one (den_ne_one_of_den_lt h)
      have : (upper x : IGame) ∈ xᴿ := by rw [hx]; simp
      rw [← (toIGame_add_equiv ..).le_congr_left, hx]
      simpa using le_upper_add_of_den_ge h.le
termination_by ((x : IGame.{u}), (y : IGame.{u}))
decreasing_by igame_wf

theorem toIGame_sub_equiv (x y : Dyadic) : ((x - y : Dyadic) : IGame) ≈ x - y := by
  simpa [sub_eq_add_neg] using toIGame_add_equiv x (-y)

theorem toIGame_equiv (x : Dyadic) : (x : IGame) ≈ (x : ℚ) := by
  by_cases h : x.den = 1
  · rw [toIGame_of_den_eq_one h, ← (ratCast_intCast_equiv _).antisymmRel_congr_left,
      Rat.coe_int_num_of_den_eq_one h]
  · have := den_add_self_lt h
    have := (toIGame_add_equiv x x).symm.trans (toIGame_equiv (x + x))
    simp_all [← Surreal.mk_eq_mk, ← two_mul]
termination_by x.den

@[simp]
theorem _root_.Game.mk_dyadic (x : Dyadic) : Game.mk x = x :=
  Game.mk_eq x.toIGame_equiv

@[simp]
theorem _root_.Surreal.mk_dyadic (x : Dyadic) : Surreal.mk x = x := by
  simpa using Surreal.mk_eq x.toIGame_equiv

theorem toIGame_mul_equiv (x y : Dyadic) : ((x * y : Dyadic) : IGame) ≈ x * y := by
  simp [← Surreal.mk_eq_mk]

/-! ### Simp lemmas -/

/-! #### ℚ -/

@[simp, norm_cast]
theorem toIGame_lt_ratCast {x : Dyadic} {y : ℚ} : (x : IGame) < y ↔ x < y := by
  simp [(toIGame_equiv x).lt_congr_left]
@[simp, norm_cast]
theorem toIGame_le_ratCast {x : Dyadic} {y : ℚ} : (x : IGame) ≤ y ↔ x ≤ y := by
  simp [(toIGame_equiv x).le_congr_left]

@[simp, norm_cast]
theorem ratCast_lt_toIGame {x : ℚ} {y : Dyadic} : (x : IGame) < y ↔ x < y := by
  simp [(toIGame_equiv y).lt_congr_right]
@[simp, norm_cast]
theorem ratCast_le_toIGame {x : ℚ} {y : Dyadic} : (x : IGame) ≤ y ↔ x ≤ y := by
  simp [(toIGame_equiv y).le_congr_right]

@[simp, norm_cast]
theorem toIGame_equiv_ratCast {x : Dyadic} {y : ℚ} : (x : IGame) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]
@[simp, norm_cast]
theorem ratCast_equiv_toIGame {x : ℚ} {y : Dyadic} : (x : IGame) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]

/-! #### ℤ -/

@[simp, norm_cast]
theorem toIGame_lt_intCast {x : Dyadic} {y : ℤ} : (x : IGame) < y ↔ x < y := by
  simp [← (ratCast_intCast_equiv y).lt_congr_right]
@[simp, norm_cast]
theorem toIGame_le_intCast {x : Dyadic} {y : ℤ} : (x : IGame) ≤ y ↔ x ≤ y := by
  simp [← (ratCast_intCast_equiv y).le_congr_right]

@[simp, norm_cast]
theorem intCast_lt_toIGame {x : ℤ} {y : Dyadic} : (x : IGame) < y ↔ x < y := by
  simp [← (ratCast_intCast_equiv x).lt_congr_left]
@[simp, norm_cast]
theorem intCast_le_toIGame {x : ℤ} {y : Dyadic} : (x : IGame) ≤ y ↔ x ≤ y := by
  simp [← (ratCast_intCast_equiv x).le_congr_left]

@[simp, norm_cast]
theorem toIGame_equiv_intCast {x : Dyadic} {y : ℤ} : (x : IGame) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]
@[simp, norm_cast]
theorem intCast_equiv_toIGame {x : ℤ} {y : Dyadic} : (x : IGame) ≈ y ↔ x = y := by
  simp [AntisymmRel, le_antisymm_iff]

@[simp, norm_cast]
theorem toIGame_eq_intCast {x : Dyadic} {y : ℤ} : (x : IGame) = y ↔ x = y :=
  ⟨fun h ↦ toIGame_equiv_intCast.1 h.antisymmRel, by simp_all⟩
@[simp, norm_cast]
theorem intCast_eq_toIGame {x : ℤ} {y : Dyadic} : (x : IGame) = y ↔ x = y := by
  simp [eq_comm]

/-! #### ℕ -/

@[simp, norm_cast]
theorem toIGame_lt_natCast {x : Dyadic} {y : ℕ} : (x : IGame) < y ↔ x < y :=
  toIGame_lt_intCast (y := y)
@[simp, norm_cast]
theorem toIGame_le_natCast {x : Dyadic} {y : ℕ} : (x : IGame) ≤ y ↔ x ≤ y :=
  toIGame_le_intCast (y := y)

@[simp, norm_cast]
theorem natCast_lt_toIGame {x : ℕ} {y : Dyadic} : (x : IGame) < y ↔ x < y :=
  intCast_lt_toIGame (x := x)
@[simp, norm_cast]
theorem natCast_le_toIGame {x : ℕ} {y : Dyadic} : (x : IGame) ≤ y ↔ x ≤ y :=
  intCast_le_toIGame (x := x)

@[simp, norm_cast]
theorem toIGame_equiv_natCast {x : Dyadic} {y : ℕ} : (x : IGame) ≈ y ↔ x = y :=
  toIGame_equiv_intCast (y := y)
@[simp, norm_cast]
theorem natCast_equiv_toIGame {x : ℕ} {y : Dyadic} : (x : IGame) ≈ y ↔ x = y :=
  intCast_equiv_toIGame (x := x)

@[simp, norm_cast]
theorem toIGame_eq_natCast {x : Dyadic} {y : ℕ} : (x : IGame) = y ↔ x = y :=
  toIGame_eq_intCast (y := y)
@[simp, norm_cast]
theorem natCast_eq_toIGame {x : ℕ} {y : Dyadic} : (x : IGame) = y ↔ x = y :=
  intCast_eq_toIGame (x := x)

/-! #### 0 -/

@[simp, norm_cast]
theorem toIGame_lt_zero {x : Dyadic} : (x : IGame) < 0 ↔ x < 0 :=
  toIGame_lt_natCast (y := 0)
@[simp, norm_cast]
theorem toIGame_le_zero {x : Dyadic} : (x : IGame) ≤ 0 ↔ x ≤ 0 :=
  toIGame_le_natCast (y := 0)

@[simp, norm_cast]
theorem zero_lt_toIGame {x : Dyadic} : 0 < (x : IGame) ↔ 0 < x :=
  natCast_lt_toIGame (x := 0)
@[simp, norm_cast]
theorem zero_le_toIGame {x : Dyadic} : 0 ≤ (x : IGame) ↔ 0 ≤ x :=
  natCast_le_toIGame (x := 0)

@[simp, norm_cast]
theorem toIGame_equiv_zero {x : Dyadic} : (x : IGame) ≈ 0 ↔ x = 0 :=
  toIGame_equiv_natCast (y := 0)
@[simp, norm_cast]
theorem zero_equiv_toIGame {x : Dyadic} : 0 ≈ (x : IGame) ↔ 0 = x :=
  natCast_equiv_toIGame (x := 0)

@[simp, norm_cast]
theorem toIGame_eq_zero {x : Dyadic} : (x : IGame) = 0 ↔ x = 0 :=
  toIGame_eq_natCast (y := 0)
@[simp, norm_cast]
theorem zero_eq_toIGame {x : Dyadic} : 0 = (x : IGame) ↔ 0 = x :=
  natCast_eq_toIGame (x := 0)

/-! #### 1 -/

@[simp, norm_cast]
theorem toIGame_lt_one {x : Dyadic} : (x : IGame) < 1 ↔ x < 1 := by
  simpa using toIGame_lt_natCast (y := 1)
@[simp, norm_cast]
theorem toIGame_le_one {x : Dyadic} : (x : IGame) ≤ 1 ↔ x ≤ 1 := by
  simpa using toIGame_le_natCast (y := 1)

@[simp, norm_cast]
theorem one_lt_toIGame {x : Dyadic} : 1 < (x : IGame) ↔ 1 < x := by
  simpa using natCast_lt_toIGame (x := 1)
@[simp, norm_cast]
theorem one_le_toIGame {x : Dyadic} : 1 ≤ (x : IGame) ↔ 1 ≤ x := by
  simpa using natCast_le_toIGame (x := 1)

@[simp, norm_cast]
theorem toIGame_equiv_one {x : Dyadic} : (x : IGame) ≈ 1 ↔ x = 1 := by
  simpa using toIGame_equiv_natCast (y := 1)
@[simp, norm_cast]
theorem one_equiv_toIGame {x : Dyadic} : 1 ≈ (x : IGame) ↔ 1 = x := by
  simpa using natCast_equiv_toIGame (x := 1)

@[simp, norm_cast]
theorem toIGame_eq_one {x : Dyadic} : (x : IGame) = 1 ↔ x = 1 := by
  simpa using toIGame_eq_natCast (y := 1)
@[simp, norm_cast]
theorem one_eq_toIGame {x : Dyadic} : 1 = (x : IGame) ↔ 1 = x := by
  simpa using natCast_eq_toIGame (x := 1)

end Dyadic

/-! ### Dyadic games as numbers -/

namespace IGame

private theorem equiv_dyadic (x : IGame) [Short x] [Numeric x] : ∃ y : Dyadic, x ≈ y.toIGame := by
  have H₁ (y : xᴸ) : ∃ z : Dyadic, y.1 ≈ z.toIGame := by
    have := Numeric.of_mem_moves y.2
    have := Short.of_mem_moves y.2
    exact IGame.equiv_dyadic _
  have H₂ (y : xᴿ) : ∃ z : Dyadic, y.1 ≈ z.toIGame := by
    have := Numeric.of_mem_moves y.2
    have := Short.of_mem_moves y.2
    exact IGame.equiv_dyadic _
  choose f hf using H₁
  choose g hg using H₂
  obtain ⟨y, hy₁, hy₂⟩ := by
    refine (Set.finite_range f).exists_between' (Set.finite_range g) (fun x hx y hy ↦ ?_)
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← Dyadic.toIGame_lt_toIGame]
    grw [← hf, ← hg]
    exact Numeric.left_lt_right a.2 b.2
  have : ∃ y, Fits (Dyadic.toIGame y) x := by
    use y
    constructor <;> intro z hz
    · have := hy₁ _ (Set.mem_range_self ⟨z, hz⟩)
      rw [← Dyadic.toIGame_lt_toIGame] at this
      grw [← hf] at this
      exact this.not_ge
    · have := hy₂ _ (Set.mem_range_self ⟨z, hz⟩)
      rw [← Dyadic.toIGame_lt_toIGame] at this
      grw [← hg] at this
      exact this.not_ge
  obtain ⟨z, H⟩ := exists_minimalFor_of_wellFoundedLT _ (birthday ∘ Dyadic.toIGame) this
  use z
  refine (Fits.equiv_of_forall_not_fits H.1 fun p _ hz' hz ↦ ?_).symm
  cases p
  · obtain rfl := Dyadic.eq_lower_of_mem_leftMoves_toIGame hz'
    have hz' := birthday_lt_of_mem_moves hz'
    exact (H.2 hz hz'.le).not_gt hz'
  · obtain rfl := Dyadic.eq_upper_of_mem_rightMoves_toIGame hz'
    have hz' := birthday_lt_of_mem_moves hz'
    exact (H.2 hz hz'.le).not_gt hz'
termination_by x
decreasing_by igame_wf

/-- Any dyadic game (meaning a game that is `Short` and `Numeric`) is equivalent to a `Dyadic`
rational number.

TODO: it should be possible to compute this value explicitly, given the finsets of `Dyadic`
rationals corresponding to the left and right moves. -/
@[no_expose]
noncomputable def toDyadic (x : IGame) [Short x] [Numeric x] : Dyadic :=
  Classical.choose x.equiv_dyadic

@[simp]
theorem equiv_toIGame_toDyadic (x : IGame) [Short x] [Numeric x] : x ≈ x.toDyadic :=
  Classical.choose_spec x.equiv_dyadic

@[simp]
theorem toIGame_toDyadic_equiv (x : IGame) [Short x] [Numeric x] : (x.toDyadic : IGame) ≈ x :=
  (equiv_toIGame_toDyadic x).symm

@[simp]
theorem _root_.Game.ratCast_toDyadic (x : IGame) [Short x] [Numeric x] :
    x.toDyadic = Game.mk x := by
  simpa using Game.mk_eq (toIGame_toDyadic_equiv x)

@[simp]
theorem _root_.Surreal.ratCast_toDyadic (x : IGame) [Short x] [Numeric x] :
    x.toDyadic = Surreal.mk x := by
  simpa using Surreal.mk_eq (toIGame_toDyadic_equiv x)

theorem equiv_toIGame_iff_toDyadic_eq {x : IGame} [Short x] [Numeric x] {y : Dyadic} :
    x ≈ y ↔ x.toDyadic = y := by
  constructor
  · intro h
    simpa using (equiv_toIGame_toDyadic x).symm.trans h
  · rintro rfl
    exact equiv_toIGame_toDyadic x

theorem toIGame_equiv_iff_eq_toDyadic {x : IGame} [Short x] [Numeric x] {y : Dyadic} :
    (y : IGame) ≈ x ↔ y = x.toDyadic := by
  rw [antisymmRel_comm, eq_comm, equiv_toIGame_iff_toDyadic_eq]

@[simp]
theorem toDyadic_toIGame (x : Dyadic) : toDyadic x = x := by
  simp [← equiv_toIGame_iff_toDyadic_eq]

@[simp]
theorem toDyadic_zero : toDyadic 0 = 0 := by
  simp [← equiv_toIGame_iff_toDyadic_eq]

@[simp]
theorem toDyadic_one : toDyadic 1 = 1 := by
  simp [← equiv_toIGame_iff_toDyadic_eq]

@[simp]
theorem toDyadic_half : toDyadic ½ = .half := by
  simp [← equiv_toIGame_iff_toDyadic_eq]

@[simp]
theorem toDyadic_natCast (n : ℕ) : toDyadic n = n := by
  simp [← equiv_toIGame_iff_toDyadic_eq]

@[simp]
theorem toDyadic_ofNat (n : ℕ) [n.AtLeastTwo] : toDyadic ofNat(n) = n :=
  toDyadic_natCast n

@[simp]
theorem toDyadic_intCast (n : ℤ) : toDyadic n = n := by
  simp [← equiv_toIGame_iff_toDyadic_eq]

@[simp]
theorem toDyadic_neg (x : IGame) [Short x] [Numeric x] : toDyadic (-x) = -toDyadic x := by
  simp [← equiv_toIGame_iff_toDyadic_eq]

@[simp]
theorem toDyadic_add (x y : IGame) [Short x] [Numeric x] [Short y] [Numeric y] :
    toDyadic (x + y) = toDyadic x + toDyadic y := by
  rw [← equiv_toIGame_iff_toDyadic_eq, ← Surreal.mk_eq_mk]
  simp

@[simp]
theorem toDyadic_sub (x y : IGame) [Short x] [Numeric x] [Short y] [Numeric y] :
    toDyadic (x - y) = toDyadic x - toDyadic y := by
  rw [← equiv_toIGame_iff_toDyadic_eq, ← Surreal.mk_eq_mk]
  simp

@[simp]
theorem toDyadic_mul (x y : IGame) [Short x] [Numeric x] [Short y] [Numeric y] :
    toDyadic (x * y) = toDyadic x * toDyadic y := by
  rw [← equiv_toIGame_iff_toDyadic_eq, ← Surreal.mk_eq_mk]
  simp

end IGame
end
