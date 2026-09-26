/-
Copyright (c) 2025 Violeta Hernández Palacios. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Violeta Hernández Palacios, Theodore Hwa
-/
module

public import LeanPool.ConwayRefinement.CombinatorialGames.Surreal.Multiplication
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Order.Ring.Unbundled.Rat

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Surreal division

In this file, we prove that if `x` is a positive numeric game, then `x⁻¹` (defined in
`CombinatorialGames.Game.IGame`) is a number and is a multiplicative inverse for `x`. We use
that
to define the field structure on `Surreal`.

This is Theorem 1.10 in ONAG, and we follow the broad strokes of the proof. We prove
by simultaneous induction that if `x` is positive and numeric, then (ii) `x⁻¹` is numeric, and (iv)
`x * x⁻¹ ≈ 1`. We do this by showing the inductive hypothesis implies that (i) `x * y < 1` for
`y ∈ x⁻¹ᴸ` and `1 < x * y` for `y ∈ x⁻¹ᴿ`, and that (iv) `y < 1` for
`y ∈ (x * x⁻¹)ᴸ` and `1 < y` for `y ∈ (x * x⁻¹ᴿ)`.

An important difference is that Conway assumes that `x` has no negative left options, while we don't
make use of this assumption. This is because our definition of the inverse is tweaked to ensure that
only positive left options of `x` generate the options for `x⁻¹`. To make sure the induction checks
out, we require two small extra arithmetic lemmas `mulOption_le` and `le_mulOption`.

Once we have defined the inverse for positive `x`, it is extended in the obvious way to negative
numbers.
-/

universe u

open IGame

instance {x y : IGame} [Numeric x] [Numeric y⁻¹] : Numeric (x / y) := .mul ..

instance {x y a : IGame} [Numeric x] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    Numeric (invOption x y a) :=
  .mul ..

private theorem inv_pos' {x : IGame} [Numeric x⁻¹] (hx : 0 < x) : 0 < x⁻¹ :=
  Numeric.left_lt (zero_mem_leftMoves_inv hx)

private theorem mk_div' (x y : IGame) [Numeric x] [Numeric y⁻¹] :
    Surreal.mk (x / y) = Surreal.mk x * Surreal.mk y⁻¹ :=
  rfl

/-! ### Arithmetic lemmas -/

private lemma one_neg_mul_invOption (x : IGame) {y : IGame} (hy : y * y⁻¹ ≈ 1) (a : IGame)
    [Numeric x] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    1 - x * invOption x y a ≈ (1 - x * a) * (y - x) / y := by
  rw [← Surreal.mk_eq_mk] at *
  dsimp [invOption, mk_div'] at *
  simp only [one_mul, sub_eq_add_neg, add_mul, hy]
  ring

private lemma mulOption_self_inv (x : IGame) {y : IGame} (hy : y * y⁻¹ ≈ 1) (a : IGame)
    [Numeric x] [Numeric x⁻¹] [Numeric y] [Numeric y⁻¹] [Numeric a] :
    mulOption x x⁻¹ y a ≈ 1 + (x⁻¹ - invOption x y a) * y := by
  rw [mul_comm] at hy
  rw [← Surreal.mk_eq_mk] at *
  dsimp [mulOption, invOption, mk_div'] at *
  simp only [sub_eq_add_neg, add_mul, neg_mul, mul_assoc, hy]
  ring

private lemma mulOption_le (x y : IGame) {a b : IGame} [Numeric y] [Numeric a] [Numeric b]
    (ha : a ≤ 0) (hb : b ≤ y) : mulOption x y a b ≤ x * b := by
  rw [mulOption, ← ConwayGame.mk_le_mk]
  dsimp
  have : ConwayGame.mk (a * y) - ConwayGame.mk (a * b) ≤ 0 := by
    rw [← ConwayGame.mk_mul_sub]
    apply Numeric.mul_nonpos_of_nonpos_of_nonneg ha
    rwa [IGame.sub_nonneg]
  rw [← add_le_add_iff_left (ConwayGame.mk (x * b))] at this
  convert this using 1 <;> abel

private theorem le_mulOption (x y : IGame) {a b : IGame} [Numeric y] [Numeric a] [Numeric b]
    (ha : a ≤ 0) (hb : y ≤ b) : x * b ≤ mulOption x y a b := by
  rw [mulOption, ← ConwayGame.mk_le_mk]
  dsimp
  have : 0 ≤ ConwayGame.mk (a * y) - ConwayGame.mk (a * b) := by
    rw [← ConwayGame.mk_mul_sub]
    apply Numeric.mul_nonneg_of_nonpos_of_nonpos ha
    rwa [IGame.sub_nonpos]
  rw [← add_le_add_iff_left (ConwayGame.mk (x * b))] at this
  convert this using 1 <;> abel

/-! ### Inductive proof -/

private lemma numeric_option_inv {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ xᴸ, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ xᴿ, Numeric y⁻¹) :
    (∀ p, ∀ y ∈ x⁻¹.moves p, Numeric y) := by
  refine invRec hx Numeric.zero fun p₁ p₂ y hy hyx _ _ _ ↦ ?_
  numeric
  cases p₁ <;> cases p₂
  all_goals
    first
    | have := hl _ hyx hy
    | have := hr _ hyx
    infer_instance

private lemma mul_inv_option_mem {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ xᴸ, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ xᴿ, Numeric y⁻¹)
    (hl' : ∀ y ∈ xᴸ, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ xᴿ, y * y⁻¹ ≈ 1) :
    (∀ y ∈ x⁻¹ᴸ, x * y < 1) ∧ (∀ y ∈ x⁻¹ᴿ, 1 < x * y) := by
  suffices ∀ p y, y ∈ x⁻¹.moves p → p.cases (x * y < 1) (1 < x * y) by
    exact ⟨this left, this right⟩
  apply invRec (P := fun p y hy ↦ p.cases (x * y < 1) (1 < x * y)) hx
  · simp
  rintro (_ | _) (_ | _) y hy hyx a ha h <;> dsimp
  · numeric
    have := hr y hyx
    have := numeric_option_inv hx hl hr left a ha
    rw [← IGame.sub_pos]
    grw [one_neg_mul_invOption x (hr' y hyx) a]
    apply Numeric.mul_pos (Numeric.mul_pos _ _) (inv_pos' hy)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_pos]
      exact Numeric.lt_right hyx
  · numeric
    have := hl y hyx hy
    have := numeric_option_inv hx hl hr left a ha
    rw [← IGame.sub_neg]
    grw [one_neg_mul_invOption x (hl' y hyx hy) a]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_pos_of_neg _ _) (inv_pos' hy)
    · rwa [IGame.sub_pos]
    · rw [IGame.sub_neg]
      exact Numeric.left_lt hyx
  · numeric
    have := hl y hyx hy
    have := numeric_option_inv hx hl hr right a ha
    rw [← IGame.sub_pos]
    grw [one_neg_mul_invOption x (hl' y hyx hy) a]
    apply Numeric.mul_pos (Numeric.mul_pos_of_neg_of_neg _ _) (inv_pos' hy)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_neg]
      exact Numeric.left_lt hyx
  · numeric
    have := hr y hyx
    have := numeric_option_inv hx hl hr right a ha
    rw [← IGame.sub_neg]
    grw [one_neg_mul_invOption x (hr' y hyx) a]
    apply Numeric.mul_neg_of_neg_of_pos (Numeric.mul_neg_of_neg_of_pos _ _) (inv_pos' hy)
    · rwa [IGame.sub_neg]
    · rw [IGame.sub_pos]
      exact Numeric.lt_right hyx

private lemma numeric_inv {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ xᴸ, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ xᴿ, Numeric y⁻¹)
    (hl' : ∀ y ∈ xᴸ, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ xᴿ, y * y⁻¹ ≈ 1) :
    Numeric x⁻¹ := by
  obtain ⟨Hl, Hr⟩ := mul_inv_option_mem hx hl hr hl' hr'
  have H' := numeric_option_inv hx hl hr
  refine Numeric.mk (fun y hy z hz ↦ ?_) H'
  have := H' _ y hy
  have := H' _ z hz
  exact (Numeric.mul_lt_mul_iff_right hx).1 <| (Hl y hy).trans (Hr z hz)

private lemma option_mul_inv_lt {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ xᴸ, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ xᴿ, Numeric y⁻¹)
    (hl' : ∀ y ∈ xᴸ, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ xᴿ, y * y⁻¹ ≈ 1) :
    (∀ y ∈ (x * x⁻¹)ᴸ, y < 1) ∧ (∀ y ∈ (x * x⁻¹)ᴿ, 1 < y) := by
  have := numeric_inv hx hl hr hl' hr'
  obtain H := numeric_option_inv hx hl hr
  rw [forall_moves_mul, forall_moves_mul]
  refine ⟨?_, ?_⟩ <;> rintro (_ | _)
  all_goals
    intro y hyx a ha
    numeric
    have := H _ a ha
    try (have := hr y hyx; have hy := hx.trans (Numeric.lt_right hyx))
  · obtain hy | hy := Numeric.lt_or_ge 0 y
    · have := hl y hyx hy
      grw [mulOption_self_inv x (hl' y hyx hy) a]
      rw [add_comm, ← IGame.lt_sub_iff_add_lt]
      grw [IGame.sub_self_equiv]
      apply Numeric.mul_neg_of_neg_of_pos _ hy
      rw [IGame.sub_neg]
      exact Numeric.lt_right (invOption_mem_moves_inv (p₁ := left) hx hy hyx ha)
    · apply (mulOption_le _ _ hy (Numeric.left_lt ha).le).trans_lt
      exact (mul_inv_option_mem hx hl hr hl' hr').1 a ha
  · grw [mulOption_self_inv x (hr' y hyx) a]
    rw [add_comm, ← IGame.lt_sub_iff_add_lt]
    grw [IGame.sub_self_equiv]
    apply Numeric.mul_neg_of_neg_of_pos _ hy
    rw [IGame.sub_neg]
    exact Numeric.lt_right (invOption_mem_moves_inv (p₁ := right) hx hy hyx ha)
  · obtain hy | hy := Numeric.lt_or_ge 0 y
    · have := hl y hyx hy
      grw [mulOption_self_inv x (hl' y hyx hy) a]
      rw [add_comm, ← IGame.sub_lt_iff_lt_add]
      grw [IGame.sub_self_equiv]
      apply Numeric.mul_pos _ hy
      rw [IGame.sub_pos]
      apply Numeric.left_lt (invOption_mem_moves_inv (p₁ := right) hx hy hyx ha)
    · apply ((mul_inv_option_mem hx hl hr hl' hr').2 a ha).trans_le
      exact le_mulOption _ _ hy (Numeric.lt_right ha).le
  · grw [mulOption_self_inv x (hr' y hyx) a]
    rw [add_comm, ← IGame.sub_lt_iff_lt_add]
    grw [IGame.sub_self_equiv]
    apply Numeric.mul_pos _ hy
    rw [IGame.sub_pos]
    exact Numeric.left_lt (invOption_mem_moves_inv (p₁ := left) hx hy hyx ha)

private lemma mul_inv_self {x : IGame} [Numeric x] (hx : 0 < x)
    (hl : ∀ y ∈ xᴸ, 0 < y → Numeric y⁻¹) (hr : ∀ y ∈ xᴿ, Numeric y⁻¹)
    (hl' : ∀ y ∈ xᴸ, 0 < y → y * y⁻¹ ≈ 1) (hr' : ∀ y ∈ xᴿ, y * y⁻¹ ≈ 1) :
    x * x⁻¹ ≈ 1 := by
  obtain ⟨Hl, Hr⟩ := option_mul_inv_lt hx hl hr hl' hr'
  have := numeric_inv hx hl hr hl' hr'
  apply equiv_one_of_fits ⟨fun z hz ↦ (Hl z hz).not_ge, fun z hz ↦ (Hr z hz).not_ge⟩
  rw [Numeric.mul_equiv_zero, not_or]
  exact ⟨hx.not_antisymmRel_symm, (inv_pos' hx).not_antisymmRel_symm⟩

private theorem main {x : IGame} [Numeric x] (hx : 0 < x) : Numeric x⁻¹ ∧ x * x⁻¹ ≈ 1 := by
  have IHl : ∀ y ∈ xᴸ, 0 < y → Numeric y⁻¹ ∧ y * y⁻¹ ≈ 1 :=
    fun y hy hy' ↦ have := Numeric.of_mem_moves hy; main hy'
  have IHr : ∀ y ∈ xᴿ, Numeric y⁻¹ ∧ y * y⁻¹ ≈ 1 :=
    fun y hy ↦ have := Numeric.of_mem_moves hy; main (hx.trans (Numeric.lt_right hy))
  have hl := fun y hy hy' ↦ (IHl y hy hy').1
  have hr := fun y hy ↦ (IHr y hy).1
  have hl' := fun y hy hy' ↦ (IHl y hy hy').2
  have hr' := fun y hy ↦ (IHr y hy).2
  exact ⟨numeric_inv hx hl hr hl' hr', mul_inv_self hx hl hr hl' hr'⟩
termination_by x
decreasing_by igame_wf

/-! ### Instances and corollaries -/

public section

namespace IGame.Numeric

protected instance inv (x : IGame) [Numeric x] : Numeric x⁻¹ := by
  obtain h | h | h := Numeric.lt_or_equiv_or_gt x 0
  · rw [← IGame.zero_lt_neg] at h
    simpa using (main h).1
  · simp [inv_of_equiv_zero h]
  · exact (main h).1

protected instance div (x y : IGame) [Numeric x] [Numeric y] : Numeric (x / y) := .mul ..
protected instance ratCast (q : ℚ) : Numeric q := .div ..

protected instance invOption (x y a : IGame) [Numeric x] [Numeric y] [Numeric a] :
    Numeric (invOption x y a) :=
  .div ..

protected theorem mul_inv_cancel {x : IGame} [Numeric x] (hx : ¬ x ≈ 0) : x * x⁻¹ ≈ 1 := by
  obtain h | h | h := Numeric.lt_or_equiv_or_gt x 0
  · rw [← IGame.zero_lt_neg] at h
    simpa using (main h).2
  · contradiction
  · exact (main h).2

protected theorem inv_mul_cancel {x : IGame} [Numeric x] (hx : ¬ x ≈ 0) : x⁻¹ * x ≈ 1 := by
  rw [mul_comm]
  exact Numeric.mul_inv_cancel hx

theorem inv_congr {x y : IGame} [Numeric x] [Numeric y] (he : x ≈ y) : x⁻¹ ≈ y⁻¹ := by
  by_cases hy : y ≈ 0
  · rw [inv_of_equiv_zero hy, inv_of_equiv_zero (he.trans hy)]
  · have hx := (hy <| he.symm.trans ·)
    have := (Numeric.mul_inv_cancel hx).trans (Numeric.mul_inv_cancel hy).symm
    rw [← (Numeric.mul_congr_left he).antisymmRel_congr_right] at this
    exact Numeric.mul_left_cancel hx this

theorem div_congr_left {x₁ x₂ y : IGame} [Numeric x₁] [Numeric x₂] [Numeric y] (he : x₁ ≈ x₂) :
    x₁ / y ≈ x₂ / y :=
  mul_congr_left he

theorem div_congr_right {x y₁ y₂ : IGame} [Numeric x] [Numeric y₁] [Numeric y₂] (he : y₁ ≈ y₂) :
    x / y₁ ≈ x / y₂ :=
  mul_congr_right (inv_congr he)

theorem div_congr {x₁ x₂ y₁ y₂ : IGame} [Numeric x₁] [Numeric x₂] [Numeric y₁] [Numeric y₂]
    (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : x₁ / y₁ ≈ x₂ / y₂ :=
  (div_congr_left hx).trans (div_congr_right hy)

end IGame.Numeric

namespace Surreal

noncomputable instance : Field Surreal where
  inv := Quotient.map (fun x ↦ ⟨x⁻¹, by infer_instance⟩) fun _ _ ↦ Numeric.inv_congr
  mul_inv_cancel := by rintro ⟨a⟩ h; exact mk_eq (Numeric.mul_inv_cancel (mk_eq_mk.not.1 h))
  inv_zero := by change mk 0⁻¹ = _; simp
  qsmul := _
  nnqsmul := _

@[simp] theorem mk_inv (x : IGame) [Numeric x] : mk x⁻¹ = (mk x)⁻¹ := rfl
@[simp] theorem mk_div (x y : IGame) [Numeric x] [Numeric y] : mk (x / y) = mk x / mk y := rfl

@[simp]
theorem mk_ratCast (q : ℚ) : mk q = q := by
  conv_rhs => rw [← q.num_div_den]
  simp [ratCast_def]

@[simp]
theorem toGame_ratCast (q : ℚ) : toGame q = q := by
  rw [← mk_ratCast, toGame_mk, ConwayGame.mk_ratCast]

end Surreal

namespace IGame
namespace Numeric

@[simp]
protected theorem inv_pos {x : IGame} [Numeric x] : 0 < x⁻¹ ↔ 0 < x := by
  simp [← Surreal.mk_lt_mk]

@[simp]
protected theorem inv_neg {x : IGame} [Numeric x] : x⁻¹ < 0 ↔ x < 0 := by
  simp [← Surreal.mk_lt_mk]

@[simp]
protected theorem inv_nonneg {x : IGame} [Numeric x] : 0 ≤ x⁻¹ ↔ 0 ≤ x := by
  simp [← Surreal.mk_le_mk]

@[simp]
protected theorem inv_nonpos {x : IGame} [Numeric x] : x⁻¹ ≤ 0 ↔ x ≤ 0 := by
  simp [← Surreal.mk_le_mk]

theorem inv_equiv_of_mul_eq_one {x y : IGame} [Numeric x] [Numeric y]
    (he : x * y ≈ 1) : x⁻¹ ≈ y := by
  rw [← Surreal.mk_eq_mk] at *
  exact inv_eq_of_mul_eq_one_right (a := Surreal.mk x) he

theorem equiv_inv_of_mul_eq_one {x y : IGame} [Numeric x] [Numeric y]
    (he : x * y ≈ 1) : x ≈ y⁻¹ :=
  (Numeric.inv_equiv_of_mul_eq_one (mul_comm x y ▸ he)).symm

protected theorem lt_div_iff {x y z : IGame} [Numeric x] [Numeric y] [Numeric z] (hz : 0 < z) :
    x < y / z ↔ x * z < y := by
  simp_all [← Surreal.mk_lt_mk, lt_div_iff₀]

protected theorem lt_div_iff' {x y z : IGame} [Numeric x] [Numeric y] [Numeric z] (hz : 0 < z) :
    x < y / z ↔ z * x < y := by
  simp_all [← Surreal.mk_lt_mk, lt_div_iff₀']

protected theorem div_lt_iff {x y z : IGame} [Numeric x] [Numeric y] [Numeric z] (hy : 0 < y) :
    x / y < z ↔ x < z * y := by
  simp_all [← Surreal.mk_lt_mk, div_lt_iff₀]

protected theorem div_lt_iff' {x y z : IGame} [Numeric x] [Numeric y] [Numeric z] (hz : 0 < y) :
    x / y < z ↔ x < y * z := by
  simp_all [← Surreal.mk_lt_mk, div_lt_iff₀']

protected theorem lt_div_iff_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hz : z < 0) : x < y / z ↔ y < x * z := by
  simp_all [← Surreal.mk_lt_mk, lt_div_iff_of_neg]

protected theorem div_lt_iff_of_neg {x y z : IGame} [Numeric x] [Numeric y] [Numeric z]
    (hy : y < 0) : x / y < z ↔ z * y < x := by
  simp_all [← Surreal.mk_lt_mk, div_lt_iff_of_neg]

end Numeric

@[simp, norm_cast]
theorem ratCast_le {m n : ℚ} : (m : IGame) ≤ n ↔ m ≤ n := by
  simp [← Surreal.mk_le_mk]

@[simp, norm_cast]
theorem ratCast_lt {m n : ℚ} : (m : IGame) < n ↔ m < n := by
  simp [← Surreal.mk_lt_mk]

theorem ratCast_strictMono : StrictMono ((↑) : ℚ → IGame) :=
  fun _ _ h ↦ ratCast_lt.2 h

@[simp, norm_cast]
theorem ratCast_inj {m n : ℚ} : (m : IGame) = n ↔ m = n :=
  ratCast_strictMono.injective.eq_iff

@[simp, norm_cast]
theorem ratCast_equiv {m n : ℚ} : (m : IGame) ≈ n ↔ m = n := by
  simp [AntisymmRel, le_antisymm_iff]

theorem ratCast_natCast_equiv (n : ℕ) : ((n : ℚ) : IGame) ≈ n := by
  simp [← Surreal.mk_eq_mk]

theorem ratCast_intCast_equiv (n : ℤ) : ((n : ℚ) : IGame) ≈ n := by
  simp [← Surreal.mk_eq_mk]

theorem ratCast_add_equiv (m n : ℚ) : ((m + n : ℚ) : IGame) ≈ m + n := by
  simp [← Surreal.mk_eq_mk]

theorem ratCast_sub_equiv (m n : ℚ) : ((m - n : ℚ) : IGame) ≈ m - n := by
  simp [← Surreal.mk_eq_mk]

theorem ratCast_mul_equiv (m n : ℚ) : ((m * n : ℚ) : IGame) ≈ m * n := by
  simp [← Surreal.mk_eq_mk]

theorem ratCast_inv_equiv (m : ℚ) : ((m⁻¹ : ℚ) : IGame) ≈ m⁻¹ := by
  simp [← Surreal.mk_eq_mk]

theorem ratCast_div_equiv (m n : ℚ) : ((m / n : ℚ) : IGame) ≈ m / n := by
  simp [← Surreal.mk_eq_mk]

@[simp, norm_cast]
theorem zero_lt_ratCast {q : ℚ} : 0 < (q : IGame) ↔ 0 < q := by
  simpa using ratCast_lt (m := 0)

@[simp, norm_cast]
theorem ratCast_lt_zero {q : ℚ} : (q : IGame) < 0 ↔ q < 0 := by
  simpa using ratCast_lt (n := 0)

@[simp, norm_cast]
theorem zero_le_ratCast {q : ℚ} : 0 ≤ (q : IGame) ↔ 0 ≤ q := by
  simpa using ratCast_le (m := 0)

@[simp, norm_cast]
theorem ratCast_le_zero {q : ℚ} : (q : IGame) ≤ 0 ↔ q ≤ 0 := by
  simpa using ratCast_le (n := 0)

private theorem equiv_ratCast_of_mem_move_inv_natCast {n : ℕ} :
    (∀ p, ∀ x ∈ moves.{u} p n⁻¹, ∃ q : ℚ, x ≈ q) := by
  cases n with
  | zero => simp
  | succ n =>
    refine invRec (mod_cast n.succ_pos) ⟨0, by simp⟩ ?_
    rintro (_ | _) (_ | _) <;> try (· simp)
    all_goals
      dsimp
      simp_rw [Nat.cast_add, Nat.cast_one, leftMoves_natCast_succ, forall_exists_index]
      rintro _ hn rfl x hx q hq
      use (1 + -q) / n
      numeric
      simp_all [invOption, ← Surreal.mk_eq_mk]

private theorem equiv_ratCast_of_mem_move_ratCast {q : ℚ} :
    (∀ x ∈ (q : IGame.{u})ᴸ, ∃ r : ℚ, x ≈ r) ∧ (∀ x ∈ (q : IGame.{u})ᴿ, ∃ r : ℚ, x ≈ r) := by
  constructor
  all_goals
    rw [ratCast_def]
    simp only [IGame.div_eq_mul_inv, forall_moves_mul, forall_moves_mul]
    obtain ⟨m, n, hn, _⟩ := q
    rintro (_ | _)
    all_goals
    · intro x hx y hy
      first |
        obtain ⟨k, _, rfl⟩ := eq_intCast_of_mem_leftMoves_intCast hx |
        obtain ⟨k, _, rfl⟩ := eq_intCast_of_mem_rightMoves_intCast hx
      obtain ⟨q, hq⟩ := equiv_ratCast_of_mem_move_inv_natCast _ _ hy
      use k * (n : ℚ)⁻¹ + m * q - k * q
      numeric
      simp_all [mulOption, ← Surreal.mk_eq_mk]

/-- Every left option of a rational number is equivalent to a smaller rational number. -/
theorem equiv_ratCast_of_mem_leftMoves_ratCast {q : ℚ} {x : IGame} (hx : x ∈ qᴸ) :
    ∃ r : ℚ, r < q ∧ x ≈ r := by
  obtain ⟨r, hr⟩ := equiv_ratCast_of_mem_move_ratCast.1 x hx
  refine ⟨r, ?_, hr⟩
  rw [← ratCast_lt]
  grw [← hr]
  simpa using Numeric.left_lt hx

/-- Every right option of a rational number is equivalent to a larger rational number. -/
theorem equiv_ratCast_of_mem_rightMoves_ratCast {q : ℚ} {x : IGame} (hx : x ∈ qᴿ) :
    ∃ r : ℚ, q < r ∧ x ≈ r := by
  obtain ⟨r, hr⟩ := equiv_ratCast_of_mem_move_ratCast.2 x hx
  refine ⟨r, ?_, hr⟩
  rw [← ratCast_lt]
  grw [← hr]
  simpa using Numeric.lt_right hx

@[simp]
theorem mk_half : Surreal.mk ½ = 2⁻¹ := by
  rw [← mul_left_inj' two_ne_zero, mul_two, inv_mul_cancel₀ two_ne_zero]
  exact Surreal.mk_eq half_add_half_equiv_one

end IGame

namespace ConwayGame

@[simp, norm_cast]
theorem ratCast_le {m n : ℚ} : (m : ConwayGame) ≤ n ↔ m ≤ n :=
  IGame.ratCast_le

@[simp, norm_cast]
theorem ratCast_lt {m n : ℚ} : (m : ConwayGame) < n ↔ m < n :=
  IGame.ratCast_lt

theorem ratCast_strictMono : StrictMono ((↑) : ℚ → ConwayGame) :=
  fun _ _ h ↦ ratCast_lt.2 h

@[simp, norm_cast]
theorem ratCast_inj {m n : ℚ} : (m : ConwayGame) = n ↔ m = n :=
  ratCast_strictMono.injective.eq_iff

@[simp, norm_cast]
theorem ratCast_natCast (n : ℕ) : ((n : ℚ) : ConwayGame) = n := by
  simpa using ConwayGame.mk_eq (IGame.ratCast_natCast_equiv n)

@[simp, norm_cast]
theorem ratCast_intCast (n : ℤ) : ((n : ℚ) : ConwayGame) = n := by
  simpa using ConwayGame.mk_eq (IGame.ratCast_intCast_equiv n)

@[simp, norm_cast]
theorem ratCast_add (m n : ℚ) : ((m + n : ℚ) : ConwayGame) = m + n :=
  ConwayGame.mk_eq (IGame.ratCast_add_equiv m n)

@[simp, norm_cast]
theorem ratCast_sub (m n : ℚ) : ((m - n : ℚ) : ConwayGame) = m - n :=
  ConwayGame.mk_eq (IGame.ratCast_sub_equiv m n)

@[simp, norm_cast]
theorem zero_lt_ratCast {q : ℚ} : 0 < (q : ConwayGame) ↔ 0 < q :=
  IGame.zero_lt_ratCast

@[simp, norm_cast]
theorem ratCast_lt_zero {q : ℚ} : (q : ConwayGame) < 0 ↔ q < 0 :=
  IGame.ratCast_lt_zero

@[simp, norm_cast]
theorem zero_le_ratCast {q : ℚ} : 0 ≤ (q : ConwayGame) ↔ 0 ≤ q :=
  IGame.zero_le_ratCast

@[simp, norm_cast]
theorem ratCast_le_zero {q : ℚ} : (q : ConwayGame) ≤ 0 ↔ q ≤ 0 :=
  IGame.ratCast_le_zero

end ConwayGame
