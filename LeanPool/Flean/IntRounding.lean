/-
Copyright (c) 2026 Joseph McKinsey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph McKinsey
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Positivity.Core
import Mathlib.Tactic.Zify
import Mathlib.Tactic.Qify
import Mathlib.Algebra.Order.Interval.Set.Group

/-!
# Integer Rounding Functions

This module collects the integer-valued rounding primitives (`round0`,
`roundinf`, `roundup`, `rounddown`, `roundnearest`) used to round a rational to a
mantissa, together with their basic correctness properties such as round-to-even
behaviour on half-integers.
-/

/-- An integer-valued rounding rule taking a sign bit and a rational mantissa. -/
abbrev IntRounder := Bool → ℚ → ℕ

/-- Round toward zero: the rounded mantissa is `⌊q⌋`, ignoring the sign. -/
def round0 (s : Bool) (q : ℚ) := if s then ⌊q⌋.natAbs else ⌊q⌋.natAbs

/-- `round0` ignores its sign argument. -/
@[simp] lemma round0_apply (s : Bool) (q : ℚ) : round0 s q = ⌊q⌋.natAbs := by
  simp only [round0, ite_self]

/-- Round away from zero: the rounded mantissa is `⌈q⌉`, ignoring the sign. -/
def roundinf (s : Bool) (q : ℚ) := if s then ⌈q⌉.natAbs else ⌈q⌉.natAbs

/-- `roundinf` ignores its sign argument. -/
@[simp] lemma roundinf_apply (s : Bool) (q : ℚ) : roundinf s q = ⌈q⌉.natAbs := by
  simp only [roundinf, ite_self]

/-- Round down (toward negative infinity), branching on the sign. -/
def roundup := fun (s : Bool) q => if s then round0 s q else roundinf s q

/-- Round up (toward positive infinity), branching on the sign. -/
def rounddown := fun (s : Bool) (q : ℚ) => if s then roundinf s q else round0 s q

/-- Round to the nearest integer, with ties broken to the even integer. -/
def roundNearInt (q : ℚ) :=
  let i1 := ⌊q⌋
  let i2 := ⌈q⌉
  if Int.fract q < 1/2 then
    i1
  else if 1/2 < Int.fract q then
    i2
  else if i1 % 2 = 0 then
    i1
  else
    i2

/-- Round to nearest as an `IntRounder`: ties to even, ignoring the sign. -/
def roundnearest (s : Bool) (q : ℚ) :=
  if s then (roundNearInt q).natAbs else (roundNearInt q).natAbs

/-- `roundnearest` ignores its sign argument. -/
@[simp] lemma roundnearest_apply (s : Bool) (q : ℚ) :
    roundnearest s q = (roundNearInt q).natAbs := by
  simp only [roundnearest, ite_self]

lemma round_near_int_of_nonneg {q : ℚ} (h : 0 ≤ q) : 0 ≤ roundNearInt q := by
  rw [roundNearInt]
  split_ifs <;> (try exact Int.floor_nonneg.mpr h) <;> (try exact Int.ceil_nonneg h)

lemma round_near_int_of_pos {q : ℚ} (h : 0 < q) : 0 ≤ roundNearInt q := by
  apply round_near_int_of_nonneg
  exact le_of_lt h

/-
Round nearest preserves order.

Suppose q1 and q2 are far enough away (⌈q1⌉ ≤ ⌊q2⌋), then it is obviously
true in all cases.

If ⌈q1⌉ > ⌊q2⌋, then ⌈q1⌉ = ⌈q2⌉ and ⌊q1⌋ = ⌊q2⌋, then we have
Int.frac q1 ≤ Int.frac q2.

If Int.frac q1 < 1/2, then we round to ⌊q1⌋,
and
-/

lemma round_near_le_round_near {q1 q2 : ℚ} (h : q1 ≤ q2) :
  roundNearInt q1 ≤ roundNearInt q2 := by
  rw [roundNearInt, roundNearInt]
  have floor_le_ceil : ⌊q1⌋ ≤ ⌈q2⌉ := by
    qify
    calc
      ⌊q1⌋ ≤ q1 := Int.floor_le q1
      q1 ≤ q2 := h
      q2 ≤ ⌈q2⌉ := Int.le_ceil q2
  by_cases h' : ⌈q1⌉ ≤ ⌊q2⌋
  · split_ifs <;>
      (try exact Int.floor_le_floor h) <;> (try exact Int.ceil_le_ceil h) <;>
      (try exact floor_le_ceil) <;> (try exact h')
  have floorq1_le : ⌊q2⌋ ≤ ⌊q1⌋ := by
    simp only [not_le] at h'
    apply Int.lt_add_one_iff.mp
    apply lt_of_lt_of_le h'
    exact Int.ceil_le_floor_add_one q1
  have : Int.fract q1 ≤ Int.fract q2 := by
    unfold Int.fract
    apply sub_le_sub
    · exact h
    simp only [Int.cast_le, floorq1_le]
  if h1 : Int.fract q1 < 1/2 then
    simp only [h1, reduceIte, ge_iff_le]
    split_ifs <;> (try exact Int.floor_le_floor h) <;>
      (exact floor_le_ceil)
  else if h2 : 1/2 < Int.fract q1 then
    have : 1/2 < Int.fract q2 := lt_of_lt_of_le h2 this
    simp only [h1, ↓reduceIte, h2, this, not_lt_of_gt this]
    exact Int.ceil_le_ceil h
  else
    have fract_eq : Int.fract q1 = 1/2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
    simp only [fract_eq]
    rcases lt_or_eq_of_le this with h' | h'
    · simp only [not_le, fract_eq, one_div, lt_self_iff_false, not_false_eq_true, ↓reduceIte,
        ge_iff_le] at *
      simp only [h', not_lt_of_ge (le_of_lt h'), ↓reduceIte]
      split_ifs
      · exact floor_le_ceil
      exact Int.ceil_le_ceil h
    simp only [<-h', fract_eq, ge_iff_le, ↓reduceIte, lt_self_iff_false, ↓reduceIte]
    suffices ⌊q1⌋ = ⌊q2⌋ by
      rw [this]
      split_ifs <;> simp [Int.ceil_le_ceil h]
    exact le_antisymm (Int.floor_le_floor h) floorq1_le

lemma round_near_eq_of (q : ℚ) (z : ℤ) :
  z - 1/2 < q ∧ q < z + 1/2 → z = roundNearInt q := by
  rintro ⟨h1, h2⟩
  if h3 : z ≤ q then
    have : Int.fract q = q - z := by
      apply Int.fract_eq_iff.mpr
      refine ⟨?_, ?_, ⟨z, ?_⟩⟩
      · simp [h3]
      · linarith
      ring
    rw [roundNearInt, this]
    simp_rw [sub_lt_iff_lt_add, add_comm, h2]
    simp only [↓reduceIte]
    symm
    apply Int.floor_eq_iff.mpr ⟨h3, ?_⟩
    apply lt_trans h2
    linarith
  else
    simp only [not_le] at h3
    have floor_eq : ⌊q⌋ = z - 1 := by
      suffices ⌊q⌋ + 1 = z by
        linarith
      rw [<-Int.floor_add_one]
      apply Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · linarith
      linarith
    have fract_eq : Int.fract q = q - (z - 1) := by
      rw [Int.fract]
      suffices (⌊q⌋ : ℚ) = z - 1 by
        linarith
      norm_cast
    rw [roundNearInt, fract_eq]
    have : 1/2 < q - (z - 1) := by
      linarith
    simp_rw [if_neg (not_lt_of_gt this), if_pos this]
    symm
    apply Int.ceil_eq_iff.mpr ⟨?_, le_of_lt h3⟩
    linarith

lemma fract_eq_ceil_of_pos {q : ℚ} (h : 0 < Int.fract q) :
  Int.fract q = q + 1 - ⌈q⌉ := by
  rcases Int.fract_eq_zero_or_add_one_sub_ceil q
  · linarith
  assumption

lemma round_near_int_le (q : ℚ) :
  |roundNearInt q - q| ≤ 1/2 := by
  unfold roundNearInt
  simp only [Int.cast_ite]
  split_ifs with h1 h2 h3
  · rw [abs_sub_comm, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg q)]
    exact le_of_lt h1
  · rw [abs_of_nonneg (by linarith [Int.le_ceil q])]
    rw [fract_eq_ceil_of_pos] at h2
    · linarith
    linarith
  · have : Int.fract q = 1/2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
    rw [abs_sub_comm, Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg q)]
    rw [this]
  have : Int.fract q = 1/2 := le_antisymm (le_of_not_gt h2) (le_of_not_gt h1)
  rw [abs_of_nonneg (by linarith [Int.le_ceil q])]
  rw [fract_eq_ceil_of_pos] at this
  · linarith
  rw [this]
  norm_num

lemma round_near_int_of_int (z : ℤ) :
  roundNearInt z = z := by
  rw [roundNearInt,Int.fract_intCast]
  simp

lemma round_near_add_half (z : ℤ) (h : z % 2 = 0) :
  roundNearInt (z + 1/2) = z := by
  rw [roundNearInt]
  have : Int.fract (1 / 2 : ℚ) = 1/2 := by
    exact Int.fract_div_intCast_eq_div_intCast_mod
  rw [one_div] at this
  simp only [one_div, Int.fract_intCast_add, this, lt_self_iff_false, ↓reduceIte,
    Int.floor_intCast_add]
  have : ⌊(2⁻¹ : ℚ)⌋ = 0 := by norm_num
  rw [this, <-h]
  simp [h]

lemma round_near_sub_half (z : ℤ) (h : z % 2 = 0) :
  roundNearInt (z - 1/2) = z := by
  rw [roundNearInt]
  have : Int.fract (1 / 2 : ℚ) = 1/2 := by
    exact Int.fract_div_intCast_eq_div_intCast_mod
  have : Int.fract (-(1 / 2 : ℚ)) = 1/2 := by
    rw [Int.fract_neg, this]
    · norm_num
    rw [this]
    norm_num
  rw [sub_eq_add_neg]
  simp only [Int.fract_intCast_add, this, lt_self_iff_false, ↓reduceIte]
  rw [add_comm, Int.ceil_add_intCast]
  have : ⌈(-(1 / 2) : ℚ)⌉ = 0 := by norm_num
  rw [this, zero_add, if_neg]
  rw [add_comm]
  have : ⌊(z : ℚ) + -(1/2)⌋ = z - 1 := by
    apply Int.floor_eq_iff.mpr
    constructor
    · qify; linarith
    qify; linarith
  rw [this]
  omega

lemma round_of_add_half (z : ℤ) :
  roundNearInt (z + 1/2) % 2 = 0 := by
  rw [roundNearInt]
  have : Int.fract (z + 1/2 : ℚ) = 1/2 := by
    rw [Int.fract_intCast_add]
    norm_num
  rw [this]
  simp only [lt_self_iff_false, ↓reduceIte, Int.floor_intCast_add]
  rw [add_comm (z : ℚ), Int.ceil_add_intCast]
  rw [show ⌊(1 : ℚ)/2⌋ = 0 by norm_num, add_zero]
  split_ifs with h
  · assumption
  rw [show ⌈(1 : ℚ) / 2⌉ = 1 by norm_num]
  omega

/-- The set of rationals whose floor is `z`, namely `[z, z + 1)`. -/
def floorInterval (z : ℤ) : Set ℚ := Set.Ico z (z + 1)

/-- The set of rationals whose ceiling is `z`, namely `(z - 1, z]`. -/
def ceilInterval (z : ℤ) : Set ℚ := Set.Ioc (z - 1) z

lemma floor_eq_iff_interval (z : ℤ) (q : ℚ) :
  ⌊q⌋ = z ↔ q ∈ floorInterval z := Int.floor_eq_iff

lemma ceil_eq_iff_interval (z : ℤ) (q : ℚ) :
  ⌈q⌉ = z ↔ q ∈ ceilInterval z := Int.ceil_eq_iff

/-- The set of rationals that round to nearest `z`: a closed interval when `z`
is even (ties round to it) and an open interval otherwise. -/
def roundNearInterval (z : ℤ) : Set ℚ :=
  if z % 2 = 0 then
    Set.Icc (z - 1/2) (z + 1/2)
  else
    Set.Ioo (z - 1/2) (z + 1/2)


lemma Icc_of_Ioo {α : Type} [PartialOrder α] {q x y : α} (h : q ∈ Set.Icc x y)
  (not_x : q ≠ x) (not_y : q ≠ y) : q ∈ Set.Ioo x y := by
  simp only [Set.mem_Icc, Set.mem_Ioo] at *
  constructor
  · exact lt_of_le_of_ne h.1 (not_x.symm)
  exact lt_of_le_of_ne h.2 not_y


lemma round_near_eq_iff (q : ℚ) (z : ℤ) :
  roundNearInt q = z ↔ q ∈ roundNearInterval z := by
  constructor
  · intro h
    rw [<-h]
    unfold roundNearInterval
    have : q ∈ Set.Icc ((roundNearInt q) - (1 : ℚ) / 2) ((roundNearInt q) + 1 / 2) := by
      suffices |roundNearInt q - q| ≤ 1/2 by
        exact Set.mem_Icc_iff_abs_le.mp this
      exact round_near_int_le q
    split_ifs with h'
    · exact this
    · apply Icc_of_Ioo this
      · contrapose! h'
        rw [h']
        convert round_of_add_half (roundNearInt q - 1) using 3
        push_cast
        linarith
      contrapose! h'
      rw [h']
      exact round_of_add_half (roundNearInt q)
  intro h
  by_cases h' : z % 2 = 0
  · rw [roundNearInterval, if_pos h'] at h
    apply le_antisymm
    · rw [<-round_near_add_half z h']
      apply round_near_le_round_near
      linarith [h.2]
    rw [<-round_near_sub_half z h']
    apply round_near_le_round_near
    linarith [h.1]
  rw [roundNearInterval, if_neg h'] at h
  symm
  apply round_near_eq_of
  exact h


open Lean Meta Qq Mathlib.Meta.Positivity in
/-- A `positivity` extension proving `0 ≤ roundNearInt q` from `0 ≤ q`. -/
@[positivity roundNearInt _]
def evalRoundNearInt : PositivityExt where eval {u α} _ _ e := do
  match u, α, e with
  | 0, ~q(ℤ), ~q(roundNearInt $a) =>
    let zα : Q(Zero ℚ) := q(inferInstance)
    let pα : Q(PartialOrder ℚ) := q(inferInstance)
    assumeInstancesCommute
    match ← core zα pα a with
    | .positive pa => pure (.nonnegative q(round_near_int_of_pos $pa))
    | .nonnegative pa => pure (.nonnegative q(round_near_int_of_nonneg $pa))
    | _ => pure .none


/-- A rounding rule is *valid* if it is monotone on nonnegative inputs and is a
left inverse of the cast `ℕ → ℚ` (so it fixes integer mantissas). -/
class ValidRounder (f : Bool → ℚ → ℕ) where
  /-- The rounder is monotone in the mantissa on nonnegative inputs. -/
  le_iff_le s q1 q2 : (0 ≤ q1) → (q1 ≤ q2) → f s q1 ≤ f s q2
  /-- The rounder fixes integer mantissas: it left-inverts the cast `ℕ → ℚ`. -/
  leftInverse s : Function.LeftInverse (f s) ((↑) : ℕ → ℚ)

instance : ValidRounder round0 where
  le_iff_le s q1 q2 q1h q1le := by
    simp only [round0, ite_self]
    zify
    apply abs_le_abs_of_nonneg
    · positivity
    exact Int.floor_le_floor q1le
  leftInverse s := by
    intro n
    simp [round0]

instance : ValidRounder roundinf where
  le_iff_le s q1 q2 q1h q1le := by
    simp only [roundinf, ite_self]
    zify
    apply abs_le_abs_of_nonneg
    · positivity
    exact Int.ceil_le_ceil q1le
  leftInverse s := by
    intro n
    simp [roundinf]

instance : ValidRounder roundup where
  le_iff_le s := by
    simp only [roundup]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> apply ValidRounder.le_iff_le
  leftInverse s := by
    unfold roundup
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> apply ValidRounder.leftInverse


instance : ValidRounder rounddown where
  le_iff_le s := by
    simp only [rounddown]
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> apply ValidRounder.le_iff_le
  leftInverse s := by
    unfold rounddown
    cases s <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> apply ValidRounder.leftInverse

instance : ValidRounder roundnearest where
  le_iff_le s q1 q2 q1h q1le := by
    simp only [roundnearest, ite_self]
    zify
    apply abs_le_abs_of_nonneg
    · positivity
    exact round_near_le_round_near q1le
  leftInverse s := by
    intro n
    simp only [roundnearest, ite_self]
    rw [show roundNearInt n = n by exact_mod_cast round_near_int_of_int n]
    simp

/-- The rounder obtained by flipping the sign bit, used to relate rounding of
`q` and `-q`. -/
def IntRounder.neg (r : IntRounder) : IntRounder := fun s ↦ r !s

lemma neg_neg_r (r : IntRounder) :
  r.neg.neg = r := by
  funext s q
  simp [IntRounder.neg]

lemma ValidRounder.neg {r : IntRounder} (rh : ValidRounder r) :
  ValidRounder r.neg := ⟨fun s ↦ ValidRounder.le_iff_le !s,
  fun s ↦ ValidRounder.leftInverse !s⟩

lemma neg_valid_rounder (r : IntRounder) :
  ValidRounder r.neg ↔ ValidRounder r := by
  constructor
  · intro h
    rw [←neg_neg_r r]
    exact ⟨fun s ↦ ValidRounder.le_iff_le !s,
    fun s ↦ ValidRounder.leftInverse !s⟩
  intro h
  exact h.neg

lemma roundnearest_neg :
  IntRounder.neg roundnearest = roundnearest := by
  funext s q
  simp only [IntRounder.neg, roundnearest, ite_self]

lemma round_eq_or (r : IntRounder) [rh : ValidRounder r] (b : Bool)
  {q : ℚ} (h : 0 ≤ q) :
  r b q = round0 b q ∨ r b q = roundinf b q := by
  have rfloor_le : r b (⌊q⌋.natAbs) ≤ r b q:= by
    apply ValidRounder.le_iff_le
    · positivity
    rw [show (⌊q⌋.natAbs : ℚ) = (⌊q⌋.natAbs : ℤ) by rfl]
    rw [Int.natAbs_of_nonneg]
    · exact Int.floor_le q
    exact Int.floor_nonneg.mpr h
  have le_rceil : r b q ≤ r b (⌈q⌉.natAbs) := by
    apply ValidRounder.le_iff_le
    · positivity
    rw [show (⌈q⌉.natAbs : ℚ) = (⌈q⌉.natAbs : ℤ) by rfl]
    rw [Int.natAbs_of_nonneg]
    · exact Int.le_ceil q
    exact Int.ceil_nonneg h
  rw [rh.leftInverse b] at rfloor_le le_rceil
  simp only [round0, roundinf, ite_self]
  have : ⌊q⌋ = ⌈q⌉ ∨ ⌊q⌋ + 1 = ⌈q⌉ := by
    have := Int.ceil_le_floor_add_one q
    have := Int.floor_le_ceil q
    omega
  omega

lemma round_eq_or' (r : IntRounder) [rh : ValidRounder r] (b : Bool)
  {q : ℚ} (h : 0 ≤ q) :
  r b q = rounddown b q ∨ r b q = roundup b q := by
  have key := round_eq_or r b h
  cases b <;>
    simp only [rounddown, roundup, round0_apply, roundinf_apply, Bool.false_eq_true,
      ↓reduceIte] at key ⊢ <;>
    tauto


lemma roundr_le (r : IntRounder) [rh : ValidRounder r]
  {b : Bool} {n : ℕ} {q : ℚ} (h : 0 ≤ q) (h' : q ≤ n) :
  r b q ≤ n := by
  rw [show n = r b n by rw [rh.leftInverse b]]
  exact rh.le_iff_le b q n h h'

lemma le_roundr (r : IntRounder) [rh : ValidRounder r]
  {b : Bool} {n : ℕ} {q : ℚ} (h' : n ≤ q) :
  n ≤ r b q := by
  rw [show n = r b n by rw [rh.leftInverse b]]
  exact rh.le_iff_le b n q (Nat.cast_nonneg' n) h'

lemma roundup_neg : IntRounder.neg roundup = rounddown := by
  ext s q
  simp [IntRounder.neg, roundup, rounddown, round0, roundinf]
  cases s <;> rfl

lemma rounddown_neg : IntRounder.neg rounddown = roundup := by
  ext s q
  simp [IntRounder.neg, roundup, rounddown, round0, roundinf]
  cases s <;> rfl
