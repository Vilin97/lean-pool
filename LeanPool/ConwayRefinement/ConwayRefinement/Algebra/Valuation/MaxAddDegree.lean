/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Ring.Basic

/-!
# Max-additive degree functions

A `MaxAddDegree` records the properties of a unital ring filtration written in LM24's additive
convention: bottom at zero, degree at most zero for one, invariance under negation, the
ultrametric inequality with `max` for addition, and subadditivity under multiplication.

Multiplication need not preserve the degree exactly. This is necessary for quotient filtrations:
the degree of a nonzero quotient class is the least degree of a representative, and
multiplication of least-degree representatives gives only an inequality until an
associated-graded argument proves equality. The exact case is the class `IsMultiplicative`; a
multiplicative degree is a multiplicative semi-valuation in the sense of LM24, Section 4, and a
separated one is a multiplicative valuation. LM24's bespoke convention `-∞ < -∞` is not used;
the bottom value is treated by the standard order on `WithBot`.
-/

universe u v

public noncomputable section

open scoped BigOperators

/-- A ring degree function with bottom at zero, `max` for addition, and subadditivity under
multiplication. -/
structure MaxAddDegree (R : Type u) (M : Type v) [CommRing R] [AddCommMonoid M]
    [LinearOrder M] where
  toFun : R → WithBot M
  map_zero' : toFun 0 = ⊥
  map_one_le_zero' : toFun 1 ≤ 0
  map_neg' : ∀ x, toFun (-x) = toFun x
  map_add_le_max' : ∀ x y, toFun (x + y) ≤ max (toFun x) (toFun y)
  map_mul_le_add' : ∀ x y, toFun (x * y) ≤ toFun x + toFun y

namespace MaxAddDegree

variable {R : Type u} {M : Type v} [CommRing R] [AddCommMonoid M] [LinearOrder M]

instance : CoeFun (MaxAddDegree R M) (fun _ ↦ R → WithBot M) :=
  ⟨MaxAddDegree.toFun⟩

/-- Max-additive degrees are equal when their underlying functions are equal. -/
@[ext]
theorem ext {ν δ : MaxAddDegree R M} (h : ∀ x, ν x = δ x) : ν = δ := by
  have hf : ν.toFun = δ.toFun := funext h
  cases ν with
  | mk f hz ho hn ha hm =>
    cases δ with
    | mk g gz go gn ga gm =>
      dsimp only [MaxAddDegree.toFun] at hf
      subst g
      rfl

@[simp]
theorem map_zero (ν : MaxAddDegree R M) : ν 0 = ⊥ :=
  ν.map_zero'

/-- The unit lies in filtration degree zero. -/
theorem map_one_le_zero (ν : MaxAddDegree R M) : ν 1 ≤ 0 :=
  ν.map_one_le_zero'

@[simp]
theorem map_neg (ν : MaxAddDegree R M) (x : R) : ν (-x) = ν x :=
  ν.map_neg' x

theorem map_add_le_max (ν : MaxAddDegree R M) (x y : R) :
    ν (x + y) ≤ max (ν x) (ν y) :=
  ν.map_add_le_max' x y

/-- Subtraction satisfies the same ultrametric inequality as addition. -/
theorem map_sub_le_max (ν : MaxAddDegree R M) (x y : R) :
    ν (x - y) ≤ max (ν x) (ν y) := by
  simpa [sub_eq_add_neg] using ν.map_add_le_max x (-y)

theorem map_mul_le_add (ν : MaxAddDegree R M) (x y : R) :
    ν (x * y) ≤ ν x + ν y :=
  ν.map_mul_le_add' x y

/-- Two elements whose difference has degree strictly below the degree of one of them have the
same degree. -/
theorem map_eq_of_map_sub_lt (ν : MaxAddDegree R M) {x y : R} (hxy : ν (x - y) < ν x) :
    ν x = ν y := by
  apply le_antisymm
  · by_contra hyx
    have hyx' : ν y < ν x := lt_of_not_ge hyx
    have hle : ν x ≤ max (ν y) (ν (x - y)) := by
      simpa only [add_sub_cancel] using ν.map_add_le_max y (x - y)
    exact (not_lt_of_ge hle) (max_lt hyx' hxy)
  · have hle : ν y ≤ max (ν x) (ν (x - y)) := by
      simpa only [sub_sub_cancel] using ν.map_sub_le_max x (x - y)
    simpa only [max_eq_left hxy.le] using hle

/-- A finite sum has degree at most a common bound for the degrees of its summands. -/
theorem map_sum_le_of_forall_le (ν : MaxAddDegree R M) {ι : Type*}
    (s : Finset ι) (f : ι → R) (m : WithBot M)
    (h : ∀ i ∈ s, ν (f i) ≤ m) :
    ν (∑ i ∈ s, f i) ≤ m := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (ν.map_add_le_max (f i) (∑ j ∈ s, f j)).trans
        (max_le (h i (Finset.mem_insert_self i s))
          (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

/-- A finite sum has degree strictly below any bound above bottom that strictly bounds every
summand. -/
theorem map_sum_lt_of_forall_lt (ν : MaxAddDegree R M) {ι : Type*}
    (s : Finset ι) (f : ι → R) {m : WithBot M} (hm : ⊥ < m)
    (h : ∀ i ∈ s, ν (f i) < m) :
    ν (∑ i ∈ s, f i) < m := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, ν.map_zero] using hm
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (ν.map_add_le_max (f i) (∑ j ∈ s, f j)).trans_lt
        (max_lt (h i (Finset.mem_insert_self i s))
          (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj)))

/-- A max-additive degree function is separated when only zero has bottom degree. -/
def IsSeparated (ν : MaxAddDegree R M) : Prop :=
  ∀ x, ν x = ⊥ ↔ x = 0

/-- The defining condition for a separated max-additive degree function. -/
theorem isSeparated_iff (ν : MaxAddDegree R M) :
    ν.IsSeparated ↔ ∀ x, ν x = ⊥ ↔ x = 0 :=
  Iff.rfl

/-- A separated degree sends every nonzero element to a nonbottom degree. -/
theorem map_ne_bot_of_ne_zero (ν : MaxAddDegree R M) (hν : ν.IsSeparated) {x : R}
    (hx : x ≠ 0) : ν x ≠ ⊥ :=
  fun h ↦ hx (((isSeparated_iff ν).mp hν x).mp h)

/-- A max-additive degree function is multiplicative when its product inequality is always an
equality. This is the multiplicativity clause of LM24's multiplicative semi-valuations. -/
class IsMultiplicative (ν : MaxAddDegree R M) : Prop where
  map_mul : ∀ x y, ν (x * y) = ν x + ν y

/-- The defining condition for a multiplicative max-additive degree function. -/
theorem isMultiplicative_iff (ν : MaxAddDegree R M) :
    ν.IsMultiplicative ↔ ∀ x y, ν (x * y) = ν x + ν y :=
  ⟨fun h ↦ h.map_mul, fun h ↦ ⟨h⟩⟩

/-- Multiplicativity with the degree explicit, as `Valuation.map_mul`. Inside `namespace
MaxAddDegree` this shadows the root `map_mul` for homomorphisms, which is then `_root_.map_mul`. -/
@[simp]
theorem map_mul (ν : MaxAddDegree R M) [ν.IsMultiplicative] (x y : R) :
    ν (x * y) = ν x + ν y :=
  IsMultiplicative.map_mul x y

/-- Every degree sends the unit to bottom or to zero: `ν 1 ≤ ν 1 + ν 1` by submultiplicativity
and `ν 1 ≤ 0`. The bottom case is the degenerate degree that is bottom everywhere. -/
theorem map_one_eq_bot_or_eq_zero (ν : MaxAddDegree R M) [IsOrderedCancelAddMonoid M] :
    ν 1 = ⊥ ∨ ν 1 = 0 := by
  by_cases hbot : ν 1 = ⊥
  · exact Or.inl hbot
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp hbot
  have hone := ν.map_mul_le_add 1 1
  rw [one_mul, ← hm, ← WithBot.coe_add, WithBot.coe_le_coe] at hone
  have hle : m ≤ 0 := WithBot.coe_le_coe.mp (hm ▸ ν.map_one_le_zero)
  have hge : 0 ≤ m := le_of_add_le_add_left (a := m) (by simpa using hone)
  exact Or.inr (by rw [← hm, le_antisymm hle hge]; rfl)

/-- A separated degree on a nontrivial ring sends the unit to degree zero. -/
theorem map_one_eq_zero_of_isSeparated (ν : MaxAddDegree R M)
    [IsOrderedCancelAddMonoid M] [Nontrivial R] (hν : ν.IsSeparated) :
    ν 1 = 0 := by
  rcases ν.map_one_eq_bot_or_eq_zero with hbot | hzero
  · exact absurd (((ν.isSeparated_iff).mp hν 1).mp hbot) one_ne_zero
  · exact hzero

/-- If a degree sends the unit to bottom, it is bottom everywhere: `ν x ≤ ν x + ν 1`. -/
theorem map_eq_bot_of_map_one_eq_bot (ν : MaxAddDegree R M) (hone : ν 1 = ⊥) (x : R) :
    ν x = ⊥ :=
  le_bot_iff.mp (by simpa [hone] using ν.map_mul_le_add x 1)

/-- A separated multiplicative degree function detects zero products. -/
theorem eq_zero_or_eq_zero_of_mul_eq_zero (ν : MaxAddDegree R M) [ν.IsMultiplicative]
    (hν : ν.IsSeparated) {x y : R} (hxy : x * y = 0) :
    x = 0 ∨ y = 0 := by
  have hbot : ν x + ν y = ⊥ := by
    rw [← ν.map_mul x y, hxy, ν.map_zero]
  rcases WithBot.add_eq_bot.mp hbot with hx | hy
  · exact Or.inl (((isSeparated_iff ν).mp hν x).mp hx)
  · exact Or.inr (((isSeparated_iff ν).mp hν y).mp hy)

/-- A nontrivial commutative ring carrying a separated multiplicative degree function is a
domain. -/
theorem isDomain (ν : MaxAddDegree R M) [Nontrivial R] [ν.IsMultiplicative]
    (hν : ν.IsSeparated) :
    IsDomain R := by
  letI : NoZeroDivisors R :=
    ⟨fun hxy ↦ ν.eq_zero_or_eq_zero_of_mul_eq_zero hν hxy⟩
  exact NoZeroDivisors.to_isDomain R

end MaxAddDegree
