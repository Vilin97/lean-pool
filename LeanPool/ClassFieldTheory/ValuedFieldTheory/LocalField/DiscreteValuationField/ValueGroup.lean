/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Quotients
public import Mathlib.Data.Int.ModEq

/-! # Value Group -/

@[expose] public section
namespace LocalFieldTheory

/-!
# Integer value-group images

This file contains the integer value-group subgroup-image lemmas used by
  the norm and ramification-image arguments.  The results are purely about
integer-valued multiplicative valuations and integer lcm divisibility.
-/

noncomputable
section

namespace DiscreteValuationField

/-- Membership in both integer-multiple value subgroups is the same as
membership in the subgroup cut out by the lcm. -/
theorem int_lcm_dvd_iff_dvd_and_dvd (d e n : ℤ) :
    ((d.lcm e : ℕ) : ℤ) ∣ n ↔ d ∣ n ∧ e ∣ n := by
  have h :=
    (Int.modEq_and_modEq_iff_modEq_lcm
      (a := n) (b := 0) (m := d) (n := e))
  simpa [Int.modEq_iff_dvd] using h.symm

/-- Introduction form for integer lcm divisibility. -/
theorem int_lcm_dvd_of_dvd_of_dvd {d e n : ℤ}
    (hd : d ∣ n) (he : e ∣ n) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  (int_lcm_dvd_iff_dvd_and_dvd d e n).2 ⟨hd, he⟩

/-- The integer-multiple subgroup for `lcm d e` is the intersection of the two
integer-multiple subgroups for `d` and `e`. -/
theorem integerMultipleSubgroup_lcm_eq_inf (d e : ℤ) :
    integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) =
      integerMultipleSubgroup d ⊓ integerMultipleSubgroup e := by
  ext n
  change n ∈ integerMultipleSubgroup ((d.lcm e : ℕ) : ℤ) ↔
    n ∈ integerMultipleSubgroup d ∧ n ∈ integerMultipleSubgroup e
  rw [mem_integerMultipleSubgroup_iff,
    mem_integerMultipleSubgroup_iff,
    mem_integerMultipleSubgroup_iff]
  exact int_lcm_dvd_iff_dvd_and_dvd d e (Multiplicative.toAdd n)

/-- Inclusion between integer-multiple value subgroups is exactly divisibility
of the corresponding integer steps, with the order reversed. -/
theorem integerMultipleSubgroup_le_iff_dvd (a b : ℤ) :
    integerMultipleSubgroup b ≤ integerMultipleSubgroup a ↔ a ∣ b := by
  constructor
  · intro h
    have hb : Multiplicative.ofAdd b ∈ integerMultipleSubgroup b := by
      rw [ofAdd_mem_integerMultipleSubgroup_iff]
    simpa using h hb
  · intro h
    exact integerMultipleSubgroup_le_of_dvd h

/-- Extract lcm divisibility from two integer-multiple subgroup inclusions. -/
theorem int_lcm_dvd_of_integerMultipleSubgroup_le_of_le
    {n d e : ℤ}
    (hd : integerMultipleSubgroup n ≤ integerMultipleSubgroup d)
    (he : integerMultipleSubgroup n ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ n := by
  have hle : integerMultipleSubgroup n ≤
      integerMultipleSubgroup d ⊓ integerMultipleSubgroup e :=
    le_inf hd he
  rw [← integerMultipleSubgroup_lcm_eq_inf d e] at hle
  exact (integerMultipleSubgroup_le_iff_dvd ((d.lcm e : ℕ) : ℤ) n).1 hle

namespace MultiplicativeIntegerValuation

variable {G : Type _} [Group G]

/-- The subgroup of valuation values attained by elements of a subgroup of the
valued group. -/
def subgroupValueSubgroup
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G) :
    Subgroup (Multiplicative ℤ) where
  carrier := {n | ∃ x : G, x ∈ S ∧ V.valuationHom x = n}
  one_mem' := ⟨1, S.one_mem, V.valuationHom.map_one⟩
  mul_mem' := by
    rintro a b ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
    exact ⟨x * y, S.mul_mem hx hy, V.valuationHom.map_mul x y⟩
  inv_mem' := by
    rintro a ⟨x, hx, rfl⟩
    exact ⟨x⁻¹, S.inv_mem hx, V.valuationHom.map_inv x⟩

/--
Characterizes `n ∈ V.subgroupValueSubgroup S` by the equivalent condition `∃ x : G, x ∈ S ∧
V.valuationHom x = n`.
-/
@[simp] theorem mem_subgroupValueSubgroup_iff
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G)
    (n : Multiplicative ℤ) :
    n ∈ V.subgroupValueSubgroup S ↔
      ∃ x : G, x ∈ S ∧ V.valuationHom x = n :=
  Iff.rfl

/-- Membership of `Multiplicative.ofAdd n` in a subgroup value image is exactly
the existence of an element of that subgroup whose valuation is `n`. -/
theorem ofAdd_mem_subgroupValueSubgroup_iff
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G) (n : ℤ) :
    Multiplicative.ofAdd n ∈ V.subgroupValueSubgroup S ↔
      ∃ x : G, x ∈ S ∧ V.val x = n := by
  rw [V.mem_subgroupValueSubgroup_iff S (Multiplicative.ofAdd n)]
  constructor
  · rintro ⟨x, hxS, hx⟩
    rw [V.valuationHom_apply] at hx
    exact ⟨x, hxS, Multiplicative.ofAdd.injective hx⟩
  · rintro ⟨x, hxS, hx⟩
    exact ⟨x, hxS, by rw [V.valuationHom_apply, hx]⟩

/-- Subgroup inclusion induces inclusion on the corresponding value images. -/
theorem subgroupValueSubgroup_mono
    (V : MultiplicativeIntegerValuation G) {S T : Subgroup G}
    (hST : S ≤ T) :
    V.subgroupValueSubgroup S ≤ V.subgroupValueSubgroup T := by
  intro n hn
  rw [V.mem_subgroupValueSubgroup_iff S n] at hn
  rw [V.mem_subgroupValueSubgroup_iff T n]
  rcases hn with ⟨x, hxS, hxn⟩
  exact ⟨x, hST hxS, hxn⟩

/-- A subgroup value image lies in an integer-multiple subgroup exactly when
every element of the source subgroup has valuation divisible by that integer. -/
theorem subgroupValueSubgroup_le_integerMultipleSubgroup_iff
    (V : MultiplicativeIntegerValuation G) (S : Subgroup G) (d : ℤ) :
    V.subgroupValueSubgroup S ≤ integerMultipleSubgroup d ↔
      ∀ x : G, x ∈ S → d ∣ V.val x := by
  constructor
  · intro h x hx
    have hxvalue : V.valuationHom x ∈ V.subgroupValueSubgroup S := by
      rw [V.mem_subgroupValueSubgroup_iff]
      exact ⟨x, hx, rfl⟩
    have hxmultiple := h hxvalue
    rw [mem_integerMultipleSubgroup_iff] at hxmultiple
    simpa
      [_root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.valuationHom]
      using hxmultiple
  · intro h n hn
    rw [V.mem_subgroupValueSubgroup_iff S n] at hn
    rcases hn with ⟨x, hx, rfl⟩
    rw [mem_integerMultipleSubgroup_iff]
    simpa
      [_root_.LocalFieldTheory.DiscreteValuationField.MultiplicativeIntegerValuation.valuationHom]
      using h x hx

/-- A lower value-step inclusion for a larger subgroup value image restricts to
any smaller subgroup value image. -/
theorem subgroupValueSubgroup_le_integerMultipleSubgroup_of_le
    (V : MultiplicativeIntegerValuation G) {S T : Subgroup G} {d : ℤ}
    (hST : S ≤ T)
    (hT : V.subgroupValueSubgroup T ≤ integerMultipleSubgroup d) :
    V.subgroupValueSubgroup S ≤ integerMultipleSubgroup d :=
  le_trans (V.subgroupValueSubgroup_mono hST) hT

/-- If a subgroup contains an element of valuation `n`, then the
integer-multiple subgroup generated by `n` lies in the subgroup's value image. -/
theorem integerMultipleSubgroup_le_subgroupValueSubgroup_of_exists_mem_val
    (V : MultiplicativeIntegerValuation G) {S : Subgroup G} {n : ℤ}
    (hn : ∃ x : G, x ∈ S ∧ V.val x = n) :
    integerMultipleSubgroup n ≤ V.subgroupValueSubgroup S := by
  rcases hn with ⟨x, hxS, hxval⟩
  intro m hm
  rw [mem_integerMultipleSubgroup_iff] at hm
  rcases hm with ⟨k, hk⟩
  rw [V.mem_subgroupValueSubgroup_iff]
  refine ⟨x ^ k, S.zpow_mem hxS k, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [V.valuationHom_apply, toAdd_ofAdd, V.val_zpow, hxval]
  exact (mul_comm k n).trans hk.symm

/-- Generator form of the subgroup-image lcm sandwich. -/
theorem int_lcm_dvd_of_exists_mem_val_of_subgroupValueSubgroup_le
    (V : MultiplicativeIntegerValuation G) {S : Subgroup G} {n d e : ℤ}
    (hn : ∃ x : G, x ∈ S ∧ V.val x = n)
    (hd : V.subgroupValueSubgroup S ≤ integerMultipleSubgroup d)
    (he : V.subgroupValueSubgroup S ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  int_lcm_dvd_of_integerMultipleSubgroup_le_of_le
    (le_trans
      (V.integerMultipleSubgroup_le_subgroupValueSubgroup_of_exists_mem_val hn)
      hd)
    (le_trans
      (V.integerMultipleSubgroup_le_subgroupValueSubgroup_of_exists_mem_val hn)
      he)

/-- Larger common-image form of the lcm sandwich. -/
theorem int_lcm_dvd_of_exists_mem_val_of_le_of_subgroupValueSubgroup_le
    (V : MultiplicativeIntegerValuation G) {S T : Subgroup G} {n d e : ℤ}
    (hn : ∃ x : G, x ∈ S ∧ V.val x = n)
    (hST : S ≤ T)
    (hd : V.subgroupValueSubgroup T ≤ integerMultipleSubgroup d)
    (he : V.subgroupValueSubgroup T ≤ integerMultipleSubgroup e) :
    ((d.lcm e : ℕ) : ℤ) ∣ n :=
  V.int_lcm_dvd_of_exists_mem_val_of_subgroupValueSubgroup_le hn
    (V.subgroupValueSubgroup_le_integerMultipleSubgroup_of_le hST hd)
    (V.subgroupValueSubgroup_le_integerMultipleSubgroup_of_le hST he)

end MultiplicativeIntegerValuation

end DiscreteValuationField

end

end LocalFieldTheory
