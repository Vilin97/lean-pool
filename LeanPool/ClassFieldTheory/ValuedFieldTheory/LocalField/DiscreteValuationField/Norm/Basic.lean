/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.Units
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.GroupTheory.IntegerMultipleSubgroup

/-! # Basic -/

@[expose] public section
namespace LocalFieldTheory

/-!
# Integer-valued norm data

This file contains the norm-subgroup lemmas used in local CFT from an abstract
integer-valued multiplicative valuation and a norm homomorphism satisfying the
standard valuation formula.
-/

noncomputable
section

universe u v

namespace DiscreteValuationField

/-- A multiplicative group valuation with values in additive integers. -/
structure MultiplicativeIntegerValuation (G : Type u) [Group G] where
  /-- The integer valuation of a group element. -/
  val : G → ℤ
  /-- The identity has valuation zero. -/
  map_one : val 1 = 0
  /-- Valuation turns multiplication into integer addition. -/
  map_mul : ∀ x y : G, val (x * y) = val x + val y

namespace MultiplicativeIntegerValuation

variable {G : Type u} [Group G] (V : MultiplicativeIntegerValuation G)

/-- Establishes the identity `V.val (1 : G) = 0`. -/
@[simp] theorem val_one : V.val (1 : G) = 0 :=
  V.map_one

/-- `val` satisfies the multiplication formula `V.val (x * y) = V.val x + V.val y`. -/
@[simp] theorem val_mul (x y : G) :
    V.val (x * y) = V.val x + V.val y :=
  V.map_mul x y

/-- The integer-valued valuation as a multiplicative homomorphism to the
additive group of integers written multiplicatively. -/
def valuationHom : G →* Multiplicative ℤ where
  toFun x := Multiplicative.ofAdd (V.val x)
  map_one' := by
    simp [V.val_one]
  map_mul' x y := by
    rw [V.val_mul, ofAdd_add]

/--
The defining evaluation formula for `valuationHom` is `V.valuationHom x = Multiplicative.ofAdd
(V.val x)`.
-/
@[simp] theorem valuationHom_apply (x : G) :
    V.valuationHom x = Multiplicative.ofAdd (V.val x) :=
  rfl

/-- Characterizes `x ∈ V.valuationHom.ker` by the equivalent condition `V.val x = 0`. -/
theorem mem_valuationHom_ker_iff (x : G) :
    x ∈ V.valuationHom.ker ↔ V.val x = 0 := by
  change V.valuationHom x = 1 ↔ V.val x = 0
  rw [V.valuationHom_apply]
  constructor
  · intro hx
    exact Multiplicative.ofAdd.injective (by simpa using hx)
  · intro hx
    rw [hx]
    simp

/-- `val` satisfies the inverse formula `V.val x⁻¹ = -V.val x`. -/
@[simp] theorem val_inv (x : G) :
    V.val x⁻¹ = -V.val x := by
  have h := V.map_mul x x⁻¹
  have h' : V.val x + V.val x⁻¹ = 0 := by
    simpa [V.map_one] using h.symm
  exact eq_neg_iff_add_eq_zero.2 (by simpa [add_comm] using h')

/-- `val` satisfies the division formula `V.val (x / y) = V.val x - V.val y`. -/
@[simp] theorem val_div (x y : G) :
    V.val (x / y) = V.val x - V.val y := by
  rw [div_eq_mul_inv, V.val_mul, V.val_inv, sub_eq_add_neg]

/-- `val` satisfies the natural-power formula `V.val (x ^ n) = (n : ℤ) * V.val x`. -/
@[simp] theorem val_pow (x : G) (n : ℕ) :
    V.val (x ^ n) = (n : ℤ) * V.val x := by
  induction n with
  | zero =>
      rw [pow_zero, V.val_one]
      simp
  | succ n ih =>
      calc
        V.val (x ^ Nat.succ n) = V.val (x ^ n * x) := by
            rw [pow_succ]
        _ = V.val (x ^ n) + V.val x := V.val_mul _ _
        _ = (n : ℤ) * V.val x + V.val x := by
            rw [ih]
        _ = ((n : ℤ) + 1) * V.val x := by
            rw [add_mul, one_mul]
        _ = (Nat.succ n : ℤ) * V.val x := by
            rw [Nat.cast_succ]

/-- `val` satisfies the integer-power formula `V.val (x ^ n) = n * V.val x`. -/
@[simp] theorem val_zpow (x : G) (n : ℤ) :
    V.val (x ^ n) = n * V.val x := by
  cases n with
  | ofNat n =>
      rw [Int.ofNat_eq_natCast, zpow_natCast, V.val_pow]
  | negSucc n =>
      rw [zpow_negSucc, V.val_inv, V.val_pow]
      change -(((n + 1 : ℕ) : ℤ) * V.val x) =
        -(((n + 1 : ℕ) : ℤ)) * V.val x
      rw [neg_mul]

/-- Establishes the identity `V.val x⁻¹ = 0`. -/
theorem val_inv_eq_zero_of_val_eq_zero {x : G} (hx : V.val x = 0) :
    V.val x⁻¹ = 0 := by
  rw [V.val_inv, hx, neg_zero]

/-- Characterizes `V.val (x / y) = 0` by the equivalent condition `V.val x = V.val y`. -/
theorem val_div_eq_zero_iff (x y : G) :
    V.val (x / y) = 0 ↔ V.val x = V.val y := by
  rw [V.val_div]
  constructor
  · exact sub_eq_zero.mp
  · exact sub_eq_zero.mpr

/-- Characterizes `V.val (x ^ n) = 0` by the equivalent condition `V.val x = 0`. -/
theorem val_pow_eq_zero_iff_of_ne_zero (x : G) {n : ℕ} (hn : n ≠ 0) :
    V.val (x ^ n) = 0 ↔ V.val x = 0 := by
  rw [V.val_pow]
  have hn' : (n : ℤ) ≠ 0 := Int.ofNat_ne_zero.mpr hn
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hn'
  · intro hx
    rw [hx, mul_zero]

/-- Establishes the identity `V.val x = 0`. -/
theorem val_eq_zero_of_pow_eq_one (x : G) {n : ℕ}
    (hn : n ≠ 0) (hpow : x ^ n = 1) :
    V.val x = 0 := by
  have hv : V.val (x ^ n) = 0 := by rw [hpow, V.val_one]
  exact (V.val_pow_eq_zero_iff_of_ne_zero x hn).1 hv

/-- Characterizes `V.val (x ^ n) = 0` by the equivalent condition `V.val x = 0`. -/
theorem val_zpow_eq_zero_iff_of_ne_zero (x : G) {n : ℤ} (hn : n ≠ 0) :
    V.val (x ^ n) = 0 ↔ V.val x = 0 := by
  rw [V.val_zpow]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left hn
  · intro hx
    rw [hx, mul_zero]

/-- Establishes the identity `V.val x = 0`. -/
theorem val_eq_zero_of_zpow_eq_one (x : G) {n : ℤ}
    (hn : n ≠ 0) (hpow : x ^ n = 1) :
    V.val x = 0 := by
  have hv : V.val (x ^ n) = 0 := by rw [hpow, V.val_one]
  exact (V.val_zpow_eq_zero_iff_of_ne_zero x hn).1 hv

/-- Elements of valuation zero. -/
def zeroSubgroup : Subgroup G where
  carrier := {x | V.val x = 0}
  one_mem' := by simp [V.map_one]
  mul_mem' := by
    intro x y hx hy
    change V.val (x * y) = 0
    rw [V.map_mul, hx, hy, add_zero]
  inv_mem' := by
    intro x hx
    exact V.val_inv_eq_zero_of_val_eq_zero hx

/-- Characterizes `x ∈ V.zeroSubgroup` by the equivalent condition `V.val x = 0`. -/
@[simp] theorem mem_zeroSubgroup_iff (x : G) :
    x ∈ V.zeroSubgroup ↔ V.val x = 0 :=
  Iff.rfl

/-- Establishes the identity `V.valuationHom.ker = V.zeroSubgroup`. -/
theorem valuationHom_ker_eq_zeroSubgroup :
    V.valuationHom.ker = V.zeroSubgroup := by
  ext x
  rw [V.mem_valuationHom_ker_iff, V.mem_zeroSubgroup_iff]

/-- The subgroup appearing in `(V.zeroSubgroup).Normal` is normal. -/
instance zeroSubgroup_normal : (V.zeroSubgroup).Normal := by
  rw [← V.valuationHom_ker_eq_zeroSubgroup]
  infer_instance

/-- The value subgroup of an integer-valued valuation.  It is the range of the
valuation homomorphism `valuationHom`. -/
def valueSubgroup : Subgroup (Multiplicative ℤ) :=
  V.valuationHom.range

/--
Characterizes `n ∈ V.valueSubgroup` by the equivalent condition `∃ x : G, V.valuationHom x = n`.
-/
@[simp] theorem mem_valueSubgroup_iff (n : Multiplicative ℤ) :
    n ∈ V.valueSubgroup ↔ ∃ x : G, V.valuationHom x = n :=
  Iff.rfl

/--
Characterizes `Multiplicative.ofAdd n ∈ V.valueSubgroup` by the equivalent condition `∃ x : G,
V.val x = n`.
-/
theorem ofAdd_mem_valueSubgroup_iff (n : ℤ) :
    Multiplicative.ofAdd n ∈ V.valueSubgroup ↔ ∃ x : G, V.val x = n := by
  rw [V.mem_valueSubgroup_iff (Multiplicative.ofAdd n)]
  constructor
  · rintro ⟨x, hx⟩
    rw [V.valuationHom_apply] at hx
    exact ⟨x, Multiplicative.ofAdd.injective hx⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, by rw [V.valuationHom_apply, hx]⟩

/-- Establishes the membership statement `Multiplicative.ofAdd n ∈ V.valueSubgroup`. -/
theorem ofAdd_mem_valueSubgroup_of_exists_val {n : ℤ}
    (hn : ∃ x : G, V.val x = n) :
    Multiplicative.ofAdd n ∈ V.valueSubgroup :=
  (V.ofAdd_mem_valueSubgroup_iff n).2 hn

/-- Establishes the identity `∃ x : G, V.val x = n`. -/
theorem exists_val_of_ofAdd_mem_valueSubgroup {n : ℤ}
    (hn : Multiplicative.ofAdd n ∈ V.valueSubgroup) :
    ∃ x : G, V.val x = n :=
  (V.ofAdd_mem_valueSubgroup_iff n).1 hn

/--
Characterizes `Function.Surjective V.valuationHom` by the equivalent condition
`Function.Surjective V.val`.
-/
theorem valuationHom_surjective_iff :
    Function.Surjective V.valuationHom ↔ Function.Surjective V.val := by
  constructor
  · intro hV n
    rcases hV (Multiplicative.ofAdd n) with ⟨x, hx⟩
    rw [V.valuationHom_apply] at hx
    exact ⟨x, Multiplicative.ofAdd.injective hx⟩
  · intro hV n
    rcases hV (Multiplicative.toAdd n) with ⟨x, hx⟩
    exact ⟨x, by rw [V.valuationHom_apply, hx, ofAdd_toAdd]⟩

/-- Establishes the identity `V.valueSubgroup = ⊤`. -/
theorem valueSubgroup_eq_top_of_surjective (hV : Function.Surjective V.val) :
    V.valueSubgroup = ⊤ := by
  ext n
  constructor
  · intro hn
    trivial
  · intro hn
    rcases hV (Multiplicative.toAdd n) with ⟨x, hx⟩
    rw [V.mem_valueSubgroup_iff n]
    exact ⟨x, by rw [V.valuationHom_apply, hx, ofAdd_toAdd]⟩

/-- First-isomorphism-theorem form for an integer-valued valuation:
the quotient by valuation-zero elements is the value subgroup. -/
noncomputable def quotientZeroSubgroupEquivValueSubgroup :
    G ⧸ V.zeroSubgroup ≃* V.valueSubgroup :=
  (QuotientGroup.quotientMulEquivOfEq
      (V.valuationHom_ker_eq_zeroSubgroup).symm).trans
    (QuotientGroup.quotientKerEquivRange V.valuationHom)

/--
Establishes the identity `V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup x) = V.valuationHom.rangeRestrict x`.
-/
theorem quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) =
      V.valuationHom.rangeRestrict x :=
  rfl

/--
Establishes the identity `((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup x) : V.valueSubgroup) : Multiplicative ℤ) = Multiplicative.ofAdd (V.val x)`.
-/
theorem coe_quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
      Multiplicative ℤ) =
      Multiplicative.ofAdd (V.val x) := by
  rw [V.quotientZeroSubgroupEquivValueSubgroup_mk]
  rfl

/--
Establishes the identity `Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) : Multiplicative ℤ)) = V.val x`.
-/
theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_mk (x : G) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
        Multiplicative ℤ)) = V.val x := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk, toAdd_ofAdd]

/--
Establishes the identity `Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) : Multiplicative ℤ)) = V.val x -
V.val y`.
-/
theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_div_mk
    (x y : G) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) :
        Multiplicative ℤ)) = V.val x - V.val y := by
  rw [V.toAdd_quotientZeroSubgroupEquivValueSubgroup_mk, V.val_div]

/--
Characterizes `((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk' V.zeroSubgroup x) :
V.valueSubgroup) : Multiplicative ℤ) ∈ integerMultipleSubgroup d` by the equivalent condition `d ∣
V.val x`.
-/
theorem quotientZeroSubgroup_value_mem_integerMultipleSubgroup_iff
    (d : ℤ) (x : G) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
      Multiplicative ℤ) ∈ integerMultipleSubgroup d ↔ d ∣ V.val x := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk,
    ofAdd_mem_integerMultipleSubgroup_iff]

/--
Characterizes `((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk' V.zeroSubgroup (x /
y)) : V.valueSubgroup) : Multiplicative ℤ) ∈ integerMultipleSubgroup d` by the equivalent
condition `d ∣ V.val x - V.val y`.
-/
theorem quotientZeroSubgroup_value_div_mem_integerMultipleSubgroup_iff
    (d : ℤ) (x y : G) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) :
      Multiplicative ℤ) ∈ integerMultipleSubgroup d ↔
      d ∣ V.val x - V.val y := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk,
    ofAdd_mem_integerMultipleSubgroup_iff, V.val_div]

/--
Establishes the membership statement `((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) : Multiplicative ℤ) ∈
integerMultipleSubgroup d`.
-/
theorem quotientZeroSubgroup_value_mem_integerMultipleSubgroup_of_dvd_val
    {d : ℤ} {x : G} (hx : d ∣ V.val x) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
      Multiplicative ℤ) ∈ integerMultipleSubgroup d :=
  (V.quotientZeroSubgroup_value_mem_integerMultipleSubgroup_iff d x).2 hx

/-- Establishes the divisibility statement `d ∣ V.val x`. -/
theorem dvd_val_of_quotientZeroSubgroup_value_mem_integerMultipleSubgroup
    {d : ℤ} {x : G}
    (hx :
      ((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup x) : V.valueSubgroup) :
        Multiplicative ℤ) ∈ integerMultipleSubgroup d) :
    d ∣ V.val x :=
  (V.quotientZeroSubgroup_value_mem_integerMultipleSubgroup_iff d x).1 hx

/--
Establishes the membership statement `((V.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) : Multiplicative ℤ) ∈
integerMultipleSubgroup d`.
-/
theorem quotientZeroSubgroup_value_div_mem_integerMultipleSubgroup_of_dvd
    {d : ℤ} {x y : G} (hxy : d ∣ V.val x - V.val y) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) :
      Multiplicative ℤ) ∈ integerMultipleSubgroup d :=
  (V.quotientZeroSubgroup_value_div_mem_integerMultipleSubgroup_iff d x y).2 hxy

/-- Establishes the divisibility statement `d ∣ V.val x - V.val y`. -/
theorem dvd_of_quotientZeroSubgroup_value_div_mem_integerMultipleSubgroup
    {d : ℤ} {x y : G}
    (hxy :
      ((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup (x / y)) : V.valueSubgroup) :
        Multiplicative ℤ) ∈ integerMultipleSubgroup d) :
    d ∣ V.val x - V.val y :=
  (V.quotientZeroSubgroup_value_div_mem_integerMultipleSubgroup_iff d x y).1 hxy

/-- If the valuation is surjective, the quotient by valuation-zero elements is
the full multiplicative copy of `ℤ`. -/
noncomputable def quotientZeroSubgroupEquivMultiplicativeInt
    (hV : Function.Surjective V.val) :
    G ⧸ V.zeroSubgroup ≃* Multiplicative ℤ :=
  V.quotientZeroSubgroupEquivValueSubgroup.trans
    ((MulEquiv.subgroupCongr (V.valueSubgroup_eq_top_of_surjective hV)).trans
      Subgroup.topEquiv)

/-- A multiplicative element of valuation one. -/
def IsUniformizer (ϖ : G) : Prop :=
  V.val ϖ = 1

/-- Existence of a multiplicative element of valuation one. -/
def HasUniformizer : Prop :=
  ∃ ϖ : G, V.IsUniformizer ϖ

/-- A surjective integer valuation has an element of valuation one. -/
theorem hasUniformizer_of_surjective (hV : Function.Surjective V.val) :
    V.HasUniformizer := by
  rcases hV 1 with ⟨ϖ, hϖ⟩
  exact ⟨ϖ, hϖ⟩

/-- Surjectivity of the integer valuation yields a uniformizer. -/
theorem exists_uniformizer_of_surjective (hV : Function.Surjective V.val) :
    ∃ ϖ : G, V.IsUniformizer ϖ :=
  V.hasUniformizer_of_surjective hV

/-- `val_uniformizer` satisfies the integer-power formula `V.val (ϖ ^ n) = n`. -/
theorem val_uniformizer_zpow {ϖ : G} (hϖ : V.IsUniformizer ϖ)
    (n : ℤ) :
    V.val (ϖ ^ n) = n := by
  rw [V.val_zpow, hϖ, mul_one]

/-- `val_uniformizer` satisfies the natural-power formula `V.val (ϖ ^ n) = (n : ℤ)`. -/
theorem val_uniformizer_pow {ϖ : G} (hϖ : V.IsUniformizer ϖ)
    (n : ℕ) :
    V.val (ϖ ^ n) = (n : ℤ) := by
  simpa using V.val_uniformizer_zpow hϖ (n : ℤ)

/-- Characterizes `ϖ ^ n ∈ V.zeroSubgroup` by the equivalent condition `n = 0`. -/
theorem uniformizer_zpow_mem_zeroSubgroup_iff {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    ϖ ^ n ∈ V.zeroSubgroup ↔ n = 0 := by
  rw [V.mem_zeroSubgroup_iff, V.val_uniformizer_zpow hϖ n]

/-- Characterizes `ϖ ^ n ∈ V.zeroSubgroup` by the equivalent condition `n = 0`. -/
theorem uniformizer_pow_mem_zeroSubgroup_iff {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (n : ℕ) :
    ϖ ^ n ∈ V.zeroSubgroup ↔ n = 0 := by
  rw [V.mem_zeroSubgroup_iff, V.val_uniformizer_pow hϖ n]
  exact Int.ofNat_eq_zero

/-- The specified map is surjective: `Function.Surjective V.val`. -/
theorem val_surjective_of_uniformizer {ϖ : G} (hϖ : V.IsUniformizer ϖ) :
    Function.Surjective V.val := by
  intro n
  exact ⟨ϖ ^ n, V.val_uniformizer_zpow hϖ n⟩

/-- Characterizes `V.HasUniformizer` by the equivalent condition `Function.Surjective V.val`. -/
theorem hasUniformizer_iff_val_surjective :
    V.HasUniformizer ↔ Function.Surjective V.val := by
  constructor
  · rintro ⟨ϖ, hϖ⟩
    exact V.val_surjective_of_uniformizer hϖ
  · exact V.hasUniformizer_of_surjective

/-- Establishes the identity `V.valueSubgroup = ⊤`. -/
theorem valueSubgroup_eq_top_of_uniformizer {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) :
    V.valueSubgroup = ⊤ :=
  V.valueSubgroup_eq_top_of_surjective
    (V.val_surjective_of_uniformizer hϖ)

/-- Uniformizer form of the quotient equivalence `G / G⁰ ≃ Multiplicative ℤ`.
The uniformizer proves that the value group is all of `ℤ`. -/
noncomputable def quotientZeroSubgroupEquivMultiplicativeIntOfUniformizer
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) :
    G ⧸ V.zeroSubgroup ≃* Multiplicative ℤ :=
  V.quotientZeroSubgroupEquivMultiplicativeInt
    (V.val_surjective_of_uniformizer hϖ)

/--
`coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer` satisfies the integer-power formula
`((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) :
V.valueSubgroup) : Multiplicative ℤ) = Multiplicative.ofAdd n`.
-/
theorem coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    ((V.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) :
      Multiplicative ℤ) = Multiplicative.ofAdd n := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_mk,
    V.val_uniformizer_zpow hϖ n]

/--
`toAdd_quotientZeroSubgroupEquivValueSubgroup_uniformizer` satisfies the integer-power formula
`Multiplicative.toAdd (((V.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) : Multiplicative ℤ)) = n`.
-/
theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow
    {ϖ : G} (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    Multiplicative.toAdd
      (((V.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' V.zeroSubgroup (ϖ ^ n)) : V.valueSubgroup) :
        Multiplicative ℤ)) = n := by
  rw [V.coe_quotientZeroSubgroupEquivValueSubgroup_uniformizer_zpow hϖ n,
    toAdd_ofAdd]

/-- A representative-level decomposition `x = u * ϖ^n`, with `u` of valuation
zero.  This is the abstract multiplicative form of `Kˣ = O_Kˣ · ϖ^ℤ`. -/
structure UnitUniformizerDecomposition (ϖ x : G) where
  /-- The valuation-zero factor. -/
  unitPart : G
  /-- The unit factor has valuation zero. -/
  unit_mem : unitPart ∈ V.zeroSubgroup
  /-- The exponent of the chosen uniformizer. -/
  exponent : ℤ
  /-- Reconstruction from the unit factor and uniformizer power. -/
  eq_unit_mul_zpow : x = unitPart * ϖ ^ exponent

/-- Every element admits a unit-uniformizer decomposition with respect to `ϖ`. -/
def HasUnitUniformizerDecomposition (ϖ : G) : Prop :=
  ∀ x : G, Nonempty (V.UnitUniformizerDecomposition ϖ x)

/-- The canonical unit-uniformizer decomposition attached to a uniformizer. -/
def canonicalUnitUniformizerDecomposition {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    V.UnitUniformizerDecomposition ϖ x where
  unitPart := x * ϖ ^ (-(V.val x))
  unit_mem := by
    rw [V.mem_zeroSubgroup_iff, V.val_mul, V.val_zpow, hϖ]
    ring
  exponent := V.val x
  eq_unit_mul_zpow := by
    calc
      x = x * 1 := by rw [mul_one]
      _ = x * (ϖ ^ (-(V.val x)) * ϖ ^ V.val x) := by
        rw [← zpow_add, neg_add_cancel, zpow_zero]
      _ = (x * ϖ ^ (-(V.val x))) * ϖ ^ V.val x := by
        rw [mul_assoc]

/--
A chosen uniformizer gives a unit-times-uniformizer-power decomposition of every group element.
-/
theorem hasUnitUniformizerDecomposition_of_uniformizer {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) :
    V.HasUnitUniformizerDecomposition ϖ := by
  intro x
  exact ⟨V.canonicalUnitUniformizerDecomposition hϖ x⟩

/--
Every group element has a unit-times-uniformizer-power decomposition relative to a chosen
uniformizer.
-/
theorem unitUniformizerDecomposition {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    Nonempty (V.UnitUniformizerDecomposition ϖ x) :=
  V.hasUnitUniformizerDecomposition_of_uniformizer hϖ x

/--
`exists_zeroSubgroup_mul_uniformizer` satisfies the integer-power formula `∃ u : G, u ∈
V.zeroSubgroup ∧ ∃ n : ℤ, x = u * ϖ ^ n`.
-/
theorem exists_zeroSubgroup_mul_uniformizer_zpow {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ ∃ n : ℤ, x = u * ϖ ^ n := by
  rcases V.unitUniformizerDecomposition hϖ x with ⟨d⟩
  exact ⟨d.unitPart, d.unit_mem, d.exponent, d.eq_unit_mul_zpow⟩

/-- Establishes the identity `∃ u : G, u ∈ V.zeroSubgroup ∧ u * ϖ ^ V.val x = x`. -/
theorem exists_zeroSubgroup_mul_uniformizer_zpow_eq {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ u * ϖ ^ V.val x = x := by
  let d := V.canonicalUnitUniformizerDecomposition hϖ x
  exact ⟨d.unitPart, d.unit_mem, d.eq_unit_mul_zpow.symm⟩

/--
Characterizes `V.val x = n` by the equivalent condition `∃ u : G, u ∈ V.zeroSubgroup ∧ u * ϖ ^ n =
x`.
-/
theorem val_eq_iff_exists_zeroSubgroup_mul_uniformizer_zpow {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) (n : ℤ) :
    V.val x = n ↔ ∃ u : G, u ∈ V.zeroSubgroup ∧ u * ϖ ^ n = x := by
  constructor
  · intro hx
    refine ⟨x * (ϖ ^ n)⁻¹, ?_, ?_⟩
    · rw [V.mem_zeroSubgroup_iff, V.val_mul, V.val_inv,
        V.val_uniformizer_zpow hϖ n, hx]
      ring
    · rw [mul_assoc, inv_mul_cancel, mul_one]
  · rintro ⟨u, hu, hux⟩
    rw [← hux, V.val_mul, (V.mem_zeroSubgroup_iff u).1 hu,
      V.val_uniformizer_zpow hϖ n, zero_add]

/--
Characterizes `V.val x = n` by the equivalent condition `∃ u : G, u ∈ V.zeroSubgroup ∧ x = u * ϖ ^
n`.
-/
theorem val_eq_iff_exists_eq_zeroSubgroup_mul_uniformizer_zpow {ϖ : G}
    (hϖ : V.IsUniformizer ϖ) (x : G) (n : ℤ) :
    V.val x = n ↔ ∃ u : G, u ∈ V.zeroSubgroup ∧ x = u * ϖ ^ n := by
  constructor
  · intro hx
    rcases (V.val_eq_iff_exists_zeroSubgroup_mul_uniformizer_zpow hϖ x n).1 hx
      with ⟨u, hu, hux⟩
    exact ⟨u, hu, hux.symm⟩
  · rintro ⟨u, hu, hx⟩
    rw [hx, V.val_mul, (V.mem_zeroSubgroup_iff u).1 hu,
      V.val_uniformizer_zpow hϖ n]
    ring

namespace UnitUniformizerDecomposition

variable {V : MultiplicativeIntegerValuation G} {ϖ x : G}

/-- Establishes the identity `V.val d.unitPart = 0`. -/
@[simp] theorem unitPart_val_zero
    (d : V.UnitUniformizerDecomposition ϖ x) :
    V.val d.unitPart = 0 :=
  (V.mem_zeroSubgroup_iff d.unitPart).1 d.unit_mem

/-- The valuation of the represented element is the exponent when `ϖ` is a
uniformizer. -/
theorem val_eq_exponent (hϖ : V.IsUniformizer ϖ)
    (d : V.UnitUniformizerDecomposition ϖ x) :
    V.val x = d.exponent := by
  calc
    V.val x = V.val (d.unitPart * ϖ ^ d.exponent) := by
      exact congrArg V.val d.eq_unit_mul_zpow
    _ = V.val d.unitPart + V.val (ϖ ^ d.exponent) := by
      rw [V.val_mul]
    _ = 0 + V.val (ϖ ^ d.exponent) := by
      rw [unitPart_val_zero d]
    _ = 0 + d.exponent := by
      rw [V.val_uniformizer_zpow hϖ d.exponent]
    _ = d.exponent := by
      rw [zero_add]

/-- The unit part is recovered from the represented element and the recorded
exponent. -/
theorem unitPart_eq_mul_inv_zpow
    (d : V.UnitUniformizerDecomposition ϖ x) :
    d.unitPart = x * (ϖ ^ d.exponent)⁻¹ := by
  calc
    d.unitPart =
        (d.unitPart * ϖ ^ d.exponent) * (ϖ ^ d.exponent)⁻¹ := by
      rw [mul_assoc, mul_inv_cancel, mul_one]
    _ = x * (ϖ ^ d.exponent)⁻¹ := by
      rw [← d.eq_unit_mul_zpow]

/-- If two decompositions use the same exponent, then their unit parts agree. -/
theorem unitPart_unique_of_exponent_eq
    (d₁ d₂ : V.UnitUniformizerDecomposition ϖ x)
    (h : d₁.exponent = d₂.exponent) :
    d₁.unitPart = d₂.unitPart := by
  rw [unitPart_eq_mul_inv_zpow d₁, unitPart_eq_mul_inv_zpow d₂, h]

/-- The exponent in a unit-uniformizer decomposition is unique. -/
theorem exponent_unique (hϖ : V.IsUniformizer ϖ)
    (d₁ d₂ : V.UnitUniformizerDecomposition ϖ x) :
    d₁.exponent = d₂.exponent := by
  calc
    d₁.exponent = V.val x := (val_eq_exponent hϖ d₁).symm
    _ = d₂.exponent := val_eq_exponent hϖ d₂

/-- The unit part in a unit-uniformizer decomposition is unique once the
uniformizer is fixed. -/
theorem unitPart_unique (hϖ : V.IsUniformizer ϖ)
    (d₁ d₂ : V.UnitUniformizerDecomposition ϖ x) :
    d₁.unitPart = d₂.unitPart :=
  unitPart_unique_of_exponent_eq d₁ d₂ (exponent_unique hϖ d₁ d₂)

/-- A valuation-zero multiple of a uniformizer power has valuation equal to
the exponent. -/
theorem val_unit_mul_zpow (hϖ : V.IsUniformizer ϖ)
    {u : G} (hu : u ∈ V.zeroSubgroup) (n : ℤ) :
    V.val (u * ϖ ^ n) = n := by
  rw [V.val_mul, (V.mem_zeroSubgroup_iff u).1 hu,
    V.val_uniformizer_zpow hϖ n, zero_add]

/-- A uniformizer power has valuation equal to its exponent. -/
theorem val_uniformizer_zpow (hϖ : V.IsUniformizer ϖ) (n : ℤ) :
    V.val (ϖ ^ n) = n :=
  V.val_uniformizer_zpow hϖ n

/-- A natural power of a uniformizer has valuation equal to the natural
exponent. -/
theorem val_uniformizer_pow (hϖ : V.IsUniformizer ϖ) (n : ℕ) :
    V.val (ϖ ^ n) = (n : ℤ) :=
  V.val_uniformizer_pow hϖ n

/-- Equality of two unit-uniformizer normal forms forces equality of
exponents. -/
theorem exponent_unique_of_unit_mul_eq (hϖ : V.IsUniformizer ϖ)
    {u w : G} (hu : u ∈ V.zeroSubgroup) (hw : w ∈ V.zeroSubgroup)
    {m n : ℤ} (h : u * ϖ ^ m = w * ϖ ^ n) :
    m = n := by
  have hv := congrArg V.val h
  rw [val_unit_mul_zpow hϖ hu m, val_unit_mul_zpow hϖ hw n] at hv
  exact hv

/-- Equality of two unit-uniformizer normal forms is equivalent to equality of
both the unit part and exponent. -/
theorem unit_mul_zpow_eq_iff (hϖ : V.IsUniformizer ϖ)
    {u w : G} (hu : u ∈ V.zeroSubgroup) (hw : w ∈ V.zeroSubgroup)
    {m n : ℤ} :
    u * ϖ ^ m = w * ϖ ^ n ↔ u = w ∧ m = n := by
  constructor
  · intro h
    have hmn : m = n :=
      exponent_unique_of_unit_mul_eq hϖ hu hw h
    have huw : u = w := by
      calc
        u = (u * ϖ ^ m) * (ϖ ^ m)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
        _ = (w * ϖ ^ n) * (ϖ ^ m)⁻¹ := by
          rw [h]
        _ = (w * ϖ ^ m) * (ϖ ^ m)⁻¹ := by
          rw [hmn]
        _ = w := by
          rw [mul_assoc, mul_inv_cancel, mul_one]
    exact ⟨huw, hmn⟩
  · rintro ⟨huw, hmn⟩
    rw [huw, hmn]

/-- Equality of two unit-uniformizer normal forms is equivalent to equality of
exponents together with equality of unit parts. -/
theorem unit_mul_zpow_eq_iff_exponent_eq_and_unit_eq
    (hϖ : V.IsUniformizer ϖ)
    {u w : G} (hu : u ∈ V.zeroSubgroup) (hw : w ∈ V.zeroSubgroup)
    {m n : ℤ} :
    u * ϖ ^ m = w * ϖ ^ n ↔ m = n ∧ u = w := by
  rw [unit_mul_zpow_eq_iff hϖ hu hw]
  constructor
  · rintro ⟨huw, hmn⟩
    exact ⟨hmn, huw⟩
  · rintro ⟨hmn, huw⟩
    exact ⟨huw, hmn⟩

end UnitUniformizerDecomposition

/-- Establishes the identity `d₁.exponent = d₂.exponent`. -/
theorem uniformizer_exponent_unique {ϖ x : G}
    (hϖ : V.IsUniformizer ϖ)
    (d₁ d₂ : V.UnitUniformizerDecomposition ϖ x) :
    d₁.exponent = d₂.exponent :=
  UnitUniformizerDecomposition.exponent_unique hϖ d₁ d₂

/-- Establishes the identity `d₁.unitPart = d₂.unitPart`. -/
theorem uniformizer_unitPart_unique {ϖ x : G}
    (hϖ : V.IsUniformizer ϖ)
    (d₁ d₂ : V.UnitUniformizerDecomposition ϖ x) :
    d₁.unitPart = d₂.unitPart :=
  UnitUniformizerDecomposition.unitPart_unique hϖ d₁ d₂

/-- Establishes the identity `V.val (u * ϖ ^ n) = n`. -/
theorem valuation_uniformizer_normal_form {ϖ u : G}
    (hϖ : V.IsUniformizer ϖ) (hu : u ∈ V.zeroSubgroup) (n : ℤ) :
    V.val (u * ϖ ^ n) = n :=
  UnitUniformizerDecomposition.val_unit_mul_zpow hϖ hu n

/-- Characterizes `u * ϖ ^ m = w * ϖ ^ n` by the equivalent condition `u = w ∧ m = n`. -/
theorem unit_uniformizer_normal_form_eq_iff {ϖ u w : G}
    (hϖ : V.IsUniformizer ϖ) (hu : u ∈ V.zeroSubgroup)
    (hw : w ∈ V.zeroSubgroup) {m n : ℤ} :
    u * ϖ ^ m = w * ϖ ^ n ↔ u = w ∧ m = n :=
  UnitUniformizerDecomposition.unit_mul_zpow_eq_iff hϖ hu hw

/-- Establishes the membership statement `x * y ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_mul_mem {x y : G}
    (hx : x ∈ V.zeroSubgroup) (hy : y ∈ V.zeroSubgroup) :
    x * y ∈ V.zeroSubgroup :=
  V.zeroSubgroup.mul_mem hx hy

/-- Establishes the membership statement `x⁻¹ ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_inv_mem {x : G} (hx : x ∈ V.zeroSubgroup) :
    x⁻¹ ∈ V.zeroSubgroup :=
  V.zeroSubgroup.inv_mem hx

/-- Establishes the membership statement `x / y ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_div_mem {x y : G}
    (hx : x ∈ V.zeroSubgroup) (hy : y ∈ V.zeroSubgroup) :
    x / y ∈ V.zeroSubgroup := by
  simpa [div_eq_mul_inv] using
    V.zeroSubgroup_mul_mem hx (V.zeroSubgroup_inv_mem hy)

/-- Characterizes `x / y ∈ V.zeroSubgroup` by the equivalent condition `V.val x = V.val y`. -/
theorem div_mem_zeroSubgroup_iff (x y : G) :
    x / y ∈ V.zeroSubgroup ↔ V.val x = V.val y := by
  rw [MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V (x / y),
    V.val_div_eq_zero_iff]

/-- Establishes the identity `V.val x = V.val y`. -/
theorem val_eq_of_div_mem_zeroSubgroup {x y : G}
    (hxy : x / y ∈ V.zeroSubgroup) :
    V.val x = V.val y :=
  (V.div_mem_zeroSubgroup_iff x y).1 hxy

/-- Establishes the membership statement `x / y ∈ V.zeroSubgroup`. -/
theorem div_mem_zeroSubgroup_of_val_eq {x y : G} (hxy : V.val x = V.val y) :
    x / y ∈ V.zeroSubgroup :=
  (V.div_mem_zeroSubgroup_iff x y).2 hxy

/-- In the valuation-zero subgroup, the right quotient `x / y` and the left
quotient `y⁻¹ * x` give the same membership test. -/
theorem div_mem_zeroSubgroup_iff_inv_mul_mem_zeroSubgroup (x y : G) :
    x / y ∈ V.zeroSubgroup ↔ y⁻¹ * x ∈ V.zeroSubgroup := by
  simpa [div_eq_mul_inv] using
    ((inferInstance : (V.zeroSubgroup).Normal).mem_comm_iff
      (a := x) (b := y⁻¹))

/-- Left-quotient version of
`div_mem_zeroSubgroup_iff_inv_mul_mem_zeroSubgroup`. -/
theorem inv_mul_mem_zeroSubgroup_iff_div_mem_zeroSubgroup (x y : G) :
    y⁻¹ * x ∈ V.zeroSubgroup ↔ x / y ∈ V.zeroSubgroup :=
  (V.div_mem_zeroSubgroup_iff_inv_mul_mem_zeroSubgroup x y).symm

/-- Left-quotient version of `div_mem_zeroSubgroup_iff`. -/
theorem inv_mul_mem_zeroSubgroup_iff (x y : G) :
    y⁻¹ * x ∈ V.zeroSubgroup ↔ V.val x = V.val y := by
  rw [V.inv_mul_mem_zeroSubgroup_iff_div_mem_zeroSubgroup x y,
    V.div_mem_zeroSubgroup_iff x y]

/-- Establishes the identity `V.val x = V.val y`. -/
theorem val_eq_of_inv_mul_mem_zeroSubgroup {x y : G}
    (hxy : y⁻¹ * x ∈ V.zeroSubgroup) :
    V.val x = V.val y :=
  (V.inv_mul_mem_zeroSubgroup_iff x y).1 hxy

/-- Establishes the membership statement `y⁻¹ * x ∈ V.zeroSubgroup`. -/
theorem inv_mul_mem_zeroSubgroup_of_val_eq {x y : G}
    (hxy : V.val x = V.val y) :
    y⁻¹ * x ∈ V.zeroSubgroup :=
  (V.inv_mul_mem_zeroSubgroup_iff x y).2 hxy

/-- Equality in `G ⧸ zeroSubgroup`, in right-quotient form. -/
theorem quotientZeroSubgroup_mk_eq_iff_div_mem (x y : G) :
    QuotientGroup.mk' V.zeroSubgroup x =
        QuotientGroup.mk' V.zeroSubgroup y ↔
      x / y ∈ V.zeroSubgroup := by
  simpa [QuotientGroup.mk'_apply] using
    (QuotientGroup.eq_iff_div_mem
      (N := V.zeroSubgroup) (x := x) (y := y))

/-- Equality in `G ⧸ zeroSubgroup`, in left-quotient form. -/
theorem quotientZeroSubgroup_mk_eq_iff_inv_mul_mem (x y : G) :
    QuotientGroup.mk' V.zeroSubgroup x =
        QuotientGroup.mk' V.zeroSubgroup y ↔
      y⁻¹ * x ∈ V.zeroSubgroup := by
  rw [V.quotientZeroSubgroup_mk_eq_iff_div_mem x y,
    V.div_mem_zeroSubgroup_iff_inv_mul_mem_zeroSubgroup x y]

/-- Equality in `G ⧸ zeroSubgroup` is equality of valuations. -/
theorem quotientZeroSubgroup_mk_eq_iff_val_eq (x y : G) :
    QuotientGroup.mk' V.zeroSubgroup x =
        QuotientGroup.mk' V.zeroSubgroup y ↔
      V.val x = V.val y := by
  rw [V.quotientZeroSubgroup_mk_eq_iff_div_mem x y,
    V.div_mem_zeroSubgroup_iff x y]

/-- Two elements have quotient in the zero-valuation subgroup exactly when the
left element is the right element multiplied on the left by a zero-valuation
element.  This is the right-coset representative form used in
`Kˣ / O_Kˣ` calculations. -/
theorem div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq (x y : G) :
    x / y ∈ V.zeroSubgroup ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x := by
  constructor
  · intro hxy
    exact ⟨x / y, hxy, by simp [div_eq_mul_inv, mul_assoc]⟩
  · rintro ⟨u, hu, hux⟩
    have hu_eq : u = x / y := by
      have h := congrArg (fun t : G => t * y⁻¹) hux
      simpa [div_eq_mul_inv, mul_assoc] using h
    simpa [← hu_eq] using hu

/-- Establishes the identity `∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x`. -/
theorem exists_zeroSubgroup_mul_eq_of_div_mem_zeroSubgroup
    {x y : G} (hxy : x / y ∈ V.zeroSubgroup) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x :=
  (V.div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq x y).1 hxy

/-- Establishes the membership statement `x / y ∈ V.zeroSubgroup`. -/
theorem div_mem_zeroSubgroup_of_exists_zeroSubgroup_mul_eq
    {x y : G} (hxy : ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x) :
    x / y ∈ V.zeroSubgroup :=
  (V.div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq x y).2 hxy

/-- Two elements have left quotient in the zero-valuation subgroup exactly when
the left element is the right element multiplied on the right by a
zero-valuation element. -/
theorem inv_mul_mem_zeroSubgroup_iff_exists_mul_zeroSubgroup_eq (x y : G) :
    y⁻¹ * x ∈ V.zeroSubgroup ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ y * u = x := by
  constructor
  · intro hxy
    exact ⟨y⁻¹ * x, hxy, by simp⟩
  · rintro ⟨u, hu, hyu⟩
    have hu_eq : u = y⁻¹ * x := by
      have h := congrArg (fun t : G => y⁻¹ * t) hyu
      simpa [mul_assoc] using h
    simpa [← hu_eq] using hu

/-- Establishes the identity `∃ u : G, u ∈ V.zeroSubgroup ∧ y * u = x`. -/
theorem exists_mul_zeroSubgroup_eq_of_inv_mul_mem_zeroSubgroup
    {x y : G} (hxy : y⁻¹ * x ∈ V.zeroSubgroup) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ y * u = x :=
  (V.inv_mul_mem_zeroSubgroup_iff_exists_mul_zeroSubgroup_eq x y).1 hxy

/-- Establishes the membership statement `y⁻¹ * x ∈ V.zeroSubgroup`. -/
theorem inv_mul_mem_zeroSubgroup_of_exists_mul_zeroSubgroup_eq
    {x y : G} (hxy : ∃ u : G, u ∈ V.zeroSubgroup ∧ y * u = x) :
    y⁻¹ * x ∈ V.zeroSubgroup :=
  (V.inv_mul_mem_zeroSubgroup_iff_exists_mul_zeroSubgroup_eq x y).2 hxy

/--
Characterizes `V.val x = V.val y` by the equivalent condition `∃ u : G, u ∈ V.zeroSubgroup ∧ u * y
= x`.
-/
theorem val_eq_iff_exists_zeroSubgroup_mul_eq (x y : G) :
    V.val x = V.val y ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x := by
  rw [← V.div_mem_zeroSubgroup_iff x y,
    V.div_mem_zeroSubgroup_iff_exists_zeroSubgroup_mul_eq x y]

/--
Characterizes `V.val x = V.val y` by the equivalent condition `∃ u : G, u ∈ V.zeroSubgroup ∧ y * u
= x`.
-/
theorem val_eq_iff_exists_mul_zeroSubgroup_eq (x y : G) :
    V.val x = V.val y ↔
      ∃ u : G, u ∈ V.zeroSubgroup ∧ y * u = x := by
  rw [← V.inv_mul_mem_zeroSubgroup_iff x y,
    V.inv_mul_mem_zeroSubgroup_iff_exists_mul_zeroSubgroup_eq x y]

/-- Establishes the identity `∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x`. -/
theorem exists_zeroSubgroup_mul_eq_of_val_eq {x y : G}
    (hxy : V.val x = V.val y) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x :=
  (V.val_eq_iff_exists_zeroSubgroup_mul_eq x y).1 hxy

/-- Establishes the identity `∃ u : G, u ∈ V.zeroSubgroup ∧ y * u = x`. -/
theorem exists_mul_zeroSubgroup_eq_of_val_eq {x y : G}
    (hxy : V.val x = V.val y) :
    ∃ u : G, u ∈ V.zeroSubgroup ∧ y * u = x :=
  (V.val_eq_iff_exists_mul_zeroSubgroup_eq x y).1 hxy

/-- Establishes the identity `V.val x = V.val y`. -/
theorem val_eq_of_exists_zeroSubgroup_mul_eq {x y : G}
    (hxy : ∃ u : G, u ∈ V.zeroSubgroup ∧ u * y = x) :
    V.val x = V.val y :=
  (V.val_eq_iff_exists_zeroSubgroup_mul_eq x y).2 hxy

/-- Establishes the identity `V.val x = V.val y`. -/
theorem val_eq_of_exists_mul_zeroSubgroup_eq {x y : G}
    (hxy : ∃ u : G, u ∈ V.zeroSubgroup ∧ y * u = x) :
    V.val x = V.val y :=
  (V.val_eq_iff_exists_mul_zeroSubgroup_eq x y).2 hxy

/-- Characterizes `V.val x = 0` by the equivalent condition `x ∈ V.zeroSubgroup`. -/
theorem val_eq_zero_iff_mem_zeroSubgroup (x : G) :
    V.val x = 0 ↔ x ∈ V.zeroSubgroup :=
  (MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V x).symm

/-- Establishes the membership statement `x ^ n ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_pow_mem {x : G} (hx : x ∈ V.zeroSubgroup) (n : ℕ) :
    x ^ n ∈ V.zeroSubgroup :=
  V.zeroSubgroup.pow_mem hx n

/-- Establishes the membership statement `x ^ n ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_zpow_mem {x : G} (hx : x ∈ V.zeroSubgroup) (n : ℤ) :
    x ^ n ∈ V.zeroSubgroup :=
  V.zeroSubgroup.zpow_mem hx n

/-- Characterizes `x ^ n ∈ V.zeroSubgroup` by the equivalent condition `x ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_pow_mem_iff_of_ne_zero (x : G) {n : ℕ} (hn : n ≠ 0) :
    x ^ n ∈ V.zeroSubgroup ↔ x ∈ V.zeroSubgroup := by
  rw [MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V (x ^ n),
    MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V x]
  exact V.val_pow_eq_zero_iff_of_ne_zero x hn

/-- Characterizes `x ^ n ∈ V.zeroSubgroup` by the equivalent condition `x ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_zpow_mem_iff_of_ne_zero (x : G) {n : ℤ} (hn : n ≠ 0) :
    x ^ n ∈ V.zeroSubgroup ↔ x ∈ V.zeroSubgroup := by
  rw [MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V (x ^ n),
    MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V x]
  exact V.val_zpow_eq_zero_iff_of_ne_zero x hn

/-- Characterizes `x * u ∈ V.zeroSubgroup` by the equivalent condition `x ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_mul_iff_right {x u : G} (hu : u ∈ V.zeroSubgroup) :
    x * u ∈ V.zeroSubgroup ↔ x ∈ V.zeroSubgroup := by
  constructor
  · intro hxu
    have h : (x * u) * u⁻¹ ∈ V.zeroSubgroup :=
      V.zeroSubgroup_mul_mem hxu (V.zeroSubgroup_inv_mem hu)
    simpa [mul_assoc] using h
  · intro hx
    exact V.zeroSubgroup_mul_mem hx hu

/-- Characterizes `u * x ∈ V.zeroSubgroup` by the equivalent condition `x ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_mul_iff_left {u x : G} (hu : u ∈ V.zeroSubgroup) :
    u * x ∈ V.zeroSubgroup ↔ x ∈ V.zeroSubgroup := by
  constructor
  · intro hux
    have h : u⁻¹ * (u * x) ∈ V.zeroSubgroup :=
      V.zeroSubgroup_mul_mem (V.zeroSubgroup_inv_mem hu) hux
    simpa [mul_assoc] using h
  · intro hx
    exact V.zeroSubgroup_mul_mem hu hx

/-- Characterizes `x / u ∈ V.zeroSubgroup` by the equivalent condition `x ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_div_iff_right {x u : G} (hu : u ∈ V.zeroSubgroup) :
    x / u ∈ V.zeroSubgroup ↔ x ∈ V.zeroSubgroup := by
  simpa [div_eq_mul_inv] using
    V.zeroSubgroup_mul_iff_right (x := x) (u := u⁻¹)
      (V.zeroSubgroup_inv_mem hu)

/-- Characterizes `u / x ∈ V.zeroSubgroup` by the equivalent condition `x ∈ V.zeroSubgroup`. -/
theorem zeroSubgroup_div_iff_left {u x : G} (hu : u ∈ V.zeroSubgroup) :
    u / x ∈ V.zeroSubgroup ↔ x ∈ V.zeroSubgroup := by
  rw [V.div_mem_zeroSubgroup_iff,
    (MultiplicativeIntegerValuation.mem_zeroSubgroup_iff V u).1 hu]
  constructor
  · intro h
    exact (V.val_eq_zero_iff_mem_zeroSubgroup x).1 h.symm
  · intro hx
    rw [(V.val_eq_zero_iff_mem_zeroSubgroup x).2 hx]

/-- Establishes the identity `V.val (x * u) = V.val x`. -/
theorem val_mul_eq_left_of_right_zero {x u : G} (hu : V.val u = 0) :
    V.val (x * u) = V.val x := by
  rw [V.val_mul, hu, add_zero]

/-- Establishes the identity `V.val (u * x) = V.val x`. -/
theorem val_mul_eq_right_of_left_zero {u x : G} (hu : V.val u = 0) :
    V.val (u * x) = V.val x := by
  rw [V.val_mul, hu, zero_add]

/-- `val_zeroSubgroup_mul` satisfies the integer-power formula `V.val (u * γ ^ n) = n * V.val γ`. -/
theorem val_zeroSubgroup_mul_zpow {u γ : G}
    (hu : u ∈ V.zeroSubgroup) (n : ℤ) :
    V.val (u * γ ^ n) = n * V.val γ := by
  rw [V.val_mul, (V.mem_zeroSubgroup_iff u).1 hu, V.val_zpow, zero_add]

/-- Establishes the identity `V.val (u * γ ^ n) = n * V.val γ`. -/
theorem val_subgroup_mul_zpow_of_le_zeroSubgroup
    (P : Subgroup G) (hP : P ≤ V.zeroSubgroup)
    {u γ : G} (hu : u ∈ P) (n : ℤ) :
    V.val (u * γ ^ n) = n * V.val γ :=
  V.val_zeroSubgroup_mul_zpow (hP hu) n

/--
`val_eq_generator_multiple_of_mem_subgroup_mul` satisfies the integer-power formula `V.val x = n *
V.val γ`.
-/
theorem val_eq_generator_multiple_of_mem_subgroup_mul_zpow
    (P : Subgroup G) (hP : P ≤ V.zeroSubgroup)
    {x u γ : G} (hu : u ∈ P) {n : ℤ}
    (hx : x = u * γ ^ n) :
    V.val x = n * V.val γ := by
  rw [hx]
  exact V.val_subgroup_mul_zpow_of_le_zeroSubgroup P hP hu n

end MultiplicativeIntegerValuation

/-- A norm-like homomorphism compatible with integer-valued valuations.

`residueDegree` is proof-attached data: it is the multiplier in
`valuation_formula`, not an independent field-extension invariant.  In the
usual discrete-valued application the source has a uniformizer, and evaluating
`valuation_formula` at that uniformizer uniquely determines this coefficient.
The generic group-level abstraction does not require a uniformizer, so it keeps
the coefficient together with the formula that certifies it. -/
structure ValuedNorm {G : Type u} {H : Type v} [Group G] [Group H]
    (vG : MultiplicativeIntegerValuation G)
    (vH : MultiplicativeIntegerValuation H) where
  /-- The multiplicative norm homomorphism. -/
  toHom : H →* G
  /-- The nonnegative scaling factor in the valuation formula. -/
  residueDegree : ℕ
  /-- Applying the norm scales valuation by the residue-degree factor. -/
  valuation_formula :
    ∀ x : H, vG.val (toHom x) = (residueDegree : ℤ) * vH.val x

end DiscreteValuationField

end

end LocalFieldTheory
