/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.SetTheory.Cardinal.Finite
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NormUnits
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.NormFiltration
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.ValueGroup

/-! # Field Norm -/

@[expose] public section
namespace LocalFieldTheory

/-!
# Field norm on unit groups

This file connects mathlib's `Algebra.norm` with the unit-group and valued-norm
APIs used by local CFT.
-/

noncomputable
section

universe u v w

namespace DiscreteValuationField

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- The norm subgroup of `Kˣ` attached to `L/K`. -/
noncomputable def fieldNormSubgroup : Subgroup Kˣ :=
  (normUnits K L).range

/-- The norm subgroup from the top field of a tower lies in the norm subgroup from the
intermediate field. -/
theorem fieldNormSubgroup_le_of_tower
    (E : Type w) [Field E] [Algebra K E] [Algebra E L] [IsScalarTower K E L]
    [Module.Free E L] :
    fieldNormSubgroup K L ≤ fieldNormSubgroup K E := by
  intro x hx
  rcases hx with ⟨z, hz⟩
  exact ⟨normUnits E L z, by
    rw [normUnits_tower K E L z, hz]⟩

/--
Characterizes `fieldNormSubgroup K L = ⊤` by the equivalent condition `Function.Surjective
(normUnits K L)`.
-/
theorem fieldNormSubgroup_eq_top_iff :
    fieldNormSubgroup K L = ⊤ ↔ Function.Surjective (normUnits K L) := by
  rw [fieldNormSubgroup, MonoidHom.range_eq_top]

/--
Characterizes `z ∈ MonoidHom.ker (normUnits K L)` by the equivalent condition `Algebra.norm K
(z : L) = 1`.
-/
theorem mem_fieldNormUnits_ker_iff_norm_eq_one (z : Lˣ) :
    z ∈ MonoidHom.ker (normUnits K L) ↔
      Algebra.norm K (z : L) = 1 := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hz
    exact congrArg (fun u : Kˣ => (u : K)) hz
  · intro hz
    ext
    simpa using hz

/-- First-isomorphism-theorem form for the field norm on unit groups:
`Lˣ / ker(N)` is the norm subgroup of `Kˣ`. -/
noncomputable def fieldNormUnitsQuotientKerEquivFieldNormSubgroup :
    Lˣ ⧸ MonoidHom.ker (normUnits K L) ≃*
      fieldNormSubgroup K L :=
  QuotientGroup.quotientKerEquivRange (normUnits K L)

/--
Establishes the identity `fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L (QuotientGroup.mk'
(MonoidHom.ker (normUnits K L)) z) = (normUnits K L).rangeRestrict z`.
-/
theorem fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk
    (z : Lˣ) :
    fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L
        (QuotientGroup.mk'
          (MonoidHom.ker (normUnits K L)) z) =
      (normUnits K L).rangeRestrict z :=
  rfl

/--
Establishes the identity `((fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L (QuotientGroup.mk'
(MonoidHom.ker (normUnits K L)) z) : fieldNormSubgroup K L) : Kˣ) = normUnits K L z`.
-/
theorem coe_fieldNormUnitsQuotientKerEquivFieldNormSubgroup_mk
    (z : Lˣ) :
    ((fieldNormUnitsQuotientKerEquivFieldNormSubgroup K L
        (QuotientGroup.mk'
          (MonoidHom.ker (normUnits K L)) z) :
        fieldNormSubgroup K L) : Kˣ) =
      normUnits K L z :=
  rfl

/-- The quotient map `Kˣ → Kˣ / N_{L/K}(Lˣ)` attached to the field norm. -/
noncomputable def fieldNormQuotientMap :
    Kˣ →* Kˣ ⧸ fieldNormSubgroup K L :=
  QuotientGroup.mk' (fieldNormSubgroup K L)

/--
The defining evaluation formula for `fieldNormQuotientMap` is `fieldNormQuotientMap K L x =
QuotientGroup.mk' (fieldNormSubgroup K L) x`.
-/
@[simp] theorem fieldNormQuotientMap_apply (x : Kˣ) :
    fieldNormQuotientMap K L x =
      QuotientGroup.mk' (fieldNormSubgroup K L) x :=
  rfl

/-- The kernel of the norm quotient map is exactly the field-norm subgroup. -/
theorem fieldNormQuotientMap_ker :
    MonoidHom.ker (fieldNormQuotientMap K L) = fieldNormSubgroup K L :=
  by
    rw [fieldNormQuotientMap]
    exact QuotientGroup.ker_mk' (fieldNormSubgroup K L)

/--
Characterizes `fieldNormQuotientMap K L x = 1` by the equivalent condition `x ∈ fieldNormSubgroup
K L`.
-/
theorem fieldNormQuotientMap_eq_one_iff (x : Kˣ) :
    fieldNormQuotientMap K L x = 1 ↔
      x ∈ fieldNormSubgroup K L := by
  rw [← MonoidHom.mem_ker, fieldNormQuotientMap_ker]

/--
Characterizes `fieldNormQuotientMap K L x = 1` by the equivalent condition `∃ z : Lˣ,
normUnits K L z = x`.
-/
theorem fieldNormQuotientMap_eq_one_iff_exists_norm_eq (x : Kˣ) :
    fieldNormQuotientMap K L x = 1 ↔
      ∃ z : Lˣ, normUnits K L z = x := by
  rw [fieldNormQuotientMap_eq_one_iff K L x]
  exact MonoidHom.mem_range

/--
Characterizes `fieldNormQuotientMap K L x = fieldNormQuotientMap K L y` by the equivalent
condition `x / y ∈ fieldNormSubgroup K L`.
-/
theorem fieldNormQuotientMap_eq_iff_div_mem (x y : Kˣ) :
    fieldNormQuotientMap K L x = fieldNormQuotientMap K L y ↔
      x / y ∈ fieldNormSubgroup K L := by
  simpa [fieldNormQuotientMap] using
    (QuotientGroup.eq_iff_div_mem
      (N := fieldNormSubgroup K L) (x := x) (y := y))

/--
Characterizes `x / y ∈ fieldNormSubgroup K L` by the equivalent condition `y⁻¹ * x ∈
fieldNormSubgroup K L`.
-/
theorem fieldNormSubgroup_div_mem_iff_inv_mul_mem (x y : Kˣ) :
    x / y ∈ fieldNormSubgroup K L ↔
      y⁻¹ * x ∈ fieldNormSubgroup K L := by
  simp [div_eq_mul_inv, mul_comm]

/--
Characterizes `y⁻¹ * x ∈ fieldNormSubgroup K L` by the equivalent condition `x / y ∈
fieldNormSubgroup K L`.
-/
theorem fieldNormSubgroup_inv_mul_mem_iff_div_mem (x y : Kˣ) :
    y⁻¹ * x ∈ fieldNormSubgroup K L ↔
      x / y ∈ fieldNormSubgroup K L :=
  (fieldNormSubgroup_div_mem_iff_inv_mul_mem K L x y).symm

/--
Characterizes `x / y ∈ fieldNormSubgroup K L` by the equivalent condition `∃ z : Lˣ,
normUnits K L z * y = x`.
-/
theorem fieldNormSubgroup_div_mem_iff_exists_norm_mul_eq
    (x y : Kˣ) :
    x / y ∈ fieldNormSubgroup K L ↔
      ∃ z : Lˣ, normUnits K L z * y = x := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz]; simp [div_eq_mul_inv, mul_assoc]⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    have h := congrArg (fun t : Kˣ => t * y⁻¹) hz
    simpa [div_eq_mul_inv, mul_assoc] using h

/--
Characterizes `y⁻¹ * x ∈ fieldNormSubgroup K L` by the equivalent condition `∃ z : Lˣ, y *
normUnits K L z = x`.
-/
theorem fieldNormSubgroup_inv_mul_mem_iff_exists_mul_norm_eq
    (x y : Kˣ) :
    y⁻¹ * x ∈ fieldNormSubgroup K L ↔
      ∃ z : Lˣ, y * normUnits K L z = x := by
  rw [fieldNormSubgroup_inv_mul_mem_iff_div_mem K L x y,
    fieldNormSubgroup_div_mem_iff_exists_norm_mul_eq K L x y]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa [mul_comm, mul_left_comm, mul_assoc] using hz⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by simpa [mul_comm, mul_left_comm, mul_assoc] using hz⟩

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = 1` by the equivalent condition `x ∈
fieldNormSubgroup K L`.
-/
theorem fieldNormQuotient_mk_eq_one_iff (x : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x = 1 ↔
      x ∈ fieldNormSubgroup K L := by
  rw [QuotientGroup.mk'_apply]
  exact QuotientGroup.eq_one_iff (N := fieldNormSubgroup K L) x

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = 1` by the equivalent condition `∃ z :
Lˣ, normUnits K L z = x`.
-/
theorem fieldNormQuotient_mk_eq_one_iff_exists_norm_eq (x : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x = 1 ↔
      ∃ z : Lˣ, normUnits K L z = x := by
  rw [fieldNormQuotient_mk_eq_one_iff K L x]
  exact MonoidHom.mem_range

/--
Establishes the identity `QuotientGroup.mk' (fieldNormSubgroup K L) (normUnits K L z) = 1`.
-/
theorem fieldNormQuotient_norm_mk_eq_one (z : Lˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L)
        (normUnits K L z) = 1 :=
  (fieldNormQuotient_mk_eq_one_iff K L
    (normUnits K L z)).2
      ((MonoidHom.mem_range (f := normUnits K L)).2 ⟨z, rfl⟩)

/--
Characterizes `(QuotientGroup.mk' (fieldNormSubgroup K L) x) ^ n = 1` by the equivalent condition
`x ^ n ∈ fieldNormSubgroup K L`.
-/
theorem fieldNormQuotient_mk_pow_eq_one_iff_pow_mem
    (x : Kˣ) (n : ℕ) :
    (QuotientGroup.mk' (fieldNormSubgroup K L) x) ^ n = 1 ↔
      x ^ n ∈ fieldNormSubgroup K L := by
  rw [← (QuotientGroup.mk' (fieldNormSubgroup K L)).map_pow,
    fieldNormQuotient_mk_eq_one_iff K L (x ^ n)]

/--
Characterizes `(QuotientGroup.mk' (fieldNormSubgroup K L) x) ^ n = 1` by the equivalent condition
`∃ z : Lˣ, normUnits K L z = x ^ n`.
-/
theorem fieldNormQuotient_mk_pow_eq_one_iff_exists_norm_eq_pow
    (x : Kˣ) (n : ℕ) :
    (QuotientGroup.mk' (fieldNormSubgroup K L) x) ^ n = 1 ↔
      ∃ z : Lˣ, normUnits K L z = x ^ n := by
  rw [fieldNormQuotient_mk_pow_eq_one_iff_pow_mem K L x n]
  exact MonoidHom.mem_range

/--
Characterizes `q ^ n = 1` by the equivalent condition `∃ x : Kˣ, QuotientGroup.mk'
(fieldNormSubgroup K L) x = q ∧ x ^ n ∈ fieldNormSubgroup K L`.
-/
theorem fieldNormQuotient_pow_eq_one_iff_exists_pow_mem
    (q : Kˣ ⧸ fieldNormSubgroup K L) (n : ℕ) :
    q ^ n = 1 ↔
      ∃ x : Kˣ, QuotientGroup.mk' (fieldNormSubgroup K L) x = q ∧
        x ^ n ∈ fieldNormSubgroup K L := by
  constructor
  · intro hq
    rcases QuotientGroup.mk'_surjective (fieldNormSubgroup K L) q with
      ⟨x, rfl⟩
    exact ⟨x, rfl,
      (fieldNormQuotient_mk_pow_eq_one_iff_pow_mem K L x n).1 hq⟩
  · rintro ⟨x, hxq, hx⟩
    rw [← hxq]
    exact (fieldNormQuotient_mk_pow_eq_one_iff_pow_mem K L x n).2 hx

/--
Characterizes `q ^ n = 1` by the equivalent condition `∃ x : Kˣ, QuotientGroup.mk'
(fieldNormSubgroup K L) x = q ∧ ∃ z : Lˣ, normUnits K L z = x ^ n`.
-/
theorem fieldNormQuotient_pow_eq_one_iff_exists_norm_eq_pow
    (q : Kˣ ⧸ fieldNormSubgroup K L) (n : ℕ) :
    q ^ n = 1 ↔
      ∃ x : Kˣ, QuotientGroup.mk' (fieldNormSubgroup K L) x = q ∧
        ∃ z : Lˣ, normUnits K L z = x ^ n := by
  rw [fieldNormQuotient_pow_eq_one_iff_exists_pow_mem K L q n]
  constructor
  · rintro ⟨x, hxq, hx⟩
    exact ⟨x, hxq,
      (MonoidHom.mem_range (f := normUnits K L)).1 hx⟩
  · rintro ⟨x, hxq, hz⟩
    exact ⟨x, hxq,
      (MonoidHom.mem_range (f := normUnits K L)).2 hz⟩

/--
Characterizes `(QuotientGroup.mk' (fieldNormSubgroup K L) x) ^ n = 1` by the equivalent condition
`x ^ n ∈ fieldNormSubgroup K L`.
-/
theorem fieldNormQuotient_mk_zpow_eq_one_iff_zpow_mem
    (x : Kˣ) (n : ℤ) :
    (QuotientGroup.mk' (fieldNormSubgroup K L) x) ^ n = 1 ↔
      x ^ n ∈ fieldNormSubgroup K L := by
  have hpow : QuotientGroup.mk' (fieldNormSubgroup K L) (x ^ n) =
      (QuotientGroup.mk' (fieldNormSubgroup K L) x) ^ n :=
    map_zpow (QuotientGroup.mk' (fieldNormSubgroup K L)) x n
  rw [← hpow,
    fieldNormQuotient_mk_eq_one_iff K L (x ^ n)]

/--
Characterizes `(QuotientGroup.mk' (fieldNormSubgroup K L) x) ^ n = 1` by the equivalent condition
`∃ z : Lˣ, normUnits K L z = x ^ n`.
-/
theorem fieldNormQuotient_mk_zpow_eq_one_iff_exists_norm_eq_zpow
    (x : Kˣ) (n : ℤ) :
    (QuotientGroup.mk' (fieldNormSubgroup K L) x) ^ n = 1 ↔
      ∃ z : Lˣ, normUnits K L z = x ^ n := by
  rw [fieldNormQuotient_mk_zpow_eq_one_iff_zpow_mem K L x n]
  exact MonoidHom.mem_range

/--
Characterizes `q ^ n = 1` by the equivalent condition `∃ x : Kˣ, QuotientGroup.mk'
(fieldNormSubgroup K L) x = q ∧ x ^ n ∈ fieldNormSubgroup K L`.
-/
theorem fieldNormQuotient_zpow_eq_one_iff_exists_zpow_mem
    (q : Kˣ ⧸ fieldNormSubgroup K L) (n : ℤ) :
    q ^ n = 1 ↔
      ∃ x : Kˣ, QuotientGroup.mk' (fieldNormSubgroup K L) x = q ∧
        x ^ n ∈ fieldNormSubgroup K L := by
  constructor
  · intro hq
    rcases QuotientGroup.mk'_surjective (fieldNormSubgroup K L) q with
      ⟨x, rfl⟩
    exact ⟨x, rfl,
      (fieldNormQuotient_mk_zpow_eq_one_iff_zpow_mem K L x n).1 hq⟩
  · rintro ⟨x, hxq, hx⟩
    rw [← hxq]
    exact (fieldNormQuotient_mk_zpow_eq_one_iff_zpow_mem K L x n).2 hx

/--
Characterizes `q ^ n = 1` by the equivalent condition `∃ x : Kˣ, QuotientGroup.mk'
(fieldNormSubgroup K L) x = q ∧ ∃ z : Lˣ, normUnits K L z = x ^ n`.
-/
theorem fieldNormQuotient_zpow_eq_one_iff_exists_norm_eq_zpow
    (q : Kˣ ⧸ fieldNormSubgroup K L) (n : ℤ) :
    q ^ n = 1 ↔
      ∃ x : Kˣ, QuotientGroup.mk' (fieldNormSubgroup K L) x = q ∧
        ∃ z : Lˣ, normUnits K L z = x ^ n := by
  rw [fieldNormQuotient_zpow_eq_one_iff_exists_zpow_mem K L q n]
  constructor
  · rintro ⟨x, hxq, hx⟩
    exact ⟨x, hxq,
      (MonoidHom.mem_range (f := normUnits K L)).1 hx⟩
  · rintro ⟨x, hxq, hz⟩
    exact ⟨x, hxq,
      (MonoidHom.mem_range (f := normUnits K L)).2 hz⟩

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk' (fieldNormSubgroup
K L) y` by the equivalent condition `x / y ∈ fieldNormSubgroup K L`.
-/
theorem fieldNormQuotient_mk_eq_iff_div_mem (x y : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
        QuotientGroup.mk' (fieldNormSubgroup K L) y ↔
      x / y ∈ fieldNormSubgroup K L := by
  simpa [QuotientGroup.mk'_apply] using
    (QuotientGroup.eq_iff_div_mem
      (N := fieldNormSubgroup K L) (x := x) (y := y))

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk' (fieldNormSubgroup
K L) y` by the equivalent condition `y⁻¹ * x ∈ fieldNormSubgroup K L`.
-/
theorem fieldNormQuotient_mk_eq_iff_inv_mul_mem (x y : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
        QuotientGroup.mk' (fieldNormSubgroup K L) y ↔
      y⁻¹ * x ∈ fieldNormSubgroup K L := by
  rw [fieldNormQuotient_mk_eq_iff_div_mem K L x y,
    fieldNormSubgroup_div_mem_iff_inv_mul_mem K L x y]

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk' (fieldNormSubgroup
K L) y` by the equivalent condition `∃ z : Lˣ, normUnits K L z = x / y`.
-/
theorem fieldNormQuotient_mk_eq_iff_exists_norm_eq_div
    (x y : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
        QuotientGroup.mk' (fieldNormSubgroup K L) y ↔
      ∃ z : Lˣ, normUnits K L z = x / y := by
  rw [fieldNormQuotient_mk_eq_iff_div_mem K L x y]
  exact MonoidHom.mem_range

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk' (fieldNormSubgroup
K L) y` by the equivalent condition `∃ z : Lˣ, normUnits K L z = y⁻¹ * x`.
-/
theorem fieldNormQuotient_mk_eq_iff_exists_norm_eq_inv_mul
    (x y : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
        QuotientGroup.mk' (fieldNormSubgroup K L) y ↔
      ∃ z : Lˣ, normUnits K L z = y⁻¹ * x := by
  rw [fieldNormQuotient_mk_eq_iff_inv_mul_mem K L x y]
  exact MonoidHom.mem_range

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk' (fieldNormSubgroup
K L) y` by the equivalent condition `∃ z : Lˣ, normUnits K L z * y = x`.
-/
theorem fieldNormQuotient_mk_eq_iff_exists_norm_mul_eq (x y : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
        QuotientGroup.mk' (fieldNormSubgroup K L) y ↔
      ∃ z : Lˣ, normUnits K L z * y = x := by
  rw [fieldNormQuotient_mk_eq_iff_div_mem K L x y,
    fieldNormSubgroup_div_mem_iff_exists_norm_mul_eq K L x y]

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk' (fieldNormSubgroup
K L) y` by the equivalent condition `∃ z : Lˣ, y * normUnits K L z = x`.
-/
theorem fieldNormQuotient_mk_eq_iff_exists_mul_norm_eq (x y : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
        QuotientGroup.mk' (fieldNormSubgroup K L) y ↔
      ∃ z : Lˣ, y * normUnits K L z = x := by
  rw [fieldNormQuotient_mk_eq_iff_inv_mul_mem K L x y,
    fieldNormSubgroup_inv_mul_mem_iff_exists_mul_norm_eq K L x y]

/--
Establishes the identity `QuotientGroup.mk' (fieldNormSubgroup K L) (normUnits K L z * x) =
QuotientGroup.mk' (fieldNormSubgroup K L) x`.
-/
theorem fieldNormQuotient_norm_mul_mk_eq (z : Lˣ) (x : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L)
        (normUnits K L z * x) =
      QuotientGroup.mk' (fieldNormSubgroup K L) x := by
  rw [fieldNormQuotient_mk_eq_iff_exists_norm_mul_eq K L
    (normUnits K L z * x) x]
  exact ⟨z, rfl⟩

/--
Establishes the identity `QuotientGroup.mk' (fieldNormSubgroup K L) (x * normUnits K L z) =
QuotientGroup.mk' (fieldNormSubgroup K L) x`.
-/
theorem fieldNormQuotient_mul_norm_mk_eq (x : Kˣ) (z : Lˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L)
        (x * normUnits K L z) =
      QuotientGroup.mk' (fieldNormSubgroup K L) x := by
  rw [mul_comm]
  exact fieldNormQuotient_norm_mul_mk_eq K L z x

/--
Establishes the identity `QuotientGroup.mk' (fieldNormSubgroup K L) x * QuotientGroup.mk'
(fieldNormSubgroup K L) (normUnits K L z) = QuotientGroup.mk' (fieldNormSubgroup K L) x`.
-/
theorem fieldNormQuotient_mk_mul_norm_eq (x : Kˣ) (z : Lˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x *
        QuotientGroup.mk' (fieldNormSubgroup K L) (normUnits K L z) =
      QuotientGroup.mk' (fieldNormSubgroup K L) x := by
  rw [← (QuotientGroup.mk' (fieldNormSubgroup K L)).map_mul,
    fieldNormQuotient_mul_norm_mk_eq K L x z]

/--
Establishes the identity `QuotientGroup.mk' (fieldNormSubgroup K L) (normUnits K L z) *
QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk' (fieldNormSubgroup K L) x`.
-/
theorem fieldNormQuotient_norm_mul_mk_eq_mk (z : Lˣ) (x : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) (normUnits K L z) *
        QuotientGroup.mk' (fieldNormSubgroup K L) x =
      QuotientGroup.mk' (fieldNormSubgroup K L) x := by
  rw [← (QuotientGroup.mk' (fieldNormSubgroup K L)).map_mul,
    fieldNormQuotient_norm_mul_mk_eq K L z x]

/-- Norm of an element coming from the base field. -/
theorem fieldNormUnits_algebraMap (u : Kˣ) :
    normUnits K L (Units.map (algebraMap K L).toMonoidHom u) =
      u ^ Module.finrank K L := by
  ext
  simp [normUnits, Algebra.norm_algebraMap]

/-- Establishes the identity `normUnits K L (Units.map (algebraMap K L).toMonoidHom u) = u`. -/
theorem fieldNormUnits_algebraMap_of_finrank_eq_one
    (hfin : Module.finrank K L = 1) (u : Kˣ) :
    normUnits K L (Units.map (algebraMap K L).toMonoidHom u) = u := by
  simpa [hfin] using fieldNormUnits_algebraMap K L u

/-- Establishes the membership statement `u ^ Module.finrank K L ∈ fieldNormSubgroup K L`. -/
theorem fieldNormSubgroup_pow_finrank_mem (u : Kˣ) :
    u ^ Module.finrank K L ∈ fieldNormSubgroup K L :=
  ⟨Units.map (algebraMap K L).toMonoidHom u,
    by rw [fieldNormUnits_algebraMap K L u]⟩

/-- Establishes the identity `fieldNormSubgroup K L = ⊤`. -/
theorem fieldNormSubgroup_eq_top_of_finrank_eq_one
    (hfin : Module.finrank K L = 1) :
    fieldNormSubgroup K L = ⊤ := by
  ext u
  constructor
  · intro _
    simp
  · intro _
    simpa [hfin] using fieldNormSubgroup_pow_finrank_mem K L u

/--
Establishes the identity `(QuotientGroup.mk' (fieldNormSubgroup K L) u) ^ Module.finrank K L = 1`.
-/
theorem fieldNormQuotient_mk_pow_finrank_eq_one (u : Kˣ) :
    (QuotientGroup.mk' (fieldNormSubgroup K L) u) ^
        Module.finrank K L = 1 := by
  rw [← (QuotientGroup.mk' (fieldNormSubgroup K L)).map_pow]
  exact (fieldNormQuotient_mk_eq_one_iff K L
    (u ^ Module.finrank K L)).2
      (fieldNormSubgroup_pow_finrank_mem K L u)

/-- Establishes the identity `q ^ Module.finrank K L = 1`. -/
theorem fieldNormQuotient_pow_finrank_eq_one
    (q : Kˣ ⧸ fieldNormSubgroup K L) :
    q ^ Module.finrank K L = 1 := by
  rcases QuotientGroup.mk'_surjective (fieldNormSubgroup K L) q with
    ⟨u, rfl⟩
  exact fieldNormQuotient_mk_pow_finrank_eq_one K L u

/-- Establishes the identity `(QuotientGroup.mk' (fieldNormSubgroup K L) u) ^ n = 1`. -/
theorem fieldNormQuotient_mk_pow_eq_one_of_finrank_dvd
    {n : ℕ} (hn : Module.finrank K L ∣ n) (u : Kˣ) :
    (QuotientGroup.mk' (fieldNormSubgroup K L) u) ^ n = 1 := by
  rcases hn with ⟨m, rfl⟩
  rw [pow_mul, fieldNormQuotient_mk_pow_finrank_eq_one K L u, one_pow]

/-- Establishes the identity `q ^ n = 1`. -/
theorem fieldNormQuotient_pow_eq_one_of_finrank_dvd
    {n : ℕ} (hn : Module.finrank K L ∣ n)
    (q : Kˣ ⧸ fieldNormSubgroup K L) :
    q ^ n = 1 := by
  rcases QuotientGroup.mk'_surjective (fieldNormSubgroup K L) q with
    ⟨u, rfl⟩
  exact fieldNormQuotient_mk_pow_eq_one_of_finrank_dvd K L hn u

/-- Establishes the identity `q = 1`. -/
theorem fieldNormQuotient_eq_one_of_finrank_eq_one
    (hfin : Module.finrank K L = 1)
    (q : Kˣ ⧸ fieldNormSubgroup K L) :
    q = 1 := by
  rcases QuotientGroup.mk'_surjective (fieldNormSubgroup K L) q with
    ⟨u, rfl⟩
  exact (fieldNormQuotient_mk_eq_one_iff K L u).2
    (by simpa [hfin] using fieldNormSubgroup_pow_finrank_mem K L u)

/-- Establishes the identity `q = r`. -/
theorem fieldNormQuotient_eq_of_finrank_eq_one
    (hfin : Module.finrank K L = 1)
    (q r : Kˣ ⧸ fieldNormSubgroup K L) :
    q = r := by
  rw [fieldNormQuotient_eq_one_of_finrank_eq_one K L hfin q,
    fieldNormQuotient_eq_one_of_finrank_eq_one K L hfin r]

/-- Package a field norm as a `ValuedNorm` once the valuation formula has been
proved for the concrete extension.  The natural-number argument is not a
second source of extension-invariant data: `hformula` certifies it as the
valuation multiplier (and a source uniformizer makes that multiplier unique). -/
@[reducible] noncomputable def valuedFieldNorm
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    ValuedNorm vK vL where
  toHom := normUnits K L
  residueDegree := residueDegree
  valuation_formula := hformula

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).toHom =
normUnits K L`.
-/
@[simp] theorem valuedFieldNorm_toHom
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    (valuedFieldNorm K L vK vL residueDegree hformula).toHom =
      normUnits K L :=
  rfl

/--
Establishes the identity `(valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
fieldNormSubgroup K L`.
-/
theorem valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x) :
    (valuedFieldNorm K L vK vL residueDegree hformula).normSubgroup =
      fieldNormSubgroup K L := by
  ext x
  rfl

/-- Concrete cyclic description of the field-norm quotient.  The assumptions
are the valuation formula for the field norm and the assertion that every
target valuation-zero element is already a field norm. -/
noncomputable def fieldNormQuotientEquivZMod
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) :
    Kˣ ⧸ fieldNormSubgroup K L ≃* Multiplicative (ZMod residueDegree) :=
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  (QuotientGroup.quotientMulEquivOfEq hnorm.symm).trans
    (N.normQuotientEquivZMod hϖK hϖL hzero')

/--
Establishes the identity `fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL
hzero (QuotientGroup.mk' (fieldNormSubgroup K L) x) = Multiplicative.ofAdd ((vK.val x : ℤ) : ZMod
residueDegree)`.
-/
theorem fieldNormQuotientEquivZMod_mk
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x : Kˣ) :
    fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero
        (QuotientGroup.mk' (fieldNormSubgroup K L) x) =
      Multiplicative.ofAdd ((vK.val x : ℤ) : ZMod residueDegree) := by
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  unfold fieldNormQuotientEquivZMod
  rw [MulEquiv.trans_apply, QuotientGroup.mk'_apply,
    QuotientGroup.quotientMulEquivOfEq_mk]
  simpa [N, valuedFieldNorm] using
    N.normQuotientEquivZMod_mk hϖK hϖL hzero' x

/--
`fieldNormQuotientEquivZMod_uniformizer` satisfies the integer-power formula
`fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL hzero (QuotientGroup.mk'
(fieldNormSubgroup K L) (ϖK ^ n)) = Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)`.
-/
theorem fieldNormQuotientEquivZMod_uniformizer_zpow
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (n : ℤ) :
    fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero
        (QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ n)) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree) := by
  rw [fieldNormQuotientEquivZMod_mk K L vK vL residueDegree
      hformula hϖK hϖL hzero (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK n]

/--
`fieldNormQuotientEquivZMod_uniformizerClass` satisfies the integer-power formula
`fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL hzero ((QuotientGroup.mk'
(fieldNormSubgroup K L) ϖK) ^ n) = Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)`.
-/
theorem fieldNormQuotientEquivZMod_uniformizerClass_zpow
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (n : ℤ) :
    fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero
        ((QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree) := by
  have hpow : QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ n) =
      (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n :=
    map_zpow (QuotientGroup.mk' (fieldNormSubgroup K L)) ϖK n
  rw [← hpow,
    fieldNormQuotientEquivZMod_uniformizer_zpow K L vK vL
      residueDegree hformula hϖK hϖL hzero n]

/--
Establishes the identity `(fieldNormQuotientEquivZMod K L vK vL residueDegree hformula hϖK hϖL
hzero).symm (Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)) = QuotientGroup.mk'
(fieldNormSubgroup K L) (ϖK ^ n)`.
-/
@[simp] theorem fieldNormQuotientEquivZMod_symm_mk_ofAdd
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (n : ℤ) :
    (fieldNormQuotientEquivZMod K L vK vL residueDegree
        hformula hϖK hϖL hzero).symm
        (Multiplicative.ofAdd ((n : ℤ) : ZMod residueDegree)) =
      QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ n) := by
  apply (fieldNormQuotientEquivZMod K L vK vL residueDegree
    hformula hϖK hϖL hzero).injective
  rw [MulEquiv.apply_symm_apply,
    fieldNormQuotientEquivZMod_uniformizer_zpow K L vK vL
      residueDegree hformula hϖK hϖL hzero n]

/-- Cardinality form of the concrete field-norm quotient computation. -/
theorem cardinalMk_fieldNormQuotient_eq_residueDegree
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    [NeZero residueDegree] :
    Cardinal.mk (Kˣ ⧸ fieldNormSubgroup K L) = residueDegree := by
  let e := fieldNormQuotientEquivZMod K L vK vL residueDegree
    hformula hϖK hϖL hzero
  calc
    Cardinal.mk (Kˣ ⧸ fieldNormSubgroup K L) =
        Cardinal.lift (Cardinal.mk (Multiplicative (ZMod residueDegree))) :=
      by simpa only [Cardinal.lift_id'] using Cardinal.mk_congr_lift e.toEquiv
    _ = residueDegree := by
      simp only [Cardinal.mk_fintype, Cardinal.lift_natCast]
      rw [← Nat.card_eq_fintype_card,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod residueDegree) ≃
          ZMod residueDegree), Nat.card_zmod]

/-- Field-norm value-image criterion: an integer is attained as the valuation
of a field norm exactly when it is divisible by the residue degree. -/
theorem exists_mem_fieldNormSubgroup_val_eq_iff_residueDegree_dvd
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL) (n : ℤ) :
    (∃ x : Kˣ, x ∈ fieldNormSubgroup K L ∧ vK.val x = n) ↔
      (residueDegree : ℤ) ∣ n := by
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  simpa [N, valuedFieldNorm, hnorm] using
    (N.exists_normSubgroup_val_eq_iff_residueDegree_dvd_of_uniformizer
      hϖL n)

/-- The value image of the field-norm subgroup is exactly `fℤ`. -/
theorem fieldNormSubgroup_valueImage_eq_residueDegree
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL) :
    vK.subgroupValueSubgroup (fieldNormSubgroup K L) =
      integerMultipleSubgroup (residueDegree : ℤ) := by
  apply le_antisymm
  · refine
      (MultiplicativeIntegerValuation.subgroupValueSubgroup_le_integerMultipleSubgroup_iff
        vK (fieldNormSubgroup K L) (residueDegree : ℤ)).2 ?_
    intro x hx
    let N := valuedFieldNorm K L vK vL residueDegree hformula
    have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
      simpa [N] using
        valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
          K L vK vL residueDegree hformula
    have hx' : x ∈ N.normSubgroup := by
      simpa [hnorm] using hx
    simpa [N, valuedFieldNorm] using
      N.residueDegree_dvd_valuation_of_mem_normSubgroup hx'
  · intro n hn
    rw [mem_integerMultipleSubgroup_iff] at hn
    rcases
      (exists_mem_fieldNormSubgroup_val_eq_iff_residueDegree_dvd
        K L vK vL residueDegree hformula hϖL (Multiplicative.toAdd n)).2
        hn with
      ⟨x, hx, hval⟩
    rw [vK.mem_subgroupValueSubgroup_iff]
    exact ⟨x, hx, by rw [vK.valuationHom_apply, hval, ofAdd_toAdd]⟩

/--
Characterizes `x ∈ fieldNormSubgroup K L` by the equivalent condition `(residueDegree : ℤ) ∣
vK.val x`.
-/
theorem mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) (x : Kˣ) :
    x ∈ fieldNormSubgroup K L ↔ (residueDegree : ℤ) ∣ vK.val x := by
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hzero' : vK.zeroSubgroup ≤ N.normSubgroup := by
    rw [hnorm]
    exact hzero
  simpa [N, valuedFieldNorm, hnorm] using
    (N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖL hzero' x)

/-- Establishes the divisibility statement `(residueDegree : ℤ) ∣ vK.val x`. -/
theorem fieldNormSubgroup_residueDegree_dvd_val_of_mem
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {x : Kˣ} (hx : x ∈ fieldNormSubgroup K L) :
    (residueDegree : ℤ) ∣ vK.val x := by
  let N := valuedFieldNorm K L vK vL residueDegree hformula
  have hnorm : N.normSubgroup = fieldNormSubgroup K L := by
    simpa [N] using
      valuedFieldNorm_normSubgroup_eq_fieldNormSubgroup
        K L vK vL residueDegree hformula
  have hx' : x ∈ N.normSubgroup := by
    simpa [hnorm] using hx
  simpa [N, valuedFieldNorm] using
    N.residueDegree_dvd_valuation_of_mem_normSubgroup hx'

/-- Establishes the membership statement `x ∈ fieldNormSubgroup K L`. -/
theorem fieldNormSubgroup_mem_of_residueDegree_dvd_val_of_zeroSubgroup_le
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    {x : Kˣ} (hx : (residueDegree : ℤ) ∣ vK.val x) :
    x ∈ fieldNormSubgroup K L :=
  (mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    K L vK vL residueDegree hformula hϖL hzero x).2 hx

/--
Characterizes `x / y ∈ fieldNormSubgroup K L` by the equivalent condition `(residueDegree : ℤ) ∣
vK.val x - vK.val y`.
-/
theorem fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x y : Kˣ) :
    x / y ∈ fieldNormSubgroup K L ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      K L vK vL residueDegree hformula hϖL hzero (x / y),
    vK.val_div]

/--
Characterizes `y⁻¹ * x ∈ fieldNormSubgroup K L` by the equivalent condition `(residueDegree : ℤ) ∣
vK.val x - vK.val y`.
-/
theorem fieldNormSubgroup_inv_mul_mem_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x y : Kˣ) :
    y⁻¹ * x ∈ fieldNormSubgroup K L ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [fieldNormSubgroup_inv_mul_mem_iff_div_mem K L x y,
    fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x y]

/-- Under the standard valuation formula and valuation-zero norm-surjectivity,
the norm equation `N z = x` is solvable exactly when `f` divides `v(x)`. -/
theorem exists_fieldNormUnits_eq_iff_residueDegree_dvd_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) (x : Kˣ) :
    (∃ z : Lˣ, normUnits K L z = x) ↔
      (residueDegree : ℤ) ∣ vK.val x := by
  rw [← (MonoidHom.mem_range (f := normUnits K L))]
  change x ∈ fieldNormSubgroup K L ↔ (residueDegree : ℤ) ∣ vK.val x
  exact mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    K L vK vL residueDegree hformula hϖL hzero x

/-- Establishes the identity `∃ z : Lˣ, normUnits K L z = x`. -/
theorem exists_fieldNormUnits_eq_of_residueDegree_dvd_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    {x : Kˣ} (hx : (residueDegree : ℤ) ∣ vK.val x) :
    ∃ z : Lˣ, normUnits K L z = x :=
  (exists_fieldNormUnits_eq_iff_residueDegree_dvd_val
    K L vK vL residueDegree hformula hϖL hzero x).2 hx

/-- Difference form of the concrete norm equation criterion. -/
theorem exists_fieldNormUnits_eq_div_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x y : Kˣ) :
    (∃ z : Lˣ, normUnits K L z = x / y) ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [← (MonoidHom.mem_range (f := normUnits K L))]
  change x / y ∈ fieldNormSubgroup K L ↔
    (residueDegree : ℤ) ∣ vK.val x - vK.val y
  exact fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
    K L vK vL residueDegree hformula hϖL hzero x y

/-- Multiplicative equation form of the concrete norm-lift criterion. -/
theorem exists_fieldNormUnits_mul_eq_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x y : Kˣ) :
    (∃ z : Lˣ, normUnits K L z * y = x) ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [← fieldNormSubgroup_div_mem_iff_exists_norm_mul_eq K L x y,
    fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x y]

/-- Left-multiplicative equation form of the concrete norm-lift criterion. -/
theorem exists_mul_fieldNormUnits_eq_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x y : Kˣ) :
    (∃ z : Lˣ, y * normUnits K L z = x) ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [← fieldNormSubgroup_inv_mul_mem_iff_exists_mul_norm_eq K L x y,
    fieldNormSubgroup_inv_mul_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x y]

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = 1` by the equivalent condition
`(residueDegree : ℤ) ∣ vK.val x`.
-/
theorem fieldNormQuotient_mk_eq_one_iff_residueDegree_dvd_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x = 1 ↔
      (residueDegree : ℤ) ∣ vK.val x := by
  rw [fieldNormQuotient_mk_eq_one_iff K L x,
    mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      K L vK vL residueDegree hformula hϖL hzero x]

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk' (fieldNormSubgroup
K L) y` by the equivalent condition `(residueDegree : ℤ) ∣ vK.val x - vK.val y`.
-/
theorem fieldNormQuotient_mk_eq_iff_residueDegree_dvd_valuation_difference
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x y : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
        QuotientGroup.mk' (fieldNormSubgroup K L) y ↔
      (residueDegree : ℤ) ∣ vK.val x - vK.val y := by
  rw [fieldNormQuotient_mk_eq_iff_div_mem K L x y,
    fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x y]

/--
Characterizes `ϖK ^ n ∈ fieldNormSubgroup K L` by the equivalent condition `(residueDegree : ℤ) ∣
n`.
-/
theorem fieldNormSubgroup_uniformizer_zpow_mem_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (n : ℤ) :
    ϖK ^ n ∈ fieldNormSubgroup K L ↔
      (residueDegree : ℤ) ∣ n := by
  rw [mem_fieldNormSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      K L vK vL residueDegree hformula hϖL hzero (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK n]

/--
Characterizes `ϖK ^ m / ϖK ^ n ∈ fieldNormSubgroup K L` by the equivalent condition
`(residueDegree : ℤ) ∣ m - n`.
-/
theorem fieldNormSubgroup_uniformizer_zpow_div_mem_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (m n : ℤ) :
    ϖK ^ m / ϖK ^ n ∈ fieldNormSubgroup K L ↔
      (residueDegree : ℤ) ∣ m - n := by
  rw [fieldNormSubgroup_div_mem_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero (ϖK ^ m) (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK m,
    vK.val_uniformizer_zpow hϖK n]

/--
Establishes the identity `QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk'
(fieldNormSubgroup K L) (ϖK ^ vK.val x)`.
-/
theorem fieldNormQuotient_mk_eq_uniformizer_zpow_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) (x : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
      QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ vK.val x) := by
  rw [fieldNormQuotient_mk_eq_iff_div_mem K L x (ϖK ^ vK.val x)]
  exact hzero ((vK.div_mem_zeroSubgroup_iff x (ϖK ^ vK.val x)).2
    (by rw [vK.val_uniformizer_zpow hϖK (vK.val x)]))

/--
Establishes the identity `QuotientGroup.mk' (fieldNormSubgroup K L) x = (QuotientGroup.mk'
(fieldNormSubgroup K L) ϖK) ^ vK.val x`.
-/
theorem fieldNormQuotient_mk_eq_uniformizerClass_zpow_val
    (vK : MultiplicativeIntegerValuation Kˣ)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) (x : Kˣ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
      (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ vK.val x := by
  exact (fieldNormQuotient_mk_eq_uniformizer_zpow_val
    K L vK hϖK hzero x).trans
      (map_zpow (QuotientGroup.mk' (fieldNormSubgroup K L)) ϖK (vK.val x))

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = QuotientGroup.mk' (fieldNormSubgroup
K L) (ϖK ^ n)` by the equivalent condition `(residueDegree : ℤ) ∣ vK.val x - n`.
-/
theorem fieldNormQuotient_mk_eq_uniformizer_zpow_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x : Kˣ) (n : ℤ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
        QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ n) ↔
      (residueDegree : ℤ) ∣ vK.val x - n := by
  rw [fieldNormQuotient_mk_eq_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero x (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK n]

/--
Characterizes `QuotientGroup.mk' (fieldNormSubgroup K L) x = (QuotientGroup.mk' (fieldNormSubgroup
K L) ϖK) ^ n` by the equivalent condition `(residueDegree : ℤ) ∣ vK.val x - n`.
-/
theorem fieldNormQuotient_mk_eq_uniformizerClass_zpow_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (x : Kˣ) (n : ℤ) :
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
        (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n ↔
      (residueDegree : ℤ) ∣ vK.val x - n := by
  have hpow : QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ n) =
      (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n :=
    map_zpow (QuotientGroup.mk' (fieldNormSubgroup K L)) ϖK n
  rw [← hpow]
  exact fieldNormQuotient_mk_eq_uniformizer_zpow_iff
    K L vK vL residueDegree hformula hϖK hϖL hzero x n

/--
Characterizes `(QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ m = (QuotientGroup.mk'
(fieldNormSubgroup K L) ϖK) ^ n` by the equivalent condition `(residueDegree : ℤ) ∣ m - n`.
-/
theorem fieldNormQuotient_uniformizerClass_zpow_eq_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (m n : ℤ) :
    (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ m =
        (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n ↔
      (residueDegree : ℤ) ∣ m - n := by
  have hpow (k : ℤ) : QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ k) =
      (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ k :=
    map_zpow (QuotientGroup.mk' (fieldNormSubgroup K L)) ϖK k
  rw [← hpow m, ← hpow n,
    fieldNormQuotient_mk_eq_iff_residueDegree_dvd_valuation_difference
      K L vK vL residueDegree hformula hϖL hzero (ϖK ^ m) (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK m,
    vK.val_uniformizer_zpow hϖK n]

/--
Characterizes `(QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n = 1` by the equivalent condition
`(residueDegree : ℤ) ∣ n`.
-/
theorem fieldNormQuotient_uniformizerClass_zpow_eq_one_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (n : ℤ) :
    (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n = 1 ↔
      (residueDegree : ℤ) ∣ n := by
  have hpow : QuotientGroup.mk' (fieldNormSubgroup K L) (ϖK ^ n) =
      (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n :=
    map_zpow (QuotientGroup.mk' (fieldNormSubgroup K L)) ϖK n
  rw [← hpow,
    fieldNormQuotient_mk_eq_one_iff_residueDegree_dvd_val
      K L vK vL residueDegree hformula hϖL hzero (ϖK ^ n),
    vK.val_uniformizer_zpow hϖK n]

/--
Establishes the identity `(QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ (residueDegree : ℤ) =
1`.
-/
theorem fieldNormQuotient_uniformizerClass_zpow_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) :
    (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^
        (residueDegree : ℤ) = 1 := by
  rw [fieldNormQuotient_uniformizerClass_zpow_eq_one_iff
      K L vK vL residueDegree hformula hϖK hϖL hzero
      (residueDegree : ℤ)]

/-- The concrete field-norm quotient is generated by the class of any target
uniformizer under the standard valuation-zero norm-surjectivity hypothesis. -/
theorem fieldNormQuotient_generated_by_uniformizerClass
    (vK : MultiplicativeIntegerValuation Kˣ)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (q : Kˣ ⧸ fieldNormSubgroup K L) :
    ∃ n : ℤ,
      q = (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n := by
  refine QuotientGroup.induction_on q ?_
  intro x
  change ∃ n : ℤ,
    QuotientGroup.mk' (fieldNormSubgroup K L) x =
      (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK) ^ n
  exact ⟨vK.val x,
    fieldNormQuotient_mk_eq_uniformizerClass_zpow_val
      K L vK hϖK hzero x⟩

/--
Establishes the identity `Subgroup.closure ({QuotientGroup.mk' (fieldNormSubgroup K L) ϖK} : Set
(Kˣ ⧸ fieldNormSubgroup K L)) = ⊤`.
-/
theorem fieldNormQuotient_closure_uniformizerClass_eq_top
    (vK : MultiplicativeIntegerValuation Kˣ)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) :
    Subgroup.closure
        ({QuotientGroup.mk' (fieldNormSubgroup K L) ϖK} :
          Set (Kˣ ⧸ fieldNormSubgroup K L)) =
      ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro q hq
    rcases fieldNormQuotient_generated_by_uniformizerClass
        K L vK hϖK hzero q with
      ⟨n, hqpow⟩
    rw [hqpow]
    exact Subgroup.zpow_mem
      (Subgroup.closure
        ({QuotientGroup.mk' (fieldNormSubgroup K L) ϖK} :
          Set (Kˣ ⧸ fieldNormSubgroup K L)))
      (Subgroup.subset_closure (by simp)) n

/-- Establishes the identity `fieldNormSubgroup K L = ⊤`. -/
theorem fieldNormSubgroup_eq_top_of_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (hres : residueDegree = 1) :
    fieldNormSubgroup K L = ⊤ := by
  ext x
  constructor
  · intro _
    simp
  · intro _
    exact
      fieldNormSubgroup_mem_of_residueDegree_dvd_val_of_zeroSubgroup_le
        K L vK vL residueDegree hformula hϖL hzero
        (by rw [hres]; exact one_dvd (vK.val x))

/-- The specified map is surjective: `Function.Surjective (normUnits K L)`. -/
theorem fieldNormUnits_surjective_of_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (hres : residueDegree = 1) :
    Function.Surjective (normUnits K L) := by
  rw [← fieldNormSubgroup_eq_top_iff K L]
  exact fieldNormSubgroup_eq_top_of_residueDegree_eq_one
    K L vK vL residueDegree hformula hϖL hzero hres

/-- Under the standard valuation formula and valuation-zero norm-surjectivity,
the field norm on units is surjective exactly in residue degree one. -/
theorem fieldNormUnits_surjective_iff_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) :
    Function.Surjective (normUnits K L) ↔ residueDegree = 1 := by
  constructor
  · intro hsurj
    have hvalϖK : vK.val ϖK = 1 := hϖK
    rcases hsurj ϖK with ⟨z, hz⟩
    have hmem : ϖK ∈ fieldNormSubgroup K L := ⟨z, hz⟩
    have hdiv : (residueDegree : ℤ) ∣ (1 : ℤ) := by
      simpa [hvalϖK] using
        fieldNormSubgroup_residueDegree_dvd_val_of_mem
          K L vK vL residueDegree hformula hmem
    have hInt : (residueDegree : ℤ) = 1 :=
      Int.eq_one_of_dvd_one (by exact_mod_cast Nat.zero_le residueDegree) hdiv
    exact_mod_cast hInt
  · intro hres
    exact fieldNormUnits_surjective_of_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖL hzero hres

/-- Subgroup form of the residue-degree-one norm-surjectivity criterion. -/
theorem fieldNormSubgroup_eq_top_iff_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) :
    fieldNormSubgroup K L = ⊤ ↔ residueDegree = 1 := by
  rw [fieldNormSubgroup_eq_top_iff K L]
  exact fieldNormUnits_surjective_iff_residueDegree_eq_one
    K L vK vL residueDegree hformula hϖK hϖL hzero

/-- Establishes the identity `q = 1`. -/
theorem fieldNormQuotient_eq_one_of_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (hres : residueDegree = 1)
    (q : Kˣ ⧸ fieldNormSubgroup K L) :
    q = 1 := by
  rcases QuotientGroup.mk'_surjective (fieldNormSubgroup K L) q with
    ⟨x, rfl⟩
  exact (fieldNormQuotient_mk_eq_one_iff_residueDegree_dvd_val
    K L vK vL residueDegree hformula hϖL hzero x).2
      (by rw [hres]; exact one_dvd (vK.val x))

/-- Establishes the identity `q = r`. -/
theorem fieldNormQuotient_eq_of_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L)
    (hres : residueDegree = 1)
    (q r : Kˣ ⧸ fieldNormSubgroup K L) :
    q = r := by
  rw [fieldNormQuotient_eq_one_of_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖL hzero hres q,
    fieldNormQuotient_eq_one_of_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖL hzero hres r]

/-- Quotient form of the residue-degree-one norm-surjectivity criterion. -/
theorem fieldNormQuotient_forall_eq_one_iff_residueDegree_eq_one
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    {ϖK : Kˣ} (hϖK : vK.IsUniformizer ϖK)
    {ϖL : Lˣ} (hϖL : vL.IsUniformizer ϖL)
    (hzero : vK.zeroSubgroup ≤ fieldNormSubgroup K L) :
    (∀ q : Kˣ ⧸ fieldNormSubgroup K L, q = 1) ↔ residueDegree = 1 := by
  constructor
  · intro hq
    have hvalϖK : vK.val ϖK = 1 := hϖK
    have hclass :
        QuotientGroup.mk' (fieldNormSubgroup K L) ϖK = 1 :=
      hq (QuotientGroup.mk' (fieldNormSubgroup K L) ϖK)
    have hdiv : (residueDegree : ℤ) ∣ (1 : ℤ) := by
      simpa [hvalϖK] using
        (fieldNormQuotient_mk_eq_one_iff_residueDegree_dvd_val
          K L vK vL residueDegree hformula hϖL hzero ϖK).1 hclass
    have hInt : (residueDegree : ℤ) = 1 :=
      Int.eq_one_of_dvd_one (by exact_mod_cast Nat.zero_le residueDegree) hdiv
    exact_mod_cast hInt
  · intro hres q
    exact fieldNormQuotient_eq_one_of_residueDegree_eq_one
      K L vK vL residueDegree hformula hϖL hzero hres q

/-- Concrete compatibility condition saying that the field norm maps the
`n`-th source principal-unit subgroup into the requested target level. -/
abbrev fieldNormMapsFiltrationLevels
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) : Prop :=
  ∀ n {x : Lˣ}, x ∈ UL.principalUnitSubgroup n →
    normUnits K L x ∈ UK.principalUnitSubgroup (targetLevel n)

/--
Characterizes `ValuedNorm.MapsFiltrationLevels (valuedFieldNorm K L vK vL residueDegree hformula)
UK UL targetLevel` by the equivalent condition `fieldNormMapsFiltrationLevels K L UK UL
targetLevel`.
-/
theorem valuedFieldNorm_mapsFiltrationLevels_iff
    (vK : MultiplicativeIntegerValuation Kˣ)
    (vL : MultiplicativeIntegerValuation Lˣ)
    (residueDegree : ℕ)
    (hformula :
      ∀ x : Lˣ, vK.val (normUnits K L x) =
        (residueDegree : ℤ) * vL.val x)
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) :
    ValuedNorm.MapsFiltrationLevels
        (valuedFieldNorm K L vK vL residueDegree hformula)
        UK UL targetLevel ↔
      fieldNormMapsFiltrationLevels K L UK UL targetLevel :=
  Iff.rfl

/-- Filtration compatibility can be weakened by replacing the target level by
a coarser one. -/
theorem fieldNormMapsFiltrationLevels_of_le
    {UK : AntitoneSubgroupFiltration Kˣ} {UL : AntitoneSubgroupFiltration Lˣ}
    {targetLevel targetLevel' : ℕ → ℕ}
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel)
    (hle : ∀ n, targetLevel' n ≤ targetLevel n) :
    fieldNormMapsFiltrationLevels K L UK UL targetLevel' := by
  intro n x hx
  exact UK.mem_of_mem_of_le (hle n) (hN n hx)

/-- The field norm restricted to a principal-unit filtration level. -/
def fieldNormMapLevelOfMapsFiltrationLevels
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ) :
    UL.principalUnitSubgroup n →*
      UK.principalUnitSubgroup (targetLevel n) where
  toFun x := ⟨normUnits K L x.1, hN n x.2⟩
  map_one' := by
    apply Subtype.ext
    exact (normUnits K L).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (normUnits K L).map_mul x.1 y.1

/--
The defining evaluation formula for `fieldNormMapLevelOfMapsFiltrationLevels` is
`(fieldNormMapLevelOfMapsFiltrationLevels K L UK UL targetLevel hN n x : Kˣ) = normUnits K L
x.1`.
-/
@[simp] theorem fieldNormMapLevelOfMapsFiltrationLevels_apply
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    (x : UL.principalUnitSubgroup n) :
    (fieldNormMapLevelOfMapsFiltrationLevels K L UK UL targetLevel hN n x :
        Kˣ) =
      normUnits K L x.1 :=
  rfl

/-- The field norm descended to quotients by compatible principal-unit
filtration levels. -/
def fieldNormFiltrationQuotientMap
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    Lˣ ⧸ UL.principalUnitSubgroup n →*
      Kˣ ⧸ UK.principalUnitSubgroup (targetLevel n) :=
  QuotientGroup.map (UL.principalUnitSubgroup n)
    (UK.principalUnitSubgroup (targetLevel n)) (normUnits K L) (by
      intro x hx
      exact hN n hx)

/--
The defining evaluation formula for `fieldNormFiltrationQuotientMap` is
`fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n (QuotientGroup.mk x) = QuotientGroup.mk
(normUnits K L x)`.
-/
@[simp] theorem fieldNormFiltrationQuotientMap_apply_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk x) =
      QuotientGroup.mk (normUnits K L x) :=
  rfl

/--
Establishes the identity `fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
(QuotientGroup.mk' (UL.principalUnitSubgroup n) x) = QuotientGroup.mk' (UK.principalUnitSubgroup
(targetLevel n)) (normUnits K L x)`.
-/
@[simp] theorem fieldNormFiltrationQuotientMap_apply_mk'
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk' (UL.principalUnitSubgroup n) x) =
      QuotientGroup.mk' (UK.principalUnitSubgroup (targetLevel n))
        (normUnits K L x) :=
  rfl

/--
Characterizes `fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n (QuotientGroup.mk'
(UL.principalUnitSubgroup n) x) = 1` by the equivalent condition `normUnits K L x ∈
UK.principalUnitSubgroup (targetLevel n)`.
-/
theorem fieldNormFiltrationQuotientMap_mk_eq_one_iff
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk' (UL.principalUnitSubgroup n) x) = 1 ↔
      normUnits K L x ∈
        UK.principalUnitSubgroup (targetLevel n) := by
  rw [fieldNormFiltrationQuotientMap_apply_mk']
  exact UK.quotient_principalUnitSubgroup_mk_eq_one_iff
    (targetLevel n) (normUnits K L x)

/--
Characterizes `fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n (QuotientGroup.mk'
(UL.principalUnitSubgroup n) x) = fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
(QuotientGroup.mk' (UL.principalUnitSubgroup n) y)` by the equivalent condition `normUnits K
L (x / y) ∈ UK.principalUnitSubgroup (targetLevel n)`.
-/
theorem fieldNormFiltrationQuotientMap_mk_eq_iff_div_mem
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x y : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk' (UL.principalUnitSubgroup n) x) =
      fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk' (UL.principalUnitSubgroup n) y) ↔
      normUnits K L (x / y) ∈
        UK.principalUnitSubgroup (targetLevel n) := by
  rw [fieldNormFiltrationQuotientMap_apply_mk',
    fieldNormFiltrationQuotientMap_apply_mk']
  rw [(normUnits K L).map_div x y]
  exact
    (UK.quotient_principalUnitSubgroup_mk_eq_iff_div_mem
      (targetLevel n) (normUnits K L x) (normUnits K L y))

/--
Characterizes `fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n (QuotientGroup.mk'
(UL.principalUnitSubgroup n) x) = fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
(QuotientGroup.mk' (UL.principalUnitSubgroup n) y)` by the equivalent condition `normUnits K
L (y⁻¹ * x) ∈ UK.principalUnitSubgroup (targetLevel n)`.
-/
theorem fieldNormFiltrationQuotientMap_mk_eq_iff_inv_mul_mem
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] (x y : Lˣ) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk' (UL.principalUnitSubgroup n) x) =
      fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n
        (QuotientGroup.mk' (UL.principalUnitSubgroup n) y) ↔
      normUnits K L (y⁻¹ * x) ∈
        UK.principalUnitSubgroup (targetLevel n) := by
  rw [fieldNormFiltrationQuotientMap_mk_eq_iff_div_mem
      K L UK UL targetLevel hN n x y,
    (normUnits K L).map_div x y,
    UK.principalUnitSubgroup_div_mem_iff_inv_mul_mem
      (targetLevel n) (normUnits K L x) (normUnits K L y)]
  simp [mul_comm]

/--
Characterizes `Function.Surjective (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n)` by
the equivalent condition `∀ y : Kˣ, ∃ x : Lˣ, normUnits K L x / y ∈ UK.principalUnitSubgroup
(targetLevel n)`.
-/
theorem fieldNormFiltrationQuotientMap_surjective_iff_exists_div_mem
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    Function.Surjective
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n) ↔
      ∀ y : Kˣ, ∃ x : Lˣ,
        normUnits K L x / y ∈
          UK.principalUnitSubgroup (targetLevel n) := by
  constructor
  · intro hsurj y
    rcases hsurj (QuotientGroup.mk y) with ⟨q, hq⟩
    revert hq
    refine QuotientGroup.induction_on q ?_
    intro x hq
    rw [fieldNormFiltrationQuotientMap_apply_mk] at hq
    exact ⟨x,
      (QuotientGroup.eq_iff_div_mem
        (N := UK.principalUnitSubgroup (targetLevel n))
        (x := normUnits K L x) (y := y)).1 hq⟩
  · intro h yq
    refine QuotientGroup.induction_on yq ?_
    intro y
    rcases h y with ⟨x, hx⟩
    refine ⟨QuotientGroup.mk x, ?_⟩
    rw [fieldNormFiltrationQuotientMap_apply_mk]
    exact
      (QuotientGroup.eq_iff_div_mem
        (N := UK.principalUnitSubgroup (targetLevel n))
        (x := normUnits K L x) (y := y)).2 hx

/--
The specified map is surjective: `Function.Surjective (fieldNormFiltrationQuotientMap K L UK UL
targetLevel hN n)`.
-/
theorem fieldNormFiltrationQuotientMap_surjective_of_exists_div_mem
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (hLift : ∀ y : Kˣ, ∃ x : Lˣ,
      normUnits K L x / y ∈
        UK.principalUnitSubgroup (targetLevel n)) :
    Function.Surjective
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n) :=
  (fieldNormFiltrationQuotientMap_surjective_iff_exists_div_mem
    K L UK UL targetLevel hN n).2 hLift

/-- The preimage of a target principal-unit filtration subgroup under the
field norm. -/
def fieldNormFiltrationPreimageSubgroup
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ) :
    Subgroup Lˣ :=
  (UK.principalUnitSubgroup (targetLevel n)).comap (normUnits K L)

/--
Characterizes `x ∈ fieldNormFiltrationPreimageSubgroup K L UK targetLevel n` by the equivalent
condition `normUnits K L x ∈ UK.principalUnitSubgroup (targetLevel n)`.
-/
@[simp] theorem mem_fieldNormFiltrationPreimageSubgroup_iff
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ)
    (x : Lˣ) :
    x ∈ fieldNormFiltrationPreimageSubgroup K L UK targetLevel n ↔
      normUnits K L x ∈
        UK.principalUnitSubgroup (targetLevel n) :=
  Iff.rfl

/--
Proves the bound `UL.principalUnitSubgroup n ≤ fieldNormFiltrationPreimageSubgroup K L UK
targetLevel n`.
-/
theorem principalUnitSubgroup_le_fieldNormFiltrationPreimageSubgroup
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ) :
    UL.principalUnitSubgroup n ≤
      fieldNormFiltrationPreimageSubgroup K L UK targetLevel n := by
  intro x hx
  exact hN n hx

/--
The subgroup appearing in `(fieldNormFiltrationPreimageSubgroup K L UK targetLevel n).Normal` is
normal.
-/
instance fieldNormFiltrationPreimageSubgroup_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageSubgroup]
  infer_instance

/-- The class of the field-norm preimage of the target filtration subgroup
inside the source filtration quotient. -/
def fieldNormFiltrationPreimageClassInQuotient
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal] :
    Subgroup (Lˣ ⧸ UL.principalUnitSubgroup n) :=
  Subgroup.map (QuotientGroup.mk' (UL.principalUnitSubgroup n))
    (fieldNormFiltrationPreimageSubgroup K L UK targetLevel n)

/--
The subgroup appearing in `(fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel
n).Normal` is normal.
-/
instance fieldNormFiltrationPreimageClassInQuotient_normal
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationPreimageClassInQuotient
      K L UK UL targetLevel n).Normal := by
  dsimp [fieldNormFiltrationPreimageClassInQuotient]
  infer_instance

/--
Characterizes `q ∈ fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel n` by the
equivalent condition `∃ x : Lˣ, x ∈ fieldNormFiltrationPreimageSubgroup K L UK targetLevel n ∧
QuotientGroup.mk' (UL.principalUnitSubgroup n) x = q`.
-/
theorem mem_fieldNormFiltrationPreimageClassInQuotient_iff
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    q ∈ fieldNormFiltrationPreimageClassInQuotient
        K L UK UL targetLevel n ↔
      ∃ x : Lˣ,
        x ∈ fieldNormFiltrationPreimageSubgroup K L UK targetLevel n ∧
        QuotientGroup.mk' (UL.principalUnitSubgroup n) x = q :=
  Iff.rfl

/--
Characterizes `q ∈ fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel n` by the
equivalent condition `∃ x : Lˣ, normUnits K L x ∈ UK.principalUnitSubgroup (targetLevel n) ∧
QuotientGroup.mk' (UL.principalUnitSubgroup n) x = q`.
-/
theorem mem_fieldNormFiltrationPreimageClassInQuotient_iff_exists_norm_mem
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    q ∈ fieldNormFiltrationPreimageClassInQuotient
        K L UK UL targetLevel n ↔
      ∃ x : Lˣ,
        normUnits K L x ∈
          UK.principalUnitSubgroup (targetLevel n) ∧
        QuotientGroup.mk' (UL.principalUnitSubgroup n) x = q := by
  rw [mem_fieldNormFiltrationPreimageClassInQuotient_iff
    K L UK UL targetLevel n q]
  rfl

/--
Establishes the membership statement `QuotientGroup.mk' (UL.principalUnitSubgroup n) x ∈
fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel n`.
-/
theorem fieldNormFiltrationPreimageClassInQuotient_mk_mem
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ) {n : ℕ}
    [(UL.principalUnitSubgroup n).Normal] {x : Lˣ}
    (hx : x ∈ fieldNormFiltrationPreimageSubgroup K L UK targetLevel n) :
    QuotientGroup.mk' (UL.principalUnitSubgroup n) x ∈
      fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel n :=
  Subgroup.mem_map_of_mem (QuotientGroup.mk' (UL.principalUnitSubgroup n)) hx

/-- The kernel of the concrete field-norm filtration quotient map is the class
of the norm-preimage of the target filtration subgroup. -/
theorem fieldNormFiltrationQuotientMap_ker_eq_preimageClass
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).ker =
      fieldNormFiltrationPreimageClassInQuotient
        K L UK UL targetLevel n := by
  exact QuotientGroup.ker_map (UL.principalUnitSubgroup n)
    (UK.principalUnitSubgroup (targetLevel n)) (normUnits K L)
    (by intro x hx; exact hN n hx)

/--
Characterizes `fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n q = 1` by the equivalent
condition `q ∈ fieldNormFiltrationPreimageClassInQuotient K L UK UL targetLevel n`.
-/
theorem fieldNormFiltrationQuotientMap_eq_one_iff_mem_preimageClass
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n q = 1 ↔
      q ∈ fieldNormFiltrationPreimageClassInQuotient
        K L UK UL targetLevel n := by
  rw [← MonoidHom.mem_ker,
    fieldNormFiltrationQuotientMap_ker_eq_preimageClass
      K L UK UL targetLevel hN n]

/-- First-isomorphism form of the concrete field-norm filtration quotient map,
with codomain the actual range when no surjectivity hypothesis is available. -/
noncomputable def fieldNormFiltrationQuotientModuloPreimageClassEquivRange
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal] :
    (Lˣ ⧸ UL.principalUnitSubgroup n) ⧸
        fieldNormFiltrationPreimageClassInQuotient
          K L UK UL targetLevel n ≃*
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).range :=
  (QuotientGroup.quotientMulEquivOfEq
      (fieldNormFiltrationQuotientMap_ker_eq_preimageClass
        K L UK UL targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivRange
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n))

/--
Establishes the identity `fieldNormFiltrationQuotientModuloPreimageClassEquivRange K L UK UL
targetLevel hN n (QuotientGroup.mk' (fieldNormFiltrationPreimageClassInQuotient K L UK UL
targetLevel n) q) = (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).rangeRestrict q`.
-/
theorem fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    fieldNormFiltrationQuotientModuloPreimageClassEquivRange
        K L UK UL targetLevel hN n
        (QuotientGroup.mk'
          (fieldNormFiltrationPreimageClassInQuotient
            K L UK UL targetLevel n) q) =
      (fieldNormFiltrationQuotientMap
        K L UK UL targetLevel hN n).rangeRestrict q :=
  rfl

/--
Establishes the identity `((fieldNormFiltrationQuotientModuloPreimageClassEquivRange K L UK UL
targetLevel hN n (QuotientGroup.mk' (fieldNormFiltrationPreimageClassInQuotient K L UK UL
targetLevel n) q) : (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n).range) : Kˣ ⧸
UK.principalUnitSubgroup (targetLevel n)) = fieldNormFiltrationQuotientMap K L UK UL targetLevel
hN n q`.
-/
theorem coe_fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    ((fieldNormFiltrationQuotientModuloPreimageClassEquivRange
        K L UK UL targetLevel hN n
        (QuotientGroup.mk'
          (fieldNormFiltrationPreimageClassInQuotient
            K L UK UL targetLevel n) q) :
      (fieldNormFiltrationQuotientMap
        K L UK UL targetLevel hN n).range) :
        Kˣ ⧸ UK.principalUnitSubgroup (targetLevel n)) =
      fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n q := by
  rw [fieldNormFiltrationQuotientModuloPreimageClassEquivRange_mk]
  rfl

/-- First-isomorphism form of a surjective concrete field-norm filtration
quotient map. -/
noncomputable def fieldNormFiltrationQuotientModuloPreimageClassEquivTarget
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n)) :
    (Lˣ ⧸ UL.principalUnitSubgroup n) ⧸
        fieldNormFiltrationPreimageClassInQuotient
          K L UK UL targetLevel n ≃*
      Kˣ ⧸ UK.principalUnitSubgroup (targetLevel n) :=
  (QuotientGroup.quotientMulEquivOfEq
      (fieldNormFiltrationQuotientMap_ker_eq_preimageClass
        K L UK UL targetLevel hN n).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (φ := fieldNormFiltrationQuotientMap
        K L UK UL targetLevel hN n) hSurj)

/--
Establishes the identity `fieldNormFiltrationQuotientModuloPreimageClassEquivTarget K L UK UL
targetLevel hN n hSurj (QuotientGroup.mk' (fieldNormFiltrationPreimageClassInQuotient K L UK UL
targetLevel n) q) = fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n q`.
-/
theorem fieldNormFiltrationQuotientModuloPreimageClassEquivTarget_mk
    (UK : AntitoneSubgroupFiltration Kˣ) (UL : AntitoneSubgroupFiltration Lˣ)
    (targetLevel : ℕ → ℕ)
    (hN : fieldNormMapsFiltrationLevels K L UK UL targetLevel) (n : ℕ)
    [(UL.principalUnitSubgroup n).Normal]
    [(UK.principalUnitSubgroup (targetLevel n)).Normal]
    (hSurj : Function.Surjective
      (fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n))
    (q : Lˣ ⧸ UL.principalUnitSubgroup n) :
    fieldNormFiltrationQuotientModuloPreimageClassEquivTarget
        K L UK UL targetLevel hN n hSurj
        (QuotientGroup.mk'
          (fieldNormFiltrationPreimageClassInQuotient
            K L UK UL targetLevel n) q) =
      fieldNormFiltrationQuotientMap K L UK UL targetLevel hN n q := by
  rw [fieldNormFiltrationQuotientModuloPreimageClassEquivTarget,
    QuotientGroup.quotientKerEquivOfSurjective,
    QuotientGroup.quotientKerEquivOfRightInverse]
  exact QuotientGroup.kerLift_mk
    (φ := fieldNormFiltrationQuotientMap
      K L UK UL targetLevel hN n) q

end DiscreteValuationField

end

end LocalFieldTheory
