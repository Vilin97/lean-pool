/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.SetTheory.Cardinal.Finite
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.DiscreteValuationField.Norm.Basic

/-!
Develops quotient groups attached to an abstract valued norm, including kernel, image, and
representative criteria.
-/

/-!
Identifies norm-quotient classes with valuation classes modulo the residue degree and constructs
the resulting cyclic equivalences.
-/
namespace LocalFieldTheory

noncomputable section

universe u v

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)

/--
The defining evaluation formula for `valuation` is `vG.val (N.toHom x) = (N.residueDegree : ℤ) *
vH.val x`.
-/
@[simp] theorem valuation_apply (x : H) :
    vG.val (N.toHom x) = (N.residueDegree : ℤ) * vH.val x :=
  N.valuation_formula x

/--
`valuation_apply` satisfies the division formula `vG.val (N.toHom (x / y)) = (N.residueDegree : ℤ)
* (vH.val x - vH.val y)`.
-/
theorem valuation_apply_div (x y : H) :
    vG.val (N.toHom (x / y)) =
      (N.residueDegree : ℤ) * (vH.val x - vH.val y) := by
  rw [N.valuation_apply, vH.val_div]

/--
`valuation_apply_uniformizer` satisfies the integer-power formula `vG.val (N.toHom (ϖH ^ n)) =
(N.residueDegree : ℤ) * n`.
-/
theorem valuation_apply_uniformizer_zpow {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (n : ℤ) :
    vG.val (N.toHom (ϖH ^ n)) = (N.residueDegree : ℤ) * n := by
  rw [N.valuation_apply, vH.val_uniformizer_zpow hϖH n]

/--
`valuation_apply_uniformizer` satisfies the natural-power formula `vG.val (N.toHom (ϖH ^ n)) =
(N.residueDegree : ℤ) * (n : ℤ)`.
-/
theorem valuation_apply_uniformizer_pow {ϖH : H}
    (hϖH : vH.IsUniformizer ϖH) (n : ℕ) :
    vG.val (N.toHom (ϖH ^ n)) = (N.residueDegree : ℤ) * (n : ℤ) := by
  rw [N.valuation_apply, vH.val_uniformizer_pow hϖH n]

/--
`valuation_apply_zeroSubgroup_mul_uniformizer` satisfies the integer-power formula `vG.val
(N.toHom (u * ϖH ^ n)) = (N.residueDegree : ℤ) * n`.
-/
theorem valuation_apply_zeroSubgroup_mul_uniformizer_zpow
    {ϖH u : H} (hϖH : vH.IsUniformizer ϖH)
    (hu : u ∈ vH.zeroSubgroup) (n : ℤ) :
    vG.val (N.toHom (u * ϖH ^ n)) = (N.residueDegree : ℤ) * n := by
  rw [N.valuation_apply, vH.valuation_uniformizer_normal_form hϖH hu n]

/--
`valuation_apply_zeroSubgroup_mul_uniformizer` satisfies the natural-power formula `vG.val
(N.toHom (u * ϖH ^ n)) = (N.residueDegree : ℤ) * (n : ℤ)`.
-/
theorem valuation_apply_zeroSubgroup_mul_uniformizer_pow
    {ϖH u : H} (hϖH : vH.IsUniformizer ϖH)
    (hu : u ∈ vH.zeroSubgroup) (n : ℕ) :
    vG.val (N.toHom (u * ϖH ^ n)) =
      (N.residueDegree : ℤ) * (n : ℤ) := by
  rw [N.valuation_apply]
  have hv := vH.valuation_uniformizer_normal_form hϖH hu (n : ℤ)
  simpa using congrArg (fun m : ℤ => (N.residueDegree : ℤ) * m) hv

/--
Establishes the identity `vG.valuationHom (N.toHom x) = vH.valuationHom x ^ (N.residueDegree :
ℤ)`.
-/
theorem valuationHom_apply_norm (x : H) :
    vG.valuationHom (N.toHom x) =
      vH.valuationHom x ^ (N.residueDegree : ℤ) := by
  rw [MultiplicativeIntegerValuation.valuationHom_apply,
    N.valuation_apply,
    MultiplicativeIntegerValuation.valuationHom_apply,
    mul_comm (N.residueDegree : ℤ) (vH.val x),
    Int.ofAdd_mul]

/--
Establishes the identity `Multiplicative.toAdd (vG.valuationHom (N.toHom x)) = (N.residueDegree :
ℤ) * Multiplicative.toAdd (vH.valuationHom x)`.
-/
theorem toAdd_valuationHom_apply_norm (x : H) :
    Multiplicative.toAdd (vG.valuationHom (N.toHom x)) =
      (N.residueDegree : ℤ) *
        Multiplicative.toAdd (vH.valuationHom x) := by
  rw [N.valuationHom_apply_norm, Int.toAdd_zpow,
    MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
    mul_comm (vH.val x) (N.residueDegree : ℤ)]

/--
`valuationHom_apply_norm` satisfies the division formula `vG.valuationHom (N.toHom (x / y)) =
vH.valuationHom (x / y) ^ (N.residueDegree : ℤ)`.
-/
theorem valuationHom_apply_norm_div (x y : H) :
    vG.valuationHom (N.toHom (x / y)) =
      vH.valuationHom (x / y) ^ (N.residueDegree : ℤ) :=
  N.valuationHom_apply_norm (x / y)

/-- Norms of valuation-zero elements have valuation zero. -/
theorem maps_zeroSubgroup {x : H} (hx : x ∈ vH.zeroSubgroup) :
    N.toHom x ∈ vG.zeroSubgroup := by
  rw [MultiplicativeIntegerValuation.mem_zeroSubgroup_iff,
    N.valuation_apply,
    (MultiplicativeIntegerValuation.mem_zeroSubgroup_iff vH x).mp hx,
    mul_zero]

/-- The norm subgroup attached to a valued norm. -/
def normSubgroup : Subgroup G :=
  N.toHom.range

/-- The valuation of any norm is divisible by the residue degree. -/
theorem residueDegree_dvd_valuation_of_mem_normSubgroup
    {x : G} (hx : x ∈ N.normSubgroup) :
    (N.residueDegree : ℤ) ∣ vG.val x := by
  rcases hx with ⟨y, rfl⟩
  exact ⟨vH.val y, N.valuation_apply y⟩

/-- If the source valuation has a uniformizer, every residue-degree multiple is
realized as the valuation of an element of the norm subgroup. -/
theorem exists_normSubgroup_val_eq_residueDegree_mul_of_uniformizer
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH) (n : ℤ) :
    ∃ x : G, x ∈ N.normSubgroup ∧
      vG.val x = (N.residueDegree : ℤ) * n :=
  ⟨N.toHom (ϖH ^ n),
    (MonoidHom.mem_range (f := N.toHom)).2 ⟨ϖH ^ n, rfl⟩,
    N.valuation_apply_uniformizer_zpow hϖH n⟩

/-- Source-uniformizer form of the value image of the norm subgroup. -/
theorem exists_normSubgroup_val_eq_iff_residueDegree_dvd_of_uniformizer
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH) (m : ℤ) :
    (∃ x : G, x ∈ N.normSubgroup ∧ vG.val x = m) ↔
      (N.residueDegree : ℤ) ∣ m := by
  constructor
  · rintro ⟨x, hx, hxm⟩
    rw [← hxm]
    exact N.residueDegree_dvd_valuation_of_mem_normSubgroup hx
  · rintro ⟨n, hm⟩
    rcases
      N.exists_normSubgroup_val_eq_residueDegree_mul_of_uniformizer hϖH n
        with ⟨x, hx, hvx⟩
    exact ⟨x, hx, by rw [hvx, ← hm]⟩

/-- The value of any norm-subgroup element lies in the residue-degree multiple
subgroup of the target value group. -/
theorem valuationHom_mem_integerMultipleSubgroup_of_mem_normSubgroup
    {x : G} (hx : x ∈ N.normSubgroup) :
    vG.valuationHom x ∈ integerMultipleSubgroup (N.residueDegree : ℤ) := by
  rw [mem_integerMultipleSubgroup_iff,
    MultiplicativeIntegerValuation.valuationHom_apply,
    toAdd_ofAdd]
  exact N.residueDegree_dvd_valuation_of_mem_normSubgroup hx

/--
Establishes the membership statement `vG.valuationHom (N.toHom x) ∈ integerMultipleSubgroup
(N.residueDegree : ℤ)`.
-/
theorem valuationHom_norm_mem_integerMultipleSubgroup (x : H) :
    vG.valuationHom (N.toHom x) ∈
      integerMultipleSubgroup (N.residueDegree : ℤ) :=
  N.valuationHom_mem_integerMultipleSubgroup_of_mem_normSubgroup
    ((MonoidHom.mem_range (f := N.toHom)).2 ⟨x, rfl⟩)

/--
Establishes the identity `((vG.quotientZeroSubgroupEquivValueSubgroup (QuotientGroup.mk'
vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) : Multiplicative ℤ) = vH.valuationHom x ^
(N.residueDegree : ℤ)`.
-/
theorem coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk
    (x : H) :
    ((vG.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) :
      Multiplicative ℤ) =
      vH.valuationHom x ^ (N.residueDegree : ℤ) := by
  rw [MultiplicativeIntegerValuation.coe_quotientZeroSubgroupEquivValueSubgroup_mk]
  exact N.valuationHom_apply_norm x

/--
Establishes the identity `Multiplicative.toAdd (((vG.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) : Multiplicative ℤ)) =
(N.residueDegree : ℤ) * vH.val x`.
-/
theorem toAdd_quotientZeroSubgroupEquivValueSubgroup_norm_mk
    (x : H) :
    Multiplicative.toAdd
      (((vG.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) :
        Multiplicative ℤ)) =
      (N.residueDegree : ℤ) * vH.val x := by
  rw [N.coe_quotientZeroSubgroupEquivValueSubgroup_norm_mk,
    Int.toAdd_zpow,
    MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
    mul_comm (vH.val x) (N.residueDegree : ℤ)]

/-- If an element is a norm, then its class modulo valuation-zero elements maps
to a residue-degree multiple in the value group. -/
theorem quotientZeroSubgroup_value_mem_integerMultipleSubgroup_of_mem_normSubgroup
    {x : G} (hx : x ∈ N.normSubgroup) :
    ((vG.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) : vG.valueSubgroup) :
      Multiplicative ℤ) ∈
      integerMultipleSubgroup (N.residueDegree : ℤ) := by
  change (N.residueDegree : ℤ) ∣
    Multiplicative.toAdd
      (((vG.quotientZeroSubgroupEquivValueSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x) : vG.valueSubgroup) :
        Multiplicative ℤ))
  rw [vG.toAdd_quotientZeroSubgroupEquivValueSubgroup_mk]
  exact N.valuationHom_mem_integerMultipleSubgroup_of_mem_normSubgroup hx

/--
Establishes the membership statement `((vG.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) : Multiplicative ℤ) ∈
integerMultipleSubgroup (N.residueDegree : ℤ)`.
-/
theorem quotientZeroSubgroup_value_norm_mem_integerMultipleSubgroup
    (x : H) :
    ((vG.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (N.toHom x)) : vG.valueSubgroup) :
      Multiplicative ℤ) ∈
      integerMultipleSubgroup (N.residueDegree : ℤ) :=
  N.quotientZeroSubgroup_value_mem_integerMultipleSubgroup_of_mem_normSubgroup
    ((MonoidHom.mem_range (f := N.toHom)).2 ⟨x, rfl⟩)

/--
Establishes the membership statement `((vG.quotientZeroSubgroupEquivValueSubgroup
(QuotientGroup.mk' vG.zeroSubgroup (x / y)) : vG.valueSubgroup) : Multiplicative ℤ) ∈
integerMultipleSubgroup (N.residueDegree : ℤ)`.
-/
theorem quotientZeroSubgroup_value_div_mem_integerMultipleSubgroup_of_div_mem_normSubgroup
    {x y : G} (hxy : x / y ∈ N.normSubgroup) :
    ((vG.quotientZeroSubgroupEquivValueSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (x / y)) : vG.valueSubgroup) :
      Multiplicative ℤ) ∈
      integerMultipleSubgroup (N.residueDegree : ℤ) :=
  N.quotientZeroSubgroup_value_mem_integerMultipleSubgroup_of_mem_normSubgroup
    hxy

/-- If a quotient is a norm, then the valuation difference is divisible by the
residue degree. -/
theorem residueDegree_dvd_valuation_difference_of_div_mem_normSubgroup
    {x y : G} (hxy : x / y ∈ N.normSubgroup) :
    (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  have h := N.residueDegree_dvd_valuation_of_mem_normSubgroup hxy
  simpa [vG.val_div] using h

/-- Explicit multiple form of
`residueDegree_dvd_valuation_difference_of_div_mem_normSubgroup`. -/
theorem exists_valuation_difference_eq_residueDegree_mul_of_div_mem_normSubgroup
    {x y : G} (hxy : x / y ∈ N.normSubgroup) :
    ∃ n : ℤ, vG.val x - vG.val y = (N.residueDegree : ℤ) * n :=
  N.residueDegree_dvd_valuation_difference_of_div_mem_normSubgroup hxy

/-- Right-multiple form of the valuation difference forced by norm-subgroup
membership of a quotient. -/
theorem exists_valuation_difference_eq_mul_residueDegree_of_div_mem_normSubgroup
    {x y : G} (hxy : x / y ∈ N.normSubgroup) :
    ∃ n : ℤ, vG.val x - vG.val y = n * (N.residueDegree : ℤ) := by
  rcases
    N.exists_valuation_difference_eq_residueDegree_mul_of_div_mem_normSubgroup
      hxy with ⟨n, hn⟩
  exact ⟨n, by rw [hn, mul_comm]⟩

/-- If a quotient is represented by the norm of a specific element, its
valuation difference is computed by that element's valuation. -/
theorem valuation_difference_eq_residueDegree_mul_of_norm_eq_div
    {x y : G} {z : H} (hz : N.toHom z = x / y) :
    vG.val x - vG.val y = (N.residueDegree : ℤ) * vH.val z := by
  calc
    vG.val x - vG.val y = vG.val (x / y) := (vG.val_div x y).symm
    _ = vG.val (N.toHom z) := by rw [← hz]
    _ = (N.residueDegree : ℤ) * vH.val z := N.valuation_apply z

/-- Right-multiple form of
`valuation_difference_eq_residueDegree_mul_of_norm_eq_div`. -/
theorem valuation_difference_eq_mul_residueDegree_of_norm_eq_div
    {x y : G} {z : H} (hz : N.toHom z = x / y) :
    vG.val x - vG.val y = vH.val z * (N.residueDegree : ℤ) := by
  rw [N.valuation_difference_eq_residueDegree_mul_of_norm_eq_div hz,
    mul_comm]

/-- A norm-subgroup element is a valuation-zero factor times the norm of a
source-uniformizer power.  This is the abstract normal form behind local CFT
norm quotient calculations; no surjectivity on units is assumed. -/
theorem exists_zeroSubgroup_mul_norm_uniformizer_zpow_eq_of_mem_normSubgroup
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    {x : G} (hx : x ∈ N.normSubgroup) :
    ∃ u : G, u ∈ vG.zeroSubgroup ∧
      ∃ n : ℤ, x = u * N.toHom (ϖH ^ n) := by
  rcases N.residueDegree_dvd_valuation_of_mem_normSubgroup hx with ⟨n, hn⟩
  have hval :
      vG.val x = vG.val (N.toHom (ϖH ^ n)) := by
    rw [N.valuation_apply_uniformizer_zpow hϖH n, hn]
  rcases vG.exists_zeroSubgroup_mul_eq_of_val_eq hval with ⟨u, hu, hux⟩
  exact ⟨u, hu, n, hux.symm⟩

/-- If all valuation-zero target elements are norms and the source valuation
has a uniformizer, valuation divisibility by the residue degree is sufficient
for norm-subgroup membership. -/
theorem mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    {x : G} (hx : (N.residueDegree : ℤ) ∣ vG.val x) :
    x ∈ N.normSubgroup := by
  rcases hx with ⟨n, hn⟩
  have hval :
      vG.val x = vG.val (N.toHom (ϖH ^ n)) := by
    rw [N.valuation_apply_uniformizer_zpow hϖH n, hn]
  rcases vG.exists_zeroSubgroup_mul_eq_of_val_eq hval with ⟨u, hu, hux⟩
  have hu_norm : u ∈ N.normSubgroup := hzero hu
  have hnorm : u * N.toHom (ϖH ^ n) ∈ N.normSubgroup :=
    N.normSubgroup.mul_mem hu_norm
      ((MonoidHom.mem_range (f := N.toHom)).2 ⟨ϖH ^ n, rfl⟩)
  simpa [← hux] using hnorm

/-- With source uniformizer and norm-surjectivity on valuation-zero target
elements, the norm subgroup is exactly the elements whose valuation is
divisible by the residue degree. -/
theorem mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    x ∈ N.normSubgroup ↔ (N.residueDegree : ℤ) ∣ vG.val x := by
  constructor
  · exact N.residueDegree_dvd_valuation_of_mem_normSubgroup
  · exact N.mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero

/-- Quotient form of
`mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le`. -/
theorem div_mem_normSubgroup_iff_residueDegree_dvd_valuation_difference_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x y : G) :
    x / y ∈ N.normSubgroup ↔
      (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  rw [N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero (x / y),
    vG.val_div]

/-- In a normal norm subgroup, the right quotient `x / y` and the left quotient
`y⁻¹ * x` give the same membership test. -/
theorem div_mem_normSubgroup_iff_inv_mul_mem_normSubgroup
    [(N.normSubgroup).Normal] (x y : G) :
    x / y ∈ N.normSubgroup ↔ y⁻¹ * x ∈ N.normSubgroup := by
  simpa [div_eq_mul_inv] using
    ((inferInstance : (N.normSubgroup).Normal).mem_comm_iff
      (a := x) (b := y⁻¹))

/-- Left-quotient version of
`div_mem_normSubgroup_iff_inv_mul_mem_normSubgroup`. -/
theorem inv_mul_mem_normSubgroup_iff_div_mem_normSubgroup
    [(N.normSubgroup).Normal] (x y : G) :
    y⁻¹ * x ∈ N.normSubgroup ↔ x / y ∈ N.normSubgroup :=
  (N.div_mem_normSubgroup_iff_inv_mul_mem_normSubgroup x y).symm

/-- Left-quotient form of residue-degree divisibility for norm-subgroup
membership. -/
theorem inv_mul_mem_normSubgroup_iff_residueDegree_dvd_valuation_difference_of_zeroSubgroup_le
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x y : G) :
    y⁻¹ * x ∈ N.normSubgroup ↔
      (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  rw [N.inv_mul_mem_normSubgroup_iff_div_mem_normSubgroup x y,
    N.div_mem_normSubgroup_iff_residueDegree_dvd_valuation_difference_of_zeroSubgroup_le
      hϖH hzero x y]

/-- The valuation map modulo the residue-degree multiple subgroup.  This is
the canonical value-group map used to compare norm quotients with
`ℤ / fℤ`. -/
def valueModResidueDegreeHom :
    G →* Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.mk'
      (integerMultipleSubgroup (N.residueDegree : ℤ))).comp
    vG.valuationHom

/--
The defining evaluation formula for `valueModResidueDegreeHom` is `N.valueModResidueDegreeHom x =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (vG.valuationHom x)`.
-/
@[simp] theorem valueModResidueDegreeHom_apply (x : G) :
    N.valueModResidueDegreeHom x =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) :=
  rfl

/--
Establishes the identity `N.valueModResidueDegreeHom x = QuotientGroup.mk'
(integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val x))`.
-/
theorem valueModResidueDegreeHom_apply_ofAdd (x : G) :
    N.valueModResidueDegreeHom x =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.valueModResidueDegreeHom_apply,
    MultiplicativeIntegerValuation.valuationHom_apply]

/-- The specified map is surjective: `Function.Surjective N.valueModResidueDegreeHom`. -/
theorem valueModResidueDegreeHom_surjective_of_uniformizer
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    Function.Surjective N.valueModResidueDegreeHom := by
  intro q
  rcases
    QuotientGroup.mk'_surjective
      (integerMultipleSubgroup (N.residueDegree : ℤ)) q with
    ⟨m, rfl⟩
  exact ⟨ϖG ^ Multiplicative.toAdd m, by
    rw [N.valueModResidueDegreeHom_apply,
      MultiplicativeIntegerValuation.valuationHom_apply,
      vG.val_uniformizer_zpow hϖG (Multiplicative.toAdd m),
      ofAdd_toAdd]⟩

/--
Characterizes `x ∈ N.valueModResidueDegreeHom.ker` by the equivalent condition `(N.residueDegree :
ℤ) ∣ vG.val x`.
-/
theorem mem_valueModResidueDegreeHom_ker_iff (x : G) :
    x ∈ N.valueModResidueDegreeHom.ker ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  change N.valueModResidueDegreeHom x = 1 ↔
    (N.residueDegree : ℤ) ∣ vG.val x
  rw [N.valueModResidueDegreeHom_apply,
    MultiplicativeIntegerValuation.valuationHom_apply]
  simp [QuotientGroup.mk'_apply]

/-- The map `G/G⁰ → ℤ/fℤ` induced by valuation modulo the
residue-degree multiple subgroup. -/
def zeroSubgroupQuotientToValueModResidueDegree :
    G ⧸ vG.zeroSubgroup →*
      Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  QuotientGroup.map vG.zeroSubgroup
    (integerMultipleSubgroup (N.residueDegree : ℤ)) vG.valuationHom (by
      intro x hx
      change vG.valuationHom x ∈
        integerMultipleSubgroup (N.residueDegree : ℤ)
      rw [mem_integerMultipleSubgroup_iff,
        MultiplicativeIntegerValuation.valuationHom_apply, toAdd_ofAdd,
        (MultiplicativeIntegerValuation.mem_zeroSubgroup_iff vG x).1 hx]
      exact dvd_zero (N.residueDegree : ℤ))

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk'
vG.zeroSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
(vG.valuationHom x)`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_mk (x : G) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) := by
  simp [zeroSubgroupQuotientToValueModResidueDegree]

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk'
vG.zeroSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
(Multiplicative.ofAdd (vG.val x))`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_mk_ofAdd (x : G) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk x,
    MultiplicativeIntegerValuation.valuationHom_apply]

/--
The specified map is surjective: `Function.Surjective
N.zeroSubgroupQuotientToValueModResidueDegree`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_surjective_of_uniformizer
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    Function.Surjective N.zeroSubgroupQuotientToValueModResidueDegree := by
  intro q
  rcases
    QuotientGroup.mk'_surjective
      (integerMultipleSubgroup (N.residueDegree : ℤ)) q with
    ⟨m, rfl⟩
  exact ⟨QuotientGroup.mk' vG.zeroSubgroup
      (ϖG ^ Multiplicative.toAdd m), by
    rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk,
      MultiplicativeIntegerValuation.valuationHom_apply,
      vG.val_uniformizer_zpow hϖG (Multiplicative.toAdd m),
      ofAdd_toAdd]⟩

/--
Characterizes `N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk' vG.zeroSubgroup x)
= 1` by the equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_mk_eq_one_iff
    (x : G) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) = 1 ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk,
    MultiplicativeIntegerValuation.valuationHom_apply]
  simp [QuotientGroup.mk'_apply]

/--
Characterizes `N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk' vG.zeroSubgroup x)
= N.zeroSubgroupQuotientToValueModResidueDegree (QuotientGroup.mk' vG.zeroSubgroup y)` by the
equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x - vG.val y`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_mk_eq_iff
    (x y : G) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup y) ↔
      (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk x,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk y,
    MultiplicativeIntegerValuation.valuationHom_apply,
    MultiplicativeIntegerValuation.valuationHom_apply]
  simpa [QuotientGroup.mk'_apply, ← ofAdd_sub,
    ofAdd_mem_integerMultipleSubgroup_iff] using
    (QuotientGroup.eq_iff_div_mem
      (N := integerMultipleSubgroup (N.residueDegree : ℤ))
      (x := Multiplicative.ofAdd (vG.val x))
      (y := Multiplicative.ofAdd (vG.val y)))

/--
Establishes the identity `N.valueModResidueDegreeHom.ker = (integerMultipleSubgroup
(N.residueDegree : ℤ)).comap vG.valuationHom`.
-/
theorem valueModResidueDegreeHom_ker_eq_valuationHom_comap :
    N.valueModResidueDegreeHom.ker =
      (integerMultipleSubgroup (N.residueDegree : ℤ)).comap
        vG.valuationHom := by
  rw [valueModResidueDegreeHom,
    ← MonoidHom.comap_ker
      (QuotientGroup.mk'
        (integerMultipleSubgroup (N.residueDegree : ℤ)))
      vG.valuationHom,
    QuotientGroup.ker_mk']

/-- The subgroup of `G/G⁰` consisting of classes whose value is divisible by the
residue degree.  This is the kernel of the value-mod-residue-degree map. -/
def residueDegreeClassSubgroup :
    Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup)
    N.valueModResidueDegreeHom.ker

/-- The subgroup appearing in `N.residueDegreeClassSubgroup.Normal` is normal. -/
instance residueDegreeClassSubgroup_normal :
    N.residueDegreeClassSubgroup.Normal := by
  dsimp [residueDegreeClassSubgroup]
  infer_instance

/--
Characterizes `q ∈ N.residueDegreeClassSubgroup` by the equivalent condition `∃ x : G, x ∈
N.valueModResidueDegreeHom.ker ∧ QuotientGroup.mk' vG.zeroSubgroup x = q`.
-/
theorem mem_residueDegreeClassSubgroup_iff
    (q : G ⧸ vG.zeroSubgroup) :
    q ∈ N.residueDegreeClassSubgroup ↔
      ∃ x : G, x ∈ N.valueModResidueDegreeHom.ker ∧
        QuotientGroup.mk' vG.zeroSubgroup x = q :=
  Iff.rfl

/--
Establishes the membership statement `QuotientGroup.mk' vG.zeroSubgroup x ∈
N.residueDegreeClassSubgroup`.
-/
theorem residueDegreeClassSubgroup_mk_mem {x : G}
    (hx : (N.residueDegree : ℤ) ∣ vG.val x) :
    QuotientGroup.mk' vG.zeroSubgroup x ∈
      N.residueDegreeClassSubgroup :=
  Subgroup.mem_map_of_mem (QuotientGroup.mk' vG.zeroSubgroup)
    ((N.mem_valueModResidueDegreeHom_ker_iff x).2 hx)

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree.ker =
N.residueDegreeClassSubgroup`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup :
    N.zeroSubgroupQuotientToValueModResidueDegree.ker =
      N.residueDegreeClassSubgroup := by
  rw [zeroSubgroupQuotientToValueModResidueDegree, QuotientGroup.ker_map,
    ← N.valueModResidueDegreeHom_ker_eq_valuationHom_comap]
  rfl

/--
Characterizes `q ∈ N.zeroSubgroupQuotientToValueModResidueDegree.ker` by the equivalent condition
`q ∈ N.residueDegreeClassSubgroup`.
-/
theorem mem_zeroSubgroupQuotientToValueModResidueDegree_ker_iff
    (q : G ⧸ vG.zeroSubgroup) :
    q ∈ N.zeroSubgroupQuotientToValueModResidueDegree.ker ↔
      q ∈ N.residueDegreeClassSubgroup := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup]

/--
Characterizes `QuotientGroup.mk' vG.zeroSubgroup x ∈ N.residueDegreeClassSubgroup` by the
equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x`.
-/
theorem quotientZeroSubgroup_mk_mem_residueDegreeClassSubgroup_iff
    (x : G) :
    QuotientGroup.mk' vG.zeroSubgroup x ∈
        N.residueDegreeClassSubgroup ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  rw [← N.mem_zeroSubgroupQuotientToValueModResidueDegree_ker_iff
      (QuotientGroup.mk' vG.zeroSubgroup x),
    MonoidHom.mem_ker,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk_eq_one_iff x]

/--
Characterizes `N.zeroSubgroupQuotientToValueModResidueDegree q = 1` by the equivalent condition `q
∈ N.residueDegreeClassSubgroup`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_eq_one_iff_mem_residueDegreeClassSubgroup
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroSubgroupQuotientToValueModResidueDegree q = 1 ↔
      q ∈ N.residueDegreeClassSubgroup := by
  rw [← MonoidHom.mem_ker,
    N.mem_zeroSubgroupQuotientToValueModResidueDegree_ker_iff q]

/--
Characterizes `N.zeroSubgroupQuotientToValueModResidueDegree q = 1` by the equivalent condition `∃
x : G, (N.residueDegree : ℤ) ∣ vG.val x ∧ QuotientGroup.mk' vG.zeroSubgroup x = q`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_eq_one_iff_exists_residueDegree_repr
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroSubgroupQuotientToValueModResidueDegree q = 1 ↔
      ∃ x : G, (N.residueDegree : ℤ) ∣ vG.val x ∧
        QuotientGroup.mk' vG.zeroSubgroup x = q := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_eq_one_iff_mem_residueDegreeClassSubgroup
      q,
    N.mem_residueDegreeClassSubgroup_iff q]
  constructor
  · rintro ⟨x, hx, hxq⟩
    exact ⟨x, (N.mem_valueModResidueDegreeHom_ker_iff x).1 hx, hxq⟩
  · rintro ⟨x, hx, hxq⟩
    exact ⟨x, (N.mem_valueModResidueDegreeHom_ker_iff x).2 hx, hxq⟩

/--
Characterizes `N.zeroSubgroupQuotientToValueModResidueDegree q =
N.zeroSubgroupQuotientToValueModResidueDegree r` by the equivalent condition `q / r ∈
N.residueDegreeClassSubgroup`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_eq_iff_div_mem_residueDegreeClassSubgroup
    (q r : G ⧸ vG.zeroSubgroup) :
    N.zeroSubgroupQuotientToValueModResidueDegree q =
        N.zeroSubgroupQuotientToValueModResidueDegree r ↔
      q / r ∈ N.residueDegreeClassSubgroup := by
  rw [← N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup,
    MonoidHom.mem_ker,
    MonoidHom.map_div,
    div_eq_one]

/-- First-isomorphism form of the value-mod-residue-degree map.  A target
uniformizer makes `G/G⁰ → ℤ/fℤ` surjective. -/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.quotientMulEquivOfEq
    (N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (φ := N.zeroSubgroupQuotientToValueModResidueDegree)
      (N.zeroSubgroupQuotientToValueModResidueDegree_surjective_of_uniformizer hϖG))

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = N.zeroSubgroupQuotientToValueModResidueDegree
q`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroSubgroupQuotientToValueModResidueDegree q := by
  change QuotientGroup.kerLift N.zeroSubgroupQuotientToValueModResidueDegree
      ((QuotientGroup.quotientMulEquivOfEq
        N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup.symm)
        (QuotientGroup.mk q)) = N.zeroSubgroupQuotientToValueModResidueDegree q
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk N.zeroSubgroupQuotientToValueModResidueDegree q

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val
x))`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk hϖG,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk_ofAdd x]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree
hϖG).symm (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd
(vG.val x))) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup
x)`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_val
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd (vG.val x))) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        ((N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
          (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
            (Multiplicative.ofAdd (vG.val x)))) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
          hϖG x]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree
hϖG).symm (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd
n)) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^
n))`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ n)) := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).injective
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
      hϖG (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]
  simp

/-- One criterion in the double quotient by the residue-degree class subgroup. -/
theorem zeroQuotientModuloResidueDegreeClass_mk_eq_one_iff
    (q : G ⧸ vG.zeroSubgroup) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup q = 1 ↔
      q ∈ N.residueDegreeClassSubgroup := by
  simp [QuotientGroup.mk'_apply]

/--
Characterizes `QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup
x) = 1` by the equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x`.
-/
theorem zeroQuotientModuloResidueDegreeClass_mk_mk_eq_one_iff
    (x : G) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) = 1 ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  rw [N.zeroQuotientModuloResidueDegreeClass_mk_eq_one_iff,
    N.quotientZeroSubgroup_mk_mem_residueDegreeClassSubgroup_iff x]

/-- Equality criterion in the double quotient by the residue-degree class
subgroup. -/
theorem zeroQuotientModuloResidueDegreeClass_mk_eq_iff_div_mem
    (q r : G ⧸ vG.zeroSubgroup) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup q =
        QuotientGroup.mk' N.residueDegreeClassSubgroup r ↔
      q / r ∈ N.residueDegreeClassSubgroup := by
  simpa [QuotientGroup.mk'_apply] using
    (QuotientGroup.eq_iff_div_mem
      (N := N.residueDegreeClassSubgroup) (x := q) (y := r))

/--
Characterizes `QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup
x) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup y)` by the
equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x - vG.val y`.
-/
theorem zeroQuotientModuloResidueDegreeClass_mk_mk_eq_iff_residueDegree_dvd
    (x y : G) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup y) ↔
      (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  rw [N.zeroQuotientModuloResidueDegreeClass_mk_eq_iff_div_mem]
  rw [← (QuotientGroup.mk' vG.zeroSubgroup).map_div x y,
    N.quotientZeroSubgroup_mk_mem_residueDegreeClassSubgroup_iff (x / y),
    vG.val_div x y]

/--
Characterizes `QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup
(ϖG ^ m)) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup (ϖG
^ n))` by the equivalent condition `(N.residueDegree : ℤ) ∣ m - n`.
-/
theorem zeroQuotientModuloResidueDegreeClass_uniformizer_zpow_mk_eq_iff
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (m n : ℤ) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ m)) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ n)) ↔
      (N.residueDegree : ℤ) ∣ m - n := by
  rw [N.zeroQuotientModuloResidueDegreeClass_mk_mk_eq_iff_residueDegree_dvd,
    vG.val_uniformizer_zpow hϖG m, vG.val_uniformizer_zpow hϖG n]

/--
Establishes the identity `QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk'
vG.zeroSubgroup (ϖG ^ m)) = QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk'
vG.zeroSubgroup (ϖG ^ n))`.
-/
theorem zeroQuotientModuloResidueDegreeClass_uniformizer_zpow_mk_eq_of_sub_dvd
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) {m n : ℤ}
    (hmn : (N.residueDegree : ℤ) ∣ m - n) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ m)) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ n)) :=
  (N.zeroQuotientModuloResidueDegreeClass_uniformizer_zpow_mk_eq_iff
    hϖG m n).2 hmn

/--
Characterizes `QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup
(ϖG ^ n)) = 1` by the equivalent condition `(N.residueDegree : ℤ) ∣ n`.
-/
theorem zeroQuotientModuloResidueDegreeClass_uniformizer_zpow_mk_eq_one_iff
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ n)) = 1 ↔
      (N.residueDegree : ℤ) ∣ n := by
  rw [N.zeroQuotientModuloResidueDegreeClass_mk_mk_eq_one_iff,
    vG.val_uniformizer_zpow hϖG n]

/--
Establishes the divisibility statement `(N.residueDegree : ℤ) ∣ (n + (N.residueDegree : ℤ) * k) -
n`.
-/
theorem residueDegree_dvd_add_residueDegree_mul_sub (n k : ℤ) :
    (N.residueDegree : ℤ) ∣
      (n + (N.residueDegree : ℤ) * k) - n := by
  refine ⟨k, ?_⟩
  ring

/-- The value-mod-residue-degree map is periodic on target-uniformizer powers
with period the residue degree. -/
theorem valueModResidueDegreeHom_uniformizer_zpow_add_residueDegree_mul_eq
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n k : ℤ) :
    N.valueModResidueDegreeHom
        (ϖG ^ (n + (N.residueDegree : ℤ) * k)) =
      N.valueModResidueDegreeHom (ϖG ^ n) := by
  rw [N.valueModResidueDegreeHom_apply_ofAdd,
    N.valueModResidueDegreeHom_apply_ofAdd,
    vG.val_uniformizer_zpow hϖG (n + (N.residueDegree : ℤ) * k),
    vG.val_uniformizer_zpow hϖG n]
  have hmem :
      Multiplicative.ofAdd (n + (N.residueDegree : ℤ) * k) /
          Multiplicative.ofAdd n ∈
        integerMultipleSubgroup (N.residueDegree : ℤ) := by
    rw [← ofAdd_sub, ofAdd_mem_integerMultipleSubgroup_iff]
    exact N.residueDegree_dvd_add_residueDegree_mul_sub n k
  simp [QuotientGroup.mk'_apply]

/-- The map `G/G⁰ → ℤ/fℤ` induced by valuation is periodic on
target-uniformizer powers with period the residue degree. -/
theorem zeroSubgroupQuotientToValueModResidueDegree_uniformizer_zpow_add_residueDegree_mul_mk_eq
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n k : ℤ) :
    N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup
          (ϖG ^ (n + (N.residueDegree : ℤ) * k))) =
      N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ n)) := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_mk_eq_iff,
    vG.val_uniformizer_zpow hϖG (n + (N.residueDegree : ℤ) * k),
    vG.val_uniformizer_zpow hϖG n]
  exact N.residueDegree_dvd_add_residueDegree_mul_sub n k

/-- Uniformizer powers in the residue-degree double quotient are periodic modulo
the residue degree. -/
theorem zeroQuotientModuloResidueDegreeClass_uniformizer_zpow_add_residueDegree_mul_mk_eq
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n k : ℤ) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup
          (ϖG ^ (n + (N.residueDegree : ℤ) * k))) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ n)) :=
  N.zeroQuotientModuloResidueDegreeClass_uniformizer_zpow_mk_eq_of_sub_dvd
    hϖG (N.residueDegree_dvd_add_residueDegree_mul_sub n k)

/-- Every residue-degree double-quotient class has the same representative as a
target-uniformizer power with exponent given by the valuation. -/
theorem zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizer_zpow_val
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup (ϖG ^ vG.val x)) := by
  rw [N.zeroQuotientModuloResidueDegreeClass_mk_mk_eq_iff_residueDegree_dvd,
    vG.val_uniformizer_zpow hϖG (vG.val x), sub_self]
  exact dvd_zero (N.residueDegree : ℤ)

/-- Generator-power form of
`zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizer_zpow_val`. -/
theorem zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizerClass_zpow_val
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ vG.val x := by
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) (vG.val x),
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG (vG.val x)]
  exact N.zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizer_zpow_val
    hϖG x

/-- Criterion for a residue-degree double-quotient class to be a prescribed
power of the target uniformizer class. -/
theorem zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizerClass_zpow_iff
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (x : G) (n : ℤ) :
    QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n ↔
      (N.residueDegree : ℤ) ∣ vG.val x - n := by
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClass_mk_mk_eq_iff_residueDegree_dvd,
    vG.val_uniformizer_zpow hϖG n]

/-- Equality of two powers of the target uniformizer class in the residue-degree
double quotient is residue-degree divisibility of the exponent difference. -/
theorem zeroQuotientModuloResidueDegreeClass_uniformizerClass_zpow_eq_iff
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (m n : ℤ) :
    (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ m =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n ↔
      (N.residueDegree : ℤ) ∣ m - n := by
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) m,
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG m,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]
  exact N.zeroQuotientModuloResidueDegreeClass_uniformizer_zpow_mk_eq_iff
    hϖG m n

/--
Establishes the identity `(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk'
vG.zeroSubgroup ϖG)) ^ m = (QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk'
vG.zeroSubgroup ϖG)) ^ n`.
-/
theorem zeroQuotientModuloResidueDegreeClass_uniformizerClass_zpow_eq_of_sub_dvd
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) {m n : ℤ}
    (hmn : (N.residueDegree : ℤ) ∣ m - n) :
    (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ m =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n :=
  (N.zeroQuotientModuloResidueDegreeClass_uniformizerClass_zpow_eq_iff
    hϖG m n).2 hmn

/--
Establishes the identity `(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk'
vG.zeroSubgroup ϖG)) ^ (n + (N.residueDegree : ℤ) * k) = (QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
theorem zeroQuotientModuloResidueDegreeClass_uniformizerClass_zpow_add_residueDegree_mul_eq
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n k : ℤ) :
    (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^
        (n + (N.residueDegree : ℤ) * k) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n :=
  N.zeroQuotientModuloResidueDegreeClass_uniformizerClass_zpow_eq_of_sub_dvd
    hϖG (N.residueDegree_dvd_add_residueDegree_mul_sub n k)

/--
Establishes the identity `(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk'
vG.zeroSubgroup ϖG)) ^ (N.residueDegree : ℤ) = 1`.
-/
theorem zeroQuotientModuloResidueDegreeClass_uniformizerClass_zpow_residueDegree_eq_one
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ (N.residueDegree : ℤ) = 1 := by
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) (N.residueDegree : ℤ),
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow
      ϖG (N.residueDegree : ℤ)]
  exact (N.zeroQuotientModuloResidueDegreeClass_uniformizer_zpow_mk_eq_one_iff
    hϖG (N.residueDegree : ℤ)).2 (dvd_refl (N.residueDegree : ℤ))

/--
Characterizes `(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup
ϖG)) ^ n = 1` by the equivalent condition `(N.residueDegree : ℤ) ∣ n`.
-/
theorem zeroQuotientModuloResidueDegreeClass_uniformizerClass_zpow_eq_one_iff
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n = 1 ↔
      (N.residueDegree : ℤ) ∣ n := by
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]
  exact N.zeroQuotientModuloResidueDegreeClass_uniformizer_zpow_mk_eq_one_iff
    hϖG n

/-- The residue-degree double quotient is generated by the class of any target
uniformizer. -/
theorem zeroQuotientModuloResidueDegreeClass_generated_by_uniformizerClass
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    (q : (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup) :
    ∃ n : ℤ, q =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  refine QuotientGroup.induction_on q ?_
  intro q₀
  refine QuotientGroup.induction_on q₀ ?_
  intro x
  exact ⟨vG.val x,
    N.zeroQuotientModuloResidueDegreeClass_mk_eq_uniformizerClass_zpow_val
      hϖG x⟩

/-- The residue-degree double quotient is cyclic, generated by the class of any
target uniformizer. -/
theorem zeroQuotientModuloResidueDegreeClass_closure_uniformizerClass_eq_top
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) :
    Subgroup.closure
        ({QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)} :
          Set ((G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup)) =
      ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro q hq
    rcases N.zeroQuotientModuloResidueDegreeClass_generated_by_uniformizerClass
        hϖG q with ⟨n, hqpow⟩
    rw [hqpow]
    exact Subgroup.zpow_mem
      (Subgroup.closure
        ({QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)} :
          Set ((G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup)))
      (Subgroup.subset_closure (by simp)) n

/--
`zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_uniformizerClass` satisfies the
integer-power formula `N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
((QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_uniformizerClass_zpow
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd n) := by
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk_mk
      hϖG (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/--
`zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass`
satisfies the integer-power formula
`(N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm (QuotientGroup.mk'
(integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)) = (QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
theorem
zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass_zpow
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_symm_mk_ofAdd
      hϖG n,
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]

/-- Establishes the identity `N.valueModResidueDegreeHom.ker = N.normSubgroup`. -/
theorem valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.valueModResidueDegreeHom.ker = N.normSubgroup := by
  ext x
  rw [N.mem_valueModResidueDegreeHom_ker_iff,
    N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero x]

/-- The subgroup `N/G⁰` inside the zero-valuation quotient `G/G⁰`, where
`N` is the norm subgroup. -/
def normSubgroupClassInZeroQuotient : Subgroup (G ⧸ vG.zeroSubgroup) :=
  Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup) N.normSubgroup

/-- The subgroup appearing in `N.normSubgroupClassInZeroQuotient.Normal` is normal. -/
instance normSubgroupClassInZeroQuotient_normal
    [(N.normSubgroup).Normal] :
    N.normSubgroupClassInZeroQuotient.Normal := by
  dsimp [normSubgroupClassInZeroQuotient]
  infer_instance

/--
Characterizes `q ∈ N.normSubgroupClassInZeroQuotient` by the equivalent condition `∃ x : G, x ∈
N.normSubgroup ∧ QuotientGroup.mk' vG.zeroSubgroup x = q`.
-/
theorem mem_normSubgroupClassInZeroQuotient_iff
    (q : G ⧸ vG.zeroSubgroup) :
    q ∈ N.normSubgroupClassInZeroQuotient ↔
      ∃ x : G, x ∈ N.normSubgroup ∧
        QuotientGroup.mk' vG.zeroSubgroup x = q :=
  Iff.rfl

/--
Establishes the membership statement `QuotientGroup.mk' vG.zeroSubgroup x ∈
N.normSubgroupClassInZeroQuotient`.
-/
theorem normSubgroupClassInZeroQuotient_mk_mem {x : G}
    (hx : x ∈ N.normSubgroup) :
    QuotientGroup.mk' vG.zeroSubgroup x ∈
      N.normSubgroupClassInZeroQuotient :=
  Subgroup.mem_map_of_mem (QuotientGroup.mk' vG.zeroSubgroup) hx

/-- Establishes the identity `N.residueDegreeClassSubgroup = N.normSubgroupClassInZeroQuotient`. -/
theorem residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.residueDegreeClassSubgroup =
      N.normSubgroupClassInZeroQuotient := by
  rw [residueDegreeClassSubgroup, normSubgroupClassInZeroQuotient,
    N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
      hϖH hzero]

/-- The quotient by the value-side residue-degree class subgroup is the same
as the quotient by the norm-class subgroup when valuation-zero target elements
are norms. -/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivNormClass
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      (G ⧸ vG.zeroSubgroup) ⧸ N.normSubgroupClassInZeroQuotient :=
  QuotientGroup.quotientMulEquivOfEq
    (N.residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
      hϖH hzero)

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient q`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q := by
  rfl

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) = QuotientGroup.mk'
N.residueDegreeClassSubgroup q`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup q := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        ((N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
          (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q)) =
      QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero q]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk hϖH hzero]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass` satisfies the integer-power
formula `N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero ((QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) = (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk_mk
      hϖH hzero (ϖG ^ n)]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass` satisfies the
integer-power formula `(N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
((QuotientGroup.mk' N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n)
= (QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).symm
        ((QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_symm_mk_mk
    hϖH hzero (ϖG ^ n)]

/-- The natural map `G/G⁰ → G/N`, where `N` is a norm subgroup containing
the valuation-zero subgroup. -/
def zeroSubgroupQuotientToNormQuotient [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    G ⧸ vG.zeroSubgroup →* G ⧸ N.normSubgroup :=
  QuotientGroup.map vG.zeroSubgroup N.normSubgroup (MonoidHom.id G) (by
      intro x hx
      exact hzero hx)

/--
Establishes the identity `N.zeroSubgroupQuotientToNormQuotient hzero (QuotientGroup.mk'
vG.zeroSubgroup x) = QuotientGroup.mk' N.normSubgroup x`.
-/
theorem zeroSubgroupQuotientToNormQuotient_mk
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      QuotientGroup.mk' N.normSubgroup x := by
  exact QuotientGroup.map_mk' vG.zeroSubgroup N.normSubgroup
    (MonoidHom.id G) (fun _ hx => hzero hx) x

/--
The specified map is surjective: `Function.Surjective (N.zeroSubgroupQuotientToNormQuotient
hzero)`.
-/
theorem zeroSubgroupQuotientToNormQuotient_surjective
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    Function.Surjective (N.zeroSubgroupQuotientToNormQuotient hzero) := by
  intro q
  rcases QuotientGroup.mk'_surjective N.normSubgroup q with ⟨x, rfl⟩
  exact ⟨QuotientGroup.mk' vG.zeroSubgroup x, by
    rw [N.zeroSubgroupQuotientToNormQuotient_mk hzero x]⟩

/--
Characterizes `N.zeroSubgroupQuotientToNormQuotient hzero (QuotientGroup.mk' vG.zeroSubgroup x) =
1` by the equivalent condition `x ∈ N.normSubgroup`.
-/
theorem zeroSubgroupQuotientToNormQuotient_mk_eq_one_iff
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) = 1 ↔
      x ∈ N.normSubgroup := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk hzero x]
  simp [QuotientGroup.mk'_apply]

/-- The kernel of `G/G⁰ → G/N` is the image of `N` in `G/G⁰`. -/
theorem zeroSubgroupQuotientToNormQuotient_ker_eq_normSubgroupClassInZeroQuotient
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (N.zeroSubgroupQuotientToNormQuotient hzero).ker =
      N.normSubgroupClassInZeroQuotient := by
  exact (QuotientGroup.ker_map vG.zeroSubgroup N.normSubgroup
    (MonoidHom.id G) (fun _ hx => hzero hx)).trans
    (congrArg (Subgroup.map (QuotientGroup.mk' vG.zeroSubgroup))
      (Subgroup.comap_id N.normSubgroup))

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree.ker =
N.normSubgroupClassInZeroQuotient`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_ker_eq_normSubgroupClassInZeroQuotient
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.zeroSubgroupQuotientToValueModResidueDegree.ker =
      N.normSubgroupClassInZeroQuotient := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_residueDegreeClassSubgroup,
    N.residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
      hϖH hzero]

/--
Characterizes `q ∈ (N.zeroSubgroupQuotientToNormQuotient hzero).ker` by the equivalent condition
`q ∈ N.normSubgroupClassInZeroQuotient`.
-/
theorem mem_zeroSubgroupQuotientToNormQuotient_ker_iff
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    q ∈ (N.zeroSubgroupQuotientToNormQuotient hzero).ker ↔
      q ∈ N.normSubgroupClassInZeroQuotient := by
  rw [N.zeroSubgroupQuotientToNormQuotient_ker_eq_normSubgroupClassInZeroQuotient
    hzero]

/--
Characterizes `QuotientGroup.mk' vG.zeroSubgroup x ∈ N.normSubgroupClassInZeroQuotient` by the
equivalent condition `x ∈ N.normSubgroup`.
-/
theorem quotientZeroSubgroup_mk_mem_normSubgroupClassInZeroQuotient_iff
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    QuotientGroup.mk' vG.zeroSubgroup x ∈
        N.normSubgroupClassInZeroQuotient ↔
      x ∈ N.normSubgroup := by
  rw [← N.mem_zeroSubgroupQuotientToNormQuotient_ker_iff hzero
      (QuotientGroup.mk' vG.zeroSubgroup x),
    MonoidHom.mem_ker,
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x]
  simp [QuotientGroup.mk'_apply]

/--
Characterizes `N.zeroSubgroupQuotientToNormQuotient hzero q = 1` by the equivalent condition `q ∈
N.normSubgroupClassInZeroQuotient`.
-/
theorem zeroSubgroupQuotientToNormQuotient_eq_one_iff_mem_normSubgroupClassInZeroQuotient
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroSubgroupQuotientToNormQuotient hzero q = 1 ↔
      q ∈ N.normSubgroupClassInZeroQuotient := by
  rw [← MonoidHom.mem_ker,
    N.mem_zeroSubgroupQuotientToNormQuotient_ker_iff hzero q]

/--
Characterizes `N.zeroSubgroupQuotientToNormQuotient hzero q = 1` by the equivalent condition `∃ x
: G, x ∈ N.normSubgroup ∧ QuotientGroup.mk' vG.zeroSubgroup x = q`.
-/
theorem zeroSubgroupQuotientToNormQuotient_eq_one_iff_exists_normSubgroup_repr
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroSubgroupQuotientToNormQuotient hzero q = 1 ↔
      ∃ x : G, x ∈ N.normSubgroup ∧
        QuotientGroup.mk' vG.zeroSubgroup x = q := by
  rw [N.zeroSubgroupQuotientToNormQuotient_eq_one_iff_mem_normSubgroupClassInZeroQuotient
      hzero q,
    N.mem_normSubgroupClassInZeroQuotient_iff q]

/--
Characterizes `N.zeroSubgroupQuotientToNormQuotient hzero q = N.zeroSubgroupQuotientToNormQuotient
hzero r` by the equivalent condition `q / r ∈ N.normSubgroupClassInZeroQuotient`.
-/
theorem zeroSubgroupQuotientToNormQuotient_eq_iff_div_mem_normSubgroupClassInZeroQuotient
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q r : G ⧸ vG.zeroSubgroup) :
    N.zeroSubgroupQuotientToNormQuotient hzero q =
        N.zeroSubgroupQuotientToNormQuotient hzero r ↔
      q / r ∈ N.normSubgroupClassInZeroQuotient := by
  rw [← N.zeroSubgroupQuotientToNormQuotient_ker_eq_normSubgroupClassInZeroQuotient
      hzero,
    MonoidHom.mem_ker,
    MonoidHom.map_div,
    div_eq_one]

/-- The third-isomorphism equivalence
`(G/G⁰)/(N/G⁰) ≃ G/N` for the norm subgroup. -/
noncomputable def zeroQuotientModuloNormClassEquivNormQuotient
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.normSubgroupClassInZeroQuotient ≃*
      G ⧸ N.normSubgroup :=
  QuotientGroup.quotientQuotientEquivQuotient
    vG.zeroSubgroup N.normSubgroup hzero

/--
Establishes the identity `N.zeroQuotientModuloNormClassEquivNormQuotient hzero (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient q) = N.zeroSubgroupQuotientToNormQuotient hzero q`.
-/
theorem zeroQuotientModuloNormClassEquivNormQuotient_mk
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient q) =
      N.zeroSubgroupQuotientToNormQuotient hzero q := by
  change
    QuotientGroup.quotientQuotientEquivQuotientAux
        vG.zeroSubgroup N.normSubgroup hzero q =
      N.zeroSubgroupQuotientToNormQuotient hzero q
  exact
    (QuotientGroup.quotientQuotientEquivQuotientAux_mk
      (N := vG.zeroSubgroup) (M := N.normSubgroup) (h := hzero) q)

/--
Establishes the identity `N.zeroQuotientModuloNormClassEquivNormQuotient hzero (QuotientGroup.mk'
N.normSubgroupClassInZeroQuotient (QuotientGroup.mk' vG.zeroSubgroup x)) = QuotientGroup.mk'
N.normSubgroup x`.
-/
theorem zeroQuotientModuloNormClassEquivNormQuotient_mk_mk
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (QuotientGroup.mk' N.normSubgroupClassInZeroQuotient
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroup x := by
  rw [N.zeroQuotientModuloNormClassEquivNormQuotient_mk hzero,
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x]

/-- Direct form of the quotient comparison from the residue-degree class
subgroup to the norm quotient. -/
noncomputable def zeroQuotientModuloResidueDegreeClassEquivNormQuotient
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup ≃*
      G ⧸ N.normSubgroup :=
  (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero).trans
    (N.zeroQuotientModuloNormClassEquivNormQuotient hzero)

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup q) = N.zeroSubgroupQuotientToNormQuotient hzero
q`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroSubgroupQuotientToNormQuotient hzero q := by
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup q) =
      N.zeroQuotientModuloNormClassEquivNormQuotient hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormClass hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup q)) := rfl
    _ = N.zeroSubgroupQuotientToNormQuotient hzero q := by
      rw [N.zeroQuotientModuloResidueDegreeClassEquivNormClass_mk hϖH hzero q,
        N.zeroQuotientModuloNormClassEquivNormQuotient_mk hzero q]

/--
Establishes the identity `N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
(QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x)) =
QuotientGroup.mk' N.normSubgroup x`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      QuotientGroup.mk' N.normSubgroup x := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk hϖH hzero,
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x]

/--
Establishes the identity `(N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' N.residueDegreeClassSubgroup
(QuotientGroup.mk' vG.zeroSubgroup x)`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_mk
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  apply (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).injective
  calc
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        ((N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
          (QuotientGroup.mk' N.normSubgroup x)) =
      QuotientGroup.mk' N.normSubgroup x := by
        exact
          (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).apply_symm_apply _
    _ =
      N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) := by
        rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
          hϖH hzero x]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormQuotient_uniformizerClass` satisfies the
integer-power formula `N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
((QuotientGroup.mk' N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
(QuotientGroup.mk' N.normSubgroup ϖG) ^ n`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
        ((QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n) =
      (QuotientGroup.mk' N.normSubgroup ϖG) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
      hϖH hzero (ϖG ^ n)]

/--
`zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_uniformizerClass` satisfies the
integer-power formula `(N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) = (QuotientGroup.mk' N.residueDegreeClassSubgroup
(QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n`.
-/
theorem zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero).symm
        ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
      (QuotientGroup.mk' N.residueDegreeClassSubgroup
        (QuotientGroup.mk' vG.zeroSubgroup ϖG)) ^ n := by
  let _hϖG := hϖG
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n,
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_symm_mk
      hϖH hzero (ϖG ^ n),
    ← (QuotientGroup.mk' N.residueDegreeClassSubgroup).map_zpow
      (QuotientGroup.mk' vG.zeroSubgroup ϖG) n,
    ← (QuotientGroup.mk' vG.zeroSubgroup).map_zpow ϖG n]

/--
Establishes the identity `N.zeroSubgroupQuotientToValueModResidueDegree.ker =
(N.zeroSubgroupQuotientToNormQuotient hzero).ker`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_ker_eq_zeroSubgroupQuotientToNormQuotient_ker
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    N.zeroSubgroupQuotientToValueModResidueDegree.ker =
      (N.zeroSubgroupQuotientToNormQuotient hzero).ker := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_ker_eq_normSubgroupClassInZeroQuotient
      hϖH hzero,
    N.zeroSubgroupQuotientToNormQuotient_ker_eq_normSubgroupClassInZeroQuotient
      hzero]

/--
Characterizes `N.zeroSubgroupQuotientToValueModResidueDegree q = 1` by the equivalent condition
`N.zeroSubgroupQuotientToNormQuotient hzero q = 1`.
-/
theorem
zeroSubgroupQuotientToValueModResidueDegree_eq_one_iff_zeroSubgroupQuotientToNormQuotient_eq_one
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.zeroSubgroupQuotientToValueModResidueDegree q = 1 ↔
      N.zeroSubgroupQuotientToNormQuotient hzero q = 1 := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_eq_one_iff_mem_residueDegreeClassSubgroup
      q,
    N.residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
      hϖH hzero,
    ← N.zeroSubgroupQuotientToNormQuotient_eq_one_iff_mem_normSubgroupClassInZeroQuotient
      hzero q]

/--
Characterizes `N.zeroSubgroupQuotientToValueModResidueDegree q =
N.zeroSubgroupQuotientToValueModResidueDegree r` by the equivalent condition
`N.zeroSubgroupQuotientToNormQuotient hzero q = N.zeroSubgroupQuotientToNormQuotient hzero r`.
-/
theorem zeroSubgroupQuotientToValueModResidueDegree_eq_iff_zeroSubgroupQuotientToNormQuotient_eq
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q r : G ⧸ vG.zeroSubgroup) :
    N.zeroSubgroupQuotientToValueModResidueDegree q =
        N.zeroSubgroupQuotientToValueModResidueDegree r ↔
      N.zeroSubgroupQuotientToNormQuotient hzero q =
        N.zeroSubgroupQuotientToNormQuotient hzero r := by
  rw [N.zeroSubgroupQuotientToValueModResidueDegree_eq_iff_div_mem_residueDegreeClassSubgroup
      q r,
    N.residueDegreeClassSubgroup_eq_normSubgroupClassInZeroQuotient_of_zeroSubgroup_le
      hϖH hzero,
    ← N.zeroSubgroupQuotientToNormQuotient_eq_iff_div_mem_normSubgroupClassInZeroQuotient
      hzero q r]

/--
Characterizes `N.zeroSubgroupQuotientToNormQuotient hzero (QuotientGroup.mk' vG.zeroSubgroup x) =
N.zeroSubgroupQuotientToNormQuotient hzero (QuotientGroup.mk' vG.zeroSubgroup y)` by the
equivalent condition `x / y ∈ N.normSubgroup`.
-/
theorem zeroSubgroupQuotientToNormQuotient_mk_eq_iff
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x y : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) =
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup y) ↔
      x / y ∈ N.normSubgroup := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk hzero x,
    N.zeroSubgroupQuotientToNormQuotient_mk hzero y]
  simpa [QuotientGroup.mk'_apply] using
    (QuotientGroup.eq_iff_div_mem
      (N := N.normSubgroup) (x := x) (y := y))

/-- Left-quotient version of
`zeroSubgroupQuotientToNormQuotient_mk_eq_iff`. -/
theorem zeroSubgroupQuotientToNormQuotient_mk_eq_iff_inv_mul_mem
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x y : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup y) ↔
      y⁻¹ * x ∈ N.normSubgroup := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk_eq_iff hzero x y,
    N.div_mem_normSubgroup_iff_inv_mul_mem_normSubgroup x y]

/--
Characterizes `N.zeroSubgroupQuotientToNormQuotient hzero (QuotientGroup.mk' vG.zeroSubgroup x) =
1` by the equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x`.
-/
theorem zeroSubgroupQuotientToNormQuotient_mk_eq_one_iff_residueDegree_dvd
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) = 1 ↔
      (N.residueDegree : ℤ) ∣ vG.val x := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk_eq_one_iff hzero x,
    N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero x]

/--
Characterizes `N.zeroSubgroupQuotientToNormQuotient hzero (QuotientGroup.mk' vG.zeroSubgroup x) =
N.zeroSubgroupQuotientToNormQuotient hzero (QuotientGroup.mk' vG.zeroSubgroup y)` by the
equivalent condition `(N.residueDegree : ℤ) ∣ vG.val x - vG.val y`.
-/
theorem zeroSubgroupQuotientToNormQuotient_mk_eq_iff_residueDegree_dvd
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x y : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup y) ↔
      (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk_eq_iff hzero x y,
    N.div_mem_normSubgroup_iff_residueDegree_dvd_valuation_difference_of_zeroSubgroup_le
      hϖH hzero x y]

/-- Left-quotient proof route for equality in
`G ⧸ zeroSubgroup → G ⧸ normSubgroup`, expressed by residue-degree
divisibility. -/
theorem zeroSubgroupQuotientToNormQuotient_mk_eq_iff_inv_mul_residueDegree_dvd
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x y : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup y) ↔
      (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk_eq_iff_inv_mul_mem hzero x y,
    N.inv_mul_mem_normSubgroup_iff_residueDegree_dvd_valuation_difference_of_zeroSubgroup_le
      hϖH hzero x y]

/-- The actual norm quotient is the value-group quotient `ℤ / fℤ` when
valuation-zero target elements are norms and the target valuation has a
uniformizer. -/
noncomputable def normQuotientEquivValueModResidueDegree
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    G ⧸ N.normSubgroup ≃*
      Multiplicative ℤ ⧸ integerMultipleSubgroup (N.residueDegree : ℤ) :=
  (QuotientGroup.quotientMulEquivOfEq
      (N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
        hϖH hzero).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      N.valueModResidueDegreeHom
      (N.valueModResidueDegreeHom_surjective_of_uniformizer hϖG))

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree
: ℤ)) (vG.valuationHom x)`.
-/
theorem normQuotientEquivValueModResidueDegree_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (vG.valuationHom x) := by
  change QuotientGroup.kerLift N.valueModResidueDegreeHom
      ((QuotientGroup.quotientMulEquivOfEq
        (N.valueModResidueDegreeHom_ker_eq_normSubgroup_of_zeroSubgroup_le
          hϖH hzero).symm) (QuotientGroup.mk x)) = N.valueModResidueDegreeHom x
  rw [QuotientGroup.quotientMulEquivOfEq_mk]
  exact QuotientGroup.kerLift_mk N.valueModResidueDegreeHom x

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(QuotientGroup.mk' N.normSubgroup x) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree
: ℤ)) (Multiplicative.ofAdd (vG.val x))`.
-/
theorem normQuotientEquivValueModResidueDegree_mk_ofAdd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.normQuotientEquivValueModResidueDegree_mk hϖG hϖH hzero x,
    MultiplicativeIntegerValuation.valuationHom_apply]

/--
`normQuotientEquivValueModResidueDegree_uniformizer` satisfies the integer-power formula
`N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero (QuotientGroup.mk' N.normSubgroup (ϖG ^
n)) = QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)`.
-/
theorem normQuotientEquivValueModResidueDegree_uniformizer_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup (ϖG ^ n)) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd n) := by
  rw [N.normQuotientEquivValueModResidueDegree_mk_ofAdd
      hϖG hϖH hzero (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/--
Establishes the identity `(N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
(QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val
x))) = QuotientGroup.mk' N.normSubgroup x`.
-/
theorem normQuotientEquivValueModResidueDegree_symm_mk_val
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd (vG.val x))) =
      QuotientGroup.mk' N.normSubgroup x := by
  apply (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).injective
  calc
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        ((N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
          (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
            (Multiplicative.ofAdd (vG.val x)))) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
        exact
          (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).apply_symm_apply _
    _ =
      N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) := by
        rw [N.normQuotientEquivValueModResidueDegree_mk_ofAdd
          hϖG hϖH hzero x]

/--
Establishes the identity `(N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
(QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)) =
QuotientGroup.mk' N.normSubgroup (ϖG ^ n)`.
-/
theorem normQuotientEquivValueModResidueDegree_symm_mk_ofAdd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      QuotientGroup.mk' N.normSubgroup (ϖG ^ n) := by
  apply (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).injective
  rw [N.normQuotientEquivValueModResidueDegree_uniformizer_zpow
      hϖG hϖH hzero n]
  simp

/-- Compatibility of the natural map `G/G⁰ → G/N` with the value-modulo
residue-degree map. -/
theorem normQuotientEquivValueModResidueDegree_zeroSubgroupQuotientToNormQuotient_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroSubgroupQuotientToNormQuotient hzero
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x) := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk hzero x,
    N.normQuotientEquivValueModResidueDegree_mk hϖG hϖH hzero x,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk x]

/-- The direct residue-degree-class quotient to the norm quotient, followed by
the norm-quotient/value-group equivalence, agrees with the direct
value-mod-residue-degree quotient map on representatives. -/
theorem
normQuotientEquivValueModResidueDegree_zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ vG.zeroSubgroup) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup q)) =
      N.zeroSubgroupQuotientToValueModResidueDegree q := by
  refine QuotientGroup.induction_on q ?_
  intro x
  change
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup
            (QuotientGroup.mk' vG.zeroSubgroup x))) =
      N.zeroSubgroupQuotientToValueModResidueDegree
        (QuotientGroup.mk' vG.zeroSubgroup x)
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
      hϖH hzero (QuotientGroup.mk' vG.zeroSubgroup x),
    N.zeroSubgroupQuotientToNormQuotient_mk hzero x,
    N.normQuotientEquivValueModResidueDegree_mk hϖG hϖH hzero x,
    N.zeroSubgroupQuotientToValueModResidueDegree_mk x]

/--
Establishes the identity `N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
(N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero (QuotientGroup.mk'
N.residueDegreeClassSubgroup (QuotientGroup.mk' vG.zeroSubgroup x))) = QuotientGroup.mk'
(integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd (vG.val x))`.
-/
theorem
normQuotientEquivValueModResidueDegree_zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup
            (QuotientGroup.mk' vG.zeroSubgroup x))) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd (vG.val x)) := by
  rw [N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk_mk
      hϖH hzero x,
    N.normQuotientEquivValueModResidueDegree_mk_ofAdd hϖG hϖH hzero x]

/-- Pointwise compatibility of the two quotient routes from
`(G/G⁰)/residueDegreeClassSubgroup` to the value group modulo the
residue-degree subgroup. -/
theorem zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_apply_eq_norm_composite
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (z : (G ⧸ vG.zeroSubgroup) ⧸ N.residueDegreeClassSubgroup) :
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG z =
      N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero z) := by
  refine QuotientGroup.induction_on z ?_
  intro q
  refine QuotientGroup.induction_on q ?_
  intro x
  change
    N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree hϖG
        (QuotientGroup.mk' N.residueDegreeClassSubgroup
          (QuotientGroup.mk' vG.zeroSubgroup x)) =
      N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        (N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient hϖH hzero
          (QuotientGroup.mk' N.residueDegreeClassSubgroup
            (QuotientGroup.mk' vG.zeroSubgroup x)))
  rw [N.zeroQuotientModuloResidueDegreeClassEquivValueModResidueDegree_mk
      hϖG (QuotientGroup.mk' vG.zeroSubgroup x),
    N.zeroQuotientModuloResidueDegreeClassEquivNormQuotient_mk
      hϖH hzero (QuotientGroup.mk' vG.zeroSubgroup x),
    N.normQuotientEquivValueModResidueDegree_zeroSubgroupQuotientToNormQuotient_mk
      hϖG hϖH hzero x]

end ValuedNorm

end DiscreteValuationField

end

end LocalFieldTheory

universe u v

namespace LocalFieldTheory

noncomputable section

namespace DiscreteValuationField
namespace ValuedNorm

variable {G : Type u} {H : Type v} [Group G] [Group H]
variable {vG : MultiplicativeIntegerValuation G}
variable {vH : MultiplicativeIntegerValuation H}
variable (N : ValuedNorm vG vH)

/-- Kernel criterion for the actual quotient by the norm subgroup. -/
theorem normQuotient_mk_eq_one_iff_mem [(N.normSubgroup).Normal] (x : G) :
    QuotientGroup.mk' N.normSubgroup x = 1 ↔ x ∈ N.normSubgroup := by
  simp [QuotientGroup.mk'_apply]

/-- Equality in the actual quotient by the norm subgroup is equality modulo
the norm subgroup. -/
theorem normQuotient_mk_eq_iff_div_mem [(N.normSubgroup).Normal] (x y : G) :
    QuotientGroup.mk' N.normSubgroup x =
        QuotientGroup.mk' N.normSubgroup y ↔
      x / y ∈ N.normSubgroup := by
  simpa [QuotientGroup.mk'_apply] using
    (QuotientGroup.eq_iff_div_mem
      (N := N.normSubgroup) (x := x) (y := y))

/-- Equality in the actual quotient by the norm subgroup, in left-quotient
form. -/
theorem normQuotient_mk_eq_iff_inv_mul_mem [(N.normSubgroup).Normal]
    (x y : G) :
    QuotientGroup.mk' N.normSubgroup x =
        QuotientGroup.mk' N.normSubgroup y ↔
      y⁻¹ * x ∈ N.normSubgroup := by
  rw [N.normQuotient_mk_eq_iff_div_mem x y,
    N.div_mem_normSubgroup_iff_inv_mul_mem_normSubgroup x y]

/-- Equality in the norm quotient, expressed by valuation divisibility under
the standard hypothesis that valuation-zero target elements are norms. -/
theorem normQuotient_mk_eq_iff_residueDegree_dvd_valuation_difference
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x y : G) :
    QuotientGroup.mk' N.normSubgroup x =
        QuotientGroup.mk' N.normSubgroup y ↔
      (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  rw [N.normQuotient_mk_eq_iff_div_mem x y,
    N.div_mem_normSubgroup_iff_residueDegree_dvd_valuation_difference_of_zeroSubgroup_le
      hϖH hzero x y]

/-- Left-quotient proof route for equality in the norm quotient, expressed by
residue-degree divisibility. -/
theorem normQuotient_mk_eq_iff_inv_mul_residueDegree_dvd
    [(N.normSubgroup).Normal]
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x y : G) :
    QuotientGroup.mk' N.normSubgroup x =
        QuotientGroup.mk' N.normSubgroup y ↔
      (N.residueDegree : ℤ) ∣ vG.val x - vG.val y := by
  rw [N.normQuotient_mk_eq_iff_inv_mul_mem x y,
    N.inv_mul_mem_normSubgroup_iff_residueDegree_dvd_valuation_difference_of_zeroSubgroup_le
      hϖH hzero x y]

/-- Establishes the membership statement `y⁻¹ * x ∈ N.normSubgroup`. -/
theorem inv_mul_mem_normSubgroup_of_normQuotient_mk_eq
    [(N.normSubgroup).Normal] {x y : G}
    (hxy : QuotientGroup.mk' N.normSubgroup x =
        QuotientGroup.mk' N.normSubgroup y) :
    y⁻¹ * x ∈ N.normSubgroup :=
  (N.normQuotient_mk_eq_iff_inv_mul_mem x y).1 hxy

/--
Establishes the identity `QuotientGroup.mk' N.normSubgroup x = QuotientGroup.mk' N.normSubgroup
y`.
-/
theorem normQuotient_mk_eq_of_inv_mul_mem
    [(N.normSubgroup).Normal] {x y : G}
    (hxy : y⁻¹ * x ∈ N.normSubgroup) :
    QuotientGroup.mk' N.normSubgroup x =
      QuotientGroup.mk' N.normSubgroup y :=
  (N.normQuotient_mk_eq_iff_inv_mul_mem x y).2 hxy

/-- Elements with the same valuation represent the same norm-quotient class
when valuation-zero target elements are norms. -/
theorem normQuotient_mk_eq_of_val_eq [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    {x y : G} (hxy : vG.val x = vG.val y) :
    QuotientGroup.mk' N.normSubgroup x =
      QuotientGroup.mk' N.normSubgroup y := by
  rw [N.normQuotient_mk_eq_iff_div_mem x y]
  exact hzero ((vG.div_mem_zeroSubgroup_iff x y).2 hxy)

/-- Every norm-quotient class has a target-uniformizer-power representative
when valuation-zero target elements are norms. -/
theorem normQuotient_mk_eq_uniformizer_zpow_val
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    QuotientGroup.mk' N.normSubgroup x =
      QuotientGroup.mk' N.normSubgroup (ϖG ^ vG.val x) := by
  apply N.normQuotient_mk_eq_of_val_eq hzero
  rw [vG.val_uniformizer_zpow hϖG (vG.val x)]

/-- Criterion for a norm-quotient class to be represented by a prescribed
target-uniformizer power. -/
theorem normQuotient_mk_eq_uniformizer_zpow_iff
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) (n : ℤ) :
    QuotientGroup.mk' N.normSubgroup x =
        QuotientGroup.mk' N.normSubgroup (ϖG ^ n) ↔
      (N.residueDegree : ℤ) ∣ vG.val x - n := by
  rw [N.normQuotient_mk_eq_iff_residueDegree_dvd_valuation_difference
      hϖH hzero x (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/-- Equality of two target-uniformizer-power classes in the norm quotient is
equivalent to residue-degree divisibility of the exponent difference. -/
theorem normQuotient_uniformizer_zpow_mk_eq_iff
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (m n : ℤ) :
    QuotientGroup.mk' N.normSubgroup (ϖG ^ m) =
        QuotientGroup.mk' N.normSubgroup (ϖG ^ n) ↔
      (N.residueDegree : ℤ) ∣ m - n := by
  rw [N.normQuotient_mk_eq_iff_residueDegree_dvd_valuation_difference
      hϖH hzero (ϖG ^ m) (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG m, vG.val_uniformizer_zpow hϖG n]

/-- The residue-degree power of a target uniformizer is trivial in the norm
quotient under the standard unit-norm-surjectivity hypothesis. -/
theorem normQuotient_uniformizer_zpow_residueDegree_eq_one
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    QuotientGroup.mk' N.normSubgroup
        (ϖG ^ (N.residueDegree : ℤ)) = 1 := by
  let _hϖG := hϖG
  rw [N.normQuotient_mk_eq_one_iff_mem]
  exact N.mem_normSubgroup_of_residueDegree_dvd_val_of_zeroSubgroup_le
    hϖH hzero (by
      simp)

/-- Uniformizer powers in the norm quotient are periodic modulo the residue
degree under the standard unit-norm-surjectivity hypothesis. -/
theorem normQuotient_uniformizer_zpow_add_residueDegree_mul_mk_eq
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n k : ℤ) :
    QuotientGroup.mk' N.normSubgroup
        (ϖG ^ (n + (N.residueDegree : ℤ) * k)) =
      QuotientGroup.mk' N.normSubgroup (ϖG ^ n) :=
  (N.normQuotient_uniformizer_zpow_mk_eq_iff
    hϖG hϖH hzero (n + (N.residueDegree : ℤ) * k) n).2
    (N.residueDegree_dvd_add_residueDegree_mul_sub n k)

/-- Generator-power form of
`normQuotient_mk_eq_uniformizer_zpow_val`: every element has the same norm
quotient class as the valuation power of a target uniformizer class. -/
theorem normQuotient_mk_eq_uniformizerClass_zpow_val
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    QuotientGroup.mk' N.normSubgroup x =
      (QuotientGroup.mk' N.normSubgroup ϖG) ^ vG.val x := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG (vG.val x)]
  exact N.normQuotient_mk_eq_uniformizer_zpow_val hϖG hzero x

/-- Criterion for a norm-quotient class to be a prescribed power of the target
uniformizer class. -/
theorem normQuotient_mk_eq_uniformizerClass_zpow_iff
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) (n : ℤ) :
    QuotientGroup.mk' N.normSubgroup x =
        (QuotientGroup.mk' N.normSubgroup ϖG) ^ n ↔
      (N.residueDegree : ℤ) ∣ vG.val x - n := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n]
  exact N.normQuotient_mk_eq_uniformizer_zpow_iff
    hϖG hϖH hzero x n

/-- Equality of two powers of the target uniformizer class is residue-degree
divisibility of the exponent difference. -/
theorem normQuotient_uniformizerClass_zpow_eq_iff
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (m n : ℤ) :
    (QuotientGroup.mk' N.normSubgroup ϖG) ^ m =
        (QuotientGroup.mk' N.normSubgroup ϖG) ^ n ↔
      (N.residueDegree : ℤ) ∣ m - n := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG m,
    ← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n]
  exact N.normQuotient_uniformizer_zpow_mk_eq_iff
    hϖG hϖH hzero m n

/-- A sufficient form of the exponent-reduction criterion for the target
uniformizer class. -/
theorem normQuotient_uniformizerClass_zpow_eq_of_sub_dvd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) {m n : ℤ}
    (hmn : (N.residueDegree : ℤ) ∣ m - n) :
    (QuotientGroup.mk' N.normSubgroup ϖG) ^ m =
      (QuotientGroup.mk' N.normSubgroup ϖG) ^ n :=
  (N.normQuotient_uniformizerClass_zpow_eq_iff
    hϖG hϖH hzero m n).2 hmn

/-- The target-uniformizer generator in the norm quotient has exponents periodic
modulo the residue degree. -/
theorem normQuotient_uniformizerClass_zpow_add_residueDegree_mul_eq
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n k : ℤ) :
    (QuotientGroup.mk' N.normSubgroup ϖG) ^
        (n + (N.residueDegree : ℤ) * k) =
      (QuotientGroup.mk' N.normSubgroup ϖG) ^ n :=
  N.normQuotient_uniformizerClass_zpow_eq_of_sub_dvd hϖG hϖH hzero
    (N.residueDegree_dvd_add_residueDegree_mul_sub n k)

/-- The residue-degree power of the target uniformizer class is trivial in the
norm quotient. -/
theorem normQuotient_uniformizerClass_zpow_residueDegree_eq_one
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    (QuotientGroup.mk' N.normSubgroup ϖG) ^ (N.residueDegree : ℤ) = 1 := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow
    ϖG (N.residueDegree : ℤ)]
  exact N.normQuotient_uniformizer_zpow_residueDegree_eq_one
    hϖG hϖH hzero

/-- A power of the target uniformizer class is trivial exactly when its
exponent is divisible by the residue degree. -/
theorem normQuotient_uniformizerClass_zpow_eq_one_iff
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (QuotientGroup.mk' N.normSubgroup ϖG) ^ n = 1 ↔
      (N.residueDegree : ℤ) ∣ n := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n]
  simpa [zpow_zero, sub_zero] using
    (N.normQuotient_uniformizer_zpow_mk_eq_iff
      hϖG hϖH hzero n 0)

/-- The norm quotient is generated by the class of any target uniformizer. -/
theorem normQuotient_generated_by_uniformizerClass
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    (q : G ⧸ N.normSubgroup) :
    ∃ n : ℤ, q = (QuotientGroup.mk' N.normSubgroup ϖG) ^ n := by
  refine QuotientGroup.induction_on q ?_
  intro x
  exact ⟨vG.val x,
    N.normQuotient_mk_eq_uniformizerClass_zpow_val
      hϖG hzero x⟩

/-- The norm quotient is cyclic, generated by the class of any target
uniformizer, under the standard unit-norm-surjectivity hypothesis. -/
theorem normQuotient_closure_uniformizerClass_eq_top
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    Subgroup.closure
        ({QuotientGroup.mk' N.normSubgroup ϖG} : Set (G ⧸ N.normSubgroup)) =
      ⊤ := by
  apply le_antisymm
  · exact le_top
  · intro q hq
    rcases N.normQuotient_generated_by_uniformizerClass hϖG hzero q with
      ⟨n, hqpow⟩
    rw [hqpow]
    exact Subgroup.zpow_mem
      (Subgroup.closure
        ({QuotientGroup.mk' N.normSubgroup ϖG} : Set (G ⧸ N.normSubgroup)))
      (Subgroup.subset_closure (by simp)) n

/-- Under the value-group equivalence, the `n`th power of the target
uniformizer class maps to the class of `n` modulo the residue-degree subgroup. -/
theorem normQuotientEquivValueModResidueDegree_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero
        ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
      QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
        (Multiplicative.ofAdd n) := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n]
  exact N.normQuotientEquivValueModResidueDegree_uniformizer_zpow
    hϖG hϖH hzero n

/--
`normQuotientEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass` satisfies the
integer-power formula `(N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
(QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ)) (Multiplicative.ofAdd n)) =
(QuotientGroup.mk' N.normSubgroup ϖG) ^ n`.
-/
theorem normQuotientEquivValueModResidueDegree_symm_mk_ofAdd_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).symm
        (QuotientGroup.mk' (integerMultipleSubgroup (N.residueDegree : ℤ))
          (Multiplicative.ofAdd n)) =
      (QuotientGroup.mk' N.normSubgroup ϖG) ^ n := by
  rw [N.normQuotientEquivValueModResidueDegree_symm_mk_ofAdd
      hϖG hϖH hzero n,
    ← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n]

/-- The actual norm quotient as the standard cyclic group
`Multiplicative (ZMod f)`, where `f` is the residue degree in the valuation
formula. -/
noncomputable def normQuotientEquivZMod
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) :
    G ⧸ N.normSubgroup ≃* Multiplicative (ZMod N.residueDegree) :=
  (N.normQuotientEquivValueModResidueDegree hϖG hϖH hzero).trans
    (valueModIntegerMultipleSubgroupEquivZMod (N.residueDegree : ℤ))

/--
Establishes the identity `N.normQuotientEquivZMod hϖG hϖH hzero (QuotientGroup.mk' N.normSubgroup
x) = Multiplicative.ofAdd ((vG.val x : ℤ) : ZMod N.residueDegree)`.
-/
theorem normQuotientEquivZMod_mk
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    N.normQuotientEquivZMod hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup x) =
      Multiplicative.ofAdd ((vG.val x : ℤ) : ZMod N.residueDegree) := by
  rw [normQuotientEquivZMod, MulEquiv.trans_apply,
    N.normQuotientEquivValueModResidueDegree_mk_ofAdd hϖG hϖH hzero x]
  rfl

/--
`normQuotientEquivZMod_uniformizer` satisfies the integer-power formula `N.normQuotientEquivZMod
hϖG hϖH hzero (QuotientGroup.mk' N.normSubgroup (ϖG ^ n)) = Multiplicative.ofAdd ((n : ℤ) : ZMod
N.residueDegree)`.
-/
theorem normQuotientEquivZMod_uniformizer_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivZMod hϖG hϖH hzero
        (QuotientGroup.mk' N.normSubgroup (ϖG ^ n)) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree) := by
  rw [N.normQuotientEquivZMod_mk hϖG hϖH hzero (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/--
`normQuotientEquivZMod_uniformizerClass` satisfies the integer-power formula
`N.normQuotientEquivZMod hϖG hϖH hzero ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree)`.
-/
theorem normQuotientEquivZMod_uniformizerClass_zpow
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    N.normQuotientEquivZMod hϖG hϖH hzero
        ((QuotientGroup.mk' N.normSubgroup ϖG) ^ n) =
      Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree) := by
  rw [← (QuotientGroup.mk' N.normSubgroup).map_zpow ϖG n,
    N.normQuotientEquivZMod_uniformizer_zpow hϖG hϖH hzero n]

/--
Establishes the identity `(N.normQuotientEquivZMod hϖG hϖH hzero).symm (Multiplicative.ofAdd ((n :
ℤ) : ZMod N.residueDegree)) = QuotientGroup.mk' N.normSubgroup (ϖG ^ n)`.
-/
@[simp] theorem normQuotientEquivZMod_symm_mk_ofAdd
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    (N.normQuotientEquivZMod hϖG hϖH hzero).symm
        (Multiplicative.ofAdd ((n : ℤ) : ZMod N.residueDegree)) =
      QuotientGroup.mk' N.normSubgroup (ϖG ^ n) := by
  apply (N.normQuotientEquivZMod hϖG hϖH hzero).injective
  rw [MulEquiv.apply_symm_apply,
    N.normQuotientEquivZMod_uniformizer_zpow hϖG hϖH hzero n]

/-- Cardinality form of the norm-quotient computation when the residue degree is
nonzero. -/
theorem card_normQuotient_eq_residueDegree
    [(N.normSubgroup).Normal]
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup)
    :
    Nat.card (G ⧸ N.normSubgroup) = N.residueDegree := by
  calc
    Nat.card (G ⧸ N.normSubgroup) =
        Nat.card (Multiplicative (ZMod N.residueDegree)) :=
      Nat.card_congr
        (N.normQuotientEquivZMod hϖG hϖH hzero).toEquiv
    _ = Nat.card (ZMod N.residueDegree) :=
      Nat.card_congr Multiplicative.toAdd
    _ = N.residueDegree := Nat.card_zmod N.residueDegree

/-- Uniformizer-power criterion for target powers lying in the norm subgroup,
assuming all target valuation-zero elements are norms. -/
theorem uniformizer_zpow_mem_normSubgroup_iff_of_zeroSubgroup_le
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (n : ℤ) :
    ϖG ^ n ∈ N.normSubgroup ↔ (N.residueDegree : ℤ) ∣ n := by
  rw [N.mem_normSubgroup_iff_residueDegree_dvd_val_of_zeroSubgroup_le
      hϖH hzero (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG n]

/-- Target uniformizer-power quotients are norms exactly when the exponent
difference is divisible by the residue degree, provided all target
valuation-zero elements are norms. -/
theorem uniformizer_zpow_div_mem_normSubgroup_iff_of_zeroSubgroup_le
    {ϖG : G} (hϖG : vG.IsUniformizer ϖG)
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (m n : ℤ) :
    ϖG ^ m / ϖG ^ n ∈ N.normSubgroup ↔
      (N.residueDegree : ℤ) ∣ m - n := by
  rw [N.div_mem_normSubgroup_iff_residueDegree_dvd_valuation_difference_of_zeroSubgroup_le
      hϖH hzero (ϖG ^ m) (ϖG ^ n),
    vG.val_uniformizer_zpow hϖG m, vG.val_uniformizer_zpow hϖG n]

/-- Normal-form criterion for the norm subgroup when target valuation-zero
elements are norms. -/
theorem mem_normSubgroup_iff_exists_zeroSubgroup_mul_norm_uniformizer_zpow_eq
    {ϖH : H} (hϖH : vH.IsUniformizer ϖH)
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x : G) :
    x ∈ N.normSubgroup ↔
      ∃ u : G, u ∈ vG.zeroSubgroup ∧
        ∃ n : ℤ, x = u * N.toHom (ϖH ^ n) := by
  constructor
  · exact N.exists_zeroSubgroup_mul_norm_uniformizer_zpow_eq_of_mem_normSubgroup
      hϖH
  · rintro ⟨u, hu, n, hx⟩
    rw [hx]
    exact N.normSubgroup.mul_mem (hzero hu)
      ((MonoidHom.mem_range (f := N.toHom)).2 ⟨ϖH ^ n, rfl⟩)

/-- Membership in the norm subgroup is invariant under right multiplication by
a norm. -/
theorem normSubgroup_mul_iff_right {x h : G} (hh : h ∈ N.normSubgroup) :
    x * h ∈ N.normSubgroup ↔ x ∈ N.normSubgroup := by
  constructor
  · intro hxh
    have h : (x * h) * h⁻¹ ∈ N.normSubgroup :=
      N.normSubgroup.mul_mem hxh (N.normSubgroup.inv_mem hh)
    simpa [mul_assoc] using h
  · intro hx
    exact N.normSubgroup.mul_mem hx hh

/-- Membership in the norm subgroup is invariant under left multiplication by
a norm. -/
theorem normSubgroup_mul_iff_left {h x : G} (hh : h ∈ N.normSubgroup) :
    h * x ∈ N.normSubgroup ↔ x ∈ N.normSubgroup := by
  constructor
  · intro hhx
    have h : h⁻¹ * (h * x) ∈ N.normSubgroup :=
      N.normSubgroup.mul_mem (N.normSubgroup.inv_mem hh) hhx
    simpa [mul_assoc] using h
  · intro hx
    exact N.normSubgroup.mul_mem hh hx

/-- Dividing on the right by a norm preserves norm-subgroup membership. -/
theorem normSubgroup_div_iff_right {x h : G} (hh : h ∈ N.normSubgroup) :
    x / h ∈ N.normSubgroup ↔ x ∈ N.normSubgroup := by
  simpa [div_eq_mul_inv] using
    N.normSubgroup_mul_iff_right (x := x) (h := h⁻¹)
      (N.normSubgroup.inv_mem hh)

/-- Dividing a norm on the left by an element detects membership of that
element in the norm subgroup. -/
theorem normSubgroup_div_iff_left {h x : G} (hh : h ∈ N.normSubgroup) :
    h / x ∈ N.normSubgroup ↔ x ∈ N.normSubgroup := by
  constructor
  · intro hhx
    have h : h⁻¹ * (h / x) ∈ N.normSubgroup :=
      N.normSubgroup.mul_mem (N.normSubgroup.inv_mem hh) hhx
    have hxinv : x⁻¹ ∈ N.normSubgroup := by
      simpa [div_eq_mul_inv, mul_assoc] using h
    simpa using N.normSubgroup.inv_mem hxinv
  · intro hx
    exact N.normSubgroup.div_mem hh hx

/--
Characterizes `x * N.toHom y ∈ N.normSubgroup` by the equivalent condition `x ∈ N.normSubgroup`.
-/
theorem normSubgroup_mul_norm_iff (x : G) (y : H) :
    x * N.toHom y ∈ N.normSubgroup ↔ x ∈ N.normSubgroup :=
  N.normSubgroup_mul_iff_right
    ((MonoidHom.mem_range (f := N.toHom)).2 ⟨y, rfl⟩)

/--
Characterizes `N.toHom y * x ∈ N.normSubgroup` by the equivalent condition `x ∈ N.normSubgroup`.
-/
theorem normSubgroup_norm_mul_iff (y : H) (x : G) :
    N.toHom y * x ∈ N.normSubgroup ↔ x ∈ N.normSubgroup :=
  N.normSubgroup_mul_iff_left
    ((MonoidHom.mem_range (f := N.toHom)).2 ⟨y, rfl⟩)

/--
Characterizes `x / N.toHom y ∈ N.normSubgroup` by the equivalent condition `x ∈ N.normSubgroup`.
-/
theorem normSubgroup_div_norm_iff (x : G) (y : H) :
    x / N.toHom y ∈ N.normSubgroup ↔ x ∈ N.normSubgroup :=
  N.normSubgroup_div_iff_right
    ((MonoidHom.mem_range (f := N.toHom)).2 ⟨y, rfl⟩)

/--
Characterizes `N.toHom y / x ∈ N.normSubgroup` by the equivalent condition `x ∈ N.normSubgroup`.
-/
theorem normSubgroup_norm_div_iff (y : H) (x : G) :
    N.toHom y / x ∈ N.normSubgroup ↔ x ∈ N.normSubgroup :=
  N.normSubgroup_div_iff_left
    ((MonoidHom.mem_range (f := N.toHom)).2 ⟨y, rfl⟩)

/-- A norm equality against a quotient can be rewritten as a right-coset
equality. -/
theorem norm_mul_eq_of_norm_eq_div {x y : G} {z : H}
    (hz : N.toHom z = x / y) :
    N.toHom z * y = x := by
  have h := congrArg (fun t : G => t * y) hz
  simpa [div_eq_mul_inv, mul_assoc] using h

/-- A right-coset equality can be rewritten as a norm equality against a
quotient. -/
theorem norm_eq_div_of_norm_mul_eq {x y : G} {z : H}
    (hz : N.toHom z * y = x) :
    N.toHom z = x / y := by
  have h := congrArg (fun t : G => t * y⁻¹) hz
  simpa [div_eq_mul_inv, mul_assoc] using h

/-- A norm equality against a left quotient can be rewritten as a left-coset
equality. -/
theorem mul_norm_eq_of_norm_eq_inv_mul {x y : G} {z : H}
    (hz : N.toHom z = y⁻¹ * x) :
    y * N.toHom z = x := by
  have h := congrArg (fun t : G => y * t) hz
  simpa [mul_assoc] using h

/-- A left-coset equality can be rewritten as a norm equality against a left
quotient. -/
theorem norm_eq_inv_mul_of_mul_norm_eq {x y : G} {z : H}
    (hz : y * N.toHom z = x) :
    N.toHom z = y⁻¹ * x := by
  have h := congrArg (fun t : G => y⁻¹ * t) hz
  simpa [mul_assoc] using h

/-- Quotient membership in the norm subgroup is the same as representing the
left element as a norm times the right element. -/
theorem div_mem_normSubgroup_iff_exists_norm_mul_eq (x y : G) :
    x / y ∈ N.normSubgroup ↔ ∃ z : H, N.toHom z * y = x := by
  constructor
  · intro hxy
    rcases (MonoidHom.mem_range (f := N.toHom)).1 hxy with ⟨z, hz⟩
    exact ⟨z, N.norm_mul_eq_of_norm_eq_div hz⟩
  · rintro ⟨z, hz⟩
    exact (MonoidHom.mem_range (f := N.toHom)).2
      ⟨z, N.norm_eq_div_of_norm_mul_eq hz⟩

/-- Establishes the identity `∃ z : H, N.toHom z * y = x`. -/
theorem exists_norm_mul_eq_of_div_mem_normSubgroup
    {x y : G} (hxy : x / y ∈ N.normSubgroup) :
    ∃ z : H, N.toHom z * y = x :=
  (N.div_mem_normSubgroup_iff_exists_norm_mul_eq x y).1 hxy

/-- Establishes the membership statement `x / y ∈ N.normSubgroup`. -/
theorem div_mem_normSubgroup_of_exists_norm_mul_eq
    {x y : G} (hxy : ∃ z : H, N.toHom z * y = x) :
    x / y ∈ N.normSubgroup :=
  (N.div_mem_normSubgroup_iff_exists_norm_mul_eq x y).2 hxy

/-- Left-quotient membership in the norm subgroup is the same as representing
the left element as the right element times a norm. -/
theorem inv_mul_mem_normSubgroup_iff_exists_mul_norm_eq (x y : G) :
    y⁻¹ * x ∈ N.normSubgroup ↔ ∃ z : H, y * N.toHom z = x := by
  constructor
  · intro hxy
    rcases (MonoidHom.mem_range (f := N.toHom)).1 hxy with ⟨z, hz⟩
    exact ⟨z, N.mul_norm_eq_of_norm_eq_inv_mul hz⟩
  · rintro ⟨z, hz⟩
    exact (MonoidHom.mem_range (f := N.toHom)).2
      ⟨z, N.norm_eq_inv_mul_of_mul_norm_eq hz⟩

/-- Establishes the identity `∃ z : H, y * N.toHom z = x`. -/
theorem exists_mul_norm_eq_of_inv_mul_mem_normSubgroup
    {x y : G} (hxy : y⁻¹ * x ∈ N.normSubgroup) :
    ∃ z : H, y * N.toHom z = x :=
  (N.inv_mul_mem_normSubgroup_iff_exists_mul_norm_eq x y).1 hxy

/-- Establishes the membership statement `y⁻¹ * x ∈ N.normSubgroup`. -/
theorem inv_mul_mem_normSubgroup_of_exists_mul_norm_eq
    {x y : G} (hxy : ∃ z : H, y * N.toHom z = x) :
    y⁻¹ * x ∈ N.normSubgroup :=
  (N.inv_mul_mem_normSubgroup_iff_exists_mul_norm_eq x y).2 hxy

/-- Equality in the norm quotient is equivalent to a left-coset representative
equation when the norm subgroup is normal. -/
theorem normQuotient_mk_eq_iff_exists_mul_norm_eq
    [(N.normSubgroup).Normal] (x y : G) :
    QuotientGroup.mk' N.normSubgroup x =
        QuotientGroup.mk' N.normSubgroup y ↔
      ∃ z : H, y * N.toHom z = x := by
  rw [N.normQuotient_mk_eq_iff_inv_mul_mem x y,
    N.inv_mul_mem_normSubgroup_iff_exists_mul_norm_eq x y]

/-- Equality after mapping from `G ⧸ zeroSubgroup` to the norm quotient is
equivalent to a left-coset representative equation. -/
theorem zeroSubgroupQuotientToNormQuotient_mk_eq_iff_exists_mul_norm_eq
    [(N.normSubgroup).Normal]
    (hzero : vG.zeroSubgroup ≤ N.normSubgroup) (x y : G) :
    N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup x) =
      N.zeroSubgroupQuotientToNormQuotient hzero
        (QuotientGroup.mk' vG.zeroSubgroup y) ↔
      ∃ z : H, y * N.toHom z = x := by
  rw [N.zeroSubgroupQuotientToNormQuotient_mk_eq_iff_inv_mul_mem hzero x y,
    N.inv_mul_mem_normSubgroup_iff_exists_mul_norm_eq x y]

/-- If every source element is a source-unit part times a power of `ϖ`, if the
image of the chosen source-unit subgroup is `P`, and if `ϖ` maps to `γ`, then
the norm subgroup is `P ∨ <γ>`.

This is the group-theoretic core of finite Lubin--Tate norm-subgroup formulas,
stated without a theorem-carrying presentation structure. -/
theorem normSubgroup_eq_sup_of_source_decomposition
    (U : Subgroup H) (P : Subgroup G) (ϖ : H) (γ : G)
    (hdecomp :
      ∀ y : H, ∃ u : H, u ∈ U ∧ ∃ n : ℤ, y = u * ϖ ^ n)
    (hU : Subgroup.map N.toHom U = P)
    (hϖ : N.toHom ϖ = γ) :
    N.normSubgroup = P ⊔ Subgroup.closure ({γ} : Set G) := by
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨y, rfl⟩
    rcases hdecomp y with ⟨u, hu, n, hy⟩
    have hNuP : N.toHom u ∈ P := by
      have hmap : N.toHom u ∈ Subgroup.map N.toHom U := ⟨u, hu, rfl⟩
      simpa [hU] using hmap
    have hγ : γ ^ n ∈ Subgroup.closure ({γ} : Set G) :=
      (Subgroup.closure ({γ} : Set G)).zpow_mem
        (Subgroup.subset_closure (by simp)) n
    rw [hy, N.toHom.map_mul, N.toHom.map_zpow, hϖ]
    exact (P ⊔ Subgroup.closure ({γ} : Set G)).mul_mem
      ((le_sup_left : P ≤ P ⊔ Subgroup.closure ({γ} : Set G)) hNuP)
      ((le_sup_right : Subgroup.closure ({γ} : Set G) ≤
          P ⊔ Subgroup.closure ({γ} : Set G)) hγ)
  · exact sup_le
      (by
        intro x hx
        have hxmap : x ∈ Subgroup.map N.toHom U := by
          simpa [hU] using hx
        rcases hxmap with ⟨u, _hu, hux⟩
        exact ⟨u, hux⟩)
      (by
        rw [Subgroup.closure_le]
        intro x hx
        have hxγ : x = γ := by simpa using hx
        rw [hxγ]
        exact ⟨ϖ, hϖ⟩)

/-- Normal form for an element of the norm subgroup from a source
decomposition and a prescribed image of the source-unit subgroup. -/
theorem exists_targetSubgroup_mul_generator_zpow_of_mem_normSubgroup
    (U : Subgroup H) (P : Subgroup G) (ϖ : H) (γ : G)
    (hdecomp :
      ∀ y : H, ∃ u : H, u ∈ U ∧ ∃ n : ℤ, y = u * ϖ ^ n)
    (hU : Subgroup.map N.toHom U = P)
    (hϖ : N.toHom ϖ = γ)
    {x : G} (hx : x ∈ N.normSubgroup) :
    ∃ p : G, p ∈ P ∧ ∃ n : ℤ, x = p * γ ^ n := by
  rcases hx with ⟨y, rfl⟩
  rcases hdecomp y with ⟨u, hu, n, hy⟩
  refine ⟨N.toHom u, ?_, n, ?_⟩
  · have hmap : N.toHom u ∈ Subgroup.map N.toHom U := ⟨u, hu, rfl⟩
    simpa [hU] using hmap
  · calc
      N.toHom y = N.toHom (u * ϖ ^ n) := by rw [hy]
      _ = N.toHom u * γ ^ n := by
        rw [N.toHom.map_mul, N.toHom.map_zpow, hϖ]

/-- A target-subgroup element times a power of the selected generator lies in
the norm subgroup when the target subgroup is the image of the chosen source
subgroup and the generator is the norm of `ϖ`. -/
theorem mem_normSubgroup_of_targetSubgroup_mul_generator_zpow
    (U : Subgroup H) (P : Subgroup G) (ϖ : H) (γ : G)
    (hU : Subgroup.map N.toHom U = P)
    (hϖ : N.toHom ϖ = γ)
    {p x : G} (hp : p ∈ P) {n : ℤ} (hx : x = p * γ ^ n) :
    x ∈ N.normSubgroup := by
  have hpmap : p ∈ Subgroup.map N.toHom U := by
    simpa [hU] using hp
  rcases hpmap with ⟨u, _hu, hup⟩
  refine ⟨u * ϖ ^ n, ?_⟩
  calc
    N.toHom (u * ϖ ^ n) = N.toHom u * N.toHom (ϖ ^ n) := by
      rw [N.toHom.map_mul]
    _ = p * γ ^ n := by rw [N.toHom.map_zpow, hϖ, hup]
    _ = x := hx.symm

/-- Elementwise normal-form characterization of the norm subgroup from source
unit decomposition data. -/
theorem mem_normSubgroup_iff_exists_targetSubgroup_mul_generator_zpow
    (U : Subgroup H) (P : Subgroup G) (ϖ : H) (γ : G)
    (hdecomp :
      ∀ y : H, ∃ u : H, u ∈ U ∧ ∃ n : ℤ, y = u * ϖ ^ n)
    (hU : Subgroup.map N.toHom U = P)
    (hϖ : N.toHom ϖ = γ) (x : G) :
    x ∈ N.normSubgroup ↔
      ∃ p : G, p ∈ P ∧ ∃ n : ℤ, x = p * γ ^ n := by
  constructor
  · exact N.exists_targetSubgroup_mul_generator_zpow_of_mem_normSubgroup
      U P ϖ γ hdecomp hU hϖ
  · rintro ⟨p, hp, n, hx⟩
    exact N.mem_normSubgroup_of_targetSubgroup_mul_generator_zpow
      U P ϖ γ hU hϖ hp hx

/-- If the target subgroup in a norm-subgroup normal form has valuation zero,
then every norm-subgroup element has valuation a multiple of the selected
generator's valuation. -/
theorem exists_valuation_generator_multiple_of_mem_normSubgroup
    (U : Subgroup H) (P : Subgroup G) (ϖ : H) (γ : G)
    (hdecomp :
      ∀ y : H, ∃ u : H, u ∈ U ∧ ∃ n : ℤ, y = u * ϖ ^ n)
    (hU : Subgroup.map N.toHom U = P)
    (hϖ : N.toHom ϖ = γ)
    (hP : P ≤ vG.zeroSubgroup)
    {x : G} (hx : x ∈ N.normSubgroup) :
    ∃ n : ℤ, vG.val x = n * vG.val γ := by
  rcases
    N.exists_targetSubgroup_mul_generator_zpow_of_mem_normSubgroup
      U P ϖ γ hdecomp hU hϖ hx with
    ⟨p, hp, n, hxform⟩
  exact ⟨n,
    vG.val_eq_generator_multiple_of_mem_subgroup_mul_zpow
      P hP hp hxform⟩

/-- If the selected source element is a source uniformizer, the valuation of
its norm-image generator is the residue degree. -/
theorem valuation_generator_of_source_uniformizer
    {ϖ : H} {γ : G}
    (hϖH : vH.IsUniformizer ϖ) (hϖ : N.toHom ϖ = γ) :
    vG.val γ = (N.residueDegree : ℤ) := by
  have h := N.valuation_apply ϖ
  rw [hϖH, mul_one] at h
  rw [← hϖ]
  exact h

/-- In a normal form `x / y = p * γ^n`, equal target valuations force the
generator exponent to be zero, provided `P` has valuation zero and `γ` has
nonzero valuation. -/
theorem targetSubgroup_normal_form_exponent_zero_of_equal_valuation
    (P : Subgroup G) (hP : P ≤ vG.zeroSubgroup)
    {x y p γ : G} (hp : p ∈ P) {n : ℤ}
    (hxy : x / y = p * γ ^ n)
    (hvxy : vG.val x = vG.val y)
    (hγ : vG.val γ ≠ 0) :
    n = 0 := by
  have hquot0 : vG.val (x / y) = 0 :=
    (vG.val_div_eq_zero_iff x y).2 hvxy
  have hform : vG.val (x / y) = n * vG.val γ :=
    vG.val_eq_generator_multiple_of_mem_subgroup_mul_zpow
      P hP hp hxy
  have hn_mul : n * vG.val γ = 0 := by
    rw [← hform, hquot0]
  exact (mul_eq_zero.mp hn_mul).resolve_right hγ

/-- Equal target valuations reduce norm-quotient membership to the target
subgroup part of a source-decomposition normal form. -/
theorem targetSubgroup_quotient_of_mem_normSubgroup_of_equal_valuation
    (U : Subgroup H) (P : Subgroup G) (ϖ : H) (γ : G)
    (hdecomp :
      ∀ y : H, ∃ u : H, u ∈ U ∧ ∃ n : ℤ, y = u * ϖ ^ n)
    (hU : Subgroup.map N.toHom U = P)
    (hϖ : N.toHom ϖ = γ)
    (hP : P ≤ vG.zeroSubgroup)
    (hγ : vG.val γ ≠ 0)
    {x y : G} (hxyN : x / y ∈ N.normSubgroup)
    (hvxy : vG.val x = vG.val y) :
    ∃ p : G, p ∈ P ∧ x / y = p := by
  rcases
    (N.mem_normSubgroup_iff_exists_targetSubgroup_mul_generator_zpow
      U P ϖ γ hdecomp hU hϖ (x / y)).1 hxyN with
    ⟨p, hp, n, hform⟩
  have hn : n = 0 :=
    targetSubgroup_normal_form_exponent_zero_of_equal_valuation
      P hP hp hform hvxy hγ
  exact ⟨p, hp, by simpa [hn] using hform⟩

/-- With equal target valuations, norm-quotient membership is equivalent to
having a representative in the target subgroup part. -/
theorem normSubgroup_quotient_iff_targetSubgroup_of_equal_valuation
    (U : Subgroup H) (P : Subgroup G) (ϖ : H) (γ : G)
    (hdecomp :
      ∀ y : H, ∃ u : H, u ∈ U ∧ ∃ n : ℤ, y = u * ϖ ^ n)
    (hU : Subgroup.map N.toHom U = P)
    (hϖ : N.toHom ϖ = γ)
    (hP : P ≤ vG.zeroSubgroup)
    (hγ : vG.val γ ≠ 0)
    {x y : G} (hvxy : vG.val x = vG.val y) :
    x / y ∈ N.normSubgroup ↔
      ∃ p : G, p ∈ P ∧ x / y = p := by
  constructor
  · intro hxyN
    exact N.targetSubgroup_quotient_of_mem_normSubgroup_of_equal_valuation
      U P ϖ γ hdecomp hU hϖ hP hγ hxyN hvxy
  · rintro ⟨p, hp, hxy⟩
    exact N.mem_normSubgroup_of_targetSubgroup_mul_generator_zpow
      U P ϖ γ hU hϖ hp (n := 0) (by simp [hxy])

/-- The source-uniformizer/residue-degree version of
`targetSubgroup_quotient_of_mem_normSubgroup_of_equal_valuation`. -/
theorem targetSubgroup_quotient_of_mem_normSubgroup_of_equal_valuation_of_source_uniformizer
    (U : Subgroup H) (P : Subgroup G) (ϖ : H) (γ : G)
    (hdecomp :
      ∀ y : H, ∃ u : H, u ∈ U ∧ ∃ n : ℤ, y = u * ϖ ^ n)
    (hU : Subgroup.map N.toHom U = P)
    (hϖ : N.toHom ϖ = γ)
    (hP : P ≤ vG.zeroSubgroup)
    (hϖH : vH.IsUniformizer ϖ)
    (hdeg : N.residueDegree ≠ 0)
    {x y : G} (hxyN : x / y ∈ N.normSubgroup)
    (hvxy : vG.val x = vG.val y) :
    ∃ p : G, p ∈ P ∧ x / y = p := by
  apply N.targetSubgroup_quotient_of_mem_normSubgroup_of_equal_valuation
    U P ϖ γ hdecomp hU hϖ hP ?_ hxyN hvxy
  rw [N.valuation_generator_of_source_uniformizer hϖH hϖ]
  exact Int.ofNat_ne_zero.mpr hdeg

/-- The source-uniformizer/residue-degree version of the equal-valuation
criterion for norm-quotient membership. -/
theorem normSubgroup_quotient_iff_targetSubgroup_of_equal_valuation_of_source_uniformizer
    (U : Subgroup H) (P : Subgroup G) (ϖ : H) (γ : G)
    (hdecomp :
      ∀ y : H, ∃ u : H, u ∈ U ∧ ∃ n : ℤ, y = u * ϖ ^ n)
    (hU : Subgroup.map N.toHom U = P)
    (hϖ : N.toHom ϖ = γ)
    (hP : P ≤ vG.zeroSubgroup)
    (hϖH : vH.IsUniformizer ϖ)
    (hdeg : N.residueDegree ≠ 0)
    {x y : G} (hvxy : vG.val x = vG.val y) :
    x / y ∈ N.normSubgroup ↔
      ∃ p : G, p ∈ P ∧ x / y = p := by
  apply N.normSubgroup_quotient_iff_targetSubgroup_of_equal_valuation
    U P ϖ γ hdecomp hU hϖ hP ?_ hvxy
  rw [N.valuation_generator_of_source_uniformizer hϖH hϖ]
  exact Int.ofNat_ne_zero.mpr hdeg

/-- A target-subgroup representative of a quotient has zero valuation
displacement when the target subgroup has valuation zero. -/
theorem equal_valuation_of_targetSubgroup_quotient
    (P : Subgroup G) (hP : P ≤ vG.zeroSubgroup)
    {x y p : G} (hp : p ∈ P) (hxy : x / y = p) :
    vG.val x = vG.val y := by
  have hquot0 : vG.val (x / y) = 0 := by
    rw [hxy]
    exact (vG.mem_zeroSubgroup_iff p).1 (hP hp)
  exact (vG.val_div_eq_zero_iff x y).1 hquot0

end ValuedNorm

end DiscreteValuationField

end

end LocalFieldTheory
