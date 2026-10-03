/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Valuation
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients
public import Mathlib.Algebra.Group.Hom.Basic
public import Mathlib.Algebra.Group.Subgroup.Basic
/-!
# The valuation exact sequence

Builds the normalized valuation map `Kˣ → ℤ` and proves exactness of the
sequence from valuation-ring units through field units to `ℤ`.
-/

@[expose] public section

namespace LocalFieldTheory

noncomputable
section

universe u

namespace IsNonarchimedeanLocalField

open scoped ValuativeRel WithZero

/-- The multiplicative normalized valuation on field units. -/
noncomputable def valuationUnitsMulHom
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] : Kˣ →* Multiplicative Int :=
  (@WithZero.unitsWithZeroEquiv (Multiplicative Int) _).toMonoidHom.comp
    ((Units.map (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).toMonoidHom).comp
      (Units.map (ValuativeRel.valuation K).toMonoidWithZeroHom.toMonoidHom))

/-- The actual normalized valuation map on field units, bundled as an additive hom. -/
noncomputable def valuationMap (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Additive Kˣ →+ Int :=
  MonoidHom.toAdditive (valuationUnitsMulHom K)

/-- Defines `valuationShortComplex`. -/
def valuationShortComplex (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Additive Kˣ →+ Int :=
  valuationMap K

/-- The additive valuation map evaluates a field unit by applying the normalized integer valuation.
The additive valuation map evaluates a field unit by applying the normalized integer valuation. -/
@[simp]
theorem valuationMap_apply (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    valuationMap K x = v K x :=
  rfl

/-- Every integer is the valuation of some field unit. -/
theorem valuationMap_surjective (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Function.Surjective (valuationMap K) :=
  v_surjective K

/-- A chosen normalized uniformizer maps to one under the additive valuation map. -/
theorem valuationMap_uniformiser (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    ∃ ϖ : Kˣ, valuationMap K (Additive.ofMul ϖ) = 1 :=
  v_uniformiser K

/-- A valuation-theoretic uniformizer, regarded as a unit of the ambient
field.  The nonzero proof is supplied by the actual uniformizer property. -/
noncomputable def uniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    Kˣ :=
  Units.mk0 (π : K) hπ.ne_zero

/-- Coercing the field unit attached to a valuation-theoretic uniformizer
recovers the original field element. -/
@[simp]
theorem uniformizerFieldUnit_coe
    (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    (uniformizerFieldUnit K π hπ : K) = (π : K) :=
  rfl

/-- A valuation-theoretic uniformizer has normalized additive value `-1`
in the inverse-standard convention used by the concrete local Artin map. -/
theorem valuationMap_uniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K)) :
    valuationMap K
        (Additive.ofMul (uniformizerFieldUnit K π hπ)) =
      -1 := by
  have hπIrreducible : Irreducible π :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).2
      (Valuation.IsUniformizer.is_generator
        (v := ValuativeRel.valuation K) hπ)
  simpa [valuationMap_apply] using
    (v_integerRingIrreducibleFieldUnit K π hπIrreducible
      (uniformizerFieldUnit K π hπ) rfl)


/-- The additive valuation map sends the zero element of the additive unit group to zero. -/
theorem valuationMap_zero (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    valuationMap K (0 : Additive Kˣ) = 0 :=
  map_zero (valuationMap K)

/-- The additive valuation map sends addition of additive field units to addition of integers. -/
theorem valuationMap_add (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x y : Additive Kˣ) :
    valuationMap K (x + y) = valuationMap K x + valuationMap K y :=
  map_add (valuationMap K) x y

/-- The additive valuation map sends additive negation to integer negation. -/
theorem valuationMap_neg (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    valuationMap K (-x) = -valuationMap K x :=
  map_neg (valuationMap K) x

/-- The additive valuation map sends subtraction to subtraction of valuations. -/
theorem valuationMap_sub (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x y : Additive Kˣ) :
    valuationMap K (x - y) = valuationMap K x - valuationMap K y :=
  map_sub (valuationMap K) x y

/-- The additive valuation map commutes with integral scalar multiplication. -/
theorem valuationMap_zsmul (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Int) (x : Additive Kˣ) :
    valuationMap K (n • x) = n • valuationMap K x :=
  map_zsmul (valuationMap K) n x

/-- An additive field unit maps to zero exactly when its normalized valuation is zero. -/
theorem valuationMap_eq_zero_iff_v_eq_zero (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    valuationMap K x = 0 ↔ v K x = 0 := by
  rw [valuationMap_apply]

/-- The kernel of the additive valuation map consists precisely of units of normalized valuation
zero. -/
theorem valuationMap_mem_ker_iff (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Additive Kˣ) :
    x ∈ AddMonoidHom.ker (valuationMap K) ↔ v K x = 0 := by
  rw [AddMonoidHom.mem_ker, valuationMap_apply]

/-- The multiplicative identity, viewed additively, has valuation zero. -/
theorem valuationMap_ofMul_one (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    valuationMap K (Additive.ofMul (1 : Kˣ)) = 0 := by
  change valuationMap K (0 : Additive Kˣ) = 0
  exact valuationMap_zero K

/-- The valuation of a product of field units is the sum of their valuations. -/
theorem valuationMap_ofMul_mul (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    valuationMap K (Additive.ofMul (x * y)) =
      valuationMap K (Additive.ofMul x) + valuationMap K (Additive.ofMul y) := by
  change v K (Additive.ofMul (x * y)) =
    v K (Additive.ofMul x) + v K (Additive.ofMul y)
  exact v_mul K x y

/-- The valuation of an inverse field unit is the negative of its valuation. -/
theorem valuationMap_ofMul_inv (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Kˣ) :
    valuationMap K (Additive.ofMul x⁻¹) =
      -valuationMap K (Additive.ofMul x) := by
  change v K (Additive.ofMul x⁻¹) = -v K (Additive.ofMul x)
  exact v_inv K x

/-- A field unit with additive valuation zero has multiplicative valuation one. -/
theorem valuation_eq_one_of_valuationMap_eq_zero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    {x : Kˣ} (hx : valuationMap K (Additive.ofMul x) = 0) :
    ValuativeRel.valuation K (x : K) = 1 := by
  rw [valuationMap_apply] at hx
  dsimp [v] at hx
  have hunzero :
      WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K (x : K)))
        (by simp) = (1 : Multiplicative Int) := by
    have h := congrArg Multiplicative.ofAdd hx
    simpa using h
  apply (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K).injective
  have hcoe :
      ((WithZero.unzero
        (x := (_root_.IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt K)
          (ValuativeRel.valuation K (x : K)))
        (by simp) : Multiplicative Int) : WithZero (Multiplicative Int)) =
        (1 : WithZero (Multiplicative Int)) := by
    simpa using congrArg
      (fun y : Multiplicative Int => (y : WithZero (Multiplicative Int))) hunzero
  rw [WithZero.coe_unzero] at hcoe
  simpa using hcoe

/-- The valuation of a quotient of field units is the difference of their valuations. -/
theorem valuationMap_ofMul_div (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x y : Kˣ) :
    valuationMap K (Additive.ofMul (x / y)) =
      valuationMap K (Additive.ofMul x) - valuationMap K (Additive.ofMul y) := by
  change v K (Additive.ofMul (x / y)) = v K (Additive.ofMul x) - v K (Additive.ofMul y)
  exact v_div K x y

/-- The valuation of an integral power is the exponent times the original valuation. -/
theorem valuationMap_ofMul_zpow (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Int) :
    valuationMap K (Additive.ofMul (x ^ n)) =
      n * valuationMap K (Additive.ofMul x) := by
  change v K (Additive.ofMul (x ^ n)) = n * v K (Additive.ofMul x)
  exact v_zpow K x n

/-- The valuation of a natural power is the power times the original valuation. -/
theorem valuationMap_ofMul_pow (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Kˣ) (n : Nat) :
    valuationMap K (Additive.ofMul (x ^ n)) =
      (n : Int) * valuationMap K (Additive.ofMul x) := by
  change v K (Additive.ofMul (x ^ n)) = (n : Int) * v K (Additive.ofMul x)
  exact v_pow K x n

/-- A field unit has additive valuation zero exactly when its multiplicative valuation is one. -/
theorem valuationMap_ofMul_eq_zero_iff (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (x : Kˣ) :
    valuationMap K (Additive.ofMul x) = 0 ↔ v K (Additive.ofMul x) = 0 :=
  valuationMap_eq_zero_iff_v_eq_zero K (Additive.ofMul x)

/-- Defines `additiveIntegerUnitsToFieldUnits`. -/
def additiveIntegerUnitsToFieldUnits (K : Type u) [Field K] [ValuativeRel K] :
    Additive 𝒪[K]ˣ →+ Additive Kˣ :=
  MonoidHom.toAdditive (integerUnitsToFieldUnits K)

/-- The additive inclusion of valuation-ring units agrees with the underlying multiplicative
inclusion. -/
@[simp]
theorem additiveIntegerUnitsToFieldUnits_apply (K : Type u) [Field K] [ValuativeRel K]
    (u : 𝒪[K]ˣ) :
    additiveIntegerUnitsToFieldUnits K (Additive.ofMul u) =
      Additive.ofMul (integerUnitsToFieldUnits K u) :=
  rfl

/-- Defines `integerUnitOfValuationMapZero`. -/
def integerUnitOfValuationMapZero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) : 𝒪[K]ˣ where
  val := ⟨(x : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  inv := ⟨(x⁻¹ : K), by
    rw [valuation_integer_membership]
    have hv := valuation_eq_one_of_valuationMap_eq_zero K hx
    simp [hv]⟩
  val_inv := by
    ext
    simp
  inv_val := by
    ext
    simp

/-- The valuation-ring unit reconstructed from a field unit of valuation zero maps back to that
field unit. -/
@[simp]
theorem integerUnitOfValuationMapZero_spec (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) (hx : valuationMap K (Additive.ofMul x) = 0) :
    integerUnitsToFieldUnits K (integerUnitOfValuationMapZero K x hx) = x := by
  ext
  rfl

/-- A field unit comes from a valuation-ring unit exactly when its additive valuation is zero. -/
theorem integerUnitsToFieldUnits_mem_range_iff_valuationMap_eq_zero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Kˣ) :
    x ∈ MonoidHom.range (integerUnitsToFieldUnits K) ↔
      valuationMap K (Additive.ofMul x) = 0 := by
  constructor
  · rintro ⟨u, rfl⟩
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K u
  · intro hx
    exact ⟨integerUnitOfValuationMapZero K x hx,
      integerUnitOfValuationMapZero_spec K x hx⟩

/-- A valuation-integer unit is an `n`-th power among integer units exactly
when it is an `n`-th power among field units. -/
theorem mem_powMonoidHom_range_integerUnits_iff (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (n : ℕ+) (x : 𝒪[K]ˣ) :
    x ∈ (powMonoidHom (n : ℕ) : 𝒪[K]ˣ →* 𝒪[K]ˣ).range ↔
      integerUnitsToFieldUnits K x ∈
        (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := 𝒪[K]ˣ)).mp hx
    rw [powMonoidHom_apply] at hy
    apply
      (MonoidHom.mem_range
        (G := Kˣ)).mpr
    refine ⟨integerUnitsToFieldUnits K y, ?_⟩
    rw [powMonoidHom_apply, ← map_pow, hy]
  · intro hx
    obtain ⟨y, hy⟩ :=
      (MonoidHom.mem_range
        (G := Kˣ)).mp hx
    rw [powMonoidHom_apply] at hy
    have hyValPow :
        valuationMap K (Additive.ofMul (y ^ (n : ℕ))) = 0 := by
      rw [hy, valuationMap_apply]
      exact v_integerUnitsToFieldUnits K x
    rw [valuationMap_ofMul_pow] at hyValPow
    have hyVal :
        valuationMap K (Additive.ofMul y) = 0 :=
      (mul_eq_zero.mp hyValPow).resolve_left
        (Int.ofNat_ne_zero.mpr n.ne_zero)
    let z : 𝒪[K]ˣ :=
      integerUnitOfValuationMapZero K y hyVal
    apply
      (MonoidHom.mem_range
        (G := 𝒪[K]ˣ)).mpr
    refine ⟨z, ?_⟩
    apply integerUnitsToFieldUnits_injective K
    rw [powMonoidHom_apply, map_pow,
      integerUnitOfValuationMapZero_spec, hy]

/-- The image of valuation-ring units inside field units is exactly the kernel of the additive
valuation map. -/
theorem additiveIntegerUnitsToFieldUnits_range_eq_ker_valuationMap (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    AddMonoidHom.range (additiveIntegerUnitsToFieldUnits K) =
      AddMonoidHom.ker (valuationMap K) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    change valuationMap K
      (Additive.ofMul (integerUnitsToFieldUnits K (Additive.toMul u))) = 0
    rw [valuationMap_apply]
    exact v_integerUnitsToFieldUnits K (Additive.toMul u)
  · intro hx
    rw [AddMonoidHom.mem_ker] at hx
    refine ⟨Additive.ofMul
      (integerUnitOfValuationMapZero K (Additive.toMul x) ?_), ?_⟩
    · simpa using hx
    · simp [additiveIntegerUnitsToFieldUnits]

/-- Additive quotient form of the local valuation sequence: `Kˣ / 𝒪[K]ˣ ≃ ℤ`. -/
noncomputable def fieldUnitsModIntegerUnitsAddEquivInt (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] :
    Additive Kˣ ⧸ AddMonoidHom.range (additiveIntegerUnitsToFieldUnits K) ≃+ Int :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (additiveIntegerUnitsToFieldUnits_range_eq_ker_valuationMap K)).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective
      (valuationMap K) (valuationMap_surjective K))

/-- The quotient of field units by valuation-ring units sends the class of a unit to its integer
valuation. -/
@[simp]
theorem fieldUnitsModIntegerUnitsAddEquivInt_mk (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Additive Kˣ) :
    fieldUnitsModIntegerUnitsAddEquivInt K (QuotientAddGroup.mk x) =
      valuationMap K x := by
  simp only [fieldUnitsModIntegerUnitsAddEquivInt, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  rw [QuotientAddGroup.quotientKerEquivOfSurjective,
    QuotientAddGroup.quotientKerEquivOfRightInverse_apply,
    QuotientAddGroup.kerLift_mk]

/-- A field-unit quotient class maps to zero exactly when its representative is a valuation-ring
unit. -/
theorem fieldUnitsModIntegerUnitsAddEquivInt_mk_eq_zero_iff (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x : Additive Kˣ) :
    fieldUnitsModIntegerUnitsAddEquivInt K (QuotientAddGroup.mk x) = 0 ↔
      valuationMap K x = 0 := by
  rw [fieldUnitsModIntegerUnitsAddEquivInt_mk]

/-- Two field units define the same class modulo valuation-ring units exactly when they have equal
valuation. -/
theorem fieldUnitsModIntegerUnitsAddEquivInt_mk_eq_mk_iff (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x y : Additive Kˣ) :
    (QuotientAddGroup.mk x :
        Additive Kˣ ⧸ AddMonoidHom.range (additiveIntegerUnitsToFieldUnits K)) =
      QuotientAddGroup.mk y ↔ valuationMap K x = valuationMap K y := by
  constructor
  · intro h
    simpa [fieldUnitsModIntegerUnitsAddEquivInt_mk] using
      congrArg (fieldUnitsModIntegerUnitsAddEquivInt K) h
  · intro h
    apply (fieldUnitsModIntegerUnitsAddEquivInt K).injective
    simpa [fieldUnitsModIntegerUnitsAddEquivInt_mk] using h

/-- The difference of two quotient classes vanishes exactly when the representatives have equal
valuation. -/
theorem fieldUnitsModIntegerUnitsAddEquivInt_mk_sub_eq_zero_iff (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (x y : Additive Kˣ) :
    fieldUnitsModIntegerUnitsAddEquivInt K (QuotientAddGroup.mk (x - y)) = 0 ↔
      valuationMap K x = valuationMap K y := by
  rw [fieldUnitsModIntegerUnitsAddEquivInt_mk, map_sub, sub_eq_zero]

/-- The quotient of a field unit by the corresponding power of a uniformizer has
normalized valuation zero. -/
theorem uniformizerUnitFactorValuationZero (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ x : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) :
    valuationMap K
      (Additive.ofMul (x / ϖ ^ valuationMap K (Additive.ofMul x))) = 0 := by
  rw [valuationMap_ofMul_div, valuationMap_ofMul_zpow, hϖ, mul_one, sub_self]

/-- The integer-unit factor in the standard decomposition `x = u * ϖ ^ v(x)`. -/
noncomputable def uniformizerUnitFactor (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1)
    (x : Kˣ) : 𝒪[K]ˣ :=
  integerUnitOfValuationMapZero K
    (x / ϖ ^ valuationMap K (Additive.ofMul x))
    (uniformizerUnitFactorValuationZero K ϖ x hϖ)

/-- Removing the uniformizer power prescribed by a field unit's valuation leaves a valuation-ring
unit. -/
@[simp]
theorem integerUnitsToFieldUnits_uniformizerUnitFactor (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) =
      x / ϖ ^ valuationMap K (Additive.ofMul x) :=
  integerUnitOfValuationMapZero_spec K
    (x / ϖ ^ valuationMap K (Additive.ofMul x))
    (uniformizerUnitFactorValuationZero K ϖ x hϖ)

/-- Standard local-field unit/uniformizer decomposition in multiplicative form. -/
theorem uniformizerUnitFactor_mul_uniformizer_zpow (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    integerUnitsToFieldUnits K (uniformizerUnitFactor K ϖ hϖ x) *
        ϖ ^ valuationMap K (Additive.ofMul x) = x := by
  rw [integerUnitsToFieldUnits_uniformizerUnitFactor]
  simp [div_eq_mul_inv, mul_assoc]

/-- Existence form of the standard decomposition `Kˣ = O_Kˣ · ⟨ϖ⟩`. -/
theorem exists_integerUnit_mul_uniformizer_zpow (K : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ) (hϖ : valuationMap K (Additive.ofMul ϖ) = 1) (x : Kˣ) :
    ∃ u : 𝒪[K]ˣ,
      integerUnitsToFieldUnits K u *
        ϖ ^ valuationMap K (Additive.ofMul x) = x :=
  ⟨uniformizerUnitFactor K ϖ hϖ x,
    uniformizerUnitFactor_mul_uniformizer_zpow K ϖ hϖ x⟩

/-- The chosen preimage operation for the valuation map has the requested integer valuation. -/
theorem valuationMap_surjective_apply (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Int) :
    ∃ x : Additive Kˣ, valuationMap K x = n :=
  valuationMap_surjective K n

/-- Defines `chosenValuationMapSection`. -/
noncomputable def chosenValuationMapSection (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] : Int → Additive Kˣ :=
  fun n => Classical.choose (valuationMap_surjective_apply K n)

/-- The chosen section of the additive valuation map is a right inverse. -/
theorem chosenValuationMapSection_spec (K : Type u) [Field K] [ValuativeRel K]
    [TopologicalSpace K] [IsNonarchimedeanLocalField K] (n : Int) :
    valuationMap K (chosenValuationMapSection K n) = n :=
  Classical.choose_spec (valuationMap_surjective_apply K n)

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
