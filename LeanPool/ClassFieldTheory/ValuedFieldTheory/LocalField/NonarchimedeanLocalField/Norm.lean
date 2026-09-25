/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.RingTheory.Norm.Transitivity
public import Mathlib.RingTheory.Valuation.Integral
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NormUnits
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuativeExtension
public import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.Basic
/-!
# Norms in valued field extensions

Packages field norms as homomorphisms on units and restricts them to valuation
rings and their unit groups under the appropriate integral hypotheses.
-/

@[expose] public section
namespace LocalFieldTheory

noncomputable
section

universe u v

namespace IsNonarchimedeanLocalField

open scoped BigOperators ValuativeRel

variable {K : Type u} {L : Type v}

section AlgebraNorm

variable [Field K] [Field L] [Algebra K L] [Module.Free K L] [Module.Finite K L]

omit [Module.Free K L] [Module.Finite K L] in
/-- Left multiplication by a nonzero field element is injective as a linear map. -/
lemma mulLeft_injective_of_ne_zero {x : L} (hx : x ≠ 0) :
    Function.Injective (LinearMap.mulLeft K x) := by
  intro y z hyz
  exact mul_left_cancel₀ hx hyz

omit [Module.Free K L] [Module.Finite K L] in
/-- Left multiplication by a nonzero field element is surjective as a linear map. -/
lemma mulLeft_surjective_of_ne_zero {x : L} (hx : x ≠ 0) :
    Function.Surjective (LinearMap.mulLeft K x) := by
  intro y
  refine ⟨x⁻¹ * y, ?_⟩
  simp [LinearMap.mulLeft, hx]

/-- A bijective linear endomorphism has nonzero determinant. -/
lemma det_ne_zero_of_bijective (f : L →ₗ[K] L) (hf : Function.Bijective f) :
    LinearMap.det f ≠ 0 := by
  intro hdet
  have hker_ne : LinearMap.ker f ≠ ⊥ :=
    (LinearMap.det_eq_zero_iff_ker_ne_bot (f := f)).1 hdet
  have hker : LinearMap.ker f = ⊥ :=
    LinearMap.ker_eq_bot.mpr hf.1
  exact hker_ne hker

end AlgebraNorm

section UnitNorm

variable [Field K] [Field L] [Algebra K L]

/-- Base units embedded in an extension. -/
def mapBaseUnitsToExtensionUnits
    (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L] :
    Kˣ →* Lˣ :=
  Units.map (algebraMap K L).toMonoidHom


/-- The inclusion of base-field units into extension-field units agrees with the algebra map on
underlying elements. -/
@[simp]
lemma mapBaseUnitsToExtensionUnits_apply_coe (x : Kˣ) :
    ((mapBaseUnitsToExtensionUnits K L x : Lˣ) : L) = algebraMap K L (x : K) :=
  rfl

/-- The norm of a base unit embedded in the extension is its underlying element raised to the
extension degree. -/
lemma normUnits_mapBaseUnitsToExtensionUnits_apply_coe (x : Kˣ) :
    ((normUnits K L (mapBaseUnitsToExtensionUnits K L x) : Kˣ) : K) =
      (x : K) ^ Module.finrank K L := by
  simp [normUnits, mapBaseUnitsToExtensionUnits, Algebra.norm_algebraMap]

/-- The unit norm of an embedded base unit is the degree-th power of that base unit. -/
lemma normUnits_algebraMap_base (x : Kˣ) :
    normUnits K L (mapBaseUnitsToExtensionUnits K L x) =
      Units.map (MonoidHom.id K) (x ^ Module.finrank K L) := by
  ext
  simp [normUnits, mapBaseUnitsToExtensionUnits, Algebra.norm_algebraMap]

/-- The field norm is invariant under `K`-algebra automorphisms of the extension. -/
lemma normUnits_algEquiv_apply (σ : L ≃ₐ[K] L) (x : Lˣ) :
    normUnits K L (Units.mapEquiv σ.toMulEquiv x) = normUnits K L x := by
  ext
  exact Algebra.norm_eq_of_algEquiv σ (x : L)

/-- The norm of an element integral over the base valuation ring lies in the base valuation ring. -/
lemma algebraNorm_mem_integers_of_mem_integers [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]) :
    Algebra.norm K (x : L) ∈ 𝒪[K] := by
  exact Valuation.Integers.mem_of_integral
    (Valuation.integer.integers (ValuativeRel.valuation K))
    (Algebra.isIntegral_norm K (LocalFieldTheory.ValuativeExtension.integer_isIntegral x))

/-- An element of an integral-closure valuation ring is integral over the base valuation ring. -/
lemma integer_element_isIntegral_over_base_integer_of_isIntegralClosure [ValuativeRel K]
    [ValuativeRel L] [IsIntegralClosure 𝒪[L] 𝒪[K] L] (x : 𝒪[L]) :
    IsIntegral 𝒪[K] (x : L) :=
  (IsIntegralClosure.isIntegral_iff (A := 𝒪[L]) (R := 𝒪[K]) (B := L)).2 ⟨x, rfl⟩

/-- Under an integral-closure identification, the norm of a target valuation-ring element lies in
the base valuation ring. -/
lemma algebraNorm_mem_integers_of_mem_integers_of_isIntegralClosure [ValuativeRel K]
    [ValuativeRel L] [IsIntegralClosure 𝒪[L] 𝒪[K] L] (x : 𝒪[L]) :
    Algebra.norm K (x : L) ∈ 𝒪[K] := by
  exact Valuation.Integers.mem_of_integral
    (Valuation.integer.integers (ValuativeRel.valuation K))
    (Algebra.isIntegral_norm K
      (integer_element_isIntegral_over_base_integer_of_isIntegralClosure x))

/-- A target valuation-ring element is integral over the base valuation ring. -/
lemma integer_element_isIntegral_over_base_integer [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]) :
    IsIntegral 𝒪[K] (x : L) :=
  LocalFieldTheory.ValuativeExtension.integer_isIntegral x

/-- A valuation-ring element in a finite valuative extension is integral over the base valuation
ring. -/
lemma integer_element_isIntegral_over_base_integer_of_valuativeExtension [ValuativeRel K]
    [ValuativeRel L] [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]) :
    IsIntegral 𝒪[K] (x : L) :=
  integer_element_isIntegral_over_base_integer x

/-- The algebra norm of an element integral over the base ring is integral over that ring. -/
lemma algebraNorm_isIntegral_of_isIntegral
    {R : Type u} [CommRing R] [Algebra R K] [Algebra R L] [IsScalarTower R K L]
    {x : L} (hx : IsIntegral R x) :
    IsIntegral R (Algebra.norm K x) :=
  Algebra.isIntegral_norm K hx

/-- An element of the base field integral over its valuation ring belongs to that valuation ring. -/
lemma mem_integers_of_isIntegral_base [ValuativeRel K] {x : K}
    (hx : IsIntegral 𝒪[K] x) :
    x ∈ 𝒪[K] :=
  Valuation.Integers.mem_of_integral
    (Valuation.integer.integers (ValuativeRel.valuation K)) hx

/-- The norm of an element integral over the base valuation ring belongs to the base valuation ring.
The norm of an element integral over the base valuation ring belongs to the base valuation ring. -/
lemma algebraNorm_mem_integers_of_isIntegral [ValuativeRel K]
    {x : L} (hx : IsIntegral 𝒪[K] x) :
    Algebra.norm K x ∈ 𝒪[K] :=
  mem_integers_of_isIntegral_base (K := K)
    (algebraNorm_isIntegral_of_isIntegral (K := K) (L := L) (R := 𝒪[K]) hx)

/-- The norm of a target valuation-ring element has base valuation at most one. -/
lemma valuation_norm_le_one_of_integer [ValuativeRel K] {x : K}
    (hx : x ∈ 𝒪[K]) :
    ValuativeRel.valuation K x ≤ 1 :=
  (Valuation.mem_integer_iff (ValuativeRel.valuation K) x).1 hx

/-- The inverse norm of a target valuation-ring unit also belongs to the base valuation ring. -/
lemma algebraNorm_inv_mem_integers_of_unit [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) ∈ 𝒪[K] :=
  algebraNorm_mem_integers_of_mem_integers (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]))

/-- Defines `normIntegerUnitsValue`. -/
def normIntegerUnitsValue [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) : 𝒪[K] :=
  ⟨Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L),
    algebraNorm_mem_integers_of_mem_integers ((x : 𝒪[L]ˣ) : 𝒪[L])⟩

/-- The norm value constructed from an integer unit multiplied by its inverse is one. -/
lemma normIntegerUnitsValue_mul_inv [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    normIntegerUnitsValue (K := K) (L := L) x *
      normIntegerUnitsValue (K := K) (L := L) x⁻¹ = 1 := by
  ext
  change Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
  have hx : (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 := by
    change (((x * x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
    simp
  rw [← map_mul (Algebra.norm K)]
  simp [hx]

/-- The inverse norm value multiplied by the norm value of an integer unit is one. -/
lemma normIntegerUnitsValue_inv_mul [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    normIntegerUnitsValue (K := K) (L := L) x⁻¹ *
      normIntegerUnitsValue (K := K) (L := L) x = 1 := by
  ext
  change Algebra.norm K (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
  have hx : (((x⁻¹ : 𝒪[L]ˣ) : 𝒪[L]) : L) *
      (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1 := by
    change (((x⁻¹ * x : 𝒪[L]ˣ) : 𝒪[L]) : L) = 1
    simp
  rw [← map_mul (Algebra.norm K)]
  simp [hx]

/-- Norm restricted to valuation-integer units. -/
def normIntegerUnits
    (K : Type u) (L : Type v)
    [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
    [Algebra K L] [LocalFieldTheory.ValuativeExtension K L] : 𝒪[L]ˣ →* 𝒪[K]ˣ where
  toFun := fun x => {
    val := normIntegerUnitsValue (K := K) (L := L) x
    inv := normIntegerUnitsValue (K := K) (L := L) x⁻¹
    val_inv := normIntegerUnitsValue_mul_inv (K := K) (L := L) x
    inv_val := normIntegerUnitsValue_inv_mul (K := K) (L := L) x
  }
  map_one' := by
    ext
    simp [normIntegerUnitsValue]
  map_mul' := by
    intro x y
    ext
    simp [normIntegerUnitsValue]

/-- Coercing the integer-unit norm to the base field yields the algebra norm of the original
unit. -/
lemma normIntegerUnits_apply_coe [ValuativeRel K] [ValuativeRel L]
    [LocalFieldTheory.ValuativeExtension K L] (x : 𝒪[L]ˣ) :
    (((normIntegerUnits K L x : 𝒪[K]ˣ) : 𝒪[K]) : K) =
      Algebra.norm K (((x : 𝒪[L]ˣ) : 𝒪[L]) : L) :=
  rfl

end UnitNorm

section Valuation

variable [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
variable [Algebra K L]

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L] in
/-- For a finite Galois extension, embedding the unit norm back into the extension equals the
product of all Galois conjugates. -/
lemma mapBaseUnits_normUnits_eq_prod_gal [FiniteDimensional K L] [IsGalois K L]
    (x : Lˣ) :
    mapBaseUnitsToExtensionUnits K L (normUnits K L x) =
      ∏ σ : L ≃ₐ[K] L, Units.mapEquiv σ.toMulEquiv x := by
  ext
  simp [mapBaseUnitsToExtensionUnits, normUnits, Algebra.norm_eq_prod_automorphisms]

end Valuation

end IsNonarchimedeanLocalField

end
end LocalFieldTheory
