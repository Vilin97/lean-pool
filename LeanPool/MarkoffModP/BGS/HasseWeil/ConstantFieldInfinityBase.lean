/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.HasseWeil.ConstantFieldFinitePlace

/-!
# The rational-function place at infinity under coefficient extension

Coefficient extension `K(X) → E(X)` preserves the integer degree of every
rational function, hence preserves the valuation at infinity exactly.  It
therefore restricts to an injective local homomorphism between the two
infinity valuation rings.  The maximal ideal of the enlarged valuation ring
contracts to the original maximal ideal.

This is the base-place comparison.  It does not identify the integral
closures of these valuation rings inside a further function field.
-/

@[expose] public section

open scoped Polynomial

namespace BGS.HasseWeil

noncomputable section

open BGS.CorvajaZannier

variable (K E : Type*) [Field K] [Field E] [Algebra K E]

/-- Injective coefficient extension preserves rational-function integer
degree. -/
theorem ratFuncCoefficientAlgHom_intDegree (z : RatFunc K) :
    RatFunc.intDegree (ratFuncCoefficientAlgHom K E z) =
      RatFunc.intDegree z := by
  by_cases hz : z = 0
  · simp [hz]
  rw [← z.num_div_denom, map_div₀]
  have hnumK : algebraMap K[X] (RatFunc K) z.num ≠ 0 := by
    simpa using
      (IsFractionRing.injective K[X] (RatFunc K)).ne
        (RatFunc.num_ne_zero hz)
  have hdenK : algebraMap K[X] (RatFunc K) z.denom ≠ 0 := by
    simpa using
      (IsFractionRing.injective K[X] (RatFunc K)).ne z.denom_ne_zero
  have hnumE : ratFuncCoefficientAlgHom K E
      (algebraMap K[X] (RatFunc K) z.num) ≠ 0 := by
    simpa using (ratFuncCoefficientAlgHom_injective K E).ne hnumK
  have hdenE : ratFuncCoefficientAlgHom K E
      (algebraMap K[X] (RatFunc K) z.denom) ≠ 0 := by
    simpa using (ratFuncCoefficientAlgHom_injective K E).ne hdenK
  rw [RatFunc.intDegree_div hnumE hdenE,
    RatFunc.intDegree_div hnumK hdenK]
  rw [ratFuncCoefficientAlgHom_algebraMap,
    ratFuncCoefficientAlgHom_algebraMap]
  simp only [RatFunc.intDegree_polynomial]
  change ((Polynomial.map (algebraMap K E) z.num).natDegree : ℤ) -
      ((Polynomial.map (algebraMap K E) z.denom).natDegree : ℤ) = _
  rw [Polynomial.natDegree_map_eq_of_injective
      (algebraMap K E).injective z.num,
    Polynomial.natDegree_map_eq_of_injective
      (algebraMap K E).injective z.denom]

/-- Coefficient extension has the expected value on constants. -/
theorem ratFuncCoefficientAlgHom_C (c : K) :
    ratFuncCoefficientAlgHom K E (RatFunc.C c) =
      RatFunc.C (algebraMap K E c) := by
  change ratFuncCoefficientAlgHom K E
      (algebraMap K[X] (RatFunc K) (Polynomial.C c)) = _
  rw [ratFuncCoefficientAlgHom_algebraMap]
  simp

variable [DecidableEq (RatFunc K)] [DecidableEq (RatFunc E)]

/-- Coefficient extension preserves the valuation at infinity exactly. -/
theorem ratFuncCoefficientAlgHom_inftyValuation (z : RatFunc K) :
    RatFunc.inftyValuation E (ratFuncCoefficientAlgHom K E z) =
      RatFunc.inftyValuation K z := by
  by_cases hz : z = 0
  · simp [hz]
  have hmap : ratFuncCoefficientAlgHom K E z ≠ 0 := by
    simpa using (ratFuncCoefficientAlgHom_injective K E).ne hz
  rw [RatFunc.inftyValuation_apply, RatFunc.inftyValuation_apply,
    RatFunc.inftyValuation_of_nonzero E hmap,
    RatFunc.inftyValuation_of_nonzero K hz,
    ratFuncCoefficientAlgHom_intDegree K E z]

/-- Coefficient extension restricted to the infinity valuation rings. -/
def ratFuncInfinityIntegersRingHom :
    RatFuncInfinityIntegers K →+* RatFuncInfinityIntegers E where
  toFun z := ⟨ratFuncCoefficientAlgHom K E z.1, by
    change RatFunc.inftyValuation E (ratFuncCoefficientAlgHom K E z.1) ≤ 1
    rw [ratFuncCoefficientAlgHom_inftyValuation K E z.1]
    exact z.2⟩
  map_one' := Subtype.ext (map_one (ratFuncCoefficientAlgHom K E))
  map_mul' x y :=
    Subtype.ext (map_mul (ratFuncCoefficientAlgHom K E) x.1 y.1)
  map_zero' := Subtype.ext (map_zero (ratFuncCoefficientAlgHom K E))
  map_add' x y :=
    Subtype.ext (map_add (ratFuncCoefficientAlgHom K E) x.1 y.1)

@[simp]
theorem ratFuncInfinityIntegersRingHom_coe
    (z : RatFuncInfinityIntegers K) :
    ((ratFuncInfinityIntegersRingHom K E z :
        RatFuncInfinityIntegers E) : RatFunc E) =
      ratFuncCoefficientAlgHom K E z.1 := rfl

theorem ratFuncInfinityIntegersRingHom_injective :
    Function.Injective (ratFuncInfinityIntegersRingHom K E) := by
  intro x y hxy
  apply Subtype.ext
  exact (ratFuncCoefficientAlgHom_injective K E)
    (congrArg Subtype.val hxy)

/-- The map of infinity valuation rings is local because it reflects the
valuation-one unit condition. -/
noncomputable instance ratFuncInfinityIntegersRingHom_isLocalHom :
    IsLocalHom (ratFuncInfinityIntegersRingHom K E) where
  map_nonunit x hx := by
    apply (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (RatFunc.inftyValuation K))).mpr
    have hx' := (Valuation.Integers.isUnit_iff_valuation_eq_one
      (Valuation.integer.integers (RatFunc.inftyValuation E))).mp hx
    change RatFunc.inftyValuation E
      (ratFuncCoefficientAlgHom K E x.1) = 1 at hx'
    rw [ratFuncCoefficientAlgHom_inftyValuation K E x.1] at hx'
    exact hx'

/-- The maximal ideal at infinity over `E` contracts to the maximal ideal at
infinity over `K`. -/
theorem ratFuncInfinityIntegersRingHom_comap_maximalIdeal :
    (IsLocalRing.maximalIdeal (RatFuncInfinityIntegers E)).comap
        (ratFuncInfinityIntegersRingHom K E) =
      IsLocalRing.maximalIdeal (RatFuncInfinityIntegers K) :=
  IsLocalRing.maximalIdeal_comap (ratFuncInfinityIntegersRingHom K E)

/-- Height-one-place form of maximal-ideal contraction. -/
theorem ratFuncInfinityIntegersRingHom_comap_infinityPlace :
    (ratFuncInfinityPlace E).asIdeal.comap
        (ratFuncInfinityIntegersRingHom K E) =
      (ratFuncInfinityPlace K).asIdeal := by
  exact ratFuncInfinityIntegersRingHom_comap_maximalIdeal K E

/-- The induced map between the two infinity residue fields. -/
def ratFuncInfinityResidueFieldRingHom :
    (ratFuncInfinityPlace K).asIdeal.ResidueField →+*
      (ratFuncInfinityPlace E).asIdeal.ResidueField :=
  Ideal.ResidueField.map (ratFuncInfinityPlace K).asIdeal
    (ratFuncInfinityPlace E).asIdeal
    (ratFuncInfinityIntegersRingHom K E)
    (ratFuncInfinityIntegersRingHom_comap_infinityPlace K E).symm

theorem ratFuncInfinityResidueFieldRingHom_injective :
    Function.Injective (ratFuncInfinityResidueFieldRingHom K E) :=
  RingHom.injective _

end

end BGS.HasseWeil
