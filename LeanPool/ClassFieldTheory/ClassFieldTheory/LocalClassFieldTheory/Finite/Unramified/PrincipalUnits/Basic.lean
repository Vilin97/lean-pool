/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import Mathlib.FieldTheory.Galois.Basic
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteUnramified
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.NormSide
/-! Provides the public declarations in the
  `LocalClassFieldTheory.Finite.Unramified.PrincipalUnits.Basic` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory

open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField
open Filter

/-- In an actual unramified valuation extension, the actual integer-unit norm
sends `U_L^n` into `U_K^n`. -/
theorem normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : 𝒪[L]ˣ) (hu : u ∈ principalUnits L n) :
    normIntegerUnits K L u ∈ principalUnits K n := by
  apply principalUnits_of_integerUnitsMap_mem_principalUnits_of_unramifiedValuation K L n
  exact integerUnitsMap_normIntegerUnits_mem_principalUnits_of_isIntegralClosure K L n u hu

/-- Actual integral-closure version of the integer-unit norm restricted to
principal units in an actual unramified valuation extension. -/
noncomputable def principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat) :
    principalUnits L n →* principalUnits K n where
  toFun u :=
    ⟨normIntegerUnits K L u.1,
      normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
        K L n u.1 u.2⟩
  map_one' := by
    ext
    simp
  map_mul' := by
    intro u v
    ext
    simp

/-- States the theorem `principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply`. -/
@[simp]
theorem principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat)
    (u : principalUnits L n) :
    ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u :
        principalUnits K n) : 𝒪[K]ˣ) =
      normIntegerUnits K L u.1 :=
  rfl

/-- Base-extending the integral-closure unramified
principal-unit norm recovers the extension-side norm expressed through the
integral-closure Galois product. -/
theorem principalUnitsMap_normOfUnramifiedValuationOfIsIntegralClosure_eq_normExtensionSide
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (u : principalUnits L n) :
    principalUnitsMapOfUnramifiedValuation K L n
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u) =
      principalUnitsNormExtensionSideOfIsIntegralClosure K L n u := by
  ext
  rfl

namespace UnramifiedPrincipalUnits

/-- The integral-closure norm-product calculation before residue trace
identification. -/
theorem norm_oneAdd_sub_galoisSum_mem_next
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    (((principalUnitsMapOfUnramifiedValuation K L n
          (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)) :
        principalUnits L n) : 𝒪[L]ˣ) : 𝒪[L]) - 1 -
      (Finset.univ.sum fun σ : Gal(L/K) =>
        galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L])) ∈
        (𝓂[L] ^ (n + 1) : Ideal 𝒪[L]) := by
  rw [principalUnitsMap_normOfUnramifiedValuationOfIsIntegralClosure_eq_normExtensionSide
    K L n (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)]
  exact
      principalUnitsNormExtensionSideOfIsIntegralClosure_oneAdd_sub_one_sub_sum_mem_maximalIdeal_pow_succ
      K L n hn a

end UnramifiedPrincipalUnits

/-- The integral-closure norm on successive principal-unit
quotients.  This is the quotient map used in the unramified norm calculation before
identifying the associated graded map with residue trace. -/
noncomputable def principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat) :
    PrincipalUnitsSuccQuot L n →* PrincipalUnitsSuccQuot K n :=
  principalUnitsSuccQuotLift n
    ((principalUnitsSuccQuotMk K n).comp
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n))
    (by
      intro u hu
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
        principalUnitsSuccQuotMk_eq_one_iff]
      change ((principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u :
          principalUnits K n) : 𝒪[K]ˣ) ∈ principalUnits K (n + 1)
      simpa [principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply]
        using
          normIntegerUnits_mem_principalUnits_of_unramifiedValuation_of_isIntegralClosure
            K L (n + 1) u.1 hu)

/-- States the theorem `principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk`. -/
@[simp]
theorem principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] (n : Nat)
    (u : principalUnits L n) :
    principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
        (principalUnitsSuccQuotMk L n u) =
      principalUnitsSuccQuotMk K n
        (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n u) :=
  rfl

/-- The integral-closure associated-graded norm-product
calculation in the unramified norm calculation. -/
theorem principalUnitsSuccQuotMap_normOfUnramifiedValuationOfIsIntegralClosure_oneAdd_base_eq_sum
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (n : Nat) (hn : 1 ≤ n) (a : (𝓂[L] ^ n : Ideal 𝒪[L])) :
    let b : (𝓂[L] ^ n : Ideal 𝒪[L]) :=
      ⟨Finset.univ.sum fun σ : Gal(L/K) =>
          galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ (a : 𝒪[L]),
        by
          classical
          exact Ideal.sum_mem _ fun σ _ =>
            (integerRingEquiv_mem_maximalIdeal_pow L
              (galoisGroupIntegerRingEquivOfIsIntegralClosure K L σ) n
              (a : 𝒪[L])).2 a.2⟩
    principalUnitsSuccQuotMapOfUnramifiedValuation K L n
        (principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure K L n
          (principalUnitsSuccQuotMk L n
            (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2))) =
      principalUnitsSuccQuotOfIdealPow L n hn b := by
  classical
  intro b
  rw [principalUnitsSuccQuotNormOfUnramifiedValuationOfIsIntegralClosure_mk,
    principalUnitsSuccQuotMapOfUnramifiedValuation_mk]
  exact principalUnitsSuccQuotMk_eq_oneAdd_of_sub_one_sub_mem_succ L n hn
    (principalUnitsMapOfUnramifiedValuation K L n
      (principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure K L n
        (principalUnitOneAddOfMemPowSubgroup L hn (a : 𝒪[L]) a.2)))
    b
    (by
      simpa [b] using
    UnramifiedPrincipalUnits.norm_oneAdd_sub_galoisSum_mem_next
          K L n hn a)


end LocalClassFieldTheory
