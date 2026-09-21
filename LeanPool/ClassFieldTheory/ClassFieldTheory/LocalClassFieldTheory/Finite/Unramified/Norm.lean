/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Unramified.ResidueNorm
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup
/-! Provides the public declarations in the `LocalClassFieldTheory.Finite.Unramified.Norm` Lean module. -/

noncomputable section

universe u

namespace LocalClassFieldTheory


open scoped ValuativeRel
open LocalFieldTheory
open LocalFieldTheory.IsNonarchimedeanLocalField

/-- For a finite unramified extension, actual integral-closure integer-unit
norm surjectivity: combine the quotient norm on `𝒪[L]ˣ/U_L¹` with the
actual `U_L¹ -> U_K¹` lifting. -/
theorem normIntegerUnits_surjective_unramified_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L] :
    Function.Surjective (normIntegerUnits K L) := by
  intro y
  obtain ⟨q, hq⟩ :=
    integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_surjective_of_unramifiedValuation
      K L (QuotientGroup.mk y : IntegerUnitsModPrincipalUnits K)
  obtain ⟨u, rfl⟩ := Quotient.exists_rep q
  have hclass :
      (QuotientGroup.mk (normIntegerUnits K L u) : IntegerUnitsModPrincipalUnits K) =
        QuotientGroup.mk y := by
    change integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure K L
        (integerUnitsModPrincipalUnitsMk L u) =
      integerUnitsModPrincipalUnitsMk K y at hq
    rw [integerUnitsModPrincipalUnitsNormOfGaloisOfIsIntegralClosure_mk] at hq
    exact hq
  have hresInv : normIntegerUnits K L u / y ∈ principalUnits K 1 :=
    (IntegerUnitsModPrincipalUnits_mk_eq_mk_iff K (normIntegerUnits K L u) y).1 hclass
  have hres : y / normIntegerUnits K L u ∈ principalUnits K 1 := by
    have hinv : (normIntegerUnits K L u / y)⁻¹ ∈ principalUnits K 1 :=
      (principalUnits K 1).inv_mem hresInv
    simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hinv
  let r : principalUnits K 1 := ⟨y / normIntegerUnits K L u, hres⟩
  obtain ⟨z, hz⟩ :=
    principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_surjective
      K L 1 (Nat.le_refl 1) r
  refine ⟨u * (z : 𝒪[L]ˣ), ?_⟩
  have hzUnits : normIntegerUnits K L (z : 𝒪[L]ˣ) = y / normIntegerUnits K L u := by
    have hzUnitsSub := congrArg (fun w : principalUnits K 1 => (w : 𝒪[K]ˣ)) hz
    simpa [principalUnitsNormOfUnramifiedValuationOfIsIntegralClosure_apply, r]
      using hzUnitsSub
  calc
    normIntegerUnits K L (u * (z : 𝒪[L]ˣ))
        = normIntegerUnits K L u * normIntegerUnits K L (z : 𝒪[L]ˣ) := by
          rw [(normIntegerUnits K L).map_mul]
    _ = normIntegerUnits K L u * (y / normIntegerUnits K L u) := by
          rw [hzUnits]
    _ = y := by
          simp [div_eq_mul_inv, mul_left_comm]

/-- For a finite unramified extension: the norm of an integer unit is again an integer unit,
so its normalized valuation is zero.

This is the unit part of the standard decomposition `x = u * π^m`; it uses the
actual integer-unit norm, not a norm-valuation certificate. -/
theorem v_normUnits_integerUnitsToFieldUnits
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra K L] [LocalFieldTheory.ValuativeExtension K L]
    (u : 𝒪[L]ˣ) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul (LocalFieldTheory.normUnits K L
        (integerUnitsToFieldUnits L u))) = 0 := by
  have hval :
      LocalFieldTheory.IsNonarchimedeanLocalField.v K
        (Additive.ofMul (integerUnitsToFieldUnits K (normIntegerUnits K L u))) = 0 :=
    LocalFieldTheory.IsNonarchimedeanLocalField.v_integerUnitsToFieldUnits K (normIntegerUnits K L u)
  simpa [LocalFieldTheory.normUnits,
    normIntegerUnits_to_fieldUnits K L u] using hval

/-- The norm of a base-field inverse uniformizer power has the expected
valuation.  This is the `N(π_K^m) = π_K^{m[L:K]}` part of the unramified norm calculation,
proved from the algebra norm of a base element. -/
theorem v_normUnits_mapBase_inverseIntegerRingUniformizerFieldUnit_zpow
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [Algebra K L] (m : Int) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul
        (LocalFieldTheory.normUnits K L
          ((mapBaseUnitsToExtensionUnits K L
            (inverseIntegerRingUniformizerFieldUnit K)) ^ m))) =
      (Module.finrank K L : Int) * m := by
  have hbase :
      LocalFieldTheory.normUnits K L
          ((mapBaseUnitsToExtensionUnits K L
            (inverseIntegerRingUniformizerFieldUnit K)) ^ m) =
        ((inverseIntegerRingUniformizerFieldUnit K) ^ m) ^
          Module.finrank K L := by
    rw [← (mapBaseUnitsToExtensionUnits K L).map_zpow]
    have hnorm := LocalFieldTheory.IsNonarchimedeanLocalField.normUnits_algebraMap_base
      (K := K) (L := L) ((inverseIntegerRingUniformizerFieldUnit K) ^ m)
    simpa [LocalFieldTheory.normUnits] using hnorm
  rw [hbase]
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_pow, LocalFieldTheory.IsNonarchimedeanLocalField.v_zpow,
    v_inverseIntegerRingUniformizerFieldUnit]
  rw [mul_one]

/-- For a finite unramified extension: after decomposing an element into an integer-unit
part and a power of the chosen inverse uniformizer, the valuation of its norm is
determined by the exponent. -/
theorem v_normUnits_integerUnit_mul_mapBase_inverseIntegerRingUniformizer_zpow
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [Algebra K L] [LocalFieldTheory.ValuativeExtension K L]
    (u : 𝒪[L]ˣ) (m : Int) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul
        (LocalFieldTheory.normUnits K L
          (integerUnitsToFieldUnits L u *
            (mapBaseUnitsToExtensionUnits K L
              (inverseIntegerRingUniformizerFieldUnit K)) ^ m))) =
      (Module.finrank K L : Int) * m := by
  rw [map_mul]
  rw [LocalFieldTheory.IsNonarchimedeanLocalField.v_mul]
  rw [v_normUnits_integerUnitsToFieldUnits,
    v_normUnits_mapBase_inverseIntegerRingUniformizerFieldUnit_zpow]
  rw [zero_add]

/-- For a finite unramified extension, norm-valuation calculation in the actual unramified
valuation case.

The proof uses the standard decomposition: choose the base inverse uniformizer, use
unramifiedness to know that it is also an upstairs normalized generator,
decompose `x = u * π^{v_L(x)}`, then combine the integer-unit norm with
`N(π^m) = π_K^{m[L:K]}`.  No common-uniformizer value, norm-valuation formula,
or residue-degree equality is assumed as an extra input. -/
theorem v_normUnits_unramifiedValuation
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [LocalFieldTheory.ValuativeExtension K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : Lˣ) :
    LocalFieldTheory.IsNonarchimedeanLocalField.v K
      (Additive.ofMul (LocalFieldTheory.normUnits K L x)) =
      (Module.finrank K L : Int) *
        LocalFieldTheory.IsNonarchimedeanLocalField.v L (Additive.ofMul x) := by
  let ϖL : Lˣ :=
    mapBaseUnitsToExtensionUnits K L (inverseIntegerRingUniformizerFieldUnit K)
  have hGenerator : valuationMap L (Additive.ofMul ϖL) = 1 := by
    simpa [valuationMap_apply, ϖL] using
      v_mapBaseUnitsToExtensionUnits_inverseIntegerRingUniformizerFieldUnit_of_unramifiedValuation
        K L
  rcases exists_integerUnit_mul_uniformizer_zpow L ϖL hGenerator x with ⟨u, hdecomp⟩
  have hnorm :
      LocalFieldTheory.IsNonarchimedeanLocalField.v K
        (Additive.ofMul (LocalFieldTheory.normUnits K L x)) =
        LocalFieldTheory.IsNonarchimedeanLocalField.v K
          (Additive.ofMul
            (LocalFieldTheory.normUnits K L
              (integerUnitsToFieldUnits L u *
                ϖL ^ valuationMap L (Additive.ofMul x)))) := by
    exact congrArg
      (fun y : Lˣ =>
        LocalFieldTheory.IsNonarchimedeanLocalField.v K
          (Additive.ofMul (LocalFieldTheory.normUnits K L y)))
      hdecomp.symm
  rw [hnorm]
  simpa [ϖL, valuationMap_apply] using
    v_normUnits_integerUnit_mul_mapBase_inverseIntegerRingUniformizer_zpow
      K L u (valuationMap L (Additive.ofMul x))

/-- For a finite unramified extension, reverse containment source: every field norm has
valuation divisible by `[L : K]` in the actual unramified valuation case. -/
theorem finrank_dvd_valuation_of_mem_normSubgroup_unramified
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [LocalFieldTheory.ValuativeExtension K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    {x : Kˣ} (hx : x ∈ localNormSubgroup K L) :
    (Module.finrank K L : Int) ∣ valuationMap K (Additive.ofMul x) := by
  rcases MonoidHom.mem_range.mp hx with ⟨y, hy⟩
  refine ⟨IsNonarchimedeanLocalField.v L (Additive.ofMul y), ?_⟩
  rw [← hy, valuationMap_apply]
  exact v_normUnits_unramifiedValuation K L y

/-- For a finite unramified extension, constructive reverse containment for the unramified norm
calculation, actual integral-closure source-producing half: if the valuation
of a base-field unit is divisible by `[L : K]`, then it is already a field norm.

This is the standard argument `a = u * π_K^(m[L:K])`, with
`u = N(ε)` by the actual integer-unit norm theorem and
`π_K^(m[L:K]) = N(π_K^m)`.  It uses the integral-closure version of the
integer-unit lifting, with no auxiliary invariant package. -/
theorem mem_normSubgroup_of_finrank_dvd_valuation_unramified_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    {x : Kˣ}
    (hdiv : (Module.finrank K L : Int) ∣ valuationMap K (Additive.ofMul x)) :
    x ∈ localNormSubgroup K L := by
  rcases valuationMap_uniformiser K with ⟨ϖ, hϖ⟩
  rcases exists_integerUnit_mul_uniformizer_zpow K ϖ hϖ x with ⟨u, hdecomp⟩
  rcases hdiv with ⟨m, hm⟩
  obtain ⟨uL, huL⟩ :=
    normIntegerUnits_surjective_unramified_of_isIntegralClosure K L u
  refine MonoidHom.mem_range.mpr ?_
  refine ⟨integerUnitsToFieldUnits L uL * mapBaseUnitsToExtensionUnits K L (ϖ ^ m), ?_⟩
  have hunitNorm :
      LocalFieldTheory.normUnits K L (integerUnitsToFieldUnits L uL) =
        integerUnitsToFieldUnits K u := by
    have hfield :
        LocalFieldTheory.normUnits K L (integerUnitsToFieldUnits L uL) =
          integerUnitsToFieldUnits K u := by
      rw [← normIntegerUnits_to_fieldUnits K L uL, huL]
    simpa [LocalFieldTheory.normUnits] using hfield
  have hbaseNorm :
      LocalFieldTheory.normUnits K L
          (mapBaseUnitsToExtensionUnits K L (ϖ ^ m)) =
        ϖ ^ valuationMap K (Additive.ofMul x) := by
    have hbase0 :
        LocalFieldTheory.normUnits K L
            (mapBaseUnitsToExtensionUnits K L (ϖ ^ m)) =
          (ϖ ^ m) ^ Module.finrank K L := by
      have hnorm := LocalFieldTheory.IsNonarchimedeanLocalField.normUnits_algebraMap_base
        (K := K) (L := L) (ϖ ^ m)
      simpa [LocalFieldTheory.normUnits] using hnorm
    calc
      LocalFieldTheory.normUnits K L
          (mapBaseUnitsToExtensionUnits K L (ϖ ^ m))
          = (ϖ ^ m) ^ Module.finrank K L := hbase0
      _ = (ϖ ^ m) ^ (Module.finrank K L : Int) := by rw [zpow_natCast]
      _ = ϖ ^ (m * (Module.finrank K L : Int)) := by rw [← zpow_mul]
      _ = ϖ ^ valuationMap K (Additive.ofMul x) := by
            rw [hm]
            rw [mul_comm m (Module.finrank K L : Int)]
  calc
    LocalFieldTheory.normUnits K L
        (integerUnitsToFieldUnits L uL * mapBaseUnitsToExtensionUnits K L (ϖ ^ m))
        = LocalFieldTheory.normUnits K L (integerUnitsToFieldUnits L uL) *
            LocalFieldTheory.normUnits K L
              (mapBaseUnitsToExtensionUnits K L (ϖ ^ m)) := by
          rw [map_mul]
    _ = integerUnitsToFieldUnits K u * ϖ ^ valuationMap K (Additive.ofMul x) := by
          rw [hunitNorm, hbaseNorm]
    _ = x := hdecomp

/-- For a finite unramified extension, actual unramified norm image membership:
the norm subgroup consists exactly of elements whose normalized valuation is
divisible by `[L : K]`.

This combines the actual norm-valuation calculation with the actual
integral-closure unit lifting. -/
theorem mem_normSubgroup_unramifiedValuation_iff_finrank_dvd_valuation_of_isIntegralClosure
    (K L : Type u)
    [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [UniformSpace L] [IsUniformAddGroup L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]
    [LocalFieldTheory.ValuativeExtension K L] [IsIntegralClosure 𝒪[L] 𝒪[K] L]
    [Module.Finite 𝒪[K] 𝒪[L]]
    [LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L]
    (x : Kˣ) :
    x ∈ localNormSubgroup K L ↔
      (Module.finrank K L : Int) ∣ valuationMap K (Additive.ofMul x) := by
  constructor
  · exact finrank_dvd_valuation_of_mem_normSubgroup_unramified K L
  · exact mem_normSubgroup_of_finrank_dvd_valuation_unramified_of_isIntegralClosure K L

end LocalClassFieldTheory
