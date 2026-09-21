/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import LeanPool.ClassFieldTheory.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.UnramifiedNormComparison
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF
import LeanPool.ClassFieldTheory.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ValuationExactSequence
/-!
# Uniqueness from an unramified norm kernel and a uniformizer value

For a fixed finite unramified abelian extension, the norm subgroup contains
every integer unit. The decomposition of a field unit into an integer unit
and a power of an inverse uniformizer therefore determines a homomorphism
with this kernel from its value on that inverse uniformizer.

This is the unramified generator step, not uniqueness of finite local Artin
maps for ramified extensions.
-/

open scoped ValuativeRel
open LocalFieldTheory.IsNonarchimedeanLocalField

noncomputable section

namespace ClassFieldTheory

/-- For an unramified extension, two norm-kernel homomorphisms that agree on
one inverse uniformizer agree on all field units. -/
theorem finiteAbelianLocalReciprocity_unramified_hom_ext
    (K L : Type)
    [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    [Field L] [ValuativeRel L] [TopologicalSpace L]
    [IsNonarchimedeanLocalField L]
    [Algebra K L] [FiniteDimensional K L] [IsAbelianGalois K L]
    [Valuation.HasExtension (ValuativeRel.valuation K)
      (ValuativeRel.valuation L)]
    (hUnram : (𝓂[L] : Ideal 𝒪[L]).ramificationIdx 𝒪[K] = 1)
    (π : 𝒪[K])
    (hπ : (ValuativeRel.valuation K).IsUniformizer (π : K))
    (f g : Kˣ →ₜ* (L ≃ₐ[K] L))
    (hfker : f.toMonoidHom.ker = fieldNormSubgroup K L)
    (hgker : g.toMonoidHom.ker = fieldNormSubgroup K L)
    (hϖ : f ((Units.mk0 (π : K) hπ.ne_zero)⁻¹) =
      g ((Units.mk0 (π : K) hπ.ne_zero)⁻¹)) :
    f = g := by
  let : IsIntegralClosure 𝒪[L] 𝒪[K] L :=
    LocalFieldTheory.localCompleteDVF_integerRing_isIntegralClosure K L
  let : Module.Finite 𝒪[K] 𝒪[L] :=
    LocalFieldTheory.localCompleteDVF_integerRing_moduleFinite K L
  let : LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension
      K L := ⟨hUnram⟩
  let ϖ : Kˣ := (Units.mk0 (π : K) hπ.ne_zero)⁻¹
  have hϖval : valuationMap K (Additive.ofMul ϖ) = 1 := by
    have hπval := valuationMap_uniformizerFieldUnit K π hπ
    calc
      valuationMap K (Additive.ofMul ϖ) =
          -valuationMap K
            (Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero)) := by
        change valuationMap K
          (-(Additive.ofMul (Units.mk0 (π : K) hπ.ne_zero))) = _
        exact valuationMap_neg K _
      _ = 1 := by
        change -(valuationMap K
          (Additive.ofMul (uniformizerFieldUnit K π hπ))) = 1
        rw [hπval]
        norm_num
  have hNorm (u : 𝒪[K]ˣ) :
      integerUnitsToFieldUnits K u ∈ fieldNormSubgroup K L := by
    change integerUnitsToFieldUnits K u ∈
      LocalFieldTheory.localNormSubgroup K L
    rw [LocalClassFieldTheory.normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure
      K L]
    apply (LocalClassFieldTheory.mem_unramifiedNormSubgroup_iff K
      (Module.finrank K L) (integerUnitsToFieldUnits K u)).2
    rw [valuationMap_apply, v_integerUnitsToFieldUnits]
    exact dvd_zero _
  apply ContinuousMonoidHom.ext
  intro x
  obtain ⟨u, hu⟩ := exists_integerUnit_mul_uniformizer_zpow K ϖ hϖval x
  have hfu : f (integerUnitsToFieldUnits K u) = 1 := by
    have hmem : integerUnitsToFieldUnits K u ∈ f.toMonoidHom.ker := by
      rw [hfker]
      exact hNorm u
    exact hmem
  have hgu : g (integerUnitsToFieldUnits K u) = 1 := by
    have hmem : integerUnitsToFieldUnits K u ∈ g.toMonoidHom.ker := by
      rw [hgker]
      exact hNorm u
    exact hmem
  calc
    f x = f (integerUnitsToFieldUnits K u *
        ϖ ^ valuationMap K (Additive.ofMul x)) := congrArg f hu.symm
    _ = f (integerUnitsToFieldUnits K u) *
        (f ϖ) ^ valuationMap K (Additive.ofMul x) := by
      rw [map_mul, map_zpow]
    _ = g (integerUnitsToFieldUnits K u) *
        (g ϖ) ^ valuationMap K (Additive.ofMul x) := by
      rw [hfu, hgu, hϖ]
    _ = g (integerUnitsToFieldUnits K u *
        ϖ ^ valuationMap K (Additive.ofMul x)) := by
      rw [map_mul, map_zpow]
    _ = g x := congrArg g hu

end ClassFieldTheory
