/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Minpoly.IsIntegrallyClosed
public import Mathlib.NumberTheory.NumberField.Ideal.KummerDedekind
public import Mathlib.LinearAlgebra.FreeModule.Finite.Quotient
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.GroupTheory.Index
/-!
# Integral primitive elements and their finite index

Every number field has an integral primitive element. Its order has full
integer rank, so its additive index is nonzero and lies in its conductor.
Consequently the exponent used in Kummer--Dedekind is nonzero.
-/

@[expose] public section

open scoped NumberField
open NumberField Module Polynomial

namespace AlgebraicNumberTheory.PrimeSelection

/-- A number field has a primitive element in its actual ring of integers. -/
theorem exists_integral_primitive_element
    (K : Type*) [Field K] [NumberField K] :
    ∃ θ : 𝓞 K, IntermediateField.adjoin ℚ ({(θ : K)} : Set K) = ⊤ := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element ℚ K
  have : Algebra.IsAlgebraic ℤ K :=
    IsFractionRing.comap_isAlgebraic_iff.mpr
      (inferInstance : Algebra.IsAlgebraic ℚ K)
  obtain ⟨m, hm, hmα⟩ :=
    (Algebra.IsAlgebraic.isAlgebraic α : IsAlgebraic ℤ α).exists_integral_multiple
  let θ : 𝓞 K := ⟨m • α, hmα⟩
  refine ⟨θ, top_le_iff.mp ?_⟩
  rw [← hα, IntermediateField.adjoin_simple_le_iff]
  have hθ : (θ : K) ∈ IntermediateField.adjoin ℚ ({(θ : K)} : Set K) :=
    IntermediateField.mem_adjoin_simple_self ℚ (θ : K)
  have hmQ : (m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm
  have hmul :=
    (IntermediateField.adjoin ℚ ({(θ : K)} : Set K)).smul_mem hθ
      (x := (m : ℚ)⁻¹)
  convert hmul using 1
  change α = (m : ℚ)⁻¹ • (m • α)
  rw [← Int.cast_smul_eq_zsmul ℚ, smul_smul, inv_mul_cancel₀ hmQ, one_smul]

/-- The order of an integral primitive element has full integer rank. -/
theorem integralPrimitiveOrder_finrank
    (K : Type*) [Field K] [NumberField K]
    (θ : 𝓞 K)
    (hθ : IntermediateField.adjoin ℚ ({(θ : K)} : Set K) = ⊤) :
    Module.finrank ℤ (Algebra.adjoin ℤ ({θ} : Set (𝓞 K))) =
      Module.finrank ℤ (𝓞 K) := by
  have hpoly : minpoly ℚ (θ : K) = (minpoly ℤ θ).map (algebraMap ℤ ℚ) :=
    minpoly.isIntegrallyClosed_eq_field_fractions ℚ K θ.isIntegral
  calc
    Module.finrank ℤ (Algebra.adjoin ℤ ({θ} : Set (𝓞 K))) =
        (minpoly ℤ θ).natDegree := (Algebra.adjoin.powerBasis' θ.isIntegral).finrank
    _ = (minpoly ℚ (θ : K)).natDegree := by
      rw [hpoly, (minpoly.monic θ.isIntegral).natDegree_map]
    _ = Module.finrank ℚ (IntermediateField.adjoin ℚ ({(θ : K)} : Set K)) :=
      (IntermediateField.adjoin.finrank
        (Algebra.IsSeparable.isIntegral ℚ (θ : K))).symm
    _ = Module.finrank ℚ K := by
      rw [hθ]
      exact IntermediateField.topEquiv.toLinearEquiv.finrank_eq
    _ = Module.finrank ℤ (𝓞 K) := (NumberField.RingOfIntegers.rank K).symm

/-- The Kummer--Dedekind exponent of an integral primitive element is nonzero. -/
theorem integralPrimitive_exponent_ne_zero
    (K : Type*) [Field K] [NumberField K]
    (θ : 𝓞 K)
    (hθ : IntermediateField.adjoin ℚ ({(θ : K)} : Set K) = ⊤) :
    RingOfIntegers.exponent θ ≠ 0 := by
  let N : Submodule ℤ (𝓞 K) := (Algebra.adjoin ℤ ({θ} : Set (𝓞 K))).toSubmodule
  have hRank : Module.finrank ℤ N = Module.finrank ℤ (𝓞 K) :=
    integralPrimitiveOrder_finrank K θ hθ
  have : Finite ((𝓞 K) ⧸ N) := Submodule.finiteQuotientOfFreeOfRankEq N hRank
  have : Finite ((𝓞 K) ⧸ N.toAddSubgroup) := by
    change Finite ((𝓞 K) ⧸ N)
    infer_instance
  have hIndex : N.toAddSubgroup.index ≠ 0 :=
    N.toAddSubgroup.index_ne_zero_of_finite
  have hmem : (N.toAddSubgroup.index : 𝓞 K) ∈ conductor ℤ θ := by
    rw [mem_conductor_iff]
    intro x
    simpa only [N, Submodule.mem_toAddSubgroup, Subalgebra.mem_toSubmodule,
      nsmul_eq_mul] using N.toAddSubgroup.nsmul_index_mem x
  change Ideal.absNorm (Ideal.under ℤ (conductor ℤ θ)) ≠ 0
  apply Ideal.absNorm_eq_zero_iff.not.mpr
  intro hbot
  have hm : (N.toAddSubgroup.index : ℤ) ∈
      Ideal.under ℤ (conductor ℤ θ) := by
    change algebraMap ℤ (𝓞 K) (N.toAddSubgroup.index : ℤ) ∈ conductor ℤ θ
    simpa only [map_natCast] using hmem
  rw [hbot, Ideal.mem_bot] at hm
  exact hIndex (Int.natCast_eq_zero.mp hm)

end AlgebraicNumberTheory.PrimeSelection
