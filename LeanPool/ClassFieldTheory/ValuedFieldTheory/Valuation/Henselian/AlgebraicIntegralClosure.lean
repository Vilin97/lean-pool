/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.SimpleRootFactorization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.MonicFactorization
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.DiscreteValuationField.ChevalleyExtension
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
/-!
# Integral closures of Henselian valuation rings

In an algebraic extension, every element or its inverse is integral over a
Henselian valuation ring. The argument extends the valuation to an algebraic
closure, uses equality of the values of conjugate roots, and bounds the
coefficients of the minimal polynomial by the nonarchimedean Vieta bound.
No restriction on the rank or value group is imposed.
-/

namespace ValuationTheory.Henselian

private theorem minpoly_coeff_mem_of_mem_extension
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (V : ValuationSubring K) [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (B : ValuationSubring Ω) [V.valuation.HasExtension B.valuation]
    (α : Ω) (hαB : α ∈ B) :
    ∀ i : ℕ, (minpoly K α).coeff i ∈ V := by
  have hα : IsIntegral K α :=
    (Algebra.IsAlgebraic.isAlgebraic (R := K) α).isIntegral
  have hmonic : ((minpoly K α).map (algebraMap K Ω)).Monic :=
    (minpoly.monic hα).map (algebraMap K Ω)
  have hsplit : ((minpoly K α).map (algebraMap K Ω)).Splits :=
    (IsAlgClosure.isAlgClosed K).splits ((minpoly K α).map (algebraMap K Ω))
  have hαroot : α ∈ ((minpoly K α).map (algebraMap K Ω)).roots := by
    apply (Polynomial.mem_roots hmonic.ne_zero).2
    rw [Polynomial.IsRoot, Polynomial.eval_map_algebraMap]
    exact minpoly.aeval K α
  have hlift : DiscreteValuationField.MonicResidualCoprimeFactorLifting V :=
    DiscreteValuationField.monicResidualCoprimeFactorLifting_of_henselianRing V
  have hroots : ∀ β ∈ ((minpoly K α).map (algebraMap K Ω)).roots,
      B.valuation β ≤ 1 := by
    intro β hβ
    rw [hlift.irreducible_roots_same_valuation B
      (minpoly.irreducible hα) hsplit hβ hαroot]
    exact (B.valuation_le_one_iff α).2 hαB
  intro i
  apply V.mem_of_valuation_le_one
  apply (Valuation.HasExtension.val_map_le_one_iff V.valuation B.valuation
    ((minpoly K α).coeff i)).1
  have hbound := DiscreteValuationField.valuation_coeff_prod_X_sub_C_le_pow_card
    B.valuation 1 le_rfl ((minpoly K α).map (algebraMap K Ω)).roots hroots i
  rw [← hsplit.eq_prod_roots_of_monic hmonic, Polynomial.coeff_map, one_pow] at hbound
  exact hbound

private theorem isIntegral_of_mem_extension
    {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (V : ValuationSubring K) [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (B : ValuationSubring Ω) [V.valuation.HasExtension B.valuation]
    (α : Ω) (hαB : α ∈ B) : IsIntegral V α := by
  have hα : IsIntegral K α :=
    (Algebra.IsAlgebraic.isAlgebraic (R := K) α).isIntegral
  have hcoeff : ∀ i : ℕ, (minpoly K α).coeff i ∈ V :=
    minpoly_coeff_mem_of_mem_extension V B α hαB
  have hlifts : minpoly K α ∈ Polynomial.lifts (algebraMap V K) := by
    apply (Polynomial.lifts_iff_coeff_lifts (minpoly K α)).2
    intro i
    exact ⟨⟨(minpoly K α).coeff i, hcoeff i⟩, rfl⟩
  obtain ⟨f, hf⟩ := (Polynomial.mem_lifts (minpoly K α)).1 hlifts
  have hfmonic : f.Monic := by
    apply Polynomial.monic_of_injective (show Function.Injective (algebraMap V K) from
      fun x y hxy => Subtype.ext hxy)
    rw [hf]
    exact minpoly.monic hα
  have hfroot : Polynomial.aeval α f = 0 := by
    rw [← Polynomial.aeval_map_algebraMap K α f, hf]
    exact minpoly.aeval K α
  exact ⟨f, hfmonic, hfroot⟩

/-- For every algebraic extension of a Henselian valued field, an element
or its inverse lies in the actual integral closure of the valuation ring. -/
theorem integralClosure_mem_or_inv_of_henselianRing
    {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L]
    (V : ValuationSubring K) [HenselianRing V (IsLocalRing.maximalIdeal V)]
    (z : L) :
    z ∈ (integralClosure V L).toSubring ∨
      z⁻¹ ∈ (integralClosure V L).toSubring := by
  let ι : L →ₐ[K] AlgebraicClosure K := IsAlgClosed.lift
  obtain ⟨B, _hB, _hlocal, _hpullback, hext⟩ :=
    DiscreteValuationField.Valuation.exists_extension_valuationSubring_with_hasExtension
      (L := AlgebraicClosure K) V.valuation
  let : V.valuation.HasExtension B.valuation := hext
  rcases B.mem_or_inv_mem (ι z) with hz | hzinv
  · left
    change IsIntegral V z
    exact (isIntegral_algHom_iff (ι.restrictScalars V) ι.injective).1
      (isIntegral_of_mem_extension V B (ι z) hz)
  · right
    change IsIntegral V z⁻¹
    apply (isIntegral_algHom_iff (ι.restrictScalars V) ι.injective).1
    apply isIntegral_of_mem_extension V B (ι z⁻¹)
    rw [map_inv₀]
    exact hzinv

end ValuationTheory.Henselian
