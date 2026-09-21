/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindPlaceOrder
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PerfectConstants
import Mathlib.Tactic

/-!
# Leading-term cancellation at a Dedekind DVR place

At a discrete valuation place, two nonzero functions of the same order have
unit leading coefficients.  If the derivation-constant field surjects onto
the residue field, one can subtract a constant multiple of one function from
the other and cancel that leading coefficient.  The result either vanishes
or has strictly larger order.

This is the global-Dedekind analogue of the Laurent-series cancellation used
in Corvaja--Zannier case (i).  The surjectivity hypothesis is stated directly
on the residue field, so the theorem can be applied independently of how the
constant field is presented.
-/

open scoped nonZeroDivisors
open IsDedekindDomain Multiplicative WithZero

namespace BGS.CorvajaZannier

noncomputable section

variable {C R L : Type*} [Field C] [CommRing R] [IsDedekindDomain R]
  [IsDiscreteValuationRing R] [Field L] [Algebra C R] [Algebra R L]
  [Algebra C L] [IsScalarTower C R L] [IsFractionRing R L]

/-- A nonzero regular element lying in the place has positive order. -/
theorem one_le_finitePlaceOrder_algebraMap_of_mem
    (v : HeightOneSpectrum R) (a : R) (ha : a ∈ v.asIdeal) (ha0 : a ≠ 0) :
    (1 : ℤ) ≤ finitePlaceOrder v (algebraMap R L a) := by
  have hmap : algebraMap R L a ≠ 0 := by
    intro hzero
    apply ha0
    exact IsFractionRing.injective R L (by simpa using hzero)
  have hvaluation :=
    valuation_eq_exp_neg_finitePlaceOrder v (algebraMap R L a) hmap
  rw [HeightOneSpectrum.valuation_of_algebraMap] at hvaluation
  have hlt : exp (-finitePlaceOrder v (algebraMap R L a)) < 1 := by
    rw [← hvaluation]
    exact (v.intValuation_lt_one_iff_mem a).2 ha
  rw [← exp_zero, exp_lt_exp] at hlt
  omega

omit [IsDedekindDomain R] [IsDiscreteValuationRing R] in
/-- Residue-field surjectivity lets constants cancel the ratio of two unit
leading coefficients. -/
theorem exists_constant_unit_sub_mul_mem
    (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField))
    (u w : Rˣ) :
    ∃ c : C, (u : R) - algebraMap C R c * (w : R) ∈ v.asIdeal := by
  let κ := v.asIdeal.ResidueField
  obtain ⟨c, hc⟩ := hresidue
    (algebraMap R κ (((u * w⁻¹ : Rˣ) : R)))
  refine ⟨c, ?_⟩
  rw [← Ideal.algebraMap_residueField_eq_zero]
  calc
    algebraMap R κ ((u : R) - algebraMap C R c * (w : R)) =
        algebraMap R κ (u : R) -
          algebraMap C κ c * algebraMap R κ (w : R) := by
      rw [map_sub, map_mul, ← IsScalarTower.algebraMap_apply C R κ]
    _ = algebraMap R κ (u : R) -
          algebraMap R κ (((u * w⁻¹ : Rˣ) : R)) *
            algebraMap R κ (w : R) := by rw [hc]
    _ = 0 := by
      rw [← map_mul]
      simp

/-- If constants surject onto the residue field at `v`, equal-order nonzero
functions have a constant leading-term cancellation.  The cancelled function
is either zero or has strictly larger finite-place order.

No uniformizer is part of the interface: one is chosen internally from the
DVR structure, and uniqueness of the maximal ideal identifies it with `v`. -/
theorem exists_constant_finitePlaceOrder_sub_mul_eq_zero_or_lt
    (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap C v.asIdeal.ResidueField))
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0)
    (horder : finitePlaceOrder v x = finitePlaceOrder v y) :
    ∃ c : C,
      x - algebraMap C L c * y = 0 ∨
        finitePlaceOrder v x <
          finitePlaceOrder v (x - algebraMap C L c * y) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal : v.asIdeal = Ideal.span {π} := by
    calc
      v.asIdeal = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal v.isMaximal
      _ = Ideal.span {π} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  obtain ⟨nx, ux, hxrepr⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := L) hπ hx
  obtain ⟨ny, uy, hyrepr⟩ :=
    IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (K := L) hπ hy
  have hxrepr' :
      x = algebraMap R L (ux : R) * (algebraMap R L π) ^ nx := by
    simpa [Units.smul_def, Algebra.smul_def] using hxrepr
  have hyrepr' :
      y = algebraMap R L (uy : R) * (algebraMap R L π) ^ ny := by
    simpa [Units.smul_def, Algebra.smul_def] using hyrepr
  have hxOrder : finitePlaceOrder v x = nx := by
    rw [hxrepr']
    exact finitePlaceOrder_unit_mul_uniformizer_zpow
      v π hπ hπIdeal ux nx
  have hyOrder : finitePlaceOrder v y = ny := by
    rw [hyrepr']
    exact finitePlaceOrder_unit_mul_uniformizer_zpow
      v π hπ hπIdeal uy ny
  have hnxny : nx = ny := by omega
  rw [← hnxny] at hyrepr'
  obtain ⟨c, hc⟩ := exists_constant_unit_sub_mul_mem v hresidue ux uy
  let a : R := (ux : R) - algebraMap C R c * (uy : R)
  have haMem : a ∈ v.asIdeal := by simpa [a] using hc
  have hfactor :
      x - algebraMap C L c * y =
        algebraMap R L a * (algebraMap R L π) ^ nx := by
    rw [hxrepr', hyrepr']
    simp only [a, map_sub, map_mul]
    rw [IsScalarTower.algebraMap_apply C R L]
    ring
  by_cases ha : a = 0
  · refine ⟨c, Or.inl ?_⟩
    rw [hfactor, ha, map_zero, zero_mul]
  · refine ⟨c, Or.inr ?_⟩
    have haMap : algebraMap R L a ≠ 0 := by
      intro hzero
      apply ha
      exact IsFractionRing.injective R L (by simpa using hzero)
    have hπMap : algebraMap R L π ≠ 0 := by
      simpa using hπ.ne_zero
    have hprod := finitePrincipalDivisor_mul (R := R)
      (algebraMap R L a) ((algebraMap R L π) ^ nx)
      haMap (zpow_ne_zero nx hπMap)
    have hprodOrder := congrArg (fun D ↦ D v) hprod
    simp only [finitePrincipalDivisor_apply, Finsupp.add_apply] at hprodOrder
    rw [finitePlaceOrder_uniformizer_zpow v π hπ hπIdeal nx] at hprodOrder
    have haOrder : (1 : ℤ) ≤ finitePlaceOrder v (algebraMap R L a) :=
      one_le_finitePlaceOrder_algebraMap_of_mem v a haMem ha
    rw [hxOrder, hfactor, hprodOrder]
    omega

section FrobeniusConstants

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime]
  [CharP K p] [CharP L p] [PerfectField K]
  [Algebra K R] [Algebra K L] [IsScalarTower K R L]

/-- Over a perfect field of constants, the cancelling coefficient may be
regarded as an element of the Frobenius subfield `L^p`, which is the constant
field of the separating derivation used by Corvaja--Zannier.

The residue-surjectivity hypothesis is deliberately imposed on the genuine
constant field `K`: the full subfield `L^p` is not contained in a nontrivial
valuation ring.  Perfectness embeds `K` into `L^p`, and this is exactly enough
to make the column operation linear over the derivation-constant field. -/
theorem exists_frobeniusSubfield_constant_finitePlaceOrder_sub_mul_eq_zero_or_lt
    (v : HeightOneSpectrum R)
    (hresidue : Function.Surjective
      (algebraMap K v.asIdeal.ResidueField))
    (x y : L) (hx : x ≠ 0) (hy : y ≠ 0)
    (horder : finitePlaceOrder v x = finitePlaceOrder v y) :
    ∃ c : frobeniusSubfield L p,
      x - algebraMap (frobeniusSubfield L p) L c * y = 0 ∨
        finitePlaceOrder v x < finitePlaceOrder v
          (x - algebraMap (frobeniusSubfield L p) L c * y) := by
  obtain ⟨c, hc⟩ :=
    exists_constant_finitePlaceOrder_sub_mul_eq_zero_or_lt
      (C := K) v hresidue x y hx hy horder
  let cF : frobeniusSubfield L p :=
    perfectConstantsToFrobeniusSubfield (K := K) (L := L) (p := p) c
  refine ⟨cF, ?_⟩
  have hcF : algebraMap (frobeniusSubfield L p) L cF = algebraMap K L c := by
    exact coe_perfectConstantsToFrobeniusSubfield
      (K := K) (L := L) (p := p) c
  simpa only [hcF] using hc

end FrobeniusConstants

end

end BGS.CorvajaZannier
