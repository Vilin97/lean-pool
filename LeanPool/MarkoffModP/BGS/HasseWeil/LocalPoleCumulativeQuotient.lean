/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.HasseWeil.LocalPoleFiltration
import Mathlib.RingTheory.LocalRing.Length
import Mathlib.RingTheory.LocalRing.Quotient

/-!
# Cumulative local principal parts

For a DVR uniformizer `π`, the quotient of functions with pole order at most
`n` by the regular functions is the quotient of the DVR by the `n`th power
of its maximal ideal.  Over a finite constant field its dimension is
therefore `n` times the residue-field degree.
-/

namespace BGS.HasseWeil

open scoped nonZeroDivisors

noncomputable section

variable {K R L : Type*} [Field K] [CommRing R]
  [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [Field L] [Algebra K R] [Algebra R L] [Algebra K L]
  [IsScalarTower K R L] [IsFractionRing R L]

omit [IsDedekindDomain R] [IsDiscreteValuationRing R]
  [IsFractionRing R L] in
private theorem cumulativeLocalPoleSpace_regular (π : R) (n : ℕ) :
    ∀ x : localPoleSpace (K := K) (L := L) π n,
      ∃ r : R, algebraMap R L (π ^ n) * x.1 = algebraMap R L r := by
  intro x
  exact x.2

/-- The normalized numerator modulo the `n`th power of the maximal ideal. -/
def localPolePrincipalPartMap (π : R) (n : ℕ) :
    localPoleSpace (K := K) (L := L) π n →ₗ[K]
      R ⧸ IsLocalRing.maximalIdeal R ^ n :=
  (Ideal.Quotient.mkₐ K (IsLocalRing.maximalIdeal R ^ n)).toLinearMap.comp
    (localNormalizedLiftLinearMap
      (localPoleSpace (K := K) (L := L) π n)
      (algebraMap R L (π ^ n))
      (cumulativeLocalPoleSpace_regular (K := K) (L := L) π n))

theorem localPolePrincipalPartMap_surjective
    (π : R) (hπ : π ≠ 0) (n : ℕ) :
    Function.Surjective
      (localPolePrincipalPartMap (K := K) (L := L) π n) := by
  intro z
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective z
  have hdenom : algebraMap R L (π ^ n) ≠ 0 := by
    rw [map_pow]
    exact pow_ne_zero n (by
      simpa using (IsFractionRing.injective R L).ne hπ)
  let x : L := (algebraMap R L (π ^ n))⁻¹ * algebraMap R L r
  have hx : algebraMap R L (π ^ n) * x = algebraMap R L r := by
    dsimp only [x]
    rw [← mul_assoc, mul_inv_cancel₀ hdenom, one_mul]
  let x' : localPoleSpace (K := K) (L := L) π n := ⟨x, r, hx⟩
  refine ⟨x', ?_⟩
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ n)
      (localNormalizedLift
        (localPoleSpace (K := K) (L := L) π n)
        (algebraMap R L (π ^ n))
        (cumulativeLocalPoleSpace_regular (K := K) (L := L) π n) x') =
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ n) r
  congr 1
  apply IsFractionRing.injective R L
  rw [← hx]
  exact (localNormalizedLift_spec
    (localPoleSpace (K := K) (L := L) π n)
    (algebraMap R L (π ^ n))
    (cumulativeLocalPoleSpace_regular (K := K) (L := L) π n) x').symm

theorem localPolePrincipalPartMap_ker
    (π : R) (hπ : π ≠ 0)
    (hπIdeal : IsLocalRing.maximalIdeal R = Ideal.span {π}) (n : ℕ) :
    (localPolePrincipalPartMap (K := K) (L := L) π n).ker =
      Submodule.comap
        (localPoleSpace (K := K) (L := L) π n).subtype
        (localPoleSpace (K := K) (L := L) π 0) := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap]
  change Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ n)
      (localNormalizedLift
        (localPoleSpace (K := K) (L := L) π n)
        (algebraMap R L (π ^ n))
        (cumulativeLocalPoleSpace_regular (K := K) (L := L) π n) x) = 0 ↔ _
  rw [Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hr
    rw [hπIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton] at hr
    obtain ⟨s, hs⟩ := hr
    rw [mem_localPoleSpace_iff]
    refine ⟨s, ?_⟩
    simp only [pow_zero, map_one, one_mul]
    have hlift := localNormalizedLift_spec
      (localPoleSpace (K := K) (L := L) π n)
      (algebraMap R L (π ^ n))
      (cumulativeLocalPoleSpace_regular (K := K) (L := L) π n) x
    rw [hs, map_mul] at hlift
    have hdenom : algebraMap R L (π ^ n) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero n (by
        simpa using (IsFractionRing.injective R L).ne hπ)
    apply mul_left_cancel₀ hdenom
    exact hlift
  · rintro ⟨s, hs⟩
    have hliftEq : localNormalizedLift
        (localPoleSpace (K := K) (L := L) π n)
        (algebraMap R L (π ^ n))
        (cumulativeLocalPoleSpace_regular (K := K) (L := L) π n) x =
      π ^ n * s := by
      apply IsFractionRing.injective R L
      rw [map_mul, ← hs]
      simp only [pow_zero, map_one, one_mul]
      change algebraMap R L
          (localNormalizedLift
            (localPoleSpace (K := K) (L := L) π n)
            (algebraMap R L (π ^ n))
            (cumulativeLocalPoleSpace_regular (K := K) (L := L) π n) x) =
        algebraMap R L (π ^ n) * x.1
      exact (localNormalizedLift_spec
        (localPoleSpace (K := K) (L := L) π n)
        (algebraMap R L (π ^ n))
        (cumulativeLocalPoleSpace_regular (K := K) (L := L) π n) x).symm
    rw [hliftEq, hπIdeal, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
    exact ⟨s, rfl⟩

/-- Cumulative local principal parts are the quotient by the corresponding
power of the maximal ideal. -/
def localPoleCumulativeQuotientEquiv
    (π : R) (hπ : π ≠ 0)
    (hπIdeal : IsLocalRing.maximalIdeal R = Ideal.span {π}) (n : ℕ) :
    (localPoleSpace (K := K) (L := L) π n ⧸
      Submodule.comap
        (localPoleSpace (K := K) (L := L) π n).subtype
        (localPoleSpace (K := K) (L := L) π 0)) ≃ₗ[K]
      R ⧸ IsLocalRing.maximalIdeal R ^ n := by
  let f := localPolePrincipalPartMap (K := K) (L := L) π n
  have hsurj : Function.Surjective f :=
    localPolePrincipalPartMap_surjective (K := K) (L := L) π hπ n
  have hker := localPolePrincipalPartMap_ker
    (K := K) (L := L) π hπ hπIdeal n
  rw [← hker]
  exact f.quotKerEquivOfSurjective hsurj

/-- Over a finite constant field, allowing poles through order `n` creates
exactly `n` copies of the local residue field. -/
theorem localPoleCumulativeQuotient_finrank
    [Fintype K] (π : R) (hπ : π ≠ 0)
    (hπIdeal : IsLocalRing.maximalIdeal R = Ideal.span {π}) (n : ℕ)
    [Finite (IsLocalRing.ResidueField R)] :
    Module.finrank K
        (localPoleSpace (K := K) (L := L) π n ⧸
          Submodule.comap
            (localPoleSpace (K := K) (L := L) π n).subtype
            (localPoleSpace (K := K) (L := L) π 0)) =
      n * Module.finrank K (IsLocalRing.ResidueField R) := by
  let I := IsLocalRing.maximalIdeal R ^ n
  let : Finite (R ⧸ I) :=
    IsLocalRing.finite_quotient_iff.mpr ⟨n, le_rfl⟩
  let : Module.Finite K (R ⧸ I) := Module.Finite.of_finite
  let : Module.Finite K (IsLocalRing.ResidueField R) :=
    Module.Finite.of_finite
  have hlocalLength : Module.length R (R ⧸ I) = n := by
    exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R n
  have hbaseRank : Module.finrank K (IsLocalRing.ResidueField K) = 1 := by
    rw [Algebra.finrank_eq_one_iff_bijective_algebraMap]
    exact ⟨(algebraMap K (IsLocalRing.ResidueField K)).injective,
      Ideal.Quotient.mk_surjective⟩
  have hresidueLength :
      Module.length (IsLocalRing.ResidueField K)
          (IsLocalRing.ResidueField R) =
        Module.finrank K (IsLocalRing.ResidueField R) := by
    rw [Module.length_eq_finrank]
    have hresidueRank :
        Module.finrank (IsLocalRing.ResidueField K)
            (IsLocalRing.ResidueField R) =
          Module.finrank K (IsLocalRing.ResidueField R) := by
      calc
      Module.finrank (IsLocalRing.ResidueField K)
          (IsLocalRing.ResidueField R) =
          1 * Module.finrank (IsLocalRing.ResidueField K)
            (IsLocalRing.ResidueField R) := by simp
      _ = Module.finrank K (IsLocalRing.ResidueField K) *
          Module.finrank (IsLocalRing.ResidueField K)
            (IsLocalRing.ResidueField R) := by rw [hbaseRank]
      _ = Module.finrank K (IsLocalRing.ResidueField R) :=
        Module.finrank_mul_finrank K (IsLocalRing.ResidueField K)
          (IsLocalRing.ResidueField R)
    exact_mod_cast hresidueRank
  rw [(localPoleCumulativeQuotientEquiv
    (K := K) (L := L) π hπ hπIdeal n).finrank_eq]
  change Module.finrank K (R ⧸ I) = _
  have hlength : Module.length K (R ⧸ I) =
      n * Module.finrank K (IsLocalRing.ResidueField R) := by
    rw [IsLocalRing.length_restrictScalars K R (R ⧸ I),
      hlocalLength, hresidueLength]
  rw [Module.length_eq_finrank] at hlength
  exact_mod_cast hlength

end

end BGS.HasseWeil
