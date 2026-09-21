/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindAuxiliaryWronskian

/-!
# Uniformizer-free Dedekind auxiliary cases

This module packages Corvaja--Zannier local cases (iii) and (iv) using only a
DVR-preserving derivation.  The uniformizer needed by the determinant estimate
is chosen internally.  In particular, callers do not need an algebra map from
the derivation's constant field into the local DVR.
-/

namespace BGS.CorvajaZannier

noncomputable section

open scoped BigOperators
open IsDedekindDomain

variable {C R L : Type*} [Field C] [CommRing R] [IsDedekindDomain R]
  [IsDiscreteValuationRing R] [Field L] [Algebra R L] [Algebra C L]
  [IsFractionRing R L]

/-- Uniformizer-free form of source case (iii). -/
theorem finitePlaceOrderTop_auxiliaryFamily_caseIII_source_lower_bound_of_preserves
    (vPlace : HeightOneSpectrum R)
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) • finitePlaceOrder vPlace u +
          (h * k) • finitePlaceOrder vPlace v +
          k • finitePlaceOrder vPlace ((1 - u) / (1 - v)) +
          ∑ rs : Fin (k + 1) × Fin h,
            finitePlaceOrder vPlace
              (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
          ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop vPlace
        (indexedDedekindLocalWronskian D epsilon
          (auxiliaryFamily u v h k)).det := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal : vPlace.asIdeal = Ideal.span {π} := by
    calc
      vPlace.asIdeal = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal vPlace.isMaximal
      _ = Ideal.span {π} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  exact finitePlaceOrderTop_auxiliaryFamily_caseIII_source_lower_bound
    vPlace π hπ hπIdeal D hDIntegral h k epsilon u v hu hv hu1 hv1

/-- Uniformizer-free form of source case (iv). -/
theorem finitePlaceOrderTop_auxiliaryFamily_caseIV_source_lower_bound_of_preserves
    (vPlace : HeightOneSpectrum R)
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : L) (hu : u ≠ 0) (hv : v ≠ 0)
    (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) • finitePlaceOrder vPlace u +
          k • finitePlaceOrder vPlace ((1 - u) / (1 - v)) +
          ∑ rs : Fin (k + 1) × Fin h,
            finitePlaceOrder vPlace
              (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
          ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop vPlace
        (indexedDedekindLocalWronskian D epsilon
          (auxiliaryFamily u v h k)).det := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
  have hπIdeal : vPlace.asIdeal = Ideal.span {π} := by
    calc
      vPlace.asIdeal = IsLocalRing.maximalIdeal R :=
        IsLocalRing.eq_maximalIdeal vPlace.isMaximal
      _ = Ideal.span {π} :=
        (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ
  exact finitePlaceOrderTop_auxiliaryFamily_caseIV_source_lower_bound
    vPlace π hπ hπIdeal D hDIntegral h k epsilon u v hu hv hu1 hv1

end

end BGS.CorvajaZannier
