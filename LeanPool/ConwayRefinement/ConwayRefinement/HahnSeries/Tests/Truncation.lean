/-
Copyright (c) 2026 Dan Abramov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dan Abramov
-/
module

public import LeanPool.ConwayRefinement.ConwayRefinement.HahnSeries.OrderType

import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Single
import Mathlib.Data.Sum.Order

/-!
# API checks for Hahn-series truncations

This client uses only the public Hahn-series interface. Its series has nonzero coefficients exactly
at `-1`, `0`, and `1`, and is truncated at `0`. The four exact support calculations distinguish the
intended intervals `< 0`, `≤ 0`, `≥ 0`, and `> 0`; in particular, they reject the nearby wrong
definitions obtained by interchanging strict and weak endpoints. The extreme cuts at `-1` and `1`
exercise the empty-summand cases.

The order-type and uniqueness checks exercise LM24, Fact 2.2.3(1), Proposition 3.2.1, and
Definition 3.2.2 through their public consequences. The root `LM24` module does not import this
client module.
-/

public noncomputable section

namespace Tests

open scoped HahnSeries

private def threeTermCoeffs : ℤ →₀ ℚ :=
  Finsupp.single (-1) 1 + Finsupp.single 0 2 + Finsupp.single 1 3

/-- A Hahn series with nonzero coefficients precisely at `-1`, `0`, and `1`. -/
def threeTermTruncationSeries : ℚ⟦ℤ⟧ :=
  HahnSeries.ofFinsupp threeTermCoeffs

@[simp]
theorem threeTermTruncationSeries_support :
    threeTermTruncationSeries.support = {-1, 0, 1} := by
  classical
  ext z
  by_cases hneg : z = -1
  · simp [threeTermTruncationSeries, threeTermCoeffs, hneg]
  by_cases hzero : z = 0
  · simp [threeTermTruncationSeries, threeTermCoeffs, hzero]
  by_cases hone : z = 1
  · simp [threeTermTruncationSeries, threeTermCoeffs, hone]
  · simp [threeTermTruncationSeries, threeTermCoeffs, hneg, hzero, hone]

/-- Strict lower truncation at zero keeps exactly the exponent `-1`. -/
theorem threeTermTruncationSeries_support_truncLT :
    (HahnSeries.truncLT 0 threeTermTruncationSeries).support = {-1} := by
  rw [HahnSeries.support_truncLT, threeTermTruncationSeries_support]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Weak lower truncation at zero keeps exactly the exponents `-1` and `0`. -/
theorem threeTermTruncationSeries_support_truncLE :
    (HahnSeries.truncLE 0 threeTermTruncationSeries).support = {-1, 0} := by
  rw [HahnSeries.support_truncLE, threeTermTruncationSeries_support]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Weak upper truncation at zero keeps exactly the exponents `0` and `1`. -/
theorem threeTermTruncationSeries_support_truncGE :
    (HahnSeries.truncGE 0 threeTermTruncationSeries).support = {0, 1} := by
  rw [HahnSeries.support_truncGE, threeTermTruncationSeries_support]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- Strict upper truncation at zero keeps exactly the exponent `1`. -/
theorem threeTermTruncationSeries_support_truncGT :
    (HahnSeries.truncGT 0 threeTermTruncationSeries).support = {1} := by
  rw [HahnSeries.support_truncGT, threeTermTruncationSeries_support]
  ext z
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  omega

/-- At the cut exponent, the weak truncations keep the coefficient and the strict truncations
discard it. -/
theorem threeTermTruncationSeries_endpoint_coefficients :
    (HahnSeries.truncLT 0 threeTermTruncationSeries).coeff 0 = 0 ∧
      (HahnSeries.truncLE 0 threeTermTruncationSeries).coeff 0 = 2 ∧
      (HahnSeries.truncGE 0 threeTermTruncationSeries).coeff 0 = 2 ∧
      (HahnSeries.truncGT 0 threeTermTruncationSeries).coeff 0 = 0 := by
  norm_num [threeTermTruncationSeries, threeTermCoeffs]

/-- Both complementary pairs of truncations reconstruct the original nonconstant series. -/
theorem threeTermTruncationSeries_splits :
    HahnSeries.truncLT 0 threeTermTruncationSeries +
        HahnSeries.truncGE 0 threeTermTruncationSeries = threeTermTruncationSeries ∧
      HahnSeries.truncLE 0 threeTermTruncationSeries +
        HahnSeries.truncGT 0 threeTermTruncationSeries = threeTermTruncationSeries :=
  ⟨HahnSeries.truncLT_add_truncGE 0 threeTermTruncationSeries,
    HahnSeries.truncLE_add_truncGT 0 threeTermTruncationSeries⟩

/-- The weak lower truncation at zero is proper because it discards the term at exponent `1`. -/
theorem threeTermTruncationSeries_truncLE_ne :
    HahnSeries.truncLE 0 threeTermTruncationSeries ≠ threeTermTruncationSeries := by
  intro h
  have hcoeff := congrArg (fun x : ℚ⟦ℤ⟧ => x.coeff 1) h
  simp [threeTermTruncationSeries, threeTermCoeffs] at hcoeff

/-- The proper weak lower truncation has strictly smaller support order type. -/
theorem threeTermTruncationSeries_truncLE_orderType_lt :
    (HahnSeries.truncLE 0 threeTermTruncationSeries).supportOrderType <
      threeTermTruncationSeries.supportOrderType :=
  HahnSeries.supportOrderType_truncLE_lt 0 threeTermTruncationSeries_truncLE_ne

/-- Both support-order-type decompositions use ordinary ordinal addition in lower-to-upper order. -/
theorem threeTermTruncationSeries_orderType_splits :
    threeTermTruncationSeries.supportOrderType =
        (HahnSeries.truncLT 0 threeTermTruncationSeries).supportOrderType +
          (HahnSeries.truncGE 0 threeTermTruncationSeries).supportOrderType ∧
      threeTermTruncationSeries.supportOrderType =
        (HahnSeries.truncLE 0 threeTermTruncationSeries).supportOrderType +
          (HahnSeries.truncGT 0 threeTermTruncationSeries).supportOrderType :=
  ⟨HahnSeries.supportOrderType_eq_truncLT_add_truncGE 0 threeTermTruncationSeries,
    HahnSeries.supportOrderType_eq_truncLE_add_truncGT 0 threeTermTruncationSeries⟩

/-- Truncation at the least and greatest support exponents exercises both empty-summand cases. -/
theorem threeTermTruncationSeries_boundary_truncations :
    HahnSeries.truncLT (-1) threeTermTruncationSeries = 0 ∧
      HahnSeries.truncGE (-1) threeTermTruncationSeries = threeTermTruncationSeries ∧
      HahnSeries.truncLE 1 threeTermTruncationSeries = threeTermTruncationSeries ∧
      HahnSeries.truncGT 1 threeTermTruncationSeries = 0 := by
  have hlt : HahnSeries.truncLT (-1) threeTermTruncationSeries = 0 := by
    rw [← HahnSeries.support_eq_empty_iff, HahnSeries.support_truncLT,
      threeTermTruncationSeries_support]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    omega
  have hgt : HahnSeries.truncGT 1 threeTermTruncationSeries = 0 := by
    rw [← HahnSeries.support_eq_empty_iff, HahnSeries.support_truncGT,
      threeTermTruncationSeries_support]
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    omega
  refine ⟨hlt, ?_, ?_, hgt⟩
  · simpa [hlt] using
      HahnSeries.truncLT_add_truncGE (-1) threeTermTruncationSeries
  · simpa [hgt] using
      HahnSeries.truncLE_add_truncGT 1 threeTermTruncationSeries

/-- Any separated decomposition with the same lower order type as the cut at zero is that cut. -/
theorem threeTermTruncationSeries_decomposition_unique (x y : ℚ⟦ℤ⟧)
    (hxy : ∀ i ∈ x.support, ∀ j ∈ y.support, i < j)
    (htype : x.supportOrderType =
      (HahnSeries.truncLE 0 threeTermTruncationSeries).supportOrderType)
    (hsum : x + y = threeTermTruncationSeries) :
    x = HahnSeries.truncLE 0 threeTermTruncationSeries ∧
      y = HahnSeries.truncGT 0 threeTermTruncationSeries := by
  have htrunc : ∀ i ∈ (HahnSeries.truncLE 0 threeTermTruncationSeries).support,
      ∀ j ∈ (HahnSeries.truncGT 0 threeTermTruncationSeries).support, i < j := by
    intro i hi j hj
    rw [HahnSeries.support_truncLE] at hi
    rw [HahnSeries.support_truncGT] at hj
    exact hi.2.trans_lt hj.2
  apply HahnSeries.add_decomposition_unique (HahnSeries.supportBelow_iff.mpr hxy)
    (HahnSeries.supportBelow_iff.mpr htrunc) htype
  exact hsum.trans (HahnSeries.truncLE_add_truncGT 0 threeTermTruncationSeries).symm

private instance : WellFoundedLT (Unit ⊕ₗ ℕ) :=
  (Sum.Lex.toLexRelIsoLT (α := Unit) (β := ℕ)).symm.toRelEmbedding.isWellFounded

/-- The coefficient-one series on an ordered singleton followed by `ℕ`. -/
def oneAddOmegaSplitSeries : ℚ⟦Unit ⊕ₗ ℕ⟧ where
  coeff _ := 1
  isPWO_support' := by
    simpa [Function.support] using
      Set.IsPWO.of_linearOrder (Set.univ : Set (Unit ⊕ₗ ℕ))

/-- The singleton first part of `oneAddOmegaSplitSeries`. -/
def oneAddOmegaLower : ℚ⟦Unit ⊕ₗ ℕ⟧ :=
  HahnSeries.filter (fun x ↦ x.isLeft) oneAddOmegaSplitSeries

/-- The `ℕ`-indexed second part of `oneAddOmegaSplitSeries`. -/
def oneAddOmegaUpper : ℚ⟦Unit ⊕ₗ ℕ⟧ :=
  HahnSeries.filter (fun x ↦ x.isRight) oneAddOmegaSplitSeries

private theorem oneAddOmegaLower_support : oneAddOmegaLower.support = Set.range Sum.inlₗ := by
  rw [oneAddOmegaLower, HahnSeries.support_filter]
  ext x
  rcases x with x | x
  · constructor
    · intro _
      exact ⟨x, rfl⟩
    · intro _
      simp [oneAddOmegaSplitSeries]
  · constructor
    · intro h
      simp at h
    · rintro ⟨y, h⟩
      have hlt : Sum.inlₗ y < Sum.inrₗ x := Sum.Lex.inl_lt_inr y x
      exact (hlt.ne h).elim

private theorem oneAddOmegaUpper_support : oneAddOmegaUpper.support = Set.range Sum.inrₗ := by
  rw [oneAddOmegaUpper, HahnSeries.support_filter]
  ext x
  rcases x with x | x
  · constructor
    · intro h
      simp at h
    · rintro ⟨y, h⟩
      have hlt : Sum.inlₗ x < Sum.inrₗ y := Sum.Lex.inl_lt_inr x y
      exact (hlt.ne h.symm).elim
  · constructor
    · intro _
      exact ⟨x, rfl⟩
    · intro _
      simp [oneAddOmegaSplitSeries]

private theorem oneAddOmegaLower_supportOrderType : oneAddOmegaLower.supportOrderType = 1 := by
  rw [HahnSeries.supportOrderType_eq_setOrderType]
  have e : oneAddOmegaLower.support ≃o Unit :=
    (OrderIso.setCongr oneAddOmegaLower.support (Set.range Sum.inlₗ)
      oneAddOmegaLower_support).trans
        (OrderEmbedding.ofStrictMono Sum.inlₗ Sum.Lex.inl_strictMono).orderIso.symm
  exact oneAddOmegaLower.isPWO_support.orderType_eq_typeLT_of_orderIso e |>.trans
    Ordinal.type_unit

private theorem oneAddOmegaUpper_supportOrderType :
    oneAddOmegaUpper.supportOrderType = Ordinal.omega0 := by
  rw [HahnSeries.supportOrderType_eq_setOrderType]
  have e : oneAddOmegaUpper.support ≃o ℕ :=
    (OrderIso.setCongr oneAddOmegaUpper.support (Set.range Sum.inrₗ)
      oneAddOmegaUpper_support).trans
        (OrderEmbedding.ofStrictMono Sum.inrₗ Sum.Lex.inr_strictMono).orderIso.symm
  exact oneAddOmegaUpper.isPWO_support.orderType_eq_typeLT_of_orderIso e |>.trans
    Ordinal.type_nat_lt

/-- The source decomposition uses ordinary `1 + ω = ω`, not the Hessenberg sum `ω + 1`. -/
theorem oneAddOmega_decomposition_uses_ordinary_addition :
    (oneAddOmegaLower + oneAddOmegaUpper).supportOrderType = Ordinal.omega0 ∧
      NatOrdinal.of oneAddOmegaLower.supportOrderType +
        NatOrdinal.of oneAddOmegaUpper.supportOrderType ≠
          NatOrdinal.of (oneAddOmegaLower + oneAddOmegaUpper).supportOrderType := by
  have hsep : ∀ i ∈ oneAddOmegaLower.support, ∀ j ∈ oneAddOmegaUpper.support, i < j := by
    rw [oneAddOmegaLower_support, oneAddOmegaUpper_support]
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact Sum.Lex.inl_lt_inr i j
  have hord := (HahnSeries.supportOrderType_eq_add_iff
    (oneAddOmegaLower + oneAddOmegaUpper) 1 Ordinal.omega0).mpr
      ⟨oneAddOmegaLower, oneAddOmegaUpper, HahnSeries.supportBelow_iff.mpr hsep,
        oneAddOmegaLower_supportOrderType, oneAddOmegaUpper_supportOrderType, rfl⟩
  constructor
  · simpa using hord
  · rw [oneAddOmegaLower_supportOrderType, oneAddOmegaUpper_supportOrderType, hord,
      Ordinal.one_add_omega0]
    intro h
    rw [add_comm] at h
    have hone : NatOrdinal.of (1 : Ordinal) = 1 := rfl
    rw [hone, ← NatOrdinal.of_add_one] at h
    exact (lt_add_one Ordinal.omega0).ne' (NatOrdinal.of.injective h)

end Tests
