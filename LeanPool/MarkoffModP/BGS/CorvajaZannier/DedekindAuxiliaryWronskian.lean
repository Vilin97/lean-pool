/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.DedekindLocalWronskian
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.LocalAuxiliaryWronskian

/-!
# Auxiliary-family Wronskian estimates at a Dedekind place

This file transports the algebraic local cases (ii)--(iv) in
Corvaja--Zannier's Proposition 2 from Laurent series to an arbitrary
height-one DVR place.  The derivation is only required to preserve the DVR;
no choice of a normalized local parameter is used.

The case-(iii) column operation is exactly the lower-unitriangular matrix
`caseIIIColumnMatrix`.  Consequently the resulting estimates retain the
source terms: the triangular `u` contribution, the `h * k` contribution of
`v`, the `k` copies of the ratio `rho`, the full grid sum, and the loss given
by the sum of the selected derivative orders.

Source provenance: published pages 1935--1936; checked semantic reconstruction
`Papers/CorvajaZannier2013/CorvajaZannier2013.tex`, lines 636--732.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped Matrix BigOperators
open IsDedekindDomain Multiplicative WithZero

variable {C R L : Type*} [Field C] [CommRing R] [IsDedekindDomain R]
  [IsDiscreteValuationRing R] [Field L] [Algebra C R] [Algebra R L]
  [Algebra C L] [IsScalarTower C R L] [IsFractionRing R L]

/-- The auxiliary family with the ratio column written using an explicit
parameter `rho`. -/
def dedekindLocalAuxiliaryFamily (u v rho : L) (h k : ℕ) :
    Sum (Fin k) (Fin (k + 1) × Fin h) → L
  | Sum.inl i => u ^ (i : ℕ) * rho
  | Sum.inr rs => u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)

@[simp]
theorem dedekindLocalAuxiliaryFamily_div_eq_auxiliaryFamily
    (u v : L) (h k : ℕ) :
    dedekindLocalAuxiliaryFamily u v ((1 - u) / (1 - v)) h k =
      auxiliaryFamily u v h k := by
  rfl

/-- The case-(iii) family after replacing each first-block column
`u ^ i * rho` by `u ^ i * v ^ h * rho`. -/
def dedekindCaseIIIImprovedAuxiliaryFamily (u v rho : L) (h k : ℕ) :
    Sum (Fin k) (Fin (k + 1) × Fin h) → L
  | Sum.inl i => u ^ (i : ℕ) * v ^ h * rho
  | Sum.inr rs => u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)

private theorem dedekind_caseIII_geometricSeries_column_identity
    (u v rho : L) (h j : ℕ) (hrho : (1 - v) * rho = 1 - u) :
    u ^ j * rho - u ^ j * (1 - u) * (∑ s ∈ Finset.range h, v ^ s) =
      u ^ j * v ^ h * rho := by
  rw [← hrho]
  calc
    u ^ j * rho - u ^ j * ((1 - v) * rho) *
        (∑ s ∈ Finset.range h, v ^ s) =
        u ^ j * rho - u ^ j * rho *
          ((1 - v) * ∑ s ∈ Finset.range h, v ^ s) := by ring
    _ = u ^ j * rho - u ^ j * rho * (1 - v ^ h) := by
      rw [mul_neg_geom_sum]
    _ = u ^ j * v ^ h * rho := by ring

private theorem dedekind_caseIIIGridCorrection_sum_smul
    (u v : L) (h k : ℕ) (i : Fin k) :
    (∑ rs : Fin (k + 1) × Fin h,
        caseIIIGridCorrection (K := C) h k rs i •
          (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ))) =
      -(u ^ (i : ℕ) * ∑ s : Fin h, v ^ (s : ℕ)) +
        u ^ (i.succ : ℕ) * ∑ s : Fin h, v ^ (s : ℕ) := by
  rw [Fintype.sum_prod_type_right]
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro s _
  have hne : i.castSucc ≠ i.succ := i.castSucc_lt_succ.ne
  simp only [caseIIIGridCorrection]
  calc
    (∑ r : Fin (k + 1),
        (if r = i.castSucc then (-1 : C)
          else if r = i.succ then 1 else 0) •
            (u ^ (r : ℕ) * v ^ (s : ℕ))) =
        (∑ r : Fin (k + 1),
          if r = i.castSucc then -(u ^ (r : ℕ) * v ^ (s : ℕ)) else 0) +
        ∑ r : Fin (k + 1),
          if r = i.succ then u ^ (r : ℕ) * v ^ (s : ℕ) else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro r _
      by_cases hr0 : r = i.castSucc
      · simp [hr0, hne]
      · by_cases hr1 : r = i.succ
        · simp [hr1, hne.symm]
        · simp [hr0, hr1]
    _ = -(u ^ (i : ℕ) * v ^ (s : ℕ)) +
        u ^ (i.succ : ℕ) * v ^ (s : ℕ) := by
      rw [Fintype.sum_ite_eq', Fintype.sum_ite_eq']
      simp

/-- The determinant-one source column operation performs the case-(iii)
replacement over an arbitrary fraction field. -/
theorem indexedDedekindLocalColumnCombination_caseIIIColumnMatrix
    (u v rho : L) (h k : ℕ) (hrho : (1 - v) * rho = 1 - u) :
    indexedDedekindLocalColumnCombination
        (dedekindLocalAuxiliaryFamily u v rho h k)
        (caseIIIColumnMatrix (K := C) h k) =
      dedekindCaseIIIImprovedAuxiliaryFamily u v rho h k := by
  classical
  funext j
  cases j with
  | inl i =>
      rw [indexedDedekindLocalColumnCombination, Fintype.sum_sum_type]
      simp only [caseIIIColumnMatrix, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₂₁, dedekindLocalAuxiliaryFamily,
        dedekindCaseIIIImprovedAuxiliaryFamily]
      have hleft :
          (∑ x : Fin k, (1 : Matrix (Fin k) (Fin k) C) x i •
            (u ^ (x : ℕ) * rho)) = u ^ (i : ℕ) * rho := by
        simp [Matrix.one_apply]
      rw [hleft, dedekind_caseIIIGridCorrection_sum_smul]
      rw [Fin.sum_univ_eq_sum_range]
      simp only [Fin.val_succ, pow_succ]
      convert dedekind_caseIII_geometricSeries_column_identity
        u v rho h (i : ℕ) hrho using 1
      all_goals ring
  | inr rs =>
      rw [indexedDedekindLocalColumnCombination, Fintype.sum_sum_type]
      simp [caseIIIColumnMatrix, dedekindLocalAuxiliaryFamily,
        dedekindCaseIIIImprovedAuxiliaryFamily, Matrix.one_apply]

omit [IsDiscreteValuationRing R] [Algebra C R] [IsScalarTower C R L] in
/-- Case (ii): if `u`, `v`, and the ratio are all represented by elements of
the DVR, then the auxiliary Wronskian is regular. -/
theorem finitePlaceOrderTop_auxiliaryFamily_caseII_nonnegative_of_integral
    (vPlace : HeightOneSpectrum R) (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : L)
    (huIntegral : ∃ u0 : R, u = algebraMap R L u0)
    (hvIntegral : ∃ v0 : R, v = algebraMap R L v0)
    (hratioIntegral : ∃ rho0 : R,
      (1 - u) / (1 - v) = algebraMap R L rho0) :
    (0 : WithTop ℤ) ≤ finitePlaceOrderTop vPlace
      (indexedDedekindLocalWronskian D epsilon
        (auxiliaryFamily u v h k)).det := by
  apply finitePlaceOrderTop_indexedDedekindLocalWronskian_det_nonnegative_of_integral
    vPlace D hDIntegral epsilon (auxiliaryFamily u v h k)
  intro j
  obtain ⟨u0, hu⟩ := huIntegral
  obtain ⟨v0, hv⟩ := hvIntegral
  obtain ⟨rho0, hrho⟩ := hratioIntegral
  cases j with
  | inl i =>
      refine ⟨u0 ^ (i : ℕ) * rho0, ?_⟩
      change u ^ (i : ℕ) * ((1 - u) / (1 - v)) =
        algebraMap R L (u0 ^ (i : ℕ) * rho0)
      rw [hrho, hu, map_mul, map_pow]
  | inr rs =>
      refine ⟨u0 ^ (rs.1 : ℕ) * v0 ^ (rs.2 : ℕ), ?_⟩
      change u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ) =
        algebraMap R L (u0 ^ (rs.1 : ℕ) * v0 ^ (rs.2 : ℕ))
      rw [hu, hv, map_mul, map_pow, map_pow]

omit [IsDiscreteValuationRing R] in
private theorem dedekind_finitePlaceOrder_mul
    (vPlace : HeightOneSpectrum R) (x y : L) (hx : x ≠ 0) (hy : y ≠ 0) :
    finitePlaceOrder vPlace (x * y) =
      finitePlaceOrder vPlace x + finitePlaceOrder vPlace y := by
  have h := finitePlaceOrderTop_mul vPlace x y
  rw [finitePlaceOrderTop_eq_coe vPlace (x * y) (mul_ne_zero hx hy),
    finitePlaceOrderTop_eq_coe vPlace x hx,
    finitePlaceOrderTop_eq_coe vPlace y hy] at h
  exact_mod_cast h

omit [IsDiscreteValuationRing R] in
private theorem dedekind_finitePlaceOrder_pow
    (vPlace : HeightOneSpectrum R) (x : L) (hx : x ≠ 0) (n : ℕ) :
    finitePlaceOrder vPlace (x ^ n) = n • finitePlaceOrder vPlace x := by
  have h := finitePlaceOrderTop_pow vPlace x n
  rw [finitePlaceOrderTop_eq_coe vPlace (x ^ n) (pow_ne_zero n hx),
    finitePlaceOrderTop_eq_coe vPlace x hx] at h
  exact_mod_cast h

omit [IsDiscreteValuationRing R] in
private theorem dedekind_finitePlaceOrder_caseIIIImproved_inl
    (vPlace : HeightOneSpectrum R) (u v rho : L) (h k : ℕ) (i : Fin k)
    (hu : u ≠ 0) (hv : v ≠ 0) (hrho : rho ≠ 0) :
    finitePlaceOrder vPlace
        (dedekindCaseIIIImprovedAuxiliaryFamily u v rho h k (Sum.inl i)) =
      (i : ℕ) • finitePlaceOrder vPlace u +
        h • finitePlaceOrder vPlace v + finitePlaceOrder vPlace rho := by
  simp only [dedekindCaseIIIImprovedAuxiliaryFamily]
  rw [dedekind_finitePlaceOrder_mul vPlace
      (u ^ (i : ℕ) * v ^ h) rho
      (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)) hrho,
    dedekind_finitePlaceOrder_mul vPlace (u ^ (i : ℕ)) (v ^ h)
      (pow_ne_zero _ hu) (pow_ne_zero _ hv),
    dedekind_finitePlaceOrder_pow vPlace u hu,
    dedekind_finitePlaceOrder_pow vPlace v hv]

omit [IsDiscreteValuationRing R] in
private theorem dedekind_finitePlaceOrder_localAuxiliary_inl
    (vPlace : HeightOneSpectrum R) (u v rho : L) (h k : ℕ) (i : Fin k)
    (hu : u ≠ 0) (hrho : rho ≠ 0) :
    finitePlaceOrder vPlace
        (dedekindLocalAuxiliaryFamily u v rho h k (Sum.inl i)) =
      (i : ℕ) • finitePlaceOrder vPlace u + finitePlaceOrder vPlace rho := by
  simp only [dedekindLocalAuxiliaryFamily]
  rw [dedekind_finitePlaceOrder_mul vPlace (u ^ (i : ℕ)) rho
      (pow_ne_zero _ hu) hrho,
    dedekind_finitePlaceOrder_pow vPlace u hu]

private theorem dedekind_sum_fin_cast_int (k : ℕ) :
    (∑ i : Fin k, (i : ℤ)) = (k * (k - 1) / 2 : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range, ← Nat.cast_sum, Finset.sum_range_id]

omit [IsDiscreteValuationRing R] in
private theorem dedekind_sum_caseIIIImproved_inl_orders
    (vPlace : HeightOneSpectrum R) (u v rho : L) (h k : ℕ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hrho : rho ≠ 0) :
    (∑ i : Fin k, finitePlaceOrder vPlace
        (dedekindCaseIIIImprovedAuxiliaryFamily u v rho h k (Sum.inl i))) =
      (k * (k - 1) / 2 : ℕ) • finitePlaceOrder vPlace u +
        (h * k) • finitePlaceOrder vPlace v +
        k • finitePlaceOrder vPlace rho := by
  simp_rw [dedekind_finitePlaceOrder_caseIIIImproved_inl
    vPlace u v rho h k _ hu hv hrho]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp_rw [nsmul_eq_mul]
  rw [← Finset.sum_mul, dedekind_sum_fin_cast_int]
  simp only [Nat.cast_mul]
  ring

omit [IsDiscreteValuationRing R] in
private theorem dedekind_sum_localAuxiliary_inl_orders
    (vPlace : HeightOneSpectrum R) (u v rho : L) (h k : ℕ)
    (hu : u ≠ 0) (hrho : rho ≠ 0) :
    (∑ i : Fin k, finitePlaceOrder vPlace
        (dedekindLocalAuxiliaryFamily u v rho h k (Sum.inl i))) =
      (k * (k - 1) / 2 : ℕ) • finitePlaceOrder vPlace u +
        k • finitePlaceOrder vPlace rho := by
  simp_rw [dedekind_finitePlaceOrder_localAuxiliary_inl
    vPlace u v rho h k _ hu hrho]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp_rw [nsmul_eq_mul]
  rw [← Finset.sum_mul, dedekind_sum_fin_cast_int]

private theorem dedekind_coe_sum_int
    {ι : Type*} [Fintype ι] (g : ι → ℤ) :
    (((∑ i, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i, ((g i : ℤ) : WithTop ℤ) := by
  classical
  induction (Finset.univ : Finset ι) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, WithTop.coe_add]

omit [Algebra C R] [IsScalarTower C R L] in
/-- Case (iii) at a Dedekind DVR place, in the displayed source form.  The
grid contribution is retained as the exact sum that cancels under the global
product formula. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_caseIII_source_lower_bound
    (vPlace : HeightOneSpectrum R) (pi : R) (hpi : Irreducible pi)
    (hpiIdeal : vPlace.asIdeal = Ideal.span {pi})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v rho : L) (hrhoIdentity : (1 - v) * rho = 1 - u)
    (hu : u ≠ 0) (hv : v ≠ 0) (hrho : rho ≠ 0) :
    (((k * (k - 1) / 2 : ℕ) • finitePlaceOrder vPlace u +
          (h * k) • finitePlaceOrder vPlace v +
          k • finitePlaceOrder vPlace rho +
          ∑ rs : Fin (k + 1) × Fin h,
            finitePlaceOrder vPlace
              (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
          ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop vPlace
        (indexedDedekindLocalWronskian D epsilon
          (dedekindLocalAuxiliaryFamily u v rho h k)).det := by
  have hbound :=
    finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_preserves
      vPlace pi hpi hpiIdeal D hDIntegral epsilon
        (dedekindCaseIIIImprovedAuxiliaryFamily u v rho h k)
  have hdet :
      (indexedDedekindLocalWronskian D epsilon
        (dedekindCaseIIIImprovedAuxiliaryFamily u v rho h k)).det =
      (indexedDedekindLocalWronskian D epsilon
        (dedekindLocalAuxiliaryFamily u v rho h k)).det := by
    rw [← indexedDedekindLocalColumnCombination_caseIIIColumnMatrix (C := C)
      u v rho h k hrhoIdentity]
    exact indexedDedekindLocalWronskian_det_columnCombination_of_det_eq_one
      D epsilon (dedekindLocalAuxiliaryFamily u v rho h k)
        (caseIIIColumnMatrix (K := C) h k) (caseIIIColumnMatrix_det h k)
  rw [hdet] at hbound
  rw [Fintype.sum_sum_type] at hbound
  simp only [dedekindCaseIIIImprovedAuxiliaryFamily] at hbound
  simp_rw [finitePlaceOrderTop_eq_coe vPlace _
    (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)) hrho)]
    at hbound
  simp_rw [finitePlaceOrderTop_eq_coe vPlace _
    (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv))] at hbound
  rw [← dedekind_coe_sum_int, ← dedekind_coe_sum_int] at hbound
  have hfirst :
      (∑ i : Fin k, finitePlaceOrder vPlace (u ^ (i : ℕ) * v ^ h * rho)) =
        (k * (k - 1) / 2 : ℕ) • finitePlaceOrder vPlace u +
          (h * k) • finitePlaceOrder vPlace v +
          k • finitePlaceOrder vPlace rho := by
    simpa only [dedekindCaseIIIImprovedAuxiliaryFamily] using
      dedekind_sum_caseIIIImproved_inl_orders
        vPlace u v rho h k hu hv hrho
  rw [hfirst] at hbound
  exact_mod_cast hbound

omit [Algebra C R] [IsScalarTower C R L] in
/-- Case (iv) at a Dedekind DVR place, in the displayed source form. -/
theorem finitePlaceOrderTop_indexedDedekindLocalWronskian_caseIV_source_lower_bound
    (vPlace : HeightOneSpectrum R) (pi : R) (hpi : Irreducible pi)
    (hpiIdeal : vPlace.asIdeal = Ideal.span {pi})
    (D : Derivation C L L)
    (hDIntegral : ∀ r : R, ∃ s : R,
      D (algebraMap R L r) = algebraMap R L s)
    (h k : ℕ) (epsilon : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v rho : L) (hu : u ≠ 0) (hv : v ≠ 0) (hrho : rho ≠ 0) :
    (((k * (k - 1) / 2 : ℕ) • finitePlaceOrder vPlace u +
          k • finitePlaceOrder vPlace rho +
          ∑ rs : Fin (k + 1) × Fin h,
            finitePlaceOrder vPlace
              (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)) -
          ∑ i, (epsilon i : ℤ) : ℤ) : WithTop ℤ) ≤
      finitePlaceOrderTop vPlace
        (indexedDedekindLocalWronskian D epsilon
          (dedekindLocalAuxiliaryFamily u v rho h k)).det := by
  have hbound :=
    finitePlaceOrderTop_indexedDedekindLocalWronskian_det_lower_bound_of_preserves
      vPlace pi hpi hpiIdeal D hDIntegral epsilon
        (dedekindLocalAuxiliaryFamily u v rho h k)
  rw [Fintype.sum_sum_type] at hbound
  simp only [dedekindLocalAuxiliaryFamily] at hbound
  simp_rw [finitePlaceOrderTop_eq_coe vPlace _
    (mul_ne_zero (pow_ne_zero _ hu) hrho)] at hbound
  simp_rw [finitePlaceOrderTop_eq_coe vPlace _
    (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv))] at hbound
  rw [← dedekind_coe_sum_int, ← dedekind_coe_sum_int] at hbound
  have hfirst :
      (∑ i : Fin k, finitePlaceOrder vPlace (u ^ (i : ℕ) * rho)) =
        (k * (k - 1) / 2 : ℕ) • finitePlaceOrder vPlace u +
          k • finitePlaceOrder vPlace rho := by
    simpa only [dedekindLocalAuxiliaryFamily] using
      dedekind_sum_localAuxiliary_inl_orders
        vPlace u v rho h k hu hrho
  rw [hfirst] at hbound
  exact_mod_cast hbound

omit [Algebra C R] [IsScalarTower C R L] in
/-- Case (iii) connected to the exact Corvaja--Zannier auxiliary family. -/
theorem finitePlaceOrderTop_auxiliaryFamily_caseIII_source_lower_bound
    (vPlace : HeightOneSpectrum R) (pi : R) (hpi : Irreducible pi)
    (hpiIdeal : vPlace.asIdeal = Ideal.span {pi})
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
  have hden : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
  have hnum : 1 - u ≠ 0 := sub_ne_zero.mpr hu1.symm
  have hratio : (1 - u) / (1 - v) ≠ 0 := div_ne_zero hnum hden
  have hclear : (1 - v) * ((1 - u) / (1 - v)) = 1 - u := by
    field_simp
  simpa only [dedekindLocalAuxiliaryFamily_div_eq_auxiliaryFamily] using
    finitePlaceOrderTop_indexedDedekindLocalWronskian_caseIII_source_lower_bound
      vPlace pi hpi hpiIdeal D hDIntegral h k epsilon u v
        ((1 - u) / (1 - v)) hclear hu hv hratio

omit [Algebra C R] [IsScalarTower C R L] in
/-- Case (iv) connected to the exact Corvaja--Zannier auxiliary family. -/
theorem finitePlaceOrderTop_auxiliaryFamily_caseIV_source_lower_bound
    (vPlace : HeightOneSpectrum R) (pi : R) (hpi : Irreducible pi)
    (hpiIdeal : vPlace.asIdeal = Ideal.span {pi})
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
  have hden : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
  have hnum : 1 - u ≠ 0 := sub_ne_zero.mpr hu1.symm
  have hratio : (1 - u) / (1 - v) ≠ 0 := div_ne_zero hnum hden
  simpa only [dedekindLocalAuxiliaryFamily_div_eq_auxiliaryFamily] using
    finitePlaceOrderTop_indexedDedekindLocalWronskian_caseIV_source_lower_bound
      vPlace pi hpi hpiIdeal D hDIntegral h k epsilon u v
        ((1 - u) / (1 - v)) hu hv hratio

end

end BGS.CorvajaZannier
