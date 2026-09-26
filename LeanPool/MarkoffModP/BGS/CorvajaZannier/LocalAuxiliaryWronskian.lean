/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.AuxiliaryFamily
public import LeanPool.MarkoffModP.BGS.CorvajaZannier.LocalWronskian
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Local auxiliary-family Wronskian estimates

This file formalizes completion-level parts of the four local cases in the
proof of Corvaja--Zannier's Proposition 2.  The functions are Laurent series,
and every order hypothesis is stated explicitly.  No assertion is made here
about embeddings of a global function field into its completions or about
summing orders over all places.

The main new ingredients are:

* an indexed ordinary-derivative Wronskian, allowing the source's exact index
  type `Fin k ⊕ (Fin (k + 1) × Fin h)`;
* the regular-family estimate used in case (ii);
* the explicit lower-unitriangular column matrix used in case (iii), together
  with its determinant-one proof; and
* the geometric-series identity which improves the first `k` columns from
  `u ^ j * ρ` to `u ^ j * v ^ h * ρ`.

Source provenance: published pages 1935--1936; checked semantic reconstruction
`Papers/CorvajaZannier2013/CorvajaZannier2013.tex`, lines 636--732.  Case (ii)
is lines 689--691, and the case-(iii) column operation is lines 694--719.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped Matrix BigOperators

open HahnSeries LaurentSeries

variable {K : Type*} [Field K]

/-- An ordinary-derivative Wronskian whose rows and columns have an arbitrary
common finite index type.  The function `ε` specifies the derivative order of
each row. -/
def indexedLaurentSeriesWronskian {ι : Type*} [Fintype ι]
    (ε : ι → ℕ) (f : ι → LaurentSeries K) :
    Matrix ι ι (LaurentSeries K) :=
  fun i j => ((LaurentSeries.derivative K)^[ε i]) (f j)

/-- Apply a constant scalar matrix to an indexed Laurent-series family. -/
def indexedLaurentSeriesColumnCombination {ι : Type*} [Fintype ι]
    (f : ι → LaurentSeries K) (A : Matrix ι ι K) :
    ι → LaurentSeries K :=
  fun j => ∑ i, A i j • f i

private theorem indexed_derivative_iterate_sum_smul {ι : Type*} [Fintype ι]
    (r : ℕ) (a : ι → K) (f : ι → LaurentSeries K) :
    ((LaurentSeries.derivative K)^[r]) (∑ i, a i • f i) =
      ∑ i, a i • ((LaurentSeries.derivative K)^[r]) (f i) := by
  induction r with
  | zero => simp
  | succ r ih =>
      simp_rw [Function.iterate_succ_apply']
      rw [ih, map_sum]
      simp

/-- Constant column operations commute with the indexed ordinary Wronskian. -/
theorem indexedLaurentSeriesWronskian_columnCombination
    {ι : Type*} [Fintype ι]
    (ε : ι → ℕ) (f : ι → LaurentSeries K) (A : Matrix ι ι K) :
    indexedLaurentSeriesWronskian ε
        (indexedLaurentSeriesColumnCombination f A) =
      indexedLaurentSeriesWronskian ε f *
        A.map (algebraMap K (LaurentSeries K)) := by
  classical
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  simp only [indexedLaurentSeriesWronskian,
    indexedLaurentSeriesColumnCombination, Matrix.map_apply]
  rw [indexed_derivative_iterate_sum_smul]
  have halgebraMap (a : K) :
      algebraMap K (LaurentSeries K) a = HahnSeries.single 0 a := by
    change ((algebraMap K (PowerSeries K) a : PowerSeries K) :
      LaurentSeries K) = HahnSeries.single 0 a
    rw [← PowerSeries.C_eq_algebraMap, PowerSeries.coe_C]
    rfl
  have hscalar (a : K) (x : LaurentSeries K) :
      a • x = algebraMap K (LaurentSeries K) a * x := by
    rw [halgebraMap]
    exact HahnSeries.single_zero_mul_eq_smul.symm
  simp_rw [hscalar]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- A determinant-one constant column operation preserves an indexed local
Wronskian determinant. -/
theorem indexedLaurentSeriesWronskian_det_columnCombination_of_det_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℕ) (f : ι → LaurentSeries K) (A : Matrix ι ι K)
    (hA : A.det = 1) :
    (indexedLaurentSeriesWronskian ε
      (indexedLaurentSeriesColumnCombination f A)).det =
        (indexedLaurentSeriesWronskian ε f).det := by
  rw [indexedLaurentSeriesWronskian_columnCombination, Matrix.det_mul]
  have hdetmap :
      (A.map (algebraMap K (LaurentSeries K))).det = 1 := by
    calc
      (A.map (algebraMap K (LaurentSeries K))).det =
          algebraMap K (LaurentSeries K) A.det := by
        simpa using ((algebraMap K (LaurentSeries K)).map_det A).symm
      _ = 1 := by rw [hA, map_one]
  rw [hdetmap, mul_one]

private theorem indexed_addVal_prod {ι : Type*}
    (s : Finset ι) (g : ι → LaurentSeries K) :
    HahnSeries.addVal ℤ K (∏ i ∈ s, g i) =
      ∑ i ∈ s, HahnSeries.addVal ℤ K (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, AddValuation.map_mul]

private theorem indexed_coe_sum_int_finset {ι : Type*}
    (s : Finset ι) (g : ι → ℤ) :
    (((∑ i ∈ s, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i ∈ s, ((g i : ℤ) : WithTop ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, WithTop.coe_add]

private theorem indexed_coe_sum_int {ι : Type*} [Fintype ι] (g : ι → ℤ) :
    (((∑ i, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i, ((g i : ℤ) : WithTop ℤ) := by
  classical
  exact indexed_coe_sum_int_finset Finset.univ g

/-- The indexed ordinary Wronskian has order at least the sum of its column
orders minus the sum of its row derivative orders. -/
theorem orderTop_indexedLaurentSeriesWronskian_det_lower_bound
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℕ) (f : ι → LaurentSeries K) :
    (((∑ j, (f j).order) - ∑ i, (ε i : ℤ) : ℤ) : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian ε f).det.orderTop := by
  rw [Matrix.det_apply]
  change (((∑ j, (f j).order) - ∑ i, (ε i : ℤ) : ℤ) : WithTop ℤ) ≤
    HahnSeries.addVal ℤ K
      (∑ σ, Equiv.Perm.sign σ •
        ∏ i, indexedLaurentSeriesWronskian ε f (σ i) i)
  apply AddValuation.map_le_sum
  intro σ _
  calc
    (((∑ j, (f j).order) - ∑ i, (ε i : ℤ) : ℤ) : WithTop ℤ) =
        ∑ j, (((f j).order - (ε (σ j) : ℤ) : ℤ) : WithTop ℤ) := by
          rw [← Equiv.sum_comp σ (fun i => (ε i : ℤ))]
          rw [← indexed_coe_sum_int]
          congr 1
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j,
        ((((LaurentSeries.derivative K)^[ε (σ j)]) (f j)).orderTop) := by
      gcongr with j
      exact order_sub_le_orderTop_derivative_iterate (ε (σ j)) (f j)
    _ = (∏ i, indexedLaurentSeriesWronskian ε f (σ i) i).orderTop := by
      rw [← HahnSeries.addVal_apply, indexed_addVal_prod]
      simp only [HahnSeries.addVal_apply]
      rfl
    _ ≤ (Equiv.Perm.sign σ •
        ∏ i, indexedLaurentSeriesWronskian ε f (σ i) i).orderTop := by
      exact orderTop_le_orderTop_smul _ _

/-- Ordinary differentiation preserves Laurent-series integrality. -/
theorem orderTop_derivative_iterate_nonnegative_of_order_nonnegative
    (r : ℕ) (f : LaurentSeries K) (hf : 0 ≤ f.order) :
    (0 : WithTop ℤ) ≤ (((LaurentSeries.derivative K)^[r]) f).orderTop := by
  rw [le_orderTop_iff_forall]
  intro j hj
  rw [LaurentSeries.derivative_iterate_coeff]
  by_cases hsum : j + (r : ℤ) < 0
  · rw [coeff_eq_zero_of_lt_order (hsum.trans_le hf), smul_zero]
  · have hnonneg : 0 ≤ j + (r : ℤ) := le_of_not_gt hsum
    obtain ⟨m, hm⟩ := Int.eq_ofNat_of_zero_le hnonneg
    have hj' : j < 0 := by exact_mod_cast hj
    have hm_lt_int : (m : ℤ) < (r : ℤ) := by omega
    have hm_lt : m < r := by exact_mod_cast hm_lt_int
    rw [hm, Polynomial.descPochhammer_smeval_eq_descFactorial]
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hm_lt, Nat.cast_zero, zero_smul]

/-- Case (ii), at the completion level: if every column is regular, then the
ordinary-derivative Wronskian determinant is regular. -/
theorem orderTop_indexedLaurentSeriesWronskian_det_nonnegative_of_regular
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ε : ι → ℕ) (f : ι → LaurentSeries K)
    (hf : ∀ i, 0 ≤ (f i).order) :
    (0 : WithTop ℤ) ≤ (indexedLaurentSeriesWronskian ε f).det.orderTop := by
  rw [Matrix.det_apply]
  change (0 : WithTop ℤ) ≤ HahnSeries.addVal ℤ K
    (∑ σ, Equiv.Perm.sign σ •
      ∏ i, indexedLaurentSeriesWronskian ε f (σ i) i)
  apply AddValuation.map_le_sum
  intro σ _
  calc
    (0 : WithTop ℤ) = ∑ _i : ι, (0 : WithTop ℤ) := by simp
    _ ≤ ∑ i,
        (((LaurentSeries.derivative K)^[ε (σ i)]) (f i)).orderTop := by
      gcongr with i
      exact orderTop_derivative_iterate_nonnegative_of_order_nonnegative
        (ε (σ i)) (f i) (hf i)
    _ = (∏ i, indexedLaurentSeriesWronskian ε f (σ i) i).orderTop := by
      rw [← HahnSeries.addVal_apply, indexed_addVal_prod]
      simp only [HahnSeries.addVal_apply]
      rfl
    _ ≤ (Equiv.Perm.sign σ •
        ∏ i, indexedLaurentSeriesWronskian ε f (σ i) i).orderTop := by
      exact orderTop_le_orderTop_smul _ _

/-- Case (ii) connected to the exact auxiliary family.  Outside the support
of `u` and `v`, both have order zero; if the ratio `(1-u)/(1-v)` is regular,
then every auxiliary column is regular and so is its Wronskian determinant. -/
theorem orderTop_auxiliaryFamily_caseII_nonnegative
    (h k : ℕ) (ε : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : LaurentSeries K)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1)
    (huOrder : u.order = 0) (hvOrder : v.order = 0)
    (hratio : 0 ≤ ((1 - u) / (1 - v)).order) :
    (0 : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian ε
        (auxiliaryFamily u v h k)).det.orderTop := by
  apply orderTop_indexedLaurentSeriesWronskian_det_nonnegative_of_regular
  intro i
  have hnum : 1 - u ≠ 0 := sub_ne_zero.mpr hu1.symm
  have hden : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
  have hratio0 : (1 - u) / (1 - v) ≠ 0 := div_ne_zero hnum hden
  cases i with
  | inl i =>
      change 0 ≤ (u ^ (i : ℕ) * ((1 - u) / (1 - v))).order
      rw [HahnSeries.order_mul (pow_ne_zero _ hu0) hratio0,
        HahnSeries.order_pow, huOrder]
      simpa using hratio
  | inr rs =>
      change 0 ≤ (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)).order
      rw [HahnSeries.order_mul (pow_ne_zero _ hu0) (pow_ne_zero _ hv0),
        HahnSeries.order_pow, HahnSeries.order_pow, huOrder, hvOrder]
      simp

/-- The lower-left block of the case-(iii) column operation.  For each first
column `i`, it subtracts every grid column `(i,s)` and adds every grid column
`(i+1,s)`. -/
def caseIIIGridCorrection (h k : ℕ) :
    Matrix (Fin (k + 1) × Fin h) (Fin k) K :=
  fun rs i =>
    if rs.1 = i.castSucc then -1
    else if rs.1 = i.succ then 1
    else 0

/-- The exact lower-unitriangular constant column matrix used in case (iii). -/
def caseIIIColumnMatrix (h k : ℕ) :
    Matrix (Sum (Fin k) (Fin (k + 1) × Fin h))
      (Sum (Fin k) (Fin (k + 1) × Fin h)) K :=
  Matrix.fromBlocks 1 0 (caseIIIGridCorrection h k) 1

/-- The case-(iii) column matrix has determinant one. -/
theorem caseIIIColumnMatrix_det (h k : ℕ) :
    (caseIIIColumnMatrix (K := K) h k).det = 1 := by
  rw [caseIIIColumnMatrix, Matrix.det_fromBlocks_zero₁₂]
  simp

/-- The geometric-series identity behind the case-(iii) column operation.
The hypothesis is the denominator-cleared identity `(1-v)ρ = 1-u`. -/
theorem caseIII_geometricSeries_column_identity
    (u v ρ : LaurentSeries K) (h j : ℕ)
    (hρ : (1 - v) * ρ = 1 - u) :
    u ^ j * ρ - u ^ j * (1 - u) * (∑ s ∈ Finset.range h, v ^ s) =
      u ^ j * v ^ h * ρ := by
  rw [← hρ]
  calc
    u ^ j * ρ - u ^ j * ((1 - v) * ρ) *
        (∑ s ∈ Finset.range h, v ^ s) =
        u ^ j * ρ - u ^ j * ρ *
          ((1 - v) * ∑ s ∈ Finset.range h, v ^ s) := by ring
    _ = u ^ j * ρ - u ^ j * ρ * (1 - v ^ h) := by
      rw [mul_neg_geom_sum]
    _ = u ^ j * v ^ h * ρ := by ring

/-- The source auxiliary family written with `ρ` as an explicit parameter.
This separates the local column algebra from the later specialization
`ρ = (1-u)/(1-v)`. -/
def localAuxiliaryFamily (u v ρ : LaurentSeries K) (h k : ℕ) :
    Sum (Fin k) (Fin (k + 1) × Fin h) → LaurentSeries K
  | Sum.inl i => u ^ (i : ℕ) * ρ
  | Sum.inr rs => u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)

/-- Specializing the explicit ratio parameter recovers the auxiliary family
from `AuxiliaryFamily`. -/
@[simp]
theorem localAuxiliaryFamily_div_eq_auxiliaryFamily
    (u v : LaurentSeries K) (h k : ℕ) :
    localAuxiliaryFamily u v ((1 - u) / (1 - v)) h k =
      auxiliaryFamily u v h k := by
  rfl

/-- The case-(iii) family after replacing its first `k` columns. -/
def caseIIIImprovedAuxiliaryFamily (u v ρ : LaurentSeries K) (h k : ℕ) :
    Sum (Fin k) (Fin (k + 1) × Fin h) → LaurentSeries K
  | Sum.inl i => u ^ (i : ℕ) * v ^ h * ρ
  | Sum.inr rs => u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)

private theorem caseIIIGridCorrection_sum_smul
    (u v : LaurentSeries K) (h k : ℕ) (i : Fin k) :
    (∑ rs : Fin (k + 1) × Fin h,
        caseIIIGridCorrection (K := K) h k rs i •
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
        (if r = i.castSucc then (-1 : K)
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

/-- The explicit determinant-one matrix performs exactly the column
replacement from case (iii). -/
theorem indexedColumnCombination_caseIIIColumnMatrix
    (u v ρ : LaurentSeries K) (h k : ℕ)
    (hρ : (1 - v) * ρ = 1 - u) :
    indexedLaurentSeriesColumnCombination (localAuxiliaryFamily u v ρ h k)
        (caseIIIColumnMatrix (K := K) h k) =
      caseIIIImprovedAuxiliaryFamily u v ρ h k := by
  classical
  funext j
  cases j with
  | inl i =>
      rw [indexedLaurentSeriesColumnCombination, Fintype.sum_sum_type]
      simp only [caseIIIColumnMatrix, Matrix.fromBlocks_apply₁₁,
        Matrix.fromBlocks_apply₂₁, localAuxiliaryFamily,
        caseIIIImprovedAuxiliaryFamily]
      have hleft :
          (∑ x : Fin k, (1 : Matrix (Fin k) (Fin k) K) x i •
            (u ^ (x : ℕ) * ρ)) = u ^ (i : ℕ) * ρ := by
        simp [Matrix.one_apply]
      rw [hleft]
      rw [caseIIIGridCorrection_sum_smul]
      rw [Fin.sum_univ_eq_sum_range]
      simp only [Fin.val_succ, pow_succ]
      convert caseIII_geometricSeries_column_identity u v ρ h (i : ℕ) hρ using 1;
        ring
  | inr rs =>
      rw [indexedLaurentSeriesColumnCombination, Fintype.sum_sum_type]
      simp [caseIIIColumnMatrix, localAuxiliaryFamily,
        caseIIIImprovedAuxiliaryFamily, Matrix.one_apply]

/-- Case (iii), completion-level determinant identity: the Wronskian is
unchanged after replacing `u^j ρ` by `u^j v^h ρ` in its first `k` columns. -/
theorem indexedWronskian_det_caseIII_columnReplacement
    (h k : ℕ) (ε : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v ρ : LaurentSeries K)
    (hρ : (1 - v) * ρ = 1 - u) :
    (indexedLaurentSeriesWronskian ε
      (caseIIIImprovedAuxiliaryFamily u v ρ h k)).det =
        (indexedLaurentSeriesWronskian ε
          (localAuxiliaryFamily u v ρ h k)).det := by
  rw [← indexedColumnCombination_caseIIIColumnMatrix u v ρ h k hρ]
  exact indexedLaurentSeriesWronskian_det_columnCombination_of_det_eq_one
    ε (localAuxiliaryFamily u v ρ h k) (caseIIIColumnMatrix h k)
      (caseIIIColumnMatrix_det h k)

/-- Case (iii), completion-level order estimate after the exact source column
replacement.  The right side retains the column orders explicitly; evaluating
those orders from `ν(u)`, `ν(v)`, and `ν(ρ)` is a separate elementary step. -/
theorem orderTop_indexedWronskian_det_caseIII_lower_bound
    (h k : ℕ) (ε : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v ρ : LaurentSeries K)
    (hρ : (1 - v) * ρ = 1 - u) :
    (((∑ j, (caseIIIImprovedAuxiliaryFamily u v ρ h k j).order) -
        ∑ i, (ε i : ℤ) : ℤ) : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian ε
        (localAuxiliaryFamily u v ρ h k)).det.orderTop := by
  rw [← indexedWronskian_det_caseIII_columnReplacement h k ε u v ρ hρ]
  exact orderTop_indexedLaurentSeriesWronskian_det_lower_bound ε
    (caseIIIImprovedAuxiliaryFamily u v ρ h k)

private theorem order_caseIIIImprovedAuxiliaryFamily_inl
    (u v ρ : LaurentSeries K) (h k : ℕ) (i : Fin k)
    (hu : u ≠ 0) (hv : v ≠ 0) (hρ0 : ρ ≠ 0) :
    (caseIIIImprovedAuxiliaryFamily u v ρ h k (Sum.inl i)).order =
      (i : ℕ) • u.order + h • v.order + ρ.order := by
  simp only [caseIIIImprovedAuxiliaryFamily]
  rw [HahnSeries.order_mul
      (mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)) hρ0,
    HahnSeries.order_mul (pow_ne_zero _ hu) (pow_ne_zero _ hv),
    HahnSeries.order_pow, HahnSeries.order_pow]

private theorem order_localAuxiliaryFamily_inl
    (u v ρ : LaurentSeries K) (h k : ℕ) (i : Fin k)
    (hu : u ≠ 0) (hρ0 : ρ ≠ 0) :
    (localAuxiliaryFamily u v ρ h k (Sum.inl i)).order =
      (i : ℕ) • u.order + ρ.order := by
  simp only [localAuxiliaryFamily]
  rw [HahnSeries.order_mul (pow_ne_zero _ hu) hρ0,
    HahnSeries.order_pow]

private theorem sum_fin_cast_int (k : ℕ) :
    (∑ i : Fin k, (i : ℤ)) = (k * (k - 1) / 2 : ℕ) := by
  rw [Fin.sum_univ_eq_sum_range, ← Nat.cast_sum, Finset.sum_range_id]

private theorem sum_caseIIIImprovedAuxiliaryFamily_inl_orders
    (u v ρ : LaurentSeries K) (h k : ℕ)
    (hu : u ≠ 0) (hv : v ≠ 0) (hρ0 : ρ ≠ 0) :
    (∑ i : Fin k,
        (caseIIIImprovedAuxiliaryFamily u v ρ h k (Sum.inl i)).order) =
      (k * (k - 1) / 2 : ℕ) • u.order +
        (h * k) • v.order + k • ρ.order := by
  simp_rw [order_caseIIIImprovedAuxiliaryFamily_inl u v ρ h k _ hu hv hρ0]
  simp only [Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin]
  simp_rw [nsmul_eq_mul]
  rw [← Finset.sum_mul]
  rw [sum_fin_cast_int]
  simp only [Nat.cast_mul]
  ring

private theorem sum_localAuxiliaryFamily_inl_orders
    (u v ρ : LaurentSeries K) (h k : ℕ)
    (hu : u ≠ 0) (hρ0 : ρ ≠ 0) :
    (∑ i : Fin k,
        (localAuxiliaryFamily u v ρ h k (Sum.inl i)).order) =
      (k * (k - 1) / 2 : ℕ) • u.order + k • ρ.order := by
  simp_rw [order_localAuxiliaryFamily_inl u v ρ h k _ hu hρ0]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  simp_rw [nsmul_eq_mul]
  rw [← Finset.sum_mul, sum_fin_cast_int]

/-- Case (iii) in the displayed source form.  The grid-column contribution is
left as the exact sum appearing in the paper; it is the part that cancels by
the global product formula after summing over places. -/
theorem orderTop_indexedWronskian_det_caseIII_source_lower_bound
    (h k : ℕ) (ε : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v ρ : LaurentSeries K)
    (hρ : (1 - v) * ρ = 1 - u)
    (hu : u ≠ 0) (hv : v ≠ 0) (hρ0 : ρ ≠ 0) :
    (((k * (k - 1) / 2 : ℕ) • u.order +
          (h * k) • v.order + k • ρ.order +
          ∑ rs : Fin (k + 1) × Fin h,
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)).order -
          ∑ i, (ε i : ℤ) : ℤ) : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian ε
        (localAuxiliaryFamily u v ρ h k)).det.orderTop := by
  have hbound := orderTop_indexedWronskian_det_caseIII_lower_bound
    h k ε u v ρ hρ
  rw [Fintype.sum_sum_type] at hbound
  rw [sum_caseIIIImprovedAuxiliaryFamily_inl_orders u v ρ h k hu hv hρ0]
    at hbound
  exact hbound

/-- Case (iv), completion-level displayed source estimate: no column operation
is made, so the first `k` columns contribute the triangular `u` term and the
`kρ` term directly. -/
theorem orderTop_indexedWronskian_det_caseIV_source_lower_bound
    (h k : ℕ) (ε : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v ρ : LaurentSeries K) (hu : u ≠ 0) (hρ0 : ρ ≠ 0) :
    (((k * (k - 1) / 2 : ℕ) • u.order + k • ρ.order +
          ∑ rs : Fin (k + 1) × Fin h,
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)).order -
          ∑ i, (ε i : ℤ) : ℤ) : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian ε
        (localAuxiliaryFamily u v ρ h k)).det.orderTop := by
  have hbound := orderTop_indexedLaurentSeriesWronskian_det_lower_bound ε
    (localAuxiliaryFamily u v ρ h k)
  rw [Fintype.sum_sum_type] at hbound
  rw [sum_localAuxiliaryFamily_inl_orders u v ρ h k hu hρ0] at hbound
  exact hbound

/-- Case (iii) connected to the exact auxiliary family defined earlier in the
formalization.  The hypotheses `u ≠ 1` and `v ≠ 1` ensure that the ratio column
is nonzero and that clearing its denominator is sound. -/
theorem orderTop_auxiliaryFamily_caseIII_source_lower_bound
    (h k : ℕ) (ε : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : LaurentSeries K)
    (hu0 : u ≠ 0) (hv0 : v ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) • u.order +
          (h * k) • v.order +
          k • ((1 - u) / (1 - v)).order +
          ∑ rs : Fin (k + 1) × Fin h,
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)).order -
          ∑ i, (ε i : ℤ) : ℤ) : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian ε
        (auxiliaryFamily u v h k)).det.orderTop := by
  have hden : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
  have hnum : 1 - u ≠ 0 := sub_ne_zero.mpr hu1.symm
  have hratio : (1 - u) / (1 - v) ≠ 0 := div_ne_zero hnum hden
  have hclear : (1 - v) * ((1 - u) / (1 - v)) = 1 - u := by
    field_simp
  simpa only [localAuxiliaryFamily_div_eq_auxiliaryFamily] using
    orderTop_indexedWronskian_det_caseIII_source_lower_bound
      h k ε u v ((1 - u) / (1 - v)) hclear hu0 hv0 hratio

/-- Case (iv) connected to the exact auxiliary family. -/
theorem orderTop_auxiliaryFamily_caseIV_source_lower_bound
    (h k : ℕ) (ε : Sum (Fin k) (Fin (k + 1) × Fin h) → ℕ)
    (u v : LaurentSeries K) (hu0 : u ≠ 0) (hu1 : u ≠ 1) (hv1 : v ≠ 1) :
    (((k * (k - 1) / 2 : ℕ) • u.order +
          k • ((1 - u) / (1 - v)).order +
          ∑ rs : Fin (k + 1) × Fin h,
            (u ^ (rs.1 : ℕ) * v ^ (rs.2 : ℕ)).order -
          ∑ i, (ε i : ℤ) : ℤ) : WithTop ℤ) ≤
      (indexedLaurentSeriesWronskian ε
        (auxiliaryFamily u v h k)).det.orderTop := by
  have hden : 1 - v ≠ 0 := sub_ne_zero.mpr hv1.symm
  have hnum : 1 - u ≠ 0 := sub_ne_zero.mpr hu1.symm
  have hratio : (1 - u) / (1 - v) ≠ 0 := div_ne_zero hnum hden
  simpa only [localAuxiliaryFamily_div_eq_auxiliaryFamily] using
    orderTop_indexedWronskian_det_caseIV_source_lower_bound
      h k ε u v ((1 - u) / (1 - v)) hu0 hratio

end

end BGS.CorvajaZannier
