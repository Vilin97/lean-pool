/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.CorvajaZannier.LocalDerivative
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.HahnSeries.Valuation

/-!
# Local Wronskian order estimates

After choosing a local parameter, the Corvaja--Zannier Wronskian becomes a
Wronskian of Laurent series.  This file proves the determinant-level local
estimate: the order of an `n × n` ordinary Wronskian is at least the sum of
the column orders minus `n * (n - 1) / 2`.

The theorem uses `orderTop`, so it also covers a vanishing determinant.  It is
the completion-level inequality in the source argument; embedding a curve's
function field in these completions and summing the resulting orders remain
separate global geometric obligations.
-/

@[expose] public section

namespace BGS.CorvajaZannier

noncomputable section

open scoped Matrix BigOperators

open HahnSeries LaurentSeries

variable {K : Type*} [Field K]

/-- The ordinary Wronskian matrix of Laurent series with respect to the local
parameter. -/
def laurentSeriesWronskian {n : ℕ} (f : Fin n → LaurentSeries K) :
    Matrix (Fin n) (Fin n) (LaurentSeries K) :=
  fun i j ↦ ((LaurentSeries.derivative K)^[i.1]) (f j)

/-- Apply a constant scalar matrix to the columns of a Laurent-series family. -/
def laurentSeriesColumnCombination {n : ℕ}
    (f : Fin n → LaurentSeries K) (A : Matrix (Fin n) (Fin n) K) :
    Fin n → LaurentSeries K :=
  fun j ↦ ∑ i, A i j • f i

private theorem derivative_iterate_sum_smul {ι : Type*} [Fintype ι]
    (r : ℕ) (a : ι → K) (f : ι → LaurentSeries K) :
    ((LaurentSeries.derivative K)^[r]) (∑ i, a i • f i) =
      ∑ i, a i • ((LaurentSeries.derivative K)^[r]) (f i) := by
  induction r with
  | zero => simp
  | succ r ih =>
      simp_rw [Function.iterate_succ_apply']
      rw [ih, map_sum]
      simp

/-- A constant change of columns commutes with formation of the local
Wronskian. -/
theorem laurentSeriesWronskian_columnCombination {n : ℕ}
    (f : Fin n → LaurentSeries K) (A : Matrix (Fin n) (Fin n) K) :
    laurentSeriesWronskian (laurentSeriesColumnCombination f A) =
      laurentSeriesWronskian f * A.map (algebraMap K (LaurentSeries K)) := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  simp only [laurentSeriesWronskian, laurentSeriesColumnCombination,
    Matrix.map_apply]
  rw [derivative_iterate_sum_smul]
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
  intro k _
  exact mul_comm _ _

/-- A determinant-one constant column operation leaves the local Wronskian
determinant unchanged.  This is the formal column-operation principle used in
the source's local cases. -/
theorem laurentSeriesWronskian_det_columnCombination_of_det_eq_one {n : ℕ}
    (f : Fin n → LaurentSeries K) (A : Matrix (Fin n) (Fin n) K)
    (hA : A.det = 1) :
    (laurentSeriesWronskian (laurentSeriesColumnCombination f A)).det =
      (laurentSeriesWronskian f).det := by
  rw [laurentSeriesWronskian_columnCombination, Matrix.det_mul]
  have hdetmap :
      (A.map (algebraMap K (LaurentSeries K))).det = 1 := by
    calc
      (A.map (algebraMap K (LaurentSeries K))).det =
          algebraMap K (LaurentSeries K) A.det := by
        simpa using ((algebraMap K (LaurentSeries K)).map_det A).symm
      _ = 1 := by rw [hA, map_one]
  rw [hdetmap, mul_one]

private theorem addVal_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → LaurentSeries K) :
    HahnSeries.addVal ℤ K (∏ i ∈ s, g i) =
      ∑ i ∈ s, HahnSeries.addVal ℤ K (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, AddValuation.map_mul]

private theorem coe_sum_int_finset {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (g : ι → ℤ) :
    (((∑ i ∈ s, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i ∈ s, ((g i : ℤ) : WithTop ℤ) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih, WithTop.coe_add]

private theorem coe_sum_int {ι : Type*} [Fintype ι] (g : ι → ℤ) :
    (((∑ i, g i : ℤ) : ℤ) : WithTop ℤ) =
      ∑ i, ((g i : ℤ) : WithTop ℤ) := by
  classical
  exact coe_sum_int_finset Finset.univ g

/-- Before evaluating the triangular number, the local Wronskian determinant
has order at least the sum of the column orders minus the sum of the derivative
orders `0, ..., n - 1`. -/
theorem orderTop_laurentSeriesWronskian_det_lower_bound {n : ℕ}
    (f : Fin n → LaurentSeries K) :
    (((∑ j, (f j).order) - ∑ j : Fin n, (j : ℤ) : ℤ) : WithTop ℤ) ≤
      (laurentSeriesWronskian f).det.orderTop := by
  rw [Matrix.det_apply]
  change (((∑ j, (f j).order) - ∑ j : Fin n, (j : ℤ) : ℤ) : WithTop ℤ) ≤
    HahnSeries.addVal ℤ K
      (∑ σ, Equiv.Perm.sign σ • ∏ i, laurentSeriesWronskian f (σ i) i)
  apply AddValuation.map_le_sum
  intro σ _
  calc
    (((∑ j, (f j).order) - ∑ j : Fin n, (j : ℤ) : ℤ) : WithTop ℤ) =
        ∑ j : Fin n, (((f j).order - (σ j : ℕ) : ℤ) : WithTop ℤ) := by
          rw [← Equiv.sum_comp σ (fun j : Fin n ↦ (j : ℤ))]
          rw [← coe_sum_int]
          congr 1
          rw [Finset.sum_sub_distrib]
    _ ≤ ∑ j : Fin n,
        ((((LaurentSeries.derivative K)^[((σ j : Fin n) : ℕ)])
          (f j)).orderTop) := by
      gcongr with j
      exact order_sub_le_orderTop_derivative_iterate
        ((σ j : Fin n) : ℕ) (f j)
    _ = (∏ i, laurentSeriesWronskian f (σ i) i).orderTop := by
      rw [← HahnSeries.addVal_apply, addVal_prod]
      simp only [HahnSeries.addVal_apply]
      rfl
    _ ≤ (Equiv.Perm.sign σ •
        ∏ i, laurentSeriesWronskian f (σ i) i).orderTop := by
      exact orderTop_le_orderTop_smul _ _

/-- The local Wronskian determinant loses at most the triangular number
`n * (n - 1) / 2` from the sum of its column orders. -/
theorem orderTop_laurentSeriesWronskian_det_lower_bound_closed {n : ℕ}
    (f : Fin n → LaurentSeries K) :
    (((∑ j, (f j).order) - (n * (n - 1) / 2 : ℕ) : ℤ) : WithTop ℤ) ≤
      (laurentSeriesWronskian f).det.orderTop := by
  convert orderTop_laurentSeriesWronskian_det_lower_bound f using 1
  congr 1
  apply congrArg (fun x : ℤ ↦ (∑ j, (f j).order) - x)
  rw [Fin.sum_univ_eq_sum_range]
  rw [← Nat.cast_sum]
  exact congrArg (fun x : ℕ ↦ (x : ℤ)) (Finset.sum_range_id n).symm

/-- The determinant order can be estimated after any determinant-one constant
column operation.  This is the form used when the source separates repeated
pole orders or replaces columns by better local approximations. -/
theorem orderTop_laurentSeriesWronskian_det_lower_bound_after_columnCombination
    {n : ℕ} (f : Fin n → LaurentSeries K)
    (A : Matrix (Fin n) (Fin n) K) (hA : A.det = 1) :
    (((∑ j, (laurentSeriesColumnCombination f A j).order) -
        (n * (n - 1) / 2 : ℕ) : ℤ) : WithTop ℤ) ≤
      (laurentSeriesWronskian f).det.orderTop := by
  rw [← laurentSeriesWronskian_det_columnCombination_of_det_eq_one f A hA]
  exact orderTop_laurentSeriesWronskian_det_lower_bound_closed
    (laurentSeriesColumnCombination f A)

end

end BGS.CorvajaZannier
