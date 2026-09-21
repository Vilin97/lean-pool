/-
Copyright (c) 2026 Christopher Albert. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Albert
-/

import Mathlib

/-!
# Retraction correction and power-series specialization

This file contains only elementary algebra intended for use in a future
formalization of the asymptotic-conormal argument. In particular, it does not formalize a DVR,
normalization, a Grassmannian limit, or coisotropy.  The useful point is that
the two algebraic operations needed by that argument are explicit:

* a left inverse for a column matrix gives an annihilator by a retraction;
* taking the residue of a power series commutes with polynomial evaluation.

The last theorem records the resulting polynomial-specialization
contradiction for an arbitrary variable type and arbitrary specialization
vector.
-/

namespace Stafford38.GeometryRetractionSpecialization

noncomputable section

universe u v w

/-! ## Rows, columns, and the explicit retraction correction -/

variable {R : Type u} [CommRing R]

/-- A row vector multiplied by a matrix on the right. -/
def rowMul {ι κ : Type*} [Fintype ι] (a : ι → R) (B : Matrix ι κ R) : κ → R :=
  fun j => ∑ i, a i * B i j

theorem rowMul_mul {ι κ μ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → R) (B : Matrix ι κ R) (C : Matrix κ μ R) :
    rowMul (rowMul a B) C = rowMul a (B * C) := by
  funext j
  simp only [rowMul, Matrix.mul_apply]
  calc
    (∑ x, (∑ i, a i * B i x) * C x j) =
        ∑ x, ∑ i, (a i * B i x) * C x j := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_mul]
    _ = ∑ i, ∑ x, (a i * B i x) * C x j := Finset.sum_comm
    _ = ∑ i, a i * (∑ x, B i x * C x j) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x hx
          ring

theorem map_rowMul {S : Type v} [CommRing S]
    {ι κ : Type*} [Fintype ι] (f : R →+* S)
    (a : ι → R) (B : Matrix ι κ R) (j : κ) :
    f (rowMul a B j) =
      rowMul (fun i => f (a i)) (fun i l => f (B i l)) j := by
  simp [rowMul]

theorem rowMul_sub {ι κ : Type*} [Fintype ι]
    (a b : ι → R) (B : Matrix ι κ R) :
    rowMul (fun i => a i - b i) B =
      fun j => rowMul a B j - rowMul b B j := by
  funext j
  simp [rowMul, Finset.sum_sub_distrib, sub_mul]

theorem rowMul_zero {ι κ : Type*} [Fintype ι]
    (B : Matrix ι κ R) : rowMul (fun _ => (0 : R)) B = 0 := by
  funext j
  simp [rowMul]

/--
The retraction correction for a row `a` and a column matrix `B`.

If `C * B = 1`, then `C` is a coordinate retraction on the columns of `B`.
The displayed subtraction is the usual projection onto the annihilator of
those columns.
-/
def annihilatorLift {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → R) (B : Matrix ι κ R) (C : Matrix κ ι R) : ι → R :=
  fun i => a i - rowMul (rowMul a B) C i

theorem annihilatorLift_rowMul_eq_zero {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (a : ι → R) (B : Matrix ι κ R) (C : Matrix κ ι R)
    (hCB : C * B = 1) :
    rowMul (annihilatorLift a B C) B = 0 := by
  change rowMul (fun i => a i - rowMul (rowMul a B) C i) B = 0
  rw [rowMul_sub]
  rw [rowMul_mul, rowMul_mul]
  rw [hCB, Matrix.mul_one]
  exact funext (fun j => sub_self (rowMul a B j))

theorem map_annihilatorLift {S : Type v} [CommRing S]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : R →+* S) (a : ι → R) (B : Matrix ι κ R) (C : Matrix κ ι R) (i : ι) :
    f (annihilatorLift a B C i) =
      annihilatorLift (fun j => f (a j))
        (fun j l => f (B j l)) (fun l j => f (C l j)) i := by
  simp only [annihilatorLift, map_sub]
  rw [map_rowMul f (rowMul a B) C i]
  have hinner :
      rowMul (fun j => f (rowMul a B j)) (fun l j => f (C l j)) i =
        rowMul (rowMul (fun j => f (a j)) (fun j l => f (B j l)))
          (fun l j => f (C l j)) i := by
    apply congrArg (fun z => rowMul z (fun l j => f (C l j)) i)
    funext j
    exact map_rowMul f a B j
  exact congrArg (fun z => f (a i) - z) hinner

/--
Explicit residue-preserving annihilator lift.

The input row is any coefficientwise lift of the residue row. The correction
preserves that residue whenever the residue row annihilates the reduced
columns. Exact annihilation is supplied separately by
`annihilatorLift_rowMul_eq_zero` under the hypothesis `C * B = 1`.
-/
theorem residue_annihilatorLift_eq
    {S : Type v} [CommRing S]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (f : R →+* S) (a : ι → R) (a₀ : ι → S)
    (B : Matrix ι κ R) (C : Matrix κ ι R)
    (ha : ∀ i, f (a i) = a₀ i)
    (h₀ : rowMul a₀ (fun i j => f (B i j)) = 0) :
    ∀ i, f (annihilatorLift a B C i) = a₀ i := by
  intro i
  rw [map_annihilatorLift]
  simp only [annihilatorLift, ha]
  rw [h₀]
  simp [rowMul]

/-! ## Power-series columns and residue -/

/-- A column with entries in a one-variable formal power-series ring. -/
abbrev PowerSeriesColumn (k : Type*) (ι : Type*) := ι → PowerSeries k

def residueColumn {k : Type*} [CommRing k] {ι : Type*}
    (a : PowerSeriesColumn k ι) : ι → k :=
  fun i => PowerSeries.constantCoeff (a i)

def constantColumn {k : Type*} [CommRing k] {ι : Type*}
    (a : ι → k) : PowerSeriesColumn k ι :=
  fun i => PowerSeries.C (a i)

@[simp] theorem residueColumn_constantColumn {k : Type*} [CommRing k] {ι : Type*}
    (a : ι → k) : residueColumn (constantColumn a) = a := by
  funext i
  simp [residueColumn, constantColumn]

theorem powerSeries_annihilatorLift_rowMul_eq_zero
    {k : Type*} [CommRing k] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (a : PowerSeriesColumn k ι) (B : Matrix ι κ (PowerSeries k))
    (C : Matrix κ ι (PowerSeries k)) (hCB : C * B = 1) :
    rowMul (annihilatorLift a B C) B = 0 :=
  annihilatorLift_rowMul_eq_zero a B C hCB

theorem residue_powerSeries_annihilatorLift_eq
    {k : Type*} [CommRing k] {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : PowerSeriesColumn k ι) (a₀ : ι → k)
    (B : Matrix ι κ (PowerSeries k)) (C : Matrix κ ι (PowerSeries k))
    (ha : residueColumn a = a₀)
    (h₀ : rowMul a₀ (fun i j => PowerSeries.constantCoeff (B i j)) = 0) :
    ∀ i, residueColumn (annihilatorLift a B C) i = a₀ i := by
  apply residue_annihilatorLift_eq PowerSeries.constantCoeff a a₀ B C
  · intro i
    simpa [residueColumn] using congrFun ha i
  · simpa [residueColumn] using h₀

/-- A split column matrix admits a corrected row which both annihilates the
matrix and retains the prescribed residue. -/
theorem powerSeries_annihilatorLift_spec
    {k : Type*} [CommRing k] {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (a : PowerSeriesColumn k ι) (a₀ : ι → k)
    (B : Matrix ι κ (PowerSeries k)) (C : Matrix κ ι (PowerSeries k))
    (hCB : C * B = 1) (ha : residueColumn a = a₀)
    (h₀ : rowMul a₀ (fun i j => PowerSeries.constantCoeff (B i j)) = 0) :
    rowMul (annihilatorLift a B C) B = 0 ∧
      residueColumn (annihilatorLift a B C) = a₀ := by
  refine ⟨powerSeries_annihilatorLift_rowMul_eq_zero a B C hCB, ?_⟩
  funext i
  exact residue_powerSeries_annihilatorLift_eq a a₀ B C ha h₀ i

/-! ## Residue/evaluation commutation for multivariate polynomials -/

theorem residue_eval_map
    {k : Type*} [CommRing k] {σ : Type*}
    (P : MvPolynomial σ k) (v : σ → PowerSeries k) :
    PowerSeries.constantCoeff
        (MvPolynomial.eval v (MvPolynomial.map PowerSeries.C P)) =
      MvPolynomial.eval (residueColumn v) P := by
  rw [MvPolynomial.eval_map]
  induction P using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp =>
      simp [hp, residueColumn, mul_comm]

theorem residue_eval_eq_zero_of_eval_map_eq_zero
    {k : Type*} [CommRing k] {σ : Type*}
    (P : MvPolynomial σ k) (v : σ → PowerSeries k)
    (hv : MvPolynomial.eval v (MvPolynomial.map PowerSeries.C P) = 0) :
    MvPolynomial.eval (residueColumn v) P = 0 := by
  rw [← residue_eval_map P v, hv]
  simp

/-! ## Polynomial-specialization contradiction -/

theorem no_axis_specialization
    {k : Type*} [CommRing k] {σ : Type*}
    (P : MvPolynomial σ k) (v : σ → PowerSeries k) (axis : σ → k)
    (hres : residueColumn v = axis)
    (hvanish : MvPolynomial.eval v (MvPolynomial.map PowerSeries.C P) = 0)
    (haxis : MvPolynomial.eval axis P ≠ 0) : False := by
  apply haxis
  rw [← hres]
  exact residue_eval_eq_zero_of_eval_map_eq_zero P v hvanish

/-! ## Small concrete pins used by the focused checker -/

example {k : Type*} [CommRing k] {σ : Type*}
    (P : MvPolynomial σ k) (v : σ → PowerSeries k) :
    PowerSeries.constantCoeff
        (MvPolynomial.eval v (MvPolynomial.map PowerSeries.C P)) =
      MvPolynomial.eval (residueColumn v) P :=
  residue_eval_map P v

example {k : Type*} [CommRing k] {σ : Type*}
    (P : MvPolynomial σ k) (v : σ → PowerSeries k) (axis : σ → k)
    (hres : residueColumn v = axis)
    (hvanish : MvPolynomial.eval v (MvPolynomial.map PowerSeries.C P) = 0)
    (haxis : MvPolynomial.eval axis P ≠ 0) : False :=
  no_axis_specialization P v axis hres hvanish haxis


end

end Stafford38.GeometryRetractionSpecialization
