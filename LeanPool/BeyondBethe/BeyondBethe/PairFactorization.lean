/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.CapacityScaling
public import LeanPool.BeyondBethe.BeyondBethe.ClusterCertificate
public import LeanPool.BeyondBethe.BeyondBethe.Gain
public import LeanPool.BeyondBethe.BeyondBethe.TransferIdentity
public import Mathlib.Tactic

/-! # Pair Factorization -/

@[expose] public section

open scoped BigOperators

namespace BeyondBethe

open MvPolynomial

/-- Multiplicative form of the KKT equations (paper (35)). -/
def HasMultiplicativeKKT
    {ι : Type*} [Fintype ι]
    (τ : ℝ) (A X : Matrix ι ι ℝ) (r c : ι → ℝ) : Prop :=
  ∀ i j, A i j = r i * c j * (X i j) ^ (1 + τ) * (1 - X i j)

theorem hasMultiplicativeKKT_of_logKKT
    {ι : Type*} [Fintype ι]
    {τ : ℝ} {A X : Matrix ι ι ℝ} {R C : ι → ℝ}
    (hApos : ∀ i j, 0 < A i j)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hKKT : HasLogKKT τ A X R C) :
    HasMultiplicativeKKT τ A X (fun i ↦ Real.exp (R i))
      (fun j ↦ Real.exp (C j)) := by
  intro i j
  have hx : 0 < X i j := (hXint i).2 j |>.1
  have hcomp : 0 < 1 - X i j := sub_pos.mpr ((hXint i).2 j |>.2)
  calc
    A i j = Real.exp (Real.log (A i j)) :=
      (Real.exp_log (hApos i j)).symm
    _ = Real.exp (R i + C j +
        (1 + τ) * Real.log (X i j) + Real.log (1 - X i j)) := by
      rw [hKKT i j]
    _ = Real.exp (R i) * Real.exp (C j) *
        (X i j) ^ (1 + τ) * (1 - X i j) := by
      rw [Real.exp_add, Real.exp_add, Real.exp_add,
        Real.rpow_def_of_pos hx, Real.exp_log hcomp]
      ring

theorem multiplicativeKKT_eq_row_column_transfer
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {τ : ℝ} {A X : Matrix ι ι ℝ} {r c : ι → ℝ}
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hKKT : HasMultiplicativeKKT τ A X r c) (i j : ι) :
    A i j = r i * complementProduct (X i) * c j *
      transferU τ (X i) j := by
  rw [hKKT i j, transferU_eq_div_complementProduct (hXint i) j]
  field_simp [ne_of_gt (complementProduct_pos (hXint i))]

theorem pairPolynomial_eval_of_row_column_scaling
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b u v c z : ι → ℝ} {R S : ℝ}
    (ha : ∀ j, a j = R * c j * u j)
    (hb : ∀ j, b j = S * c j * v j) :
    (pairPolynomial a b).eval z =
      (R * S) * (pairPolynomial u v).eval (fun j ↦ c j * z j) := by
  rw [pairPolynomial_eval, pairPolynomial_eval]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [ha e.1, hb e.2]
  ring

theorem pairPolynomial_capacity_of_row_column_scaling
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {a b u v c α : ι → ℝ} {R S : ℝ}
    (ha0 : ∀ j, 0 ≤ a j) (hb0 : ∀ j, 0 ≤ b j)
    (hu0 : ∀ j, 0 ≤ u j) (hv0 : ∀ j, 0 ≤ v j)
    (hR : 0 < R) (hS : 0 < S) (hc : ∀ j, 0 < c j)
    (ha : ∀ j, a j = R * c j * u j)
    (hb : ∀ j, b j = S * c j * v j) :
    polynomialCapacity α (pairPolynomial a b) =
      ((R * S) * realMonomial c α) *
        polynomialCapacity α (pairPolynomial u v) := by
  apply polynomialCapacity_eq_of_positive_diagonal_rescaling
    (pairPolynomial_nonnegativeCoefficients ha0 hb0)
    (pairPolynomial_nonnegativeCoefficients hu0 hv0)
    (mul_pos hR hS) hc
  intro z
  exact pairPolynomial_eval_of_row_column_scaling (z := z) ha hb

theorem singletonCoordinate_factorization
    {a x r c τ : ℝ}
    (hx : 0 < x) (hx1 : x < 1) (hr : 0 < r) (hc : 0 < c)
    (ha : a = r * c * x ^ (1 + τ) * (1 - x)) :
    (a / x) ^ x * (1 - x) ^ (1 - x) =
      r ^ x * c ^ x * x ^ (τ * x) * (1 - x) := by
  have hcomp : 0 < 1 - x := sub_pos.mpr hx1
  have hAx : a / x = r * c * x ^ τ * (1 - x) := by
    rw [ha, Real.rpow_add hx 1 τ, Real.rpow_one]
    field_simp [hx.ne']
  rw [hAx]
  rw [Real.mul_rpow (mul_nonneg
      (mul_nonneg hr.le hc.le) (Real.rpow_nonneg hx.le τ)) hcomp.le]
  rw [Real.mul_rpow (mul_nonneg hr.le hc.le)
    (Real.rpow_nonneg hx.le τ)]
  rw [Real.mul_rpow hr.le hc.le]
  rw [← Real.rpow_mul hx.le τ x]
  have hcompPow : (1 - x) ^ x * (1 - x) ^ (1 - x) = 1 - x := by
    rw [← Real.rpow_add hcomp x (1 - x)]
    convert Real.rpow_one (1 - x) using 2 <;> ring
  calc
    r ^ x * c ^ x * x ^ (τ * x) * (1 - x) ^ x *
        (1 - x) ^ (1 - x) =
        (r ^ x * c ^ x * x ^ (τ * x)) *
          ((1 - x) ^ x * (1 - x) ^ (1 - x)) := by ring
    _ = r ^ x * c ^ x * x ^ (τ * x) * (1 - x) := by
      rw [hcompPow]

/-- Paper (44), stated first for the explicit singleton product `S_i`. -/
theorem singletonProductValue_factorized_of_multiplicativeKKT
    {n : ℕ} {τ : ℝ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {r c : Fin n → ℝ}
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hr : ∀ i, 0 < r i) (hc : ∀ j, 0 < c j)
    (hKKT : HasMultiplicativeKKT τ A X r c) (i : Fin n) :
    singletonProductValue A X i =
      r i * complementProduct (X i) * rowZeta τ (X i) *
        realMonomial c (X i) := by
  rw [singletonProductValue, rowZeta, complementProduct, realMonomial]
  simp_rw [singletonCoordinate_factorization
    ((hXint i).2 _ |>.1) ((hXint i).2 _ |>.2) (hr i) (hc _)
    (hKKT i _)]
  have hrprod : (∏ j, (r i) ^ (X i j)) = r i := by
    rw [← Real.rpow_sum_of_pos (hr i), hX.row_sum i, Real.rpow_one]
  rw [show (∏ j, ((r i) ^ (X i j) * (c j) ^ (X i j) *
      (X i j) ^ (τ * X i j) * (1 - X i j))) =
      (∏ j, (r i) ^ (X i j)) * (∏ j, (c j) ^ (X i j)) *
        (∏ j, (X i j) ^ (τ * X i j)) *
          ∏ j, (1 - X i j) by
    simp only [← Finset.prod_mul_distrib]
    ]
  rw [hrprod]
  ring

theorem realMonomial_pairAlpha
    {ι : Type*} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ j, 0 < c j)
    (X : Matrix ι ι ℝ) (r s : ι) :
    realMonomial c (pairAlpha X r s) =
      realMonomial c (X r) * realMonomial c (X s) := by
  rw [realMonomial, realMonomial, realMonomial,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j _
  exact Real.rpow_add (hc j) (X r j) (X s j)

/-- The gain ratio `Gamma_rs` from paper (10), using the explicit singleton
products from paper (7). -/
noncomputable def pairGain
    {n : ℕ} (A X : Matrix (Fin n) (Fin n) ℝ) (r s : Fin n) : ℝ :=
  pairCertificateValue A X r s /
    (singletonProductValue A X r * singletonProductValue A X s)

/-- Paper Lemma 18.  Every KKT scaling and every capacity change of variables
is canceled explicitly. -/
theorem pairGain_factorization
    {n : ℕ} {τ : ℝ} {A X : Matrix (Fin n) (Fin n) ℝ}
    {rscale cscale : Fin n → ℝ}
    (hApos : ∀ i j, 0 < A i j)
    (hX : IsDoublyStochastic X)
    (hXint : ∀ i, IsInteriorProbabilityVector (X i))
    (hr : ∀ i, 0 < rscale i) (hc : ∀ j, 0 < cscale j)
    (hKKT : HasMultiplicativeKKT τ A X rscale cscale)
    (r s : Fin n) :
    pairGain A X r s =
      1 / (rowZeta τ (X r) * rowZeta τ (X s)) *
        (∏ j, (1 - pairAlpha X r s j) ^
          (1 - pairAlpha X r s j)) *
        polynomialCapacity (pairAlpha X r s)
          (pairPolynomial (fun j ↦ transferU τ (X r) j)
            (fun j ↦ transferU τ (X s) j)) := by
  let qr := complementProduct (X r)
  let qs := complementProduct (X s)
  let Ur : Fin n → ℝ := fun j ↦ transferU τ (X r) j
  let Us : Fin n → ℝ := fun j ↦ transferU τ (X s) j
  have hqr : 0 < qr := complementProduct_pos (hXint r)
  have hqs : 0 < qs := complementProduct_pos (hXint s)
  have hUr : ∀ j, 0 < Ur j := fun j ↦ transferU_pos (hXint r) j
  have hUs : ∀ j, 0 < Us j := fun j ↦ transferU_pos (hXint s) j
  have hAr : ∀ j, A r j = (rscale r * qr) * cscale j * Ur j := by
    intro j
    simpa only [qr, Ur, mul_assoc] using
      multiplicativeKKT_eq_row_column_transfer hXint hKKT r j
  have hAs : ∀ j, A s j = (rscale s * qs) * cscale j * Us j := by
    intro j
    simpa only [qs, Us, mul_assoc] using
      multiplicativeKKT_eq_row_column_transfer hXint hKKT s j
  have hcap := pairPolynomial_capacity_of_row_column_scaling
    (α := pairAlpha X r s)
    (fun j ↦ (hApos r j).le) (fun j ↦ (hApos s j).le)
    (fun j ↦ (hUr j).le) (fun j ↦ (hUs j).le)
    (mul_pos (hr r) hqr) (mul_pos (hr s) hqs) hc hAr hAs
  have hSr := singletonProductValue_factorized_of_multiplicativeKKT
    hX hXint hr hc hKKT r
  have hSs := singletonProductValue_factorized_of_multiplicativeKKT
    hX hXint hr hc hKKT s
  have hcAlpha := realMonomial_pairAlpha cscale hc X r s
  have hzetaR : 0 < rowZeta τ (X r) :=
    rowZeta_pos (fun j ↦ (hXint r).2 j |>.1)
  have hzetaS : 0 < rowZeta τ (X s) :=
    rowZeta_pos (fun j ↦ (hXint s).2 j |>.1)
  have hcR : 0 < realMonomial cscale (X r) :=
    realMonomial_pos hc (X r)
  have hcS : 0 < realMonomial cscale (X s) :=
    realMonomial_pos hc (X s)
  rw [pairGain, pairCertificateValue, hcap, hSr, hSs, hcAlpha]
  dsimp only [qr, qs, Ur, Us] at *
  field_simp [ne_of_gt (hr r), ne_of_gt (hr s), hqr.ne', hqs.ne',
    hzetaR.ne', hzetaS.ne', hcR.ne', hcS.ne']

end BeyondBethe
