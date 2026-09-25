/-
Copyright (c) 2026 Nima Anari. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nima Anari
-/
module


public import LeanPool.BeyondBethe.BeyondBethe.PairedCertificate

/-! # Pair Stability -/

@[expose] public section

open scoped BigOperators ComplexConjugate

namespace BeyondBethe

open MvPolynomial

/-- The multivariate linear polynomial whose variable coefficients are `u`; coefficient
positivity is a separate hypothesis. -/
noncomputable def positiveLinearPolynomial
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) : MvPolynomial ι ℝ :=
  ∑ j, monomial (Finsupp.single j 1) (u j)

theorem positiveLinearPolynomial_nonnegativeCoefficients
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u : ι → ℝ} (hu : ∀ i, 0 ≤ u i) :
    HasNonnegativeCoefficients (positiveLinearPolynomial u) := by
  intro d
  rw [positiveLinearPolynomial, coeff_sum]
  apply Finset.sum_nonneg
  intro i _
  rw [coeff_monomial]
  split
  · exact hu i
  · exact le_rfl

theorem positiveLinearPolynomial_isRealStable
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {u : ι → ℝ} (hu : ∀ i, 0 < u i) :
    IsRealStable (positiveLinearPolynomial u) := by
  intro z hz
  rw [positiveLinearPolynomial, eval₂_sum]
  simp only [eval₂_monomial, RingHom.id_apply,
    Finsupp.prod_single_index, pow_one, one_mul]
  have him : 0 < ∑ i, u i * (z i).im :=
    Finset.sum_pos (fun i _ ↦ mul_pos (hu i) (hz i))
      Finset.univ_nonempty
  intro heq
  have hzero := congrArg Complex.im heq
  simp at hzero
  linarith

/-- The finite real dot product of coordinate functions `a` and `x`. -/
noncomputable def realDot
    {ι : Type*} [Fintype ι] (a x : ι → ℝ) : ℝ :=
  ∑ i, a i * x i

/-- The product of two linear forms with their diagonal quadratic contribution removed. -/
noncomputable def pairQuadraticForm
    {ι : Type*} [Fintype ι] (u v x : ι → ℝ) : ℝ :=
  realDot u x * realDot v x - ∑ i, u i * v i * x i ^ 2

/-- The symmetric bilinear polarization of the pair quadratic form. -/
noncomputable def pairBilinearForm
    {ι : Type*} [Fintype ι] (u v x y : ι → ℝ) : ℝ :=
  realDot u x * realDot v y + realDot u y * realDot v x -
    2 * ∑ i, u i * v i * x i * y i

theorem realDot_mul_realDot
    {ι : Type*} [Fintype ι]
    (a b x y : ι → ℝ) :
    realDot a x * realDot b y =
      ∑ i, ∑ j, a i * b j * x i * y j := by
  simp only [realDot]
  rw [Finset.mul_sum]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem sum_offDiag_eq_sum_product_sub_diag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι × ι → ℝ) :
    (∑ e ∈ (Finset.univ : Finset ι).offDiag, f e) =
      (∑ i, ∑ j, f (i, j)) - ∑ i, f (i, i) := by
  have hunion :
      (∑ e ∈ (Finset.univ : Finset ι).diag ∪ Finset.univ.offDiag, f e) =
        (∑ e ∈ (Finset.univ : Finset ι).diag, f e) +
          ∑ e ∈ (Finset.univ : Finset ι).offDiag, f e :=
    Finset.sum_union
      (Finset.disjoint_diag_offDiag (Finset.univ : Finset ι))
  rw [Finset.diag_union_offDiag, Finset.sum_diag,
    Finset.sum_product] at hunion
  linarith

theorem pairQuadraticForm_eq_offDiag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v x : ι → ℝ) :
    pairQuadraticForm u v x =
      ∑ e ∈ (Finset.univ : Finset ι).offDiag,
        u e.1 * v e.2 * x e.1 * x e.2 := by
  rw [sum_offDiag_eq_sum_product_sub_diag]
  simp only [pairQuadraticForm]
  rw [realDot_mul_realDot]
  apply congrArg₂ (· - ·) rfl
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pairBilinearForm_eq_offDiag
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v x y : ι → ℝ) :
    pairBilinearForm u v x y =
      ∑ e ∈ (Finset.univ : Finset ι).offDiag,
        u e.1 * v e.2 * (x e.1 * y e.2 + y e.1 * x e.2) := by
  rw [sum_offDiag_eq_sum_product_sub_diag]
  simp only [pairBilinearForm]
  rw [realDot_mul_realDot, realDot_mul_realDot]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hdiag : (∑ i, u i * v i * (y i * x i)) =
      ∑ i, u i * v i * (x i * y i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdiag]
  ring

theorem pairPolynomial_eval_eq_quadraticForm
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v x : ι → ℝ) :
    (pairPolynomial u v).eval x = pairQuadraticForm u v x := by
  rw [pairPolynomial_eval, pairQuadraticForm_eq_offDiag]

theorem pairPolynomial_eval₂_complex
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) (z : ι → ℂ) :
    (pairPolynomial u v).eval₂ (algebraMap ℝ ℂ) z =
      ∑ e ∈ (Finset.univ : Finset ι).offDiag,
        ((u e.1 * v e.2 : ℝ) : ℂ) * z e.1 * z e.2 := by
  rw [pairPolynomial, eval₂_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [eval₂_monomial]
  rw [Finsupp.prod_add_index]
  · simp [Finsupp.prod_single_index, mul_assoc, mul_left_comm, mul_comm]
  · simp
  · intro a _ b c
    exact pow_add (z a) b c

theorem pairPolynomial_eval₂_complex_re
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) (z : ι → ℂ) :
    ((pairPolynomial u v).eval₂ (algebraMap ℝ ℂ) z).re =
      pairQuadraticForm u v (fun i ↦ (z i).re) -
        pairQuadraticForm u v (fun i ↦ (z i).im) := by
  rw [pairPolynomial_eval₂_complex]
  simp
  rw [pairQuadraticForm_eq_offDiag, pairQuadraticForm_eq_offDiag]

theorem pairPolynomial_eval₂_complex_im
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u v : ι → ℝ) (z : ι → ℂ) :
    ((pairPolynomial u v).eval₂ (algebraMap ℝ ℂ) z).im =
      pairBilinearForm u v (fun i ↦ (z i).re) (fun i ↦ (z i).im) := by
  rw [pairPolynomial_eval₂_complex]
  simp
  rw [pairBilinearForm_eq_offDiag]
  ring

theorem realDot_sub_mul
    {ι : Type*} [Fintype ι]
    (u x y : ι → ℝ) (t : ℝ) :
    realDot u (fun i ↦ x i - t * y i) =
      realDot u x - t * realDot u y := by
  simp only [realDot, mul_sub]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]
  apply congrArg₂ (· - ·) rfl
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem pairQuadraticForm_sub_mul
    {ι : Type*} [Fintype ι]
    (u v x y : ι → ℝ) (t : ℝ) :
    pairQuadraticForm u v (fun i ↦ x i - t * y i) =
      pairQuadraticForm u v x - t * pairBilinearForm u v x y +
        t ^ 2 * pairQuadraticForm u v y := by
  have hdiag :
      (∑ i, u i * v i * (x i - t * y i) ^ 2) =
        (∑ i, u i * v i * x i ^ 2) -
          2 * t * (∑ i, u i * v i * x i * y i) +
            t ^ 2 * (∑ i, u i * v i * y i ^ 2) := by
    calc
      (∑ i, u i * v i * (x i - t * y i) ^ 2) =
          ∑ i, (u i * v i * x i ^ 2 -
            2 * t * (u i * v i * x i * y i) +
              t ^ 2 * (u i * v i * y i ^ 2)) := by
                apply Finset.sum_congr rfl
                intro i _
                ring
      _ = (∑ i, u i * v i * x i ^ 2) -
          2 * t * (∑ i, u i * v i * x i * y i) +
            t ^ 2 * (∑ i, u i * v i * y i ^ 2) := by
              simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
                Finset.mul_sum]
  simp only [pairQuadraticForm, pairBilinearForm, realDot_sub_mul, hdiag]
  ring

theorem pairQuadraticForm_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v y : ι → ℝ} (hcard : 2 ≤ Fintype.card ι)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hy : ∀ i, 0 < y i) :
    0 < pairQuadraticForm u v y := by
  rw [pairQuadraticForm_eq_offDiag]
  apply Finset.sum_pos
  · intro e he
    exact mul_pos (mul_pos (mul_pos (hu e.1) (hv e.2)) (hy e.1)) (hy e.2)
  · obtain ⟨i, j, hij⟩ := Fintype.one_lt_card_iff.mp (by omega :
      1 < Fintype.card ι)
    exact ⟨(i, j), by simp [hij]⟩

/-- The quadratic form of the pair polynomial is nonpositive on the
bilinear-orthogonal complement of any positive direction.  This is the
at-most-one-positive-direction argument needed in the stability proof; it
uses the hyperplane `dot(u,x)=0`, on which the form is visibly nonpositive. -/
theorem pairQuadraticForm_nonpos_of_bilinear_zero
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {u v x y : ι → ℝ}
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i)
    (hy : ∀ i, 0 < y i)
    (hypos : 0 < pairQuadraticForm u v y)
    (horth : pairBilinearForm u v x y = 0) :
    pairQuadraticForm u v x ≤ 0 := by
  let uy := realDot u y
  have huy : 0 < uy := by
    dsimp [uy]
    rw [realDot]
    exact Finset.sum_pos (fun i _ ↦ mul_pos (hu i) (hy i))
      Finset.univ_nonempty
  let t := realDot u x / uy
  let z : ι → ℝ := fun i ↦ x i - t * y i
  have huz : realDot u z = 0 := by
    change realDot u (fun i ↦ x i - t * y i) = 0
    rw [realDot_sub_mul]
    dsimp [t]
    rw [div_mul_cancel₀ _ (ne_of_gt huy)]
    ring
  have hznonpos : pairQuadraticForm u v z ≤ 0 := by
    rw [pairQuadraticForm, huz, zero_mul, zero_sub]
    exact neg_nonpos.mpr (Finset.sum_nonneg fun i _ ↦
      mul_nonneg (mul_nonneg (le_of_lt (hu i)) (le_of_lt (hv i)))
        (sq_nonneg (z i)))
  have hshift : pairQuadraticForm u v z =
      pairQuadraticForm u v x + t ^ 2 * pairQuadraticForm u v y := by
    change pairQuadraticForm u v (fun i ↦ x i - t * y i) = _
    rw [pairQuadraticForm_sub_mul, horth]
    ring
  have hgain : 0 ≤ t ^ 2 * pairQuadraticForm u v y :=
    mul_nonneg (sq_nonneg t) (le_of_lt hypos)
  linarith

/-- The pair polynomial is real stable for positive row weights as soon as
there are at least two variables.  This closes the quadratic-stability step
for the polynomial used in the paper without importing an eigenvalue or
inertia theorem: the hyperplane orthogonal to `u` already witnesses that the
quadratic form has at most one positive direction. -/
theorem pairPolynomial_isRealStable_of_pos
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {u v : ι → ℝ} (hcard : 2 ≤ Fintype.card ι)
    (hu : ∀ i, 0 < u i) (hv : ∀ i, 0 < v i) :
    IsRealStable (pairPolynomial u v) := by
  letI : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  intro z hz hzero
  let x : ι → ℝ := fun i ↦ (z i).re
  let y : ι → ℝ := fun i ↦ (z i).im
  have hypos : 0 < pairQuadraticForm u v y :=
    pairQuadraticForm_pos hcard hu hv (fun i ↦ hz i)
  have hre : pairQuadraticForm u v x - pairQuadraticForm u v y = 0 := by
    have h := congrArg Complex.re hzero
    rw [pairPolynomial_eval₂_complex_re] at h
    simpa [x, y] using h
  have him : pairBilinearForm u v x y = 0 := by
    have h := congrArg Complex.im hzero
    rw [pairPolynomial_eval₂_complex_im] at h
    simpa [x, y] using h
  have hxnonpos : pairQuadraticForm u v x ≤ 0 :=
    pairQuadraticForm_nonpos_of_bilinear_zero hu hv (fun i ↦ hz i)
      hypos him
  linarith

end BeyondBethe
