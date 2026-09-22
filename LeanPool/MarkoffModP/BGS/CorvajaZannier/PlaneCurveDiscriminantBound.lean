/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.BivariateResultant
import LeanPool.MarkoffModP.BGS.CorvajaZannier.PlaneCurveBidegreeBridge

/-!
# A sharp degree bound for a bivariate discriminant

For a polynomial `F` in one variable whose coefficients are polynomials of degree at most
`a`, this file proves that the discriminant of `F` has degree at most
`(2 * F.natDegree - 2) * a` in the coefficient variable.  The missing two copies of `a`
relative to the naive Sylvester-determinant estimate come from the constant bottom row in
Mathlib's modified Sylvester matrix for the derivative.

This is the algebraic degree estimate needed in the Corvaja--Zannier canonical/divisor
calculation.
-/

namespace BGS.CorvajaZannier

noncomputable section

variable {K : Type*} [Field K]

theorem natDegree_sylvesterDeriv_apply_le_of_row_ne
    (F : Polynomial (Polynomial K)) (a : ℕ)
    (hcoeff : ∀ i, (F.coeff i).natDegree ≤ a)
    (i j : Fin (F.natDegree - 1 + F.natDegree))
    (hi : (i : ℕ) ≠ 2 * F.natDegree - 2) :
    (F.sylvesterDeriv i j).natDegree ≤ a := by
  rw [Polynomial.sylvesterDeriv]
  split_ifs with hn
  · simp
  · rw [Matrix.updateRow_ne (Fin.ne_of_val_ne hi)]
    induction j using Fin.addCases with
    | left j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_left]
        split_ifs
        · exact hcoeff _
        · simp
    | right j =>
        simp only [Polynomial.sylvester, Matrix.of_apply, Fin.addCases_right]
        split_ifs
        · rw [Polynomial.coeff_derivative]
          have hconstant :
              ((↑((i : ℕ) - (j : ℕ)) : Polynomial K) + 1).natDegree = 0 := by
            apply Nat.eq_zero_of_le_zero
            exact (Polynomial.natDegree_add_le _ _).trans (by simp)
          calc
            (F.coeff ((i : ℕ) - (j : ℕ) + 1) *
                ((↑((i : ℕ) - (j : ℕ)) : Polynomial K) + 1)).natDegree ≤
                (F.coeff ((i : ℕ) - (j : ℕ) + 1)).natDegree +
                  ((↑((i : ℕ) - (j : ℕ)) : Polynomial K) + 1).natDegree :=
              Polynomial.natDegree_mul_le
            _ ≤ a + 0 := add_le_add (hcoeff _) hconstant.le
            _ = a := by omega
        · simp

theorem natDegree_sylvesterDeriv_apply_bottom
    (F : Polynomial (Polynomial K)) (hF : 0 < F.natDegree)
    (j : Fin (F.natDegree - 1 + F.natDegree)) :
    (F.sylvesterDeriv ⟨2 * F.natDegree - 2, by omega⟩ j).natDegree = 0 := by
  rw [Polynomial.sylvesterDeriv, dite_eq_right hF.ne']
  rw [Matrix.updateRow_self]
  split_ifs <;> simp

/-- The discriminant of a degree-`b` polynomial whose coefficients have degree at most
`a` has degree at most `(2 * b - 2) * a`. -/
theorem natDegree_discr_le
    (F : Polynomial (Polynomial K)) (a : ℕ)
    (hcoeff : ∀ i, (F.coeff i).natDegree ≤ a) :
    F.discr.natDegree ≤ (2 * F.natDegree - 2) * a := by
  by_cases hF : F.natDegree = 0
  · rw [Polynomial.eq_C_of_natDegree_eq_zero hF, Polynomial.discr_C]
    simp
  have hFpos : 0 < F.natDegree := Nat.pos_of_ne_zero hF
  let bottom : Fin (F.natDegree - 1 + F.natDegree) :=
    ⟨2 * F.natDegree - 2, by omega⟩
  let rowDegree : Fin (F.natDegree - 1 + F.natDegree) → ℕ := fun i =>
    if i = bottom then 0 else a
  have hmatrix : ∀ i j,
      ((F.sylvesterDeriv.transpose) i j).natDegree ≤ rowDegree j := by
    intro i j
    simp only [Matrix.transpose_apply]
    by_cases hj : j = bottom
    · subst j
      simp only [rowDegree, ↓reduceIte]
      exact (natDegree_sylvesterDeriv_apply_bottom F hFpos i).le
    · rw [show rowDegree j = a by simp [rowDegree, hj]]
      exact natDegree_sylvesterDeriv_apply_le_of_row_ne F a hcoeff j i (by
        intro heq
        apply hj
        apply Fin.ext
        simpa [bottom] using heq)
  have hdet : F.sylvesterDeriv.det.natDegree ≤ ∑ j, rowDegree j := by
    rw [← Matrix.det_transpose]
    exact Matrix.natDegree_det_le_sum_columnDegree _ rowDegree hmatrix
  have hsum : ∑ j, rowDegree j =
      (F.natDegree - 1 + F.natDegree - 1) * a := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ bottom)]
    have hbottom : rowDegree bottom = 0 := by simp [rowDegree]
    rw [hbottom, add_zero]
    calc
      ∑ x ∈ Finset.univ.erase bottom, rowDegree x =
          ∑ x ∈ Finset.univ.erase bottom, a := by
        apply Finset.sum_congr rfl
        intro x hx
        have hne : x ≠ bottom := (Finset.mem_erase.mp hx).1
        simp [rowDegree, hne]
      _ = (F.natDegree - 1 + F.natDegree - 1) * a := by
        rw [Finset.sum_const, nsmul_eq_mul,
          Finset.card_erase_of_mem (Finset.mem_univ bottom)]
        simp
  have hindex : F.natDegree - 1 + F.natDegree - 1 =
      2 * F.natDegree - 2 := by omega
  rw [Polynomial.discr]
  calc
    (F.sylvesterDeriv.det *
        (-1) ^ (F.natDegree * (F.natDegree - 1) / 2)).natDegree ≤
        F.sylvesterDeriv.det.natDegree +
          ((-1 : Polynomial K) ^
            (F.natDegree * (F.natDegree - 1) / 2)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ (∑ j, rowDegree j) + 0 := add_le_add hdet (by simp)
    _ = (F.natDegree - 1 + F.natDegree - 1) * a := by rw [hsum]; omega
    _ = (2 * F.natDegree - 2) * a := by rw [hindex]

/-- View a bivariate polynomial as a polynomial in coordinate `1`, with ordinary
polynomial coefficients in coordinate `0`. -/
def planeCurvePolynomialInSecondCoordinate :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
  (MvPolynomial.renameEquiv K (Equiv.swap (0 : Fin 2) 1)).trans
    ((MvPolynomial.finSuccEquiv K 1).trans
      (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1))))

theorem natDegree_uniqueAlgEquiv_le_degreeOf
    {σ : Type*} [Unique σ] (P : MvPolynomial σ K) :
    (MvPolynomial.uniqueAlgEquiv K σ P).natDegree ≤
      MvPolynomial.degreeOf default P := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  rw [MvPolynomial.coeff_uniqueAlgEquiv]
  by_contra hcoeff
  have hmem : Finsupp.single (default : σ) N ∈ P.support :=
    MvPolynomial.mem_support_iff.mpr hcoeff
  have hle := MvPolynomial.monomial_le_degreeOf (default : σ) hmem
  exact (not_le_of_gt hN) (by simpa using hle)

@[simp]
theorem planeCurvePolynomialInSecondCoordinate_natDegree
    (f : MvPolynomial (Fin 2) K) :
    (planeCurvePolynomialInSecondCoordinate f).natDegree =
      MvPolynomial.degreeOf 1 f := by
  rw [planeCurvePolynomialInSecondCoordinate]
  change (Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f))).natDegree = _
  rw [Polynomial.natDegree_map_eq_of_injective
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)).injective]
  rw [MvPolynomial.natDegree_finSuccEquiv]
  simpa using MvPolynomial.degreeOf_rename_of_injective
    (Equiv.swap (0 : Fin 2) 1).injective (1 : Fin 2) (p := f)

theorem planeCurvePolynomialInSecondCoordinate_coeff_natDegree_le_degreeOf_first
    (f : MvPolynomial (Fin 2) K) (i : ℕ) :
    ((planeCurvePolynomialInSecondCoordinate f).coeff i).natDegree ≤
      MvPolynomial.degreeOf 0 f := by
  rw [planeCurvePolynomialInSecondCoordinate]
  change ((Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1
      (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f))).coeff i).natDegree ≤ _
  rw [Polynomial.coeff_map]
  calc
    (MvPolynomial.uniqueAlgEquiv K (Fin 1)
        ((MvPolynomial.finSuccEquiv K 1
          (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f)).coeff i)).natDegree ≤
        MvPolynomial.degreeOf (0 : Fin 1)
          ((MvPolynomial.finSuccEquiv K 1
            (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f)).coeff i) :=
      natDegree_uniqueAlgEquiv_le_degreeOf _
    _ ≤ MvPolynomial.degreeOf (Fin.succ (0 : Fin 1))
        (MvPolynomial.rename (Equiv.swap (0 : Fin 2) 1) f) :=
      MvPolynomial.degreeOf_coeff_finSuccEquiv _ _ _
    _ = MvPolynomial.degreeOf 0 f := by
      simpa using MvPolynomial.degreeOf_rename_of_injective
        (Equiv.swap (0 : Fin 2) 1).injective (0 : Fin 2) (p := f)

theorem planeCurvePolynomialInSecondCoordinate_coeff_natDegree_le
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree)
    (i : ℕ) :
    ((planeCurvePolynomialInSecondCoordinate f).coeff i).natDegree ≤ firstDegree :=
  (planeCurvePolynomialInSecondCoordinate_coeff_natDegree_le_degreeOf_first f i).trans
    (degreeOf_first_le_of_hasBidegreeAtMost hdegree)

/-- The discriminant in the first coordinate of a plane curve of bidegree at most
`(firstDegree, secondDegree)` has the sharp degree bound
`(2 * secondDegree - 2) * firstDegree`. -/
theorem planeCurvePolynomialInSecondCoordinate_discr_natDegree_le
    {f : MvPolynomial (Fin 2) K} {firstDegree secondDegree : ℕ}
    (hdegree : BGS.External.HasBidegreeAtMost f firstDegree secondDegree) :
    (planeCurvePolynomialInSecondCoordinate f).discr.natDegree ≤
      (2 * secondDegree - 2) * firstDegree := by
  calc
    (planeCurvePolynomialInSecondCoordinate f).discr.natDegree ≤
        (2 * (planeCurvePolynomialInSecondCoordinate f).natDegree - 2) *
          firstDegree :=
      natDegree_discr_le _ _
        (planeCurvePolynomialInSecondCoordinate_coeff_natDegree_le hdegree)
    _ ≤ (2 * secondDegree - 2) * firstDegree := by
      gcongr
      rw [planeCurvePolynomialInSecondCoordinate_natDegree]
      exact degreeOf_second_le_of_hasBidegreeAtMost hdegree

end

end BGS.CorvajaZannier
