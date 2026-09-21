/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/

import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Assembly
import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.IrreduciblePolynomialBounds
/-!
# Hensel obstruction to irreducibility

This file applies the explicit Hensel lemma from the coefficientwise Hensel construction to the
normalized residue input constructed by the coefficient-bound lemmas.  The result here is the
core contradiction for irreducible-polynomial lifting: a nontrivial factorization of
the reduction gives a nontrivial factorization over the complete valuation
ring, hence the mapped field polynomial is not irreducible.
-/

noncomputable section

open scoped Polynomial

namespace AlgebraicNumberTheory
namespace Valuations

/-- algebraic obstruction: a field polynomial with a factor of
positive degree strictly smaller than its own degree is not irreducible. -/
theorem irreduciblePolynomial_not_irreducible_of_field_factor_natDegree_lt
    {K : Type*} [Field K] {f g h : K[X]}
    (hfactor : f = g * h)
    (hgpos : 0 < g.natDegree)
    (hglt : g.natDegree < f.natDegree) :
    ¬ Irreducible f := by
  intro hirr
  have hg_notunit : ¬ IsUnit g := by
    intro hgunit
    exact (Nat.ne_of_gt hgpos) (Polynomial.natDegree_eq_zero_of_isUnit hgunit)
  rcases hirr.isUnit_or_isUnit hfactor with hgunit | hhunit
  · exact hg_notunit hgunit
  · have hg_ne : g ≠ 0 := by
      intro hgzero
      simp [hgzero] at hgpos
    have hh_ne : h ≠ 0 := hhunit.ne_zero
    have hdeg : f.natDegree = g.natDegree := by
      simpa [hfactor, Polynomial.natDegree_eq_zero_of_isUnit hhunit] using
        (Polynomial.natDegree_mul hg_ne hh_ne)
    exact (Nat.ne_of_lt hglt) hdeg.symm

/-- transport obstruction: a nontrivial factorization over the
closed-unit-ball valuation ring maps to a nontrivial field factorization. -/
theorem irreduciblePolynomial_not_irreducible_of_valuation_factorization
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    {F G H : (absoluteValueValuationSubring v hnonarch)[X]}
    {f : K[X]} {r : ℕ}
    (hFmap : F.map (algebraMap
        (absoluteValueValuationSubring v hnonarch) K) = f)
    (hFdegree : F.natDegree = f.natDegree)
    (hfactor : F = G * H)
    (hGdegree : G.natDegree = r)
    (hrpos : 0 < r)
    (hrlt : r < F.natDegree) :
    ¬ Irreducible f := by
  let V := absoluteValueValuationSubring v hnonarch
  let φ : V →+* K := algebraMap V K
  have hφinj : Function.Injective φ := by
    intro x y hxy
    exact Subtype.ext (by simpa [φ] using hxy)
  let Gk : K[X] := G.map φ
  let Hk : K[X] := H.map φ
  have hfacK : f = Gk * Hk := by
    calc
      f = F.map φ := hFmap.symm
      _ = (G * H).map φ := by rw [hfactor]
      _ = G.map φ * H.map φ := by simp [Polynomial.map_mul]
      _ = Gk * Hk := rfl
  have hGkDegree : Gk.natDegree = r := by
    calc
      Gk.natDegree = G.natDegree := by
        simpa [Gk] using Polynomial.natDegree_map_eq_of_injective hφinj G
      _ = r := hGdegree
  have hGkpos : 0 < Gk.natDegree := by
    simpa [hGkDegree] using hrpos
  have hGklt : Gk.natDegree < f.natDegree := by
    simpa [hGkDegree, hFdegree] using hrlt
  exact irreduciblePolynomial_not_irreducible_of_field_factor_natDegree_lt
    hfacK hGkpos hGklt

/-- The common nonvanishing step in the three irreducible-polynomial lifting Hensel routes:
if a polynomial is `X ^ r` times a polynomial with nonzero constant
coefficient, then it is nonzero. -/
theorem irreduciblePolynomial_polynomial_ne_zero_of_eq_X_pow_mul_of_coeff_zero_ne_zero
    {k : Type*} [Field k] {P Q : k[X]} {r : ℕ}
    (hfactor : P = Polynomial.X ^ r * Q)
    (hQ0 : Q.coeff 0 ≠ 0) :
    P ≠ 0 := by
  have hQne : Q ≠ 0 := by
    intro hQzero
    exact hQ0 (by simp [hQzero])
  rw [hfactor]
  exact mul_ne_zero (pow_ne_zero r Polynomial.X_ne_zero) hQne

/-- Hensel obstruction: the normalized `X^r` residue factor
input from the residue-polynomial coefficient bounds, together with the adic completeness and separatedness
needed by the coefficientwise Hensel construction, contradicts irreducibility of the mapped field
polynomial. -/
theorem irreduciblePolynomial_hensel_reduction_factor_input_not_irreducible
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    [IsPrecomplete (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    [IsHausdorff (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    (F : (absoluteValueValuationSubring v hnonarch)[X])
    {r : ℕ}
    (hrpos : 0 < r) (hrlt : r < F.natDegree)
    (hfactor :
      F.map (IsLocalRing.residue
          (absoluteValueValuationSubring v hnonarch)) =
        Polynomial.X ^ r *
          (F.map (IsLocalRing.residue
            (absoluteValueValuationSubring v hnonarch)) /ₘ
              Polynomial.X ^ r))
    (hnatDegree : (Polynomial.X ^ r :
        (IsLocalRing.ResidueField
          (absoluteValueValuationSubring v hnonarch))[X]).natDegree =
        r)
    (hcoprime : IsCoprime (Polynomial.X ^ r)
      (F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r))
    (hQ0 : ((F.map (IsLocalRing.residue
        (absoluteValueValuationSubring v hnonarch)) /ₘ
          Polynomial.X ^ r).coeff 0) ≠ 0)
    {f : K[X]}
    (hFmap : F.map (algebraMap
        (absoluteValueValuationSubring v hnonarch) K) = f)
    (hFdegree : F.natDegree = f.natDegree) :
    ¬ Irreducible f := by
  let V := absoluteValueValuationSubring v hnonarch
  let k := IsLocalRing.ResidueField V
  let fbar : k[X] := F.map (IsLocalRing.residue V)
  let qbar : k[X] := fbar /ₘ Polynomial.X ^ r
  have hprim : F.map (IsLocalRing.residue V) ≠ 0 := by
    exact
      irreduciblePolynomial_polynomial_ne_zero_of_eq_X_pow_mul_of_coeff_zero_ne_zero
        hfactor hQ0
  rcases henselFactorization_exists_limit_factorization_of_residual_factors_valuationRing
      (R := V) (f := F) (gbar := (Polynomial.X ^ r : k[X])) (hbar := qbar)
      hprim (by simpa [V, k, fbar, qbar] using hfactor) hcoprime with
    ⟨G, H, hGdegree_res, _hHle, hGH, _hGmap, _hHmap⟩
  have hGdegree : G.natDegree = r := hGdegree_res.trans hnatDegree
  exact irreduciblePolynomial_not_irreducible_of_valuation_factorization
    v hnonarch hFmap hFdegree hGH hGdegree hrpos hrlt

/-- coefficient form: if a field polynomial already has all
coefficients in the closed unit ball, with both endpoints in the open unit
ball and some coefficient on the unit sphere, then Hensel's lemma contradicts
irreducibility. -/
theorem irreduciblePolynomial_field_coeffs_hensel_input_not_irreducible
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    [IsPrecomplete (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    [IsHausdorff (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    (f : K[X])
    (hfcoeff : ∀ i : ℕ, v (f.coeff i) ≤ 1)
    (hconst : v (f.coeff 0) < 1)
    (hlead : v f.leadingCoeff < 1)
    {n : ℕ} (hn : v (f.coeff n) = 1) :
    ¬ Irreducible f := by
  rcases irreduciblePolynomial_exists_hensel_reduction_factor_input_of_field_coeffs
      v hnonarch f hfcoeff hconst hlead hn with
    ⟨F, r, hFmap, hFdegree, hrpos, hrlt, hfactor, hnatDegree, hcoprime, hQ0⟩
  exact irreduciblePolynomial_hensel_reduction_factor_input_not_irreducible
    v hnonarch F hrpos hrlt hfactor hnatDegree hcoprime hQ0
    hFmap hFdegree

/-- normalized-scale obstruction: after dividing by a
coefficient whose absolute value is the positive coefficient maximum, strict
endpoint inequalities force the scaled polynomial to be reducible. -/
theorem irreduciblePolynomial_normalized_scale_hensel_input_not_irreducible
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    [IsPrecomplete (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    [IsHausdorff (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m)
    (hconst : v (f.coeff 0) < m)
    (hlead : v f.leadingCoeff < m) :
    let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
    ¬ Irreducible g := by
  let g : K[X] := Polynomial.C (f.coeff n)⁻¹ * f
  rcases irreduciblePolynomial_normalized_scale_hensel_reduction_factor_input
      v hnonarch hmpos hnmax hbound hconst hlead with
    ⟨F, r, hFmap, hFdegree, hrpos, hrlt, hfactor, hnatDegree, hcoprime, hQ0⟩
  exact irreduciblePolynomial_hensel_reduction_factor_input_not_irreducible
    v hnonarch F hrpos hrlt hfactor hnatDegree hcoprime hQ0
    hFmap hFdegree

/-- scalar normalization preserves irreducibility: multiplying
by the inverse of a nonzero coefficient is multiplication by a unit. -/
theorem irreduciblePolynomial_irreducible_normalized_scale_of_irreducible
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ)
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hirr : Irreducible f) :
    Irreducible (Polynomial.C (f.coeff n)⁻¹ * f) := by
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have hn_ne : f.coeff n ≠ 0 := by
    intro hzero
    have h0m : (0 : ℝ) = m := by
      simpa [hzero] using hnmax
    exact hmne h0m.symm
  have hunit :
      IsUnit (Polynomial.C (f.coeff n)⁻¹ : K[X]) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr (inv_ne_zero hn_ne))
  exact (irreducible_isUnit_mul hunit).2 hirr

/-- endpoint contradiction: for an irreducible polynomial,
the positive maximum of the coefficient absolute values cannot be strictly
larger than both endpoint absolute values. -/
theorem irreduciblePolynomial_not_both_endpoint_abs_lt_coeff_max_of_irreducible
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    [IsPrecomplete (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    [IsHausdorff (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hirr : Irreducible f)
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m) :
    ¬ (v (f.coeff 0) < m ∧ v f.leadingCoeff < m) := by
  intro hend
  have hscaled_irreducible :
      Irreducible (Polynomial.C (f.coeff n)⁻¹ * f) :=
    irreduciblePolynomial_irreducible_normalized_scale_of_irreducible
      v hmpos hnmax hirr
  have hscaled_not_irreducible :
      ¬ Irreducible (Polynomial.C (f.coeff n)⁻¹ * f) :=
    irreduciblePolynomial_normalized_scale_hensel_input_not_irreducible
      v hnonarch hmpos hnmax hbound hend.1 hend.2
  exact hscaled_not_irreducible hscaled_irreducible

/-- coefficient maximum estimate for a chosen positive
coefficient maximum. -/
theorem irreduciblePolynomial_coeff_max_le_endpoint_max_of_irreducible
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    [IsPrecomplete (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    [IsHausdorff (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    {f : K[X]} {m : ℝ} {n : ℕ}
    (hirr : Irreducible f)
    (hmpos : 0 < m)
    (hnmax : v (f.coeff n) = m)
    (hbound : ∀ i : ℕ, v (f.coeff i) ≤ m) :
    m ≤ max (v (f.coeff 0)) (v f.leadingCoeff) := by
  by_contra hnot
  have hmaxlt : max (v (f.coeff 0)) (v f.leadingCoeff) < m :=
    lt_of_not_ge hnot
  have hconst : v (f.coeff 0) < m :=
    (le_max_left (v (f.coeff 0)) (v f.leadingCoeff)).trans_lt hmaxlt
  have hlead : v f.leadingCoeff < m :=
    (le_max_right (v (f.coeff 0)) (v f.leadingCoeff)).trans_lt hmaxlt
  exact irreduciblePolynomial_not_both_endpoint_abs_lt_coeff_max_of_irreducible
    v hnonarch hirr hmpos hnmax hbound ⟨hconst, hlead⟩

/-- coefficient estimate: every coefficient of an irreducible
polynomial is bounded by the larger of the degree-zero and leading
coefficients. -/
theorem irreduciblePolynomial_coeff_abs_le_endpoint_max_of_irreducible
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    [IsPrecomplete (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    [IsHausdorff (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    {f : K[X]} (hirr : Irreducible f) :
    ∀ i : ℕ, v (f.coeff i) ≤ max (v (f.coeff 0)) (v f.leadingCoeff) := by
  rcases irreduciblePolynomial_exists_coeff_abs_max_of_ne_zero
      v hirr.ne_zero with
    ⟨m, n, hmpos, _hnle, hnmax, hbound⟩
  have hmle : m ≤ max (v (f.coeff 0)) (v f.leadingCoeff) :=
    irreduciblePolynomial_coeff_max_le_endpoint_max_of_irreducible
      v hnonarch hirr hmpos hnmax hbound
  intro i
  exact (hbound i).trans hmle

/-- monic consequence: if an irreducible monic polynomial has
degree-zero coefficient in the closed unit ball, then every coefficient lies in
the closed unit ball. -/
theorem irreduciblePolynomial_monic_coeff_abs_le_one_of_const_abs_le_one_of_irreducible
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    [IsPrecomplete (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    [IsHausdorff (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    {f : K[X]} (hirr : Irreducible f)
    (hmonic : f.Monic)
    (hconst : v (f.coeff 0) ≤ 1) :
    ∀ i : ℕ, v (f.coeff i) ≤ 1 := by
  have hlead : v f.leadingCoeff = 1 := by
    rw [hmonic.leadingCoeff]
    simp
  have hendpoint :
      max (v (f.coeff 0)) (v f.leadingCoeff) ≤ 1 := by
    rw [hlead]
    exact max_le hconst le_rfl
  intro i
  exact
    (irreduciblePolynomial_coeff_abs_le_endpoint_max_of_irreducible
      v hnonarch hirr i).trans hendpoint

/-- monic lift consequence: the preceding coefficient bound
gives a degree-preserving lift to the closed-unit-ball valuation ring. -/
theorem irreduciblePolynomial_exists_valuation_lift_of_monic_const_abs_le_one_of_irreducible
    {K : Type*} [Field K]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    [IsPrecomplete (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    [IsHausdorff (IsLocalRing.maximalIdeal
      (absoluteValueValuationSubring v hnonarch))
      (absoluteValueValuationSubring v hnonarch)]
    {f : K[X]} (hirr : Irreducible f)
    (hmonic : f.Monic)
    (hconst : v (f.coeff 0) ≤ 1) :
    ∃ F : (absoluteValueValuationSubring v hnonarch)[X],
      F.map (algebraMap
          (absoluteValueValuationSubring v hnonarch) K) = f ∧
        F.natDegree = f.natDegree := by
  rcases
      exists_polynomial_over_absoluteValueUnitBallSubringAsValuationSubring_of_coeff_abs_le_one
        v hnonarch f
        (irreduciblePolynomial_monic_coeff_abs_le_one_of_const_abs_le_one_of_irreducible
          v hnonarch hirr hmonic hconst) with
    ⟨F, hmap, hdegree, _hcoeff⟩
  exact ⟨F, hmap, hdegree⟩

end Valuations
end AlgebraicNumberTheory

end
