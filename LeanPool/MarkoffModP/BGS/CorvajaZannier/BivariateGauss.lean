/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.CorvajaZannier.BivariateResultant
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Gauss descent for the Corvaja--Zannier bivariate resultant

When the resultant in the first variable vanishes, Corvaja and Zannier first
obtain divisibility over the rational-function coefficient field and then use
Gauss' lemma to descend that divisibility to the bivariate polynomial ring.
This descent is what permits reading off *both* coordinate degrees, rather
than only the degree in the eliminated variable.
-/

namespace BGS.CorvajaZannier

noncomputable section

variable {C : Type*} [Field C]

/-- The project-local transpose is the standard bivariate variable swap. -/
theorem transposeBivariate_eq_bivariateSwap :
    transposeBivariate (C := C) =
      (Polynomial.Bivariate.swap (R := C)).toRingHom := by
  ext <;> simp [transposeBivariate, Polynomial.Bivariate.swap_apply]

/-- Swapping the two variables twice is the identity. -/
@[simp]
theorem transposeBivariate_transposeBivariate
    (P : Polynomial (Polynomial C)) :
    transposeBivariate (transposeBivariate P) = P := by
  rw [transposeBivariate_eq_bivariateSwap]
  change Polynomial.Bivariate.swap
    (Polynomial.Bivariate.swap P) = P
  exact Polynomial.Bivariate.swap_swap_apply P

/-- Swapping the variables is injective. -/
theorem transposeBivariate_injective :
    Function.Injective (transposeBivariate (C := C)) := by
  intro P Q h
  simpa only [transposeBivariate_transposeBivariate] using
    congrArg transposeBivariate h

/-- The ordinary (actual-degree) resultant vanishes in the common-zero branch
once its degree is smaller than the minimal-polynomial degree of `v`.

Using the ordinary resultant here is essential: a Sylvester determinant
padded to an upper degree bound can vanish for the purely formal reason that
one polynomial has smaller actual degree, and therefore cannot support the
subsequent Gauss descent. -/
theorem resultant_auxiliaryRelation_default_eq_zero_of_common_zero
    {L : Type*} [Field L] [Algebra C L]
    (f : Polynomial (Polynomial C)) (a b h k q : ℕ)
    (ha : 0 < a) (hh : 0 < h) (hk : 0 < k)
    (c : Fin k → C) (d : Fin (k + 1) × Fin h → C)
    (hfDegree : f.natDegree = a)
    (hfCoeffDegree : ∀ i, (f.coeff i).natDegree ≤ b)
    (u v : L) (hminpoly : (minpoly C v).natDegree = q)
    (hfZero : evalBivariate v u f = 0)
    (hauxZero :
      evalBivariate u v (auxiliaryRelationPolynomial c d) = 0)
    (hsize : a * h + k * b < q) :
    Polynomial.resultant f
      (transposeBivariate (auxiliaryRelationPolynomial c d)) = 0 := by
  apply eq_zero_of_natDegree_lt_minpoly_of_eval₂_eq_zero v
  · rw [hminpoly]
    exact (natDegree_resultant_auxiliaryRelation_default_le
      f a b h k hh hk c d hfDegree.le hfCoeffDegree).trans_lt hsize
  · have hfNatDegreeNonzero : f.natDegree ≠ 0 :=
      hfDegree.trans_ne ha.ne'
    have hauxAtCommonZero :
        evalBivariate v u
          (transposeBivariate (auxiliaryRelationPolynomial c d)) = 0 := by
      rw [evalBivariate_transposeBivariate]
      exact hauxZero
    exact eval₂_resultant_eq_zero_of_common_zero f
      (transposeBivariate (auxiliaryRelationPolynomial c d))
      f.natDegree
      (transposeBivariate (auxiliaryRelationPolynomial c d)).natDegree
      (le_refl _) (le_refl _) (Or.inl hfNatDegreeNonzero) u v
      hfZero hauxAtCommonZero

/-- Source-faithful Gauss descent: zero resultant gives divisibility already
in `C[V][U]`, not merely after passing to `C(V)[U]`.

The nonconstant hypothesis is exactly what makes the irreducible polynomial
primitive over `C[V]`; Gauss' lemma then descends the divisibility obtained
over `Frac(C[V])`. -/
theorem dvd_of_irreducible_of_resultant_eq_zero_via_gauss
    {f g : Polynomial (Polynomial C)}
    (hf : Irreducible f) (hfNonconstant : f.natDegree ≠ 0)
    (hresultant : Polynomial.resultant f g = 0) :
    f ∣ g := by
  let K := FractionRing (Polynomial C)
  let φ : Polynomial C →+* K := algebraMap (Polynomial C) K
  have hφ : Function.Injective φ := IsFractionRing.injective _ _
  have hprimitive : f.IsPrimitive := hf.isPrimitive hfNonconstant
  have hfMap : Irreducible (f.map φ) := by
    exact hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hf
  have hdvdMap : f.map φ ∣ g.map φ :=
    map_dvd_of_resultant_eq_zero f g φ hφ hfMap hresultant
  exact hprimitive.dvd_of_fraction_map_dvd_fraction_map hdvdMap

/-- Gauss descent followed by variable swapping bounds both bidegrees of a
nonzero multiple. -/
theorem bidegree_le_of_irreducible_of_resultant_eq_zero
    {f g : Polynomial (Polynomial C)}
    (hf : Irreducible f) (hfNonconstant : f.natDegree ≠ 0)
    (hg : g ≠ 0) (hresultant : Polynomial.resultant f g = 0) :
    f.natDegree ≤ g.natDegree ∧
      (transposeBivariate f).natDegree ≤
        (transposeBivariate g).natDegree := by
  have hdvd : f ∣ g :=
    dvd_of_irreducible_of_resultant_eq_zero_via_gauss
      hf hfNonconstant hresultant
  refine ⟨Polynomial.natDegree_le_of_dvd hdvd hg, ?_⟩
  have hdvdTranspose : transposeBivariate f ∣ transposeBivariate g :=
    map_dvd transposeBivariate hdvd
  have hgTranspose : transposeBivariate g ≠ 0 :=
    fun hzero => hg (transposeBivariate_injective (by simpa using hzero))
  exact Polynomial.natDegree_le_of_dvd hdvdTranspose hgTranspose

/-- The exact degree conclusion in the zero-resultant branch of the
Corvaja--Zannier auxiliary-family argument.

Here `f` is oriented as a polynomial in `U` with coefficients in `C[V]`.
Thus `f.natDegree = a`, while the degree of its variable swap is `b`.  The
auxiliary relation is constructed in the source orientation and swapped for
the resultant. -/
theorem auxiliaryRelation_bidegree_bounds_of_resultant_eq_zero
    (f : Polynomial (Polynomial C)) (a b h k : ℕ)
    (ha : 0 < a) (hh : 0 < h) (hk : 0 < k)
    (c : Fin k → C) (d : Fin (k + 1) × Fin h → C)
    (hf : Irreducible f)
    (hfDegreeU : f.natDegree = a)
    (hfDegreeV : (transposeBivariate f).natDegree = b)
    (hauxNonzero : auxiliaryRelationPolynomial c d ≠ 0)
    (hresultant : Polynomial.resultant f
      (transposeBivariate (auxiliaryRelationPolynomial c d)) = 0) :
    a ≤ k ∧ b ≤ h := by
  have hauxTransposeNonzero :
      transposeBivariate (auxiliaryRelationPolynomial c d) ≠ 0 := by
    intro hzero
    exact hauxNonzero (transposeBivariate_injective (by simpa using hzero))
  have hdegrees := bidegree_le_of_irreducible_of_resultant_eq_zero
    hf (hfDegreeU.trans_ne ha.ne') hauxTransposeNonzero hresultant
  constructor
  · rw [← hfDegreeU]
    exact hdegrees.1.trans
      (transpose_auxiliaryRelationPolynomial_natDegree_le hk c d)
  · rw [← hfDegreeV]
    exact hdegrees.2.trans (by
      simpa only [transposeBivariate_transposeBivariate] using
        auxiliaryRelationPolynomial_natDegree_le hh c d)

/-- Corvaja--Zannier Proposition 1, through its complete algebraic resultant
branch.  If the defining relation has bidegree `(a,b)`, its ordinary
resultant with any nonzero auxiliary relation would force `a ≤ k` and
`b ≤ h`.  Excluding that degree alternative therefore makes the exact
auxiliary family linearly independent.

The assumptions expose the two genuinely external inputs to this algebraic
step: iterated-polynomial irreducibility of the defining equation and the
minimal-polynomial degree `q` of `v` over the coefficient field. -/
theorem auxiliaryFamily_linearIndependent_of_irreducible_bidegree
    {L : Type*} [Field L] [Algebra C L]
    (f : Polynomial (Polynomial C)) (a b h k q : ℕ)
    (ha : 0 < a) (hh : 0 < h) (hk : 0 < k)
    (hf : Irreducible f)
    (hfDegreeU : f.natDegree = a)
    (hfDegreeV : (transposeBivariate f).natDegree = b)
    (hfCoeffDegree : ∀ i, (f.coeff i).natDegree ≤ b)
    (u v : L) (hv : v ≠ 1)
    (hminpoly : (minpoly C v).natDegree = q)
    (hfZero : evalBivariate v u f = 0)
    (hsize : a * h + b * k < q)
    (hdegreeAlternativeExcluded : ¬ (a ≤ k ∧ b ≤ h)) :
    LinearIndependent C (auxiliaryFamily u v h k) := by
  apply auxiliaryFamily_linearIndependent_of_no_relation u v hv
  intro c d hauxNonzero hauxZero
  have hresultant : Polynomial.resultant f
      (transposeBivariate (auxiliaryRelationPolynomial c d)) = 0 :=
    resultant_auxiliaryRelation_default_eq_zero_of_common_zero
      f a b h k q ha hh hk c d hfDegreeU hfCoeffDegree u v hminpoly
      hfZero hauxZero (by simpa [Nat.mul_comm] using hsize)
  have hbidegrees : a ≤ k ∧ b ≤ h :=
    auxiliaryRelation_bidegree_bounds_of_resultant_eq_zero
      f a b h k ha hh hk c d hf hfDegreeU hfDegreeV hauxNonzero
      hresultant
  exact hdegreeAlternativeExcluded hbidegrees

end

end BGS.CorvajaZannier
