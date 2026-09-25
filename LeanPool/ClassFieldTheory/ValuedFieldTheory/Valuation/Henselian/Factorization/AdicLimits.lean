/-
Copyright (c) 2026 n-yamaguchi-0729. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: n-yamaguchi-0729
-/
module


public import LeanPool.ClassFieldTheory.ValuedFieldTheory.Valuation.Henselian.Factorization.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
/-!
# coefficientwise limit preparation

This file records the coefficientwise Cauchy form of the infinite Hensel
approximants.  It is the input needed for the adic-completeness step in
the coefficientwise proof of Hensel's lemma.
-/

@[expose] public section

noncomputable
section

open scoped Polynomial
open scoped BigOperators

namespace AlgebraicNumberTheory
namespace Valuations

/-- the directed adic Cauchy estimate for a coefficient
sequence: later differences from stage `M` lie in `I^(M+1)`. -/
def henselFactorizationAdicCoeffCauchy
    {R : Type*} [CommRing R] (I : Ideal R) (x : ℕ → R) : Prop :=
  ∀ {M N : ℕ}, M ≤ N → x N - x M ∈ I ^ (M + 1)

/-- A coefficientwise Cauchy estimate for a polynomial sequence gives an
adic Cauchy estimate for each fixed coefficient. -/
theorem henselFactorization_coeff_adicCoeffCauchy_of_sub_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) {Pseq : ℕ → R[X]}
    (hsub :
      ∀ {M N : ℕ}, M ≤ N → ∀ i : ℕ,
        (Pseq N - Pseq M).coeff i ∈ I ^ (M + 1))
    (i : ℕ) :
    henselFactorizationAdicCoeffCauchy I (fun N : ℕ => (Pseq N).coeff i) := by
  intro M N hMN
  simpa [henselFactorizationAdicCoeffCauchy, Polynomial.coeff_sub] using hsub hMN i

/-- the coefficientwise `I^(M+1)` estimate gives mathlib's
`I`-adic Cauchy condition after weakening `I^(M+1) ≤ I^M`. -/
theorem henselFactorization_adicCoeffCauchy_isAdicCauchy
    {R : Type*} [CommRing R] (I : Ideal R) {x : ℕ → R}
    (hx : henselFactorizationAdicCoeffCauchy I x) :
    AdicCompletion.IsAdicCauchy I R x := by
  intro M N hMN
  apply SModEq.sub_mem.mpr
  have hdeep : x N - x M ∈ I ^ M :=
    Ideal.pow_le_pow_right (Nat.le_succ M) (hx hMN)
  have hsign : x M - x N ∈ I ^ M := by
    simpa [neg_sub] using (I ^ M).neg_mem hdeep
  simpa [smul_eq_mul, Ideal.mul_top] using hsign

/-- precompleteness supplies a coefficient limit for every
coefficient sequence satisfying the directed estimate. -/
theorem henselFactorization_exists_adicCoeffLimit
    {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    {x : ℕ → R}
    (hx : henselFactorizationAdicCoeffCauchy I x) :
    ∃ L : R, ∀ n : ℕ, x n - L ∈ I ^ n := by
  obtain ⟨L, hL⟩ :=
    IsPrecomplete.prec (show IsPrecomplete I R from inferInstance)
      (henselFactorization_adicCoeffCauchy_isAdicCauchy I hx)
  refine ⟨L, fun n => ?_⟩
  have hmem := SModEq.sub_mem.mp (hL n)
  simpa [smul_eq_mul, Ideal.mul_top] using hmem

/-- assemble finitely many coefficient limits into the
polynomial supported in degrees at most `N`. -/
def henselFactorizationPolyOfLimitCoeffs
    {R : Type*} [Semiring R] (N : ℕ) (c : ℕ → R) : R[X] :=
  Finset.sum (Finset.range (N + 1)) fun i => Polynomial.monomial i (c i)

/-- coefficients of the finite polynomial assembled from
coefficient limits, inside the cutoff. -/
theorem henselFactorization_polyOfLimitCoeffs_coeff_of_le
    {R : Type*} [Semiring R] {N n : ℕ} (c : ℕ → R) (hn : n ≤ N) :
    (henselFactorizationPolyOfLimitCoeffs N c).coeff n = c n := by
  classical
  unfold henselFactorizationPolyOfLimitCoeffs
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single n]
  · simp
  · intro b _hb hbn
    simp [Polynomial.coeff_monomial, hbn]
  · intro hnot
    exact False.elim (hnot (Finset.mem_range.mpr (Nat.lt_succ_of_le hn)))

/-- coefficients of the finite polynomial assembled from
coefficient limits vanish above the cutoff. -/
theorem henselFactorization_polyOfLimitCoeffs_coeff_eq_zero_of_lt
    {R : Type*} [Semiring R] {N n : ℕ} (c : ℕ → R) (hn : N < n) :
    (henselFactorizationPolyOfLimitCoeffs N c).coeff n = 0 := by
  classical
  unfold henselFactorizationPolyOfLimitCoeffs
  rw [Polynomial.finsetSum_coeff]
  refine Finset.sum_eq_zero ?_
  intro b hb
  have hbn : b ≠ n := by
    intro hbn
    have hn_le : n ≤ N := Nat.lt_succ_iff.mp (by simpa [hbn] using hb)
    exact (Nat.not_lt_of_ge hn_le) hn
  simp [Polynomial.coeff_monomial, hbn]

/-- the polynomial assembled from finitely many coefficient
limits has the stated degree bound. -/
theorem henselFactorization_polyOfLimitCoeffs_natDegree_le
    {R : Type*} [Semiring R] (N : ℕ) (c : ℕ → R) :
    (henselFactorizationPolyOfLimitCoeffs N c).natDegree ≤ N := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro n hn
  exact henselFactorization_polyOfLimitCoeffs_coeff_eq_zero_of_lt (c := c) hn

/-- bounded polynomial approximants with coefficientwise
adic limits have a bounded polynomial limit. -/
theorem henselFactorization_exists_limitPolynomial_of_bounded_coeffLimits
    {R : Type*} [CommRing R] (I : Ideal R) [IsPrecomplete I R]
    {N : ℕ} {Pseq : ℕ → R[X]}
    (hdeg : ∀ n : ℕ, (Pseq n).natDegree ≤ N)
    (hcauchy :
      ∀ i : ℕ, henselFactorizationAdicCoeffCauchy I
        (fun n : ℕ => (Pseq n).coeff i)) :
    ∃ P : R[X], P.natDegree ≤ N ∧
      ∀ n i : ℕ, (Pseq n - P).coeff i ∈ I ^ n := by
  classical
  let L : ℕ → R :=
    fun i =>
      Classical.choose
        (henselFactorization_exists_adicCoeffLimit (I := I) (hcauchy i))
  let P : R[X] := henselFactorizationPolyOfLimitCoeffs N L
  refine ⟨P, henselFactorization_polyOfLimitCoeffs_natDegree_le N L, ?_⟩
  intro n i
  by_cases hi : i ≤ N
  · have hlim :=
      Classical.choose_spec
        (henselFactorization_exists_adicCoeffLimit (I := I) (hcauchy i)) n
    simpa [P, L, Polynomial.coeff_sub,
      henselFactorization_polyOfLimitCoeffs_coeff_of_le (c := L) hi] using hlim
  · have hlt : N < i := Nat.lt_of_not_ge hi
    have hseq : (Pseq n).coeff i = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hdeg n) hlt)
    have hP : P.coeff i = 0 :=
      henselFactorization_polyOfLimitCoeffs_coeff_eq_zero_of_lt (c := L) hlt
    simp [Polynomial.coeff_sub, hseq, hP]

/-- if all coefficients of the left factor lie in an ideal,
then all coefficients of its product with any polynomial lie in the same
ideal. -/
theorem henselFactorization_mul_left_coeff_mem_ideal
    {R : Type*} [CommRing R] (I : Ideal R) {A B : R[X]}
    (hA : ∀ i : ℕ, A.coeff i ∈ I) :
    ∀ i : ℕ, (A * B).coeff i ∈ I := by
  intro i
  rw [Polynomial.coeff_mul]
  exact I.sum_mem fun p _hp => I.mul_mem_right _ (hA p.1)

/-- if all coefficients of the right factor lie in an ideal,
then all coefficients of its product with any polynomial lie in the same
ideal. -/
theorem henselFactorization_mul_right_coeff_mem_ideal
    {R : Type*} [CommRing R] (I : Ideal R) {A B : R[X]}
    (hB : ∀ i : ℕ, B.coeff i ∈ I) :
    ∀ i : ℕ, (A * B).coeff i ∈ I := by
  intro i
  rw [Polynomial.coeff_mul]
  exact I.sum_mem fun p _hp => I.mul_mem_left _ (hB p.2)

/-- coefficientwise convergence is preserved by multiplying
two polynomial approximants. -/
theorem henselFactorization_mul_sub_mul_coeff_mem_of_coeff_mem
    {R : Type*} [CommRing R] (I : Ideal R) {A A' B B' : R[X]}
    (hA : ∀ i : ℕ, (A - A').coeff i ∈ I)
    (hB : ∀ i : ℕ, (B - B').coeff i ∈ I) :
    ∀ i : ℕ, (A * B - A' * B').coeff i ∈ I := by
  have hdecomp : A * B - A' * B' = (A - A') * B + A' * (B - B') := by
    ring
  intro i
  rw [hdecomp, Polynomial.coeff_add]
  exact I.add_mem
    (henselFactorization_mul_left_coeff_mem_ideal (I := I) hA i)
    (henselFactorization_mul_right_coeff_mem_ideal (I := I) hB i)

/-- combine the product convergence with the residual error
estimate at one adic level. -/
theorem henselFactorization_limit_factor_coeff_mem_of_approximants
    {R : Type*} [CommRing R] (I : Ideal R)
    {f G H Gn Hn : R[X]}
    (herr : ∀ i : ℕ, (f - Gn * Hn).coeff i ∈ I)
    (hG : ∀ i : ℕ, (Gn - G).coeff i ∈ I)
    (hH : ∀ i : ℕ, (Hn - H).coeff i ∈ I) :
    ∀ i : ℕ, (f - G * H).coeff i ∈ I := by
  have hdecomp : f - G * H = (f - Gn * Hn) + (Gn * Hn - G * H) := by
    ring
  intro i
  rw [hdecomp, Polynomial.coeff_add]
  exact I.add_mem (herr i)
    (henselFactorization_mul_sub_mul_coeff_mem_of_coeff_mem
      (I := I) hG hH i)

/-- a polynomial whose coefficients lie in every adic power is
zero in a Hausdorff coefficient ring. -/
theorem henselFactorization_polynomial_eq_zero_of_coeff_mem_all_powers
    {R : Type*} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    {P : R[X]}
    (hP : ∀ n i : ℕ, P.coeff i ∈ I ^ n) :
    P = 0 := by
  ext i
  apply IsHausdorff.haus (show IsHausdorff I R from inferInstance)
  intro n
  have hmem : P.coeff i - 0 ∈ I ^ n := by
    simpa using hP n i
  simpa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] using hmem

/-- if the approximating factorization and both factors
converge coefficientwise at every adic level, then the limiting polynomials
factor `f`. -/
theorem henselFactorization_limit_factor_eq_of_approximants
    {R : Type*} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    {f G H : R[X]} {Gseq Hseq : ℕ → R[X]}
    (herr : ∀ n i : ℕ, (f - Gseq n * Hseq n).coeff i ∈ I ^ n)
    (hG : ∀ n i : ℕ, (Gseq n - G).coeff i ∈ I ^ n)
    (hH : ∀ n i : ℕ, (Hseq n - H).coeff i ∈ I ^ n) :
    f = G * H := by
  have hzero : f - G * H = 0 := by
    apply henselFactorization_polynomial_eq_zero_of_coeff_mem_all_powers (I := I)
    intro n i
    exact henselFactorization_limit_factor_coeff_mem_of_approximants
      (I := I ^ n) (herr n) (hG n) (hH n) i
  exact sub_eq_zero.mp hzero

/-- the limit of approximants preserving a fixed residual
class preserves that residual class.  Only the first adic level is needed. -/
theorem henselFactorization_limit_reduction_of_approx_reduction
    {R : Type*} [CommRing R] (I : Ideal R)
    {P P0 : R[X]} {Pseq : ℕ → R[X]}
    (hlim : ∀ n i : ℕ, (Pseq n - P).coeff i ∈ I ^ n)
    (hred : ∀ n i : ℕ, (Pseq n - P0).coeff i ∈ I) :
    ∀ i : ℕ, (P - P0).coeff i ∈ I := by
  intro i
  have hlim1 : (Pseq 1 - P).coeff i ∈ I := by
    simpa using hlim 1 i
  have hred1 : (Pseq 1 - P0).coeff i ∈ I := hred 1 i
  have hdecomp : P - P0 = -(Pseq 1 - P) + (Pseq 1 - P0) := by
    ring
  rw [hdecomp, Polynomial.coeff_add, Polynomial.coeff_neg]
  exact I.add_mem (I.neg_mem hlim1) hred1

/-- coefficientwise membership in a ring-hom kernel gives
equality after mapping coefficients. -/
theorem henselFactorization_map_eq_of_sub_coeff_mem_ker
    {R k : Type*} [CommRing R] [CommRing k] (φ : R →+* k)
    {P Q : R[X]}
    (hcoeff : ∀ i : ℕ, (P - Q).coeff i ∈ RingHom.ker φ) :
    P.map φ = Q.map φ := by
  have hzero : (P - Q).map φ = 0 :=
    (henselFactorization_map_eq_zero_iff_coeff_mem_ker φ (P - Q)).2 hcoeff
  rw [Polynomial.map_sub] at hzero
  exact sub_eq_zero.mp hzero

/-- coefficientwise maximal-ideal congruence is exactly
equality after mapping to the residue field. -/
theorem henselFactorization_residue_map_eq_of_sub_coeff_mem_maximalIdeal
    {R : Type*} [CommRing R] [IsLocalRing R] {P Q : R[X]}
    (hcoeff : ∀ i : ℕ, (P - Q).coeff i ∈ IsLocalRing.maximalIdeal R) :
    P.map (IsLocalRing.residue R) = Q.map (IsLocalRing.residue R) := by
  apply henselFactorization_map_eq_of_sub_coeff_mem_ker
  intro i
  have hi := hcoeff i
  rwa [IsLocalRing.ker_residue]

end Valuations
end AlgebraicNumberTheory

end
