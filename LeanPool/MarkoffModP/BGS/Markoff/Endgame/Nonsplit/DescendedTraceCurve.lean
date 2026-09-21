/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Endgame.Nonsplit.CayleyParametrization
import LeanPool.MarkoffModP.BGS.Markoff.Endgame.Nonsplit.SeededCover
import LeanPool.MarkoffModP.BGS.Markoff.Endgame.WeilBoundAssumption
import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# The descended seeded nonsplit trace curve

The Cayley coordinate converts the seeded nonsplit equation into one polynomial equation over
the base field.  This file constructs that polynomial, proves the scalar-extension formula and
its bidegree bounds, and compares its base-field solutions exactly with the original torus
solutions.  Absolute irreducibility is deliberately a theorem to be proved, not an assumption.
-/

namespace BGS.Markoff

noncomputable section

variable (p : ℕ) [Fact p.Prime]

private abbrev F := ZMod p
private abbrev E := quadraticFiniteField p

noncomputable local instance : Fintype (E p) := Fintype.ofFinite (E p)
noncomputable local instance : DecidableEq (quadraticNormOneTorus p) := Classical.decEq _

/-- Apply the quadratic field trace coefficientwise to a polynomial. -/
def quadraticCoefficientTracePolynomial (P : Polynomial (E p)) : Polynomial (F p) :=
  P.sum fun n c => Polynomial.monomial n (Algebra.trace (F p) (E p) c)

@[simp]
theorem quadraticCoefficientTracePolynomial_coeff (P : Polynomial (E p)) (n : ℕ) :
    (quadraticCoefficientTracePolynomial p P).coeff n =
      Algebra.trace (F p) (E p) (P.coeff n) := by
  classical
  rw [quadraticCoefficientTracePolynomial, Polynomial.coeff_sum]
  simp only [Polynomial.sum_def]
  by_cases hn : n ∈ P.support
  · rw [Finset.sum_eq_single n]
    · simp
    · intro b hb hbn
      rw [Polynomial.coeff_monomial, if_neg hbn]
    · exact fun h => (h hn).elim
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.notMem_support_iff.mp hn, map_zero]
    · intro b hb
      rw [Polynomial.coeff_monomial]
      exact if_neg (fun h : b = n => hn (h ▸ hb))

/-- After scalar extension, coefficientwise trace is `P + Frobenius(P)`. -/
theorem quadraticCoefficientTracePolynomial_map (P : Polynomial (E p)) :
    (quadraticCoefficientTracePolynomial p P).map (algebraMap (F p) (E p)) =
      P + P.map (_root_.frobenius (E p) p) := by
  ext n
  simp [algebraMap_quadraticTrace p, frobenius_def]

/-- The linear Cayley factor whose zero is the Frobenius conjugate of the chosen nonbase
element. -/
def quadraticCayleyConjugateFactorPolynomial : Polynomial (E p) :=
  Polynomial.X - Polynomial.C (quadraticNonbaseElement p ^ p)

/-- The seed-dependent numerator before descent. -/
def seededCayleyTraceNumeratorPolynomial
    (s : (E p)ˣ) (d : ℕ) : Polynomial (F p) :=
  quadraticCoefficientTracePolynomial p
    (Polynomial.C (s : E p) * quadraticCayleyConjugateFactorPolynomial p ^ (2 * d))

theorem seededCayleyTraceNumeratorPolynomial_map (s : (E p)ˣ) (d : ℕ) :
    (seededCayleyTraceNumeratorPolynomial p s d).map (algebraMap (F p) (E p)) =
      Polynomial.C (s : E p) *
          (Polynomial.X - Polynomial.C (quadraticNonbaseElement p ^ p)) ^ (2 * d) +
        Polynomial.C ((s : E p) ^ p) *
          (Polynomial.X - Polynomial.C (quadraticNonbaseElement p)) ^ (2 * d) := by
  rw [seededCayleyTraceNumeratorPolynomial, quadraticCoefficientTracePolynomial_map]
  rw [quadraticCayleyConjugateFactorPolynomial]
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  change Polynomial.C (s : E p) *
        (Polynomial.X - Polynomial.C (quadraticNonbaseElement p ^ p)) ^ (2 * d) +
      Polynomial.C ((s : E p) ^ p) *
        (Polynomial.X - Polynomial.C ((quadraticNonbaseElement p ^ p) ^ p)) ^ (2 * d) = _
  rw [quadraticNonbaseElement_frobenius_frobenius p]

/-- The norm of the Cayley linear factor, written directly over the base field. -/
def quadraticCayleyNormPolynomial : Polynomial (F p) :=
  Polynomial.X ^ 2 -
    Polynomial.C (Algebra.trace (F p) (E p) (quadraticNonbaseElement p)) * Polynomial.X +
    Polynomial.C (Algebra.norm (F p) (quadraticNonbaseElement p))

theorem quadraticCayleyNormPolynomial_map :
    (quadraticCayleyNormPolynomial p).map (algebraMap (F p) (E p)) =
      (Polynomial.X - Polynomial.C (quadraticNonbaseElement p ^ p)) *
        (Polynomial.X - Polynomial.C (quadraticNonbaseElement p)) := by
  rw [quadraticCayleyNormPolynomial, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_C, algebraMap_quadraticTrace p, algebraMap_quadraticNorm p]
  rw [Polynomial.C_add, Polynomial.C_mul]
  ring

theorem algebraMap_eval_seededCayleyTraceNumeratorPolynomial
    (s : (E p)ˣ) (d : ℕ) (z : F p) :
    algebraMap (F p) (E p) ((seededCayleyTraceNumeratorPolynomial p s d).eval z) =
      (s : E p) *
          (algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) ^ (2 * d) +
        (s : E p) ^ p *
          (algebraMap (F p) (E p) z - quadraticNonbaseElement p) ^ (2 * d) := by
  calc
    algebraMap (F p) (E p) ((seededCayleyTraceNumeratorPolynomial p s d).eval z) =
        ((seededCayleyTraceNumeratorPolynomial p s d).map
          (algebraMap (F p) (E p))).eval (algebraMap (F p) (E p) z) := by
      rw [← Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.eval₂_at_apply (algebraMap (F p) (E p)) z).symm
    _ = _ := by rw [seededCayleyTraceNumeratorPolynomial_map]; simp

theorem algebraMap_eval_quadraticCayleyNormPolynomial (z : F p) :
    algebraMap (F p) (E p) ((quadraticCayleyNormPolynomial p).eval z) =
      (algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p) := by
  calc
    algebraMap (F p) (E p) ((quadraticCayleyNormPolynomial p).eval z) =
        ((quadraticCayleyNormPolynomial p).map
          (algebraMap (F p) (E p))).eval (algebraMap (F p) (E p) z) := by
      rw [← Polynomial.eval₂_eq_eval_map]
      exact (Polynomial.eval₂_at_apply (algebraMap (F p) (E p)) z).symm
    _ = _ := by rw [quadraticCayleyNormPolynomial_map]; simp

/-- Embed a univariate polynomial in the first coordinate of a bivariate polynomial. -/
def univariateInFirstCoordinate {K : Type*} [CommSemiring K]
    (P : Polynomial K) : MvPolynomial (Fin 2) K :=
  P.sum fun n c => MvPolynomial.C c * MvPolynomial.X 0 ^ n

@[simp]
theorem eval_univariateInFirstCoordinate {K : Type*} [CommSemiring K]
    (P : Polynomial K) (x y : K) :
    MvPolynomial.eval ![x, y] (univariateInFirstCoordinate P) = P.eval x := by
  classical
  simp [univariateInFirstCoordinate, Polynomial.sum_def, Polynomial.eval_eq_sum]

private theorem degreeOf_finset_sum_le {K ι : Type*} [CommSemiring K]
    (coordinate : Fin 2) (terms : ι → MvPolynomial (Fin 2) K)
    (indices : Finset ι) (bound : ℕ)
    (hterms : ∀ i ∈ indices, MvPolynomial.degreeOf coordinate (terms i) ≤ bound) :
    MvPolynomial.degreeOf coordinate (∑ i ∈ indices, terms i) ≤ bound := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert i indices hi ih =>
      rw [Finset.sum_insert hi]
      exact (MvPolynomial.degreeOf_add_le _ _ _).trans
        (max_le (hterms i (Finset.mem_insert_self i indices))
          (ih fun j hj => hterms j (Finset.mem_insert_of_mem hj)))

theorem univariateInFirstCoordinate_degreeOf_first_le
    {K : Type*} [CommSemiring K] [Nontrivial K] (P : Polynomial K) :
    MvPolynomial.degreeOf (0 : Fin 2) (univariateInFirstCoordinate P) ≤ P.natDegree := by
  classical
  rw [univariateInFirstCoordinate, Polynomial.sum_def]
  apply degreeOf_finset_sum_le (0 : Fin 2) _ P.support P.natDegree
  intro n hn
  calc
    MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C (P.coeff n) * MvPolynomial.X 0 ^ n) ≤
        MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.C (P.coeff n)) +
          MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 0 ^ n) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ 0 + n := by
      gcongr
      · rw [MvPolynomial.degreeOf_C]
      · calc
          MvPolynomial.degreeOf (0 : Fin 2)
              (MvPolynomial.X 0 ^ n : MvPolynomial (Fin 2) K) ≤
              n * MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 0) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = n := by rw [MvPolynomial.degreeOf_X]; simp
    _ ≤ P.natDegree := by simpa using Polynomial.le_natDegree_of_mem_supp n hn

theorem univariateInFirstCoordinate_degreeOf_second_le
    {K : Type*} [CommSemiring K] [Nontrivial K] (P : Polynomial K) :
    MvPolynomial.degreeOf (1 : Fin 2) (univariateInFirstCoordinate P) ≤ 0 := by
  classical
  rw [univariateInFirstCoordinate, Polynomial.sum_def]
  apply degreeOf_finset_sum_le (1 : Fin 2) _ P.support 0
  intro n hn
  calc
    MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.C (P.coeff n) * MvPolynomial.X 0 ^ n) ≤
        MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.C (P.coeff n)) +
          MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0 ^ n) :=
      MvPolynomial.degreeOf_mul_le _ _ _
    _ ≤ 0 := by
      have hpow : MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.X 0 ^ n : MvPolynomial (Fin 2) K) ≤ 0 := by
        calc
          _ ≤ n * MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 0) :=
            MvPolynomial.degreeOf_pow_le _ _ _
          _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num
      rw [MvPolynomial.degreeOf_C]
      simpa using hpow

private theorem natDegree_linearFactor_le_one {K : Type*} [Ring K] [Nontrivial K] (a : K) :
    (Polynomial.X - Polynomial.C a).natDegree ≤ 1 :=
  (Polynomial.natDegree_sub_le _ _).trans (by simp)

theorem seededCayleyTraceNumeratorPolynomial_natDegree_le
    (s : (E p)ˣ) (d : ℕ) :
    (seededCayleyTraceNumeratorPolynomial p s d).natDegree ≤ 2 * d := by
  rw [← Polynomial.natDegree_map_eq_of_injective
    (algebraMap (F p) (E p)).injective,
    seededCayleyTraceNumeratorPolynomial_map]
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ ?_)
  · have hlinear := natDegree_linearFactor_le_one
      (quadraticNonbaseElement p ^ p)
    have hpow : ((Polynomial.X - Polynomial.C (quadraticNonbaseElement p ^ p)) ^
        (2 * d)).natDegree ≤ 2 * d :=
      Polynomial.natDegree_pow_le.trans (by
        simpa using Nat.mul_le_mul_left (2 * d) hlinear)
    exact Polynomial.natDegree_mul_le.trans (by simpa using hpow)
  · have hlinear := natDegree_linearFactor_le_one (quadraticNonbaseElement p)
    have hpow : ((Polynomial.X - Polynomial.C (quadraticNonbaseElement p)) ^
        (2 * d)).natDegree ≤ 2 * d :=
      Polynomial.natDegree_pow_le.trans (by
        simpa using Nat.mul_le_mul_left (2 * d) hlinear)
    exact Polynomial.natDegree_mul_le.trans (by simpa using hpow)

theorem quadraticCayleyNormPolynomial_natDegree_le :
    (quadraticCayleyNormPolynomial p).natDegree ≤ 2 := by
  rw [← Polynomial.natDegree_map_eq_of_injective
    (algebraMap (F p) (E p)).injective,
    quadraticCayleyNormPolynomial_map]
  calc
    _ ≤ (Polynomial.X - Polynomial.C (quadraticNonbaseElement p ^ p)).natDegree +
        (Polynomial.X - Polynomial.C (quadraticNonbaseElement p)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ 2 := by
      have hleft := natDegree_linearFactor_le_one (quadraticNonbaseElement p ^ p)
      have hright := natDegree_linearFactor_le_one (quadraticNonbaseElement p)
      omega

/-- The explicit bivariate polynomial over `ZMod p` defining the descended seeded nonsplit
cover.  Coordinate `0` is the Cayley affine coordinate and coordinate `1` is the base-field
unit parameter. -/
def seededNonsplitDescendedPolynomial (s : (E p)ˣ) (d e : ℕ) :
    MvPolynomial (Fin 2) (F p) :=
  univariateInFirstCoordinate (seededCayleyTraceNumeratorPolynomial p s d) *
      MvPolynomial.X 1 ^ e -
    univariateInFirstCoordinate (quadraticCayleyNormPolynomial p) ^ d *
      (MvPolynomial.X 1 ^ (2 * e) + 1)

theorem eval_seededNonsplitDescendedPolynomial
    (s : (E p)ˣ) (d e : ℕ) (z u : F p) :
    MvPolynomial.eval ![z, u] (seededNonsplitDescendedPolynomial p s d e) =
      (seededCayleyTraceNumeratorPolynomial p s d).eval z * u ^ e -
        (quadraticCayleyNormPolynomial p).eval z ^ d * (u ^ (2 * e) + 1) := by
  simp [seededNonsplitDescendedPolynomial]

private theorem degreeOf_first_X_one_pow_le {K : Type*} [CommSemiring K]
    [Nontrivial K] (n : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) K) ≤ 0 := by
  calc
    _ ≤ n * MvPolynomial.degreeOf (0 : Fin 2) (MvPolynomial.X 1) :=
      MvPolynomial.degreeOf_pow_le _ _ _
    _ = 0 := by rw [MvPolynomial.degreeOf_X]; norm_num

private theorem degreeOf_second_X_one_pow_le {K : Type*} [CommSemiring K]
    [Nontrivial K] (n : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (MvPolynomial.X 1 ^ n : MvPolynomial (Fin 2) K) ≤ n := by
  calc
    _ ≤ n * MvPolynomial.degreeOf (1 : Fin 2) (MvPolynomial.X 1) :=
      MvPolynomial.degreeOf_pow_le _ _ _
    _ = n := by rw [MvPolynomial.degreeOf_X]; norm_num

theorem seededNonsplitDescendedPolynomial_degreeOf_first_le
    (s : (E p)ˣ) (d e : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2) (seededNonsplitDescendedPolynomial p s d e) ≤
      2 * d := by
  rw [seededNonsplitDescendedPolynomial]
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have hnum := (univariateInFirstCoordinate_degreeOf_first_le
      (seededCayleyTraceNumeratorPolynomial p s d)).trans
        (seededCayleyTraceNumeratorPolynomial_natDegree_le p s d)
    have hu := degreeOf_first_X_one_pow_le (K := F p) e
    omega
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have hnormBase := (univariateInFirstCoordinate_degreeOf_first_le
      (quadraticCayleyNormPolynomial p)).trans
        (quadraticCayleyNormPolynomial_natDegree_le p)
    have hnormPow := (MvPolynomial.degreeOf_pow_le (0 : Fin 2)
      (univariateInFirstCoordinate (quadraticCayleyNormPolynomial p)) d).trans
        (Nat.mul_le_mul_left d hnormBase)
    have hsum := (MvPolynomial.degreeOf_add_le (0 : Fin 2)
      (MvPolynomial.X 1 ^ (2 * e) : MvPolynomial (Fin 2) (F p)) 1).trans
        (max_le (degreeOf_first_X_one_pow_le (K := F p) (2 * e)) (by simp))
    omega

theorem seededNonsplitDescendedPolynomial_degreeOf_second_le
    (s : (E p)ˣ) (d e : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2) (seededNonsplitDescendedPolynomial p s d e) ≤
      2 * e := by
  rw [seededNonsplitDescendedPolynomial]
  refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have hnum := univariateInFirstCoordinate_degreeOf_second_le
      (seededCayleyTraceNumeratorPolynomial p s d)
    have hu := degreeOf_second_X_one_pow_le (K := F p) e
    omega
  · refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
    have hnormBase := univariateInFirstCoordinate_degreeOf_second_le
      (quadraticCayleyNormPolynomial p)
    have hnormPow := (MvPolynomial.degreeOf_pow_le (1 : Fin 2)
      (univariateInFirstCoordinate (quadraticCayleyNormPolynomial p)) d).trans
        (Nat.mul_le_mul_left d hnormBase)
    have hsum := (MvPolynomial.degreeOf_add_le (1 : Fin 2)
      (MvPolynomial.X 1 ^ (2 * e) : MvPolynomial (Fin 2) (F p)) 1).trans
        (max_le (degreeOf_second_X_one_pow_le (K := F p) (2 * e)) (by simp))
    omega

theorem seededNonsplitDescendedPolynomial_hasBidegreeAtMost
    (s : (E p)ˣ) (d e : ℕ) :
    BGS.External.HasBidegreeAtMost
      (seededNonsplitDescendedPolynomial p s d e) (2 * d) (2 * e) := by
  intro monomial hmonomial
  exact ⟨
    (MvPolynomial.degreeOf_le_iff.mp
      (seededNonsplitDescendedPolynomial_degreeOf_first_le p s d e)) monomial hmonomial,
    (MvPolynomial.degreeOf_le_iff.mp
      (seededNonsplitDescendedPolynomial_degreeOf_second_le p s d e)) monomial hmonomial⟩

private theorem clearedSeededFractionEquation_iff
    {K : Type*} [Field K] (seed conjugateSeed X Y V : K)
    (hX : X ≠ 0) (hY : Y ≠ 0) (hV : V ≠ 0) :
    (seed * X ^ 2 + conjugateSeed * Y ^ 2) * V - X * Y * (V ^ 2 + 1) = 0 ↔
      seed * (X / Y) + conjugateSeed * (X / Y)⁻¹ = V + V⁻¹ := by
  field_simp [hX, hY, hV]
  constructor <;> intro h <;> linear_combination h

private theorem clearedSeededCayleyEquation_iff
    {K : Type*} [Field K] (seed conjugateSeed A B u : K) (d e : ℕ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hu : u ≠ 0) :
    (seed * A ^ (2 * d) + conjugateSeed * B ^ (2 * d)) * u ^ e -
          (A * B) ^ d * (u ^ (2 * e) + 1) = 0 ↔
      seed * (A / B) ^ d + conjugateSeed * ((A / B) ^ d)⁻¹ =
        u ^ e + (u ^ e)⁻¹ := by
  rw [Nat.mul_comm 2 d, pow_mul, pow_mul, Nat.mul_comm 2 e, pow_mul,
    div_pow, mul_pow]
  exact clearedSeededFractionEquation_iff seed conjugateSeed (A ^ d) (B ^ d) (u ^ e)
    (pow_ne_zero d hA) (pow_ne_zero d hB) (pow_ne_zero e hu)

/-- Vanishing of the descended base-field polynomial is exactly the seeded nonsplit trace
equation at the Cayley point. -/
theorem eval_seededNonsplitDescendedPolynomial_eq_zero_iff
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ)
    (z : F p) (u : (F p)ˣ) :
    MvPolynomial.eval ![z, (u : F p)]
        (seededNonsplitDescendedPolynomial p s.1 d e) = 0 ↔
      SeededNonsplitTraceCoverEquation p k s d e (quadraticCayleyPoint p z) u := by
  rw [eval_seededNonsplitDescendedPolynomial]
  rw [seededNonsplitTraceCoverEquation_iff_weightedSplitTraceCover]
  have hmapZero :
      (seededCayleyTraceNumeratorPolynomial p s.1 d).eval z * (u : F p) ^ e -
            (quadraticCayleyNormPolynomial p).eval z ^ d * ((u : F p) ^ (2 * e) + 1) = 0 ↔
        algebraMap (F p) (E p)
          ((seededCayleyTraceNumeratorPolynomial p s.1 d).eval z * (u : F p) ^ e -
            (quadraticCayleyNormPolynomial p).eval z ^ d *
              ((u : F p) ^ (2 * e) + 1)) = 0 := by
    constructor
    · intro h; rw [h, map_zero]
    · intro h; exact (algebraMap (F p) (E p)).injective (by simpa using h)
  rw [hmapZero]
  simp only [map_sub, map_mul, map_pow, map_add, map_one]
  rw [algebraMap_eval_seededCayleyTraceNumeratorPolynomial,
    algebraMap_eval_quadraticCayleyNormPolynomial]
  unfold SplitTraceCurveEquation weightedSplitTorusTrace splitTorusTrace
  change
    (((s.1 : E p) *
          (algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) ^ (2 * d) +
        (s.1 : E p) ^ p *
          (algebraMap (F p) (E p) z - quadraticNonbaseElement p) ^ (2 * d)) *
        algebraMap (F p) (E p) (u : F p) ^ e -
      ((algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p) *
        (algebraMap (F p) (E p) z - quadraticNonbaseElement p)) ^ d *
        (algebraMap (F p) (E p) (u : F p) ^ (2 * e) + 1) = 0) ↔ _
  have hA : algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => quadraticNonbaseElement_frobenius_not_mem_range p ⟨z, h⟩
  have hB : algebraMap (F p) (E p) z - quadraticNonbaseElement p ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => quadraticNonbaseElement_not_mem_range p ⟨z, h⟩
  have hu : algebraMap (F p) (E p) (u : F p) ≠ 0 :=
    (map_ne_zero (algebraMap (F p) (E p))).mpr (Units.ne_zero u)
  rw [clearedSeededCayleyEquation_iff _ _ _ _ _ d e
    hA hB hu]
  simp only [seededBaseUnitInQuadraticField, quadraticCayleyPoint,
    quadraticCayleyUnit, Units.val_mk0, Units.val_pow_eq_pow_val,
    Units.val_inv_eq_inv_val]
  rfl

/-- Base-field solutions of the descended affine equation with the second coordinate restricted
to a unit. -/
def seededNonsplitDescendedSolutions
    (s : (E p)ˣ) (d e : ℕ) : Finset (F p × (F p)ˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    MvPolynomial.eval ![z.1, (z.2 : F p)]
      (seededNonsplitDescendedPolynomial p s d e) = 0

@[simp]
theorem mem_seededNonsplitDescendedSolutions_iff
    (s : (E p)ˣ) (d e : ℕ) (z : F p × (F p)ˣ) :
    z ∈ seededNonsplitDescendedSolutions p s d e ↔
      MvPolynomial.eval ![z.1, (z.2 : F p)]
        (seededNonsplitDescendedPolynomial p s d e) = 0 := by
  classical
  simp [seededNonsplitDescendedSolutions]

/-- Seeded nonsplit solutions with the identity point removed from the norm-one torus. -/
def seededNonsplitNonidentitySolutions
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) :
    Finset ({w : quadraticNormOneTorus p // w ≠ 1} × (F p)ˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    SeededNonsplitTraceCoverEquation p k s d e z.1.1 z.2

@[simp]
theorem mem_seededNonsplitNonidentitySolutions_iff
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ)
    (z : {w : quadraticNormOneTorus p // w ≠ 1} × (F p)ˣ) :
    z ∈ seededNonsplitNonidentitySolutions p k s d e ↔
      SeededNonsplitTraceCoverEquation p k s d e z.1.1 z.2 := by
  classical
  simp [seededNonsplitNonidentitySolutions]

/-- Cayley parametrization gives an exact bijection, with no multiplicity, between descended
solutions and nonidentity torus solutions. -/
theorem seededNonsplitDescendedSolutions_card_eq_nonidentity_card
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) :
    (seededNonsplitDescendedSolutions p s.1 d e).card =
      (seededNonsplitNonidentitySolutions p k s d e).card := by
  classical
  apply Finset.card_bij'
      (fun z _ => ((quadraticCayleyParameterEquiv p z.1), z.2))
      (fun z _ => ((quadraticCayleyParameterEquiv p).symm z.1, z.2))
  · intro z hz
    rw [mem_seededNonsplitNonidentitySolutions_iff]
    change SeededNonsplitTraceCoverEquation p k s d e
      (quadraticCayleyPoint p z.1) z.2
    rw [← eval_seededNonsplitDescendedPolynomial_eq_zero_iff p k s d e z.1 z.2]
    exact (mem_seededNonsplitDescendedSolutions_iff p s.1 d e z).mp hz
  · intro z hz
    apply Prod.ext
    · exact (quadraticCayleyParameterEquiv p).symm_apply_apply z.1
    · rfl
  · intro z hz
    apply Prod.ext
    · exact (quadraticCayleyParameterEquiv p).apply_symm_apply z.1
    · rfl
  · intro z hz
    rw [mem_seededNonsplitDescendedSolutions_iff]
    rw [eval_seededNonsplitDescendedPolynomial_eq_zero_iff p k s d e]
    have hzEquation := (mem_seededNonsplitNonidentitySolutions_iff p k s d e z).mp hz
    have hpoint := congrArg Subtype.val
      ((quadraticCayleyParameterEquiv p).apply_symm_apply z.1)
    change quadraticCayleyPoint p ((quadraticCayleyParameterEquiv p).symm z.1) = z.1.1 at hpoint
    rw [hpoint]
    exact hzEquation

theorem quadraticCayleyNormPolynomial_eval_ne_zero (z : F p) :
    (quadraticCayleyNormPolynomial p).eval z ≠ 0 := by
  intro hzero
  have hmapped := congrArg (algebraMap (F p) (E p)) hzero
  rw [map_zero, algebraMap_eval_quadraticCayleyNormPolynomial] at hmapped
  have hleft : algebraMap (F p) (E p) z - quadraticNonbaseElement p ^ p ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => quadraticNonbaseElement_frobenius_not_mem_range p ⟨z, h⟩
  have hright : algebraMap (F p) (E p) z - quadraticNonbaseElement p ≠ 0 := by
    rw [sub_ne_zero]
    exact fun h => quadraticNonbaseElement_not_mem_range p ⟨z, h⟩
  exact (mul_ne_zero hleft hright) hmapped

/-- For positive exponents the descended plane curve has no affine zero with second coordinate
zero.  Thus the affine Hasse--Weil count introduces no hidden `u = 0` boundary. -/
theorem eval_seededNonsplitDescendedPolynomial_zero_second_ne_zero
    (s : (E p)ˣ) (d e : ℕ) (hd : 0 < d) (he : 0 < e) (z : F p) :
    MvPolynomial.eval ![z, (0 : F p)]
      (seededNonsplitDescendedPolynomial p s d e) ≠ 0 := by
  rw [eval_seededNonsplitDescendedPolynomial]
  have he0 : e ≠ 0 := Nat.ne_of_gt he
  have htwoe0 : 2 * e ≠ 0 := by omega
  rw [zero_pow he0, zero_pow htwoe0]
  simp only [mul_zero, zero_add, add_zero, mul_one, zero_sub, neg_ne_zero]
  exact pow_ne_zero d (quadraticCayleyNormPolynomial_eval_ne_zero p z)

private theorem affineDescendedZero_second_ne_zero
    (s : (E p)ˣ) (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (z : F p × F p)
    (hz : z ∈ BGS.External.affinePlaneCurveZeros (F p)
      (seededNonsplitDescendedPolynomial p s d e)) : z.2 ≠ 0 := by
  intro hzero
  have hzEval := (BGS.External.mem_affinePlaneCurveZeros_iff).mp hz
  rw [hzero] at hzEval
  exact eval_seededNonsplitDescendedPolynomial_zero_second_ne_zero
    p s d e hd he z.1 hzEval

/-- The general affine-plane zero set and the unit-restricted descended set have exactly the
same cardinality for positive exponents. -/
theorem affinePlaneCurveZeros_seededNonsplitDescendedPolynomial_card_eq
    (s : (E p)ˣ) (d e : ℕ) (hd : 0 < d) (he : 0 < e) :
    (BGS.External.affinePlaneCurveZeros (F p)
      (seededNonsplitDescendedPolynomial p s d e)).card =
      (seededNonsplitDescendedSolutions p s d e).card := by
  classical
  apply Finset.card_bij'
      (fun z hz => (z.1, Units.mk0 z.2
        (affineDescendedZero_second_ne_zero p s d e hd he z hz)))
      (fun z _ => (z.1, (z.2 : F p)))
  · intro z hz
    rw [mem_seededNonsplitDescendedSolutions_iff]
    exact (BGS.External.mem_affinePlaneCurveZeros_iff).mp hz
  · intro z hz
    apply Prod.ext <;> rfl
  · intro z hz
    apply Prod.ext
    · rfl
    · apply Units.ext; rfl
  · intro z hz
    rw [BGS.External.mem_affinePlaneCurveZeros_iff]
    exact (mem_seededNonsplitDescendedSolutions_iff p s d e z).mp hz

/-- All seeded nonsplit torus solutions, including the identity point. -/
def seededNonsplitTraceCurveSolutions
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) :
    Finset (quadraticNormOneTorus p × (F p)ˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    SeededNonsplitTraceCoverEquation p k s d e z.1 z.2

@[simp]
theorem mem_seededNonsplitTraceCurveSolutions_iff
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ)
    (z : quadraticNormOneTorus p × (F p)ˣ) :
    z ∈ seededNonsplitTraceCurveSolutions p k s d e ↔
      SeededNonsplitTraceCoverEquation p k s d e z.1 z.2 := by
  classical
  simp [seededNonsplitTraceCurveSolutions]

/-- The precise omitted Cayley boundary: solutions lying above the identity of the norm-one
torus. -/
def seededNonsplitIdentityBoundarySolutions
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) : Finset (F p)ˣ := by
  classical
  exact Finset.univ.filter fun u =>
    SeededNonsplitTraceCoverEquation p k s d e 1 u

@[simp]
theorem mem_seededNonsplitIdentityBoundarySolutions_iff
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) (u : (F p)ˣ) :
    u ∈ seededNonsplitIdentityBoundarySolutions p k s d e ↔
      SeededNonsplitTraceCoverEquation p k s d e 1 u := by
  classical
  simp [seededNonsplitIdentityBoundarySolutions]

private theorem nonidentityFilter_card_eq
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) :
    ((seededNonsplitTraceCurveSolutions p k s d e).filter fun z => z.1 ≠ 1).card =
      (seededNonsplitNonidentitySolutions p k s d e).card := by
  classical
  apply Finset.card_bij'
      (fun z hz => (⟨z.1, (Finset.mem_filter.mp hz).2⟩, z.2))
      (fun z _ => (z.1.1, z.2))
  · intro z hz
    apply Prod.ext <;> rfl
  · intro z hz
    apply Prod.ext
    · apply Subtype.ext; rfl
    · rfl
  · intro z hz
    rw [mem_seededNonsplitNonidentitySolutions_iff]
    exact (mem_seededNonsplitTraceCurveSolutions_iff p k s d e z).mp
      (Finset.mem_filter.mp hz).1
  · intro z hz
    rw [Finset.mem_filter]
    exact ⟨(mem_seededNonsplitTraceCurveSolutions_iff p k s d e _).mpr
      ((mem_seededNonsplitNonidentitySolutions_iff p k s d e z).mp hz), z.1.2⟩

private theorem identityFilter_card_eq
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) :
    ((seededNonsplitTraceCurveSolutions p k s d e).filter fun z => ¬ z.1 ≠ 1).card =
      (seededNonsplitIdentityBoundarySolutions p k s d e).card := by
  classical
  apply Finset.card_bij'
      (fun z _ => z.2)
      (fun u _ => (1, u))
  · intro z hz
    have hzMem := Finset.mem_filter.mp hz
    apply Prod.ext
    · exact (not_ne_iff.mp (Finset.mem_filter.mp hz).2).symm
    · rfl
  · intro u hu
    rfl
  · intro z hz
    rw [mem_seededNonsplitIdentityBoundarySolutions_iff]
    have hzMem := Finset.mem_filter.mp hz
    have hone : z.1 = 1 := not_ne_iff.mp hzMem.2
    simpa [hone] using
      (mem_seededNonsplitTraceCurveSolutions_iff p k s d e z).mp hzMem.1
  · intro u hu
    rw [Finset.mem_filter]
    exact ⟨(mem_seededNonsplitTraceCurveSolutions_iff p k s d e _).mpr
      ((mem_seededNonsplitIdentityBoundarySolutions_iff p k s d e u).mp hu), by simp⟩

/-- Exact count comparison, including the unique missing Cayley chart fiber `w = 1`. -/
theorem seededNonsplitTraceCurveSolutions_card_eq_descended_add_identityBoundary
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) :
    (seededNonsplitTraceCurveSolutions p k s d e).card =
      (seededNonsplitDescendedSolutions p s.1 d e).card +
        (seededNonsplitIdentityBoundarySolutions p k s d e).card := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := seededNonsplitTraceCurveSolutions p k s d e) (fun z => z.1 ≠ 1)
  rw [nonidentityFilter_card_eq p k s d e,
    ← seededNonsplitDescendedSolutions_card_eq_nonidentity_card p k s d e,
    identityFilter_card_eq p k s d e] at hsplit
  exact hsplit.symm

/-- The one-variable polynomial cutting out the identity Cayley boundary. -/
def seededNonsplitIdentityBoundaryPolynomial
    (s : E p) (e : ℕ) : Polynomial (F p) :=
  Polynomial.X ^ (2 * e) -
    Polynomial.C (Algebra.trace (F p) (E p) s) * Polynomial.X ^ e + 1

theorem seededNonsplitIdentityBoundaryEquation_iff
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) (u : (F p)ˣ) :
    SeededNonsplitTraceCoverEquation p k s d e 1 u ↔
      (seededNonsplitIdentityBoundaryPolynomial p (s.1 : E p) e).eval (u : F p) = 0 := by
  unfold SeededNonsplitTraceCoverEquation seededNonsplitIdentityBoundaryPolynomial
  simp only [one_pow, Subgroup.coe_one, Units.val_one, mul_one, splitTorusTrace,
    Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val, Polynomial.eval_add,
    Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C, Polynomial.eval_one]
  rw [Nat.mul_comm 2 e, pow_mul]
  constructor
  · intro h
    field_simp [Units.ne_zero u] at h
    linear_combination -h
  · intro h
    field_simp [Units.ne_zero u]
    linear_combination -h

theorem seededNonsplitIdentityBoundaryPolynomial_ne_zero
    (s : E p) (e : ℕ) (he : 0 < e) :
    seededNonsplitIdentityBoundaryPolynomial p s e ≠ 0 := by
  intro hzero
  have hcoeff := congrArg (fun P : Polynomial (F p) => P.coeff 0) hzero
  have he0 : e ≠ 0 := Nat.ne_of_gt he
  have h0e : 0 ≠ e := he0.symm
  have htwoe0 : 2 * e ≠ 0 := by omega
  have h0twoe : 0 ≠ 2 * e := htwoe0.symm
  simp [seededNonsplitIdentityBoundaryPolynomial, he0, h0e, htwoe0, h0twoe] at hcoeff

theorem seededNonsplitIdentityBoundaryPolynomial_natDegree_le
    (s : E p) (e : ℕ) :
    (seededNonsplitIdentityBoundaryPolynomial p s e).natDegree ≤ 2 * e := by
  unfold seededNonsplitIdentityBoundaryPolynomial
  refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
  refine (Polynomial.natDegree_sub_le _ _).trans (max_le (by simp) ?_)
  exact Polynomial.natDegree_mul_le.trans (by simp; omega)

/-- The omitted identity fiber contributes at most `2e` points. -/
theorem seededNonsplitIdentityBoundarySolutions_card_le
    (k : (F p)ˣ) (s : ↑(quadraticNormFiber p k)) (d e : ℕ) (he : 0 < e) :
    (seededNonsplitIdentityBoundarySolutions p k s d e).card ≤ 2 * e := by
  classical
  let P := seededNonsplitIdentityBoundaryPolynomial p (s.1 : E p) e
  have hP : P ≠ 0 := seededNonsplitIdentityBoundaryPolynomial_ne_zero p _ e he
  have hmaps : Set.MapsTo (fun u : (F p)ˣ => (u : F p))
      ↑(seededNonsplitIdentityBoundarySolutions p k s d e) ↑P.roots.toFinset := by
    intro u hu
    change (u : F p) ∈ P.roots.toFinset
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP]
    exact (seededNonsplitIdentityBoundaryEquation_iff p k s d e u).mp
      ((mem_seededNonsplitIdentityBoundarySolutions_iff p k s d e u).mp hu)
  have hinj : Set.InjOn (fun u : (F p)ˣ => (u : F p))
      ↑(seededNonsplitIdentityBoundarySolutions p k s d e) := by
    intro u hu v hv huv
    exact Units.ext huv
  calc
    _ ≤ P.roots.toFinset.card := Finset.card_le_card_of_injOn _ hmaps hinj
    _ ≤ P.roots.card := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ ≤ 2 * e := seededNonsplitIdentityBoundaryPolynomial_natDegree_le p _ e

/-- The generic seeded solution set is definitionally the existing-conic solution set after
specializing its norm-fiber index. -/
theorem existingConicSeedNonsplitTraceCurveSolutions_eq_seeded
    (t : F p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↑(quadraticConicNormFiber p t ht ht0)) (d e : ℕ) :
    existingConicSeedNonsplitTraceCurveSolutions p t ht ht0 s d e =
      seededNonsplitTraceCurveSolutions p
        (quadraticFiberProductUnit p t ht ht0) s d e := by
  ext z
  rw [mem_existingConicSeedNonsplitTraceCurveSolutions_iff]
  erw [mem_seededNonsplitTraceCurveSolutions_iff]
  rfl

/-- Exact existing-conic count comparison with both affine boundaries exposed: `u = 0`
contributes nothing for positive exponents, while `w = 1` is the displayed boundary term. -/
theorem existingConicSeedNonsplitTraceCurveSolutions_card_eq_affine_add_identityBoundary
    (t : F p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↑(quadraticConicNormFiber p t ht ht0)) (d e : ℕ)
    (hd : 0 < d) (he : 0 < e) :
    (existingConicSeedNonsplitTraceCurveSolutions p t ht ht0 s d e).card =
      (BGS.External.affinePlaneCurveZeros (F p)
        (seededNonsplitDescendedPolynomial p s.1 d e)).card +
      (seededNonsplitIdentityBoundarySolutions p
        (quadraticFiberProductUnit p t ht ht0) s d e).card := by
  rw [existingConicSeedNonsplitTraceCurveSolutions_eq_seeded]
  erw [seededNonsplitTraceCurveSolutions_card_eq_descended_add_identityBoundary]
  rw [← affinePlaneCurveZeros_seededNonsplitDescendedPolynomial_card_eq p s.1 d e hd he]

end

end BGS.Markoff
