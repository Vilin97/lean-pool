/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierGeometry
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.Bivariate
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Absolute irreducibility of the weighted middle-game trace curve

This module proves the absolute-irreducibility hypothesis exposed by
`MiddleGameCorvajaZannierGeometry`.  The proof uses the published torus change of variables
honestly: the weighted left parameter is first scaled by `alpha`, and then the invertible
birational coordinate `u = x / y` is used after passage to the coefficient fraction field.
The resulting polynomial is the Eisenstein polynomial already proved irreducible in
`TraceCurveGeometry`.
-/

@[expose] public section

namespace BGS.Markoff

open Polynomial

section Scaling

variable {R : Type*} [CommRing R]

/-- Scaling the variable of a polynomial by a unit is an algebra automorphism. -/
noncomputable def polynomialVariableScaleEquiv (c : Rˣ) : R[X] ≃ₐ[R] R[X] := by
  let forward : R[X] →ₐ[R] R[X] := Polynomial.aeval (C (c : R) * X)
  let backward : R[X] →ₐ[R] R[X] := Polynomial.aeval (C ((c⁻¹ : Rˣ) : R) * X)
  refine AlgEquiv.ofAlgHom forward backward ?_ ?_
  · apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, forward, backward, Polynomial.aeval_X,
      map_mul, Polynomial.aeval_C]
    change C (((c⁻¹ : Rˣ) : R)) * (C (c : R) * X) = X
    rw [← mul_assoc, ← C_mul]
    simp
  · apply Polynomial.algHom_ext
    simp only [AlgHom.comp_apply, forward, backward, Polynomial.aeval_X,
      map_mul, Polynomial.aeval_C]
    change C (c : R) * (C (((c⁻¹ : Rˣ) : R)) * X) = X
    rw [← mul_assoc, ← C_mul]
    simp

@[simp]
theorem polynomialVariableScaleEquiv_X (c : Rˣ) :
    polynomialVariableScaleEquiv c X = C (c : R) * X := by
  simp [polynomialVariableScaleEquiv]

@[simp]
theorem polynomialVariableScaleEquiv_C (c : Rˣ) (r : R) :
    polynomialVariableScaleEquiv c (C r) = C r := by
  simp [polynomialVariableScaleEquiv]

end Scaling

section IteratedPolynomial

variable {K : Type*} [Field K]

/-- View a two-variable polynomial as a polynomial in variable `0`, whose coefficients are
ordinary polynomials in variable `1`. -/
noncomputable def finTwoToIteratedPolynomial :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial K[X] :=
  (MvPolynomial.finSuccEquiv K 1).trans
    (Polynomial.mapAlgEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)))

@[simp]
theorem finTwoToIteratedPolynomial_X_zero :
    finTwoToIteratedPolynomial (K := K) (MvPolynomial.X 0) = X := by
  have hinner :
      MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 0) =
        (Polynomial.X : Polynomial (MvPolynomial (Fin 1) K)) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  rw [finTwoToIteratedPolynomial]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 0)) = X
  rw [hinner]
  simp

@[simp]
theorem finTwoToIteratedPolynomial_X_one :
    finTwoToIteratedPolynomial (K := K) (MvPolynomial.X 1) = C X := by
  have hinner :
      MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1) =
        Polynomial.C (MvPolynomial.X (0 : Fin 1)) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp only [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X]
    rw [show (1 : Fin 2) = Fin.succ (0 : Fin 1) by decide]
    rfl
  rw [finTwoToIteratedPolynomial]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.X 1)) = C X
  rw [hinner]
  simp [MvPolynomial.uniqueAlgEquiv]

@[simp]
theorem finTwoToIteratedPolynomial_C (r : K) :
    finTwoToIteratedPolynomial (K := K) (MvPolynomial.C r) = C (C r) := by
  have hinner :
      MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C r) =
        Polynomial.C (MvPolynomial.C r) := by
    rw [MvPolynomial.finSuccEquiv_apply]
    simp
  rw [finTwoToIteratedPolynomial]
  change Polynomial.map (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingHom
    (MvPolynomial.finSuccEquiv K 1 (MvPolynomial.C r)) = C (C r)
  rw [hinner]
  simp [MvPolynomial.uniqueAlgEquiv]

/-- The weighted trace curve in the iterated-polynomial presentation. -/
noncomputable def weightedTraceIteratedPolynomial (alpha beta : K) : Polynomial K[X] :=
  monomial 2 (-X) + monomial 1 (C alpha * X ^ 2 + C beta) + C (-X)

theorem finTwoToIteratedPolynomial_weightedTraceTorusClosurePolynomial
    (alpha beta : K) (hbeta : beta ≠ 0) :
    finTwoToIteratedPolynomial (K := K)
        (weightedTraceTorusClosurePolynomial alpha beta) =
      weightedTraceIteratedPolynomial alpha beta := by
  rw [weightedTraceTorusClosurePolynomial, ite_eq_right hbeta]
  simp [splitTraceCoverPolynomial, weightedTraceIteratedPolynomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

private theorem weightedTraceIteratedPolynomial_isPrimitive
    (alpha beta : K) (hbeta : beta ≠ 0) :
    (weightedTraceIteratedPolynomial alpha beta).IsPrimitive := by
  rw [Polynomial.isPrimitive_iff_isUnit_of_C_dvd]
  intro r hr
  have hcoeff := (Polynomial.C_dvd_iff_dvd_coeff r
    (weightedTraceIteratedPolynomial alpha beta)).mp hr
  have hrY : r ∣ X := by
    have := hcoeff 0
    have hrNegY : r ∣ -X := by
      simpa [weightedTraceIteratedPolynomial] using this
    exact dvd_neg.mp hrNegY
  have hrMiddle : r ∣ C alpha * X ^ 2 + C beta := by
    have hpcoeff :
        (weightedTraceIteratedPolynomial alpha beta).coeff 1 =
          C alpha * X ^ 2 + C beta := by
      norm_num [weightedTraceIteratedPolynomial, Polynomial.coeff_monomial]
    rw [← hpcoeff]
    exact hcoeff 1
  rcases hrY with ⟨q, hq⟩
  rcases hrMiddle with ⟨s, hs⟩
  have hrBeta : r ∣ C beta := by
    refine ⟨s - C alpha * q * X, ?_⟩
    calc
      C beta = (C alpha * X ^ 2 + C beta) - C alpha * X * X := by ring
      _ = r * s - C alpha * (r * q) * X := by rw [hs, hq]
      _ = r * (s - C alpha * q * X) := by ring
  exact isUnit_of_dvd_unit hrBeta
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hbeta))

/-- The swapped Eisenstein polynomial after the invertible scaling `y ↦ alpha * y`.
It is a polynomial in the birational coordinate `u`, with coefficients in `K[y]`. -/
noncomputable def weightedTraceScaledBirationalPolynomial
    (alpha : Kˣ) (beta : K) : Polynomial K[X] :=
  let ay : K[X] := C (alpha : K) * X
  monomial 2 (-(ay ^ 2)) +
    monomial 1 (ay ^ 2 + C ((alpha : K) * beta)) +
    C (-1)

theorem weightedTraceScaledBirationalPolynomial_eq_map_swap
    (alpha : Kˣ) (beta : K) :
    weightedTraceScaledBirationalPolynomial alpha beta =
      Polynomial.mapAlgEquiv (polynomialVariableScaleEquiv alpha)
        (Polynomial.Bivariate.swap
          (normalizedSplitTraceBirationalPolynomial ((alpha : K) * beta))) := by
  simp [weightedTraceScaledBirationalPolynomial,
    normalizedSplitTraceBirationalPolynomial, normalizedSplitTraceLeadingCoefficient,
    normalizedSplitTraceEisensteinPrime, polynomialVariableScaleEquiv,
    Polynomial.Bivariate.swap_apply, ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

/-- The scaled-and-swapped birational polynomial remains irreducible. -/
theorem weightedTraceScaledBirationalPolynomial_irreducible
    (alpha : Kˣ) (beta : K) (hbeta : beta ≠ 0)
    (hnondegenerate : (alpha : K) * beta ≠ 1) :
    Irreducible (weightedTraceScaledBirationalPolynomial alpha beta) := by
  rw [weightedTraceScaledBirationalPolynomial_eq_map_swap]
  exact ((normalizedSplitTraceBirationalPolynomial_irreducible
    ((alpha : K) * beta) (mul_ne_zero alpha.ne_zero hbeta) hnondegenerate).map
      (Polynomial.Bivariate.swap)).map
        (Polynomial.mapAlgEquiv (polynomialVariableScaleEquiv alpha))

private theorem weightedTraceScaledBirationalPolynomial_natDegree_ne_zero
    (alpha : Kˣ) (beta : K) :
    (weightedTraceScaledBirationalPolynomial alpha beta).natDegree ≠ 0 := by
  let ay : K[X] := C (alpha : K) * X
  have hay : ay ≠ 0 := mul_ne_zero (C_ne_zero.mpr alpha.ne_zero) X_ne_zero
  have hcoeff :
      (weightedTraceScaledBirationalPolynomial alpha beta).coeff 2 = -(ay ^ 2) := by
    simp [weightedTraceScaledBirationalPolynomial, ay, Polynomial.coeff_monomial,
      Polynomial.coeff_one]
  have hcoeffNe :
      (weightedTraceScaledBirationalPolynomial alpha beta).coeff 2 ≠ 0 := by
    rw [hcoeff]
    exact neg_ne_zero.mpr (pow_ne_zero 2 hay)
  have hle : 2 ≤ (weightedTraceScaledBirationalPolynomial alpha beta).natDegree :=
    Polynomial.le_natDegree_of_ne_zero hcoeffNe
  omega

/-- The scaled birational polynomial stays irreducible over the coefficient fraction field. -/
theorem weightedTraceScaledBirationalPolynomial_irreducible_fractionMap
    (alpha : Kˣ) (beta : K) (hbeta : beta ≠ 0)
    (hnondegenerate : (alpha : K) * beta ≠ 1) :
    Irreducible
      ((weightedTraceScaledBirationalPolynomial alpha beta).map
        (algebraMap K[X] (FractionRing K[X]))) := by
  have hirr := weightedTraceScaledBirationalPolynomial_irreducible
    alpha beta hbeta hnondegenerate
  have hprimitive := hirr.isPrimitive
    (weightedTraceScaledBirationalPolynomial_natDegree_ne_zero alpha beta)
  exact hprimitive.irreducible_iff_irreducible_map_fraction_map.mp hirr

/-- The unit `alpha * y` in the rational function field `K(y)`. -/
noncomputable def weightedTraceFractionScaleUnit (alpha : Kˣ) :
    (FractionRing K[X])ˣ :=
  Units.mk0
    (algebraMap K[X] (FractionRing K[X]) (C (alpha : K) * X))
    ((map_ne_zero_iff (algebraMap K[X] (FractionRing K[X]))
      (IsFractionRing.injective K[X] (FractionRing K[X]))).mpr
        (mul_ne_zero (C_ne_zero.mpr alpha.ne_zero) X_ne_zero))

@[simp]
theorem weightedTraceFractionScaleUnit_val (alpha : Kˣ) :
    (weightedTraceFractionScaleUnit alpha : FractionRing K[X]) =
      algebraMap K[X] (FractionRing K[X]) (C (alpha : K) * X) := by
  rfl

/-- After passing to `K(y)` and scaling `x` by the invertible element `alpha * y`, the
weighted trace polynomial is `y` times the scaled Eisenstein polynomial. -/
theorem polynomialVariableScaleEquiv_map_weightedTraceIteratedPolynomial
    (alpha : Kˣ) (beta : K) :
    polynomialVariableScaleEquiv (weightedTraceFractionScaleUnit alpha)
        ((weightedTraceIteratedPolynomial (alpha : K) beta).map
          (algebraMap K[X] (FractionRing K[X]))) =
      C (algebraMap K[X] (FractionRing K[X]) X) *
        (weightedTraceScaledBirationalPolynomial alpha beta).map
          (algebraMap K[X] (FractionRing K[X])) := by
  simp [polynomialVariableScaleEquiv, weightedTraceFractionScaleUnit_val,
    weightedTraceIteratedPolynomial, weightedTraceScaledBirationalPolynomial,
    ← Polynomial.C_mul_X_pow_eq_monomial]
  ring

/-- The actual weighted trace polynomial is irreducible in the iterated presentation. -/
theorem weightedTraceIteratedPolynomial_irreducible
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1) :
    Irreducible (weightedTraceIteratedPolynomial alpha beta) := by
  let alphaUnit : Kˣ := Units.mk0 alpha halpha
  have hBirationalFraction :
      Irreducible
        ((weightedTraceScaledBirationalPolynomial alphaUnit beta).map
          (algebraMap K[X] (FractionRing K[X]))) :=
    weightedTraceScaledBirationalPolynomial_irreducible_fractionMap
      alphaUnit beta hbeta (by simpa [alphaUnit] using hnondegenerate)
  have hyNe : algebraMap K[X] (FractionRing K[X]) X ≠ 0 :=
    (map_ne_zero_iff (algebraMap K[X] (FractionRing K[X]))
      (IsFractionRing.injective K[X] (FractionRing K[X]))).mpr X_ne_zero
  have hyUnit : IsUnit
      (C (algebraMap K[X] (FractionRing K[X]) X) :
        Polynomial (FractionRing K[X])) :=
    Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hyNe)
  have hScaled : Irreducible
      (polynomialVariableScaleEquiv (weightedTraceFractionScaleUnit alphaUnit)
        ((weightedTraceIteratedPolynomial alpha beta).map
          (algebraMap K[X] (FractionRing K[X])))) := by
    rw [show alpha = (alphaUnit : K) by rfl,
      polynomialVariableScaleEquiv_map_weightedTraceIteratedPolynomial]
    exact (irreducible_isUnit_mul hyUnit).2 hBirationalFraction
  have hFraction : Irreducible
      ((weightedTraceIteratedPolynomial alpha beta).map
        (algebraMap K[X] (FractionRing K[X]))) := by
    have hback := hScaled.map
      (polynomialVariableScaleEquiv (weightedTraceFractionScaleUnit alphaUnit)).symm
    simpa using hback
  have hprimitive := weightedTraceIteratedPolynomial_isPrimitive alpha beta hbeta
  exact hprimitive.irreducible_iff_irreducible_map_fraction_map.mpr hFraction

/-- The reduced torus closure commutes with injective scalar extension in the nonzero
`beta` branch used by the `(2,2)` middle-game curve. -/
theorem map_weightedTraceTorusClosurePolynomial_of_beta_ne_zero
    {L : Type*} [Field L] (phi : K →+* L) (alpha beta : K) (hbeta : beta ≠ 0) :
    MvPolynomial.map phi (weightedTraceTorusClosurePolynomial alpha beta) =
      weightedTraceTorusClosurePolynomial (phi alpha) (phi beta) := by
  have hMapBeta : phi beta ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr hbeta
  rw [weightedTraceTorusClosurePolynomial, ite_eq_right hbeta,
    weightedTraceTorusClosurePolynomial, ite_eq_right hMapBeta]
  simp [splitTraceCoverPolynomial]

/-- Irreducibility over the ground field, obtained from the iterated-polynomial proof by
the explicit two-variable polynomial equivalence. -/
theorem weightedTraceTorusClosurePolynomial_irreducible
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1) :
    Irreducible (weightedTraceTorusClosurePolynomial alpha beta) := by
  have hImage :=
    finTwoToIteratedPolynomial_weightedTraceTorusClosurePolynomial alpha beta hbeta
  have hIterated := weightedTraceIteratedPolynomial_irreducible
    alpha beta halpha hbeta hnondegenerate
  rw [← hImage] at hIterated
  have hback := hIterated.map (finTwoToIteratedPolynomial (K := K)).symm
  simpa using hback

/-- The actual weighted trace curve is absolutely irreducible when both weights are nonzero
and their product is not one.  Every coordinate change used in the proof is an explicit
algebra equivalence or a Gauss-lemma passage to a fraction field. -/
theorem weightedTraceCurve_absolutelyIrreducible
    (alpha beta : K) (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1) :
    WeightedTraceCurveAbsolutelyIrreducible alpha beta := by
  unfold WeightedTraceCurveAbsolutelyIrreducible
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  rw [map_weightedTraceTorusClosurePolynomial_of_beta_ne_zero phi alpha beta hbeta]
  apply weightedTraceTorusClosurePolynomial_irreducible
  · exact (map_ne_zero_iff phi phi.injective).mpr halpha
  · exact (map_ne_zero_iff phi phi.injective).mpr hbeta
  · intro h
    apply hnondegenerate
    apply phi.injective
    simpa [phi] using h

end IteratedPolynomial

end BGS.Markoff
