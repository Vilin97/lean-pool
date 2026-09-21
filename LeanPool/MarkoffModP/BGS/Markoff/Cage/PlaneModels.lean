/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.Cage.PulledRadicand
import LeanPool.MarkoffModP.BGS.Markoff.Cage.BiquadraticPrimitiveQuartic
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedIrreducibility
import LeanPool.MarkoffModP.BGS.External.GeneralCurveTheorems

/-!
# Direct affine-plane models for the cage

The first variable is the primitive root coordinate and the second variable
is the power parameter.  Passing through `finTwoToIteratedPolynomial` makes
the defining equations polynomials in the root coordinate with coefficients
in the parameter polynomial ring.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The two-variable/iterated-polynomial equivalence commutes with extension
of scalar fields. -/
lemma finTwoToIteratedPolynomial_map
    {L : Type*} [Field L] (phi : K →+* L)
    (p : MvPolynomial (Fin 2) K) :
    finTwoToIteratedPolynomial (K := L) (MvPolynomial.map phi p) =
      (finTwoToIteratedPolynomial (K := K) p).map
        (Polynomial.mapRingHom phi) := by
  let lhs : MvPolynomial (Fin 2) K →+* L[X][X] :=
    (finTwoToIteratedPolynomial (K := L)).toRingEquiv.toRingHom.comp
      (MvPolynomial.map phi)
  let rhs : MvPolynomial (Fin 2) K →+* L[X][X] :=
    (Polynomial.mapRingHom (Polynomial.mapRingHom phi)).comp
      (finTwoToIteratedPolynomial (K := K)).toRingEquiv.toRingHom
  have heq : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, RingHom.comp_apply, finTwoToIteratedPolynomial_C]
    · intro i
      fin_cases i <;>
        simp [lhs, rhs, RingHom.comp_apply,
          finTwoToIteratedPolynomial_X_zero,
          finTwoToIteratedPolynomial_X_one]
  exact DFunLike.congr_fun heq p

/-- The diagonal hyperelliptic model `L² = F_ξ(t)`, written as a polynomial
in `L` over `K[t]`. -/
def cageDiagonalIteratedPolynomial (xi : K) (d : ℕ) : K[X][X] :=
  adjoinSquarePolynomial (cagePulledRadicand xi d)

/-- The off-diagonal primitive-element model.  Its root coordinate is
`S = L + M`; eliminating `L` and `M` gives
`(S² - F_ξ - F_η)² - 4 F_ξ F_η`. -/
def cageOffDiagonalIteratedPolynomial (xi eta : K) (d : ℕ) : K[X][X] :=
  (X ^ 2 - C (cagePulledRadicand xi d + cagePulledRadicand eta d)) ^ 2 -
    C (4 * (cagePulledRadicand xi d * cagePulledRadicand eta d))

/-- The pulled radicand placed in the second bivariate coordinate. -/
def cagePulledRadicandSecondCoordinate (xi : K) (d : ℕ) :
    MvPolynomial (Fin 2) K :=
  MvPolynomial.C (xi ^ 2 - 4) * MvPolynomial.X 1 ^ (4 * d) -
    MvPolynomial.C (2 * (xi ^ 2 + 4)) * MvPolynomial.X 1 ^ (2 * d) +
      MvPolynomial.C (xi ^ 2 - 4)

@[simp]
lemma finTwoToIteratedPolynomial_cagePulledRadicandSecondCoordinate
    (xi : K) (d : ℕ) :
    finTwoToIteratedPolynomial (cagePulledRadicandSecondCoordinate xi d) =
      C (cagePulledRadicand xi d) := by
  rw [cagePulledRadicand_expanded]
  simp [cagePulledRadicandSecondCoordinate]

/-- The diagonal model as the displayed bivariate polynomial
`L² - F_ξ(t)`. -/
def cageDiagonalPlanePolynomial (xi : K) (d : ℕ) : MvPolynomial (Fin 2) K :=
  MvPolynomial.X 0 ^ 2 - cagePulledRadicandSecondCoordinate xi d

/-- The off-diagonal model as an honest bivariate polynomial. -/
def cageOffDiagonalPlanePolynomial (xi eta : K) (d : ℕ) :
    MvPolynomial (Fin 2) K :=
  (MvPolynomial.X 0 ^ 2 -
      (cagePulledRadicandSecondCoordinate xi d +
        cagePulledRadicandSecondCoordinate eta d)) ^ 2 -
    MvPolynomial.C 4 * cagePulledRadicandSecondCoordinate xi d *
      cagePulledRadicandSecondCoordinate eta d

@[simp]
lemma finTwoToIteratedPolynomial_cageDiagonalPlanePolynomial (xi : K) (d : ℕ) :
    finTwoToIteratedPolynomial (cageDiagonalPlanePolynomial xi d) =
      cageDiagonalIteratedPolynomial xi d := by
  simp [cageDiagonalPlanePolynomial, cageDiagonalIteratedPolynomial,
    adjoinSquarePolynomial]

@[simp]
lemma finTwoToIteratedPolynomial_cageOffDiagonalPlanePolynomial
    (xi eta : K) (d : ℕ) :
    finTwoToIteratedPolynomial (cageOffDiagonalPlanePolynomial xi eta d) =
      cageOffDiagonalIteratedPolynomial xi eta d := by
  simp only [cageOffDiagonalPlanePolynomial,
    cageOffDiagonalIteratedPolynomial, map_sub, map_pow, map_add, map_mul,
    finTwoToIteratedPolynomial_X_zero,
    finTwoToIteratedPolynomial_cagePulledRadicandSecondCoordinate,
    finTwoToIteratedPolynomial_C]
  have hC4 : (C (4 : K) : K[X]) = 4 :=
    map_natCast (Polynomial.C : K →+* K[X]) 4
  rw [hC4]
  ring

/-- Gauss's lemma turns nonsquareness of the radicand in `K(t)` into
irreducibility of the diagonal plane equation over `K[t]`. -/
lemma cageDiagonalIteratedPolynomial_irreducible
    {xi : K} (hxi : xi ≠ 0) (hXi : xi ^ 2 - 4 ≠ 0)
    {d : ℕ} (hd : 0 < d) (h2 : (2 : K) ≠ 0)
    (hdegree : (((2 * d : ℕ) : K)) ≠ 0) :
    Irreducible (cageDiagonalIteratedPolynomial xi d) := by
  have hsquarefree :=
    (cagePulledRadicand_separable h2 hxi hXi hd hdegree).squarefree
  have hnonsquare :
      ¬ IsSquare
        (algebraMap K[X] (FractionRing K[X]) (cagePulledRadicand xi d)) :=
    not_isSquare_algebraMap_of_squarefree_not_isUnit hsquarefree
      (cagePulledRadicand_not_isUnit hXi hd)
  have hfraction : Irreducible
      ((cageDiagonalIteratedPolynomial xi d).map
        (algebraMap K[X] (FractionRing K[X]))) := by
    simpa [cageDiagonalIteratedPolynomial, adjoinSquarePolynomial] using
      adjoinSquarePolynomial_irreducible_of_not_isSquare hnonsquare
  have hmonic : (cageDiagonalIteratedPolynomial xi d).Monic :=
    adjoinSquarePolynomial_monic _
  exact hmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mpr
    hfraction

/-- Ground-field irreducibility of the diagonal bivariate polynomial. -/
lemma cageDiagonalPlanePolynomial_irreducible
    {xi : K} (hxi : xi ≠ 0) (hXi : xi ^ 2 - 4 ≠ 0)
    {d : ℕ} (hd : 0 < d) (h2 : (2 : K) ≠ 0)
    (hdegree : (((2 * d : ℕ) : K)) ≠ 0) :
    Irreducible (cageDiagonalPlanePolynomial xi d) := by
  have hiterated := cageDiagonalIteratedPolynomial_irreducible
    hxi hXi hd h2 hdegree
  have hback := hiterated.map (finTwoToIteratedPolynomial (K := K)).symm
  have heq :
      (finTwoToIteratedPolynomial (K := K)).symm
          (cageDiagonalIteratedPolynomial xi d) =
        cageDiagonalPlanePolynomial xi d := by
    rw [← finTwoToIteratedPolynomial_cageDiagonalPlanePolynomial]
    exact (finTwoToIteratedPolynomial (K := K)).symm_apply_apply _
  rw [heq] at hback
  exact hback

/-- The off-diagonal primitive quartic is irreducible over the parameter
polynomial ring.  The only geometric input is the proved independence of the
three pulled-radicand square classes. -/
lemma cageOffDiagonalIteratedPolynomial_irreducible
    {xi eta : K} (hxi : xi ≠ 0) (heta : eta ≠ 0)
    (hXi : xi ^ 2 - 4 ≠ 0) (hEta : eta ^ 2 - 4 ≠ 0)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) {d : ℕ} (hd : 0 < d)
    (h2 : (2 : K) ≠ 0) (hdegree : (((2 * d : ℕ) : K)) ≠ 0) :
    Irreducible (cageOffDiagonalIteratedPolynomial xi eta d) := by
  obtain ⟨hf, hg, hfg⟩ :=
    cagePulledRadicand_squareClasses_independent_ratFunc h2 hxi heta
      hXi hEta hoffDiagonal hd hdegree
  have h2Fraction : (2 : RatFunc K) ≠ 0 := by
    intro hzero
    apply h2
    apply FaithfulSMul.algebraMap_injective K (RatFunc K)
    simpa only [map_ofNat, map_zero] using hzero
  have hfg' : ¬ IsSquare
      (algebraMap K[X] (RatFunc K) (cagePulledRadicand xi d) *
        algebraMap K[X] (RatFunc K) (cagePulledRadicand eta d)) := by
    simpa only [map_mul] using hfg
  have hfractionGeneric := biquadraticPrimitiveQuartic_irreducible
    h2Fraction hf hg hfg'
  have hfraction : Irreducible
      ((cageOffDiagonalIteratedPolynomial xi eta d).map
        (algebraMap K[X] (RatFunc K))) := by
    have heq :
        (cageOffDiagonalIteratedPolynomial xi eta d).map
            (algebraMap K[X] (RatFunc K)) =
          biquadraticPrimitiveQuartic
            (algebraMap K[X] (RatFunc K) (cagePulledRadicand xi d))
            (algebraMap K[X] (RatFunc K) (cagePulledRadicand eta d)) := by
      simp only [cageOffDiagonalIteratedPolynomial,
        biquadraticPrimitiveQuartic, Polynomial.map_sub, Polynomial.map_pow,
        Polynomial.map_C, Polynomial.map_X, Polynomial.map_add,
        Polynomial.map_mul, map_add, map_mul]
      have hfour : algebraMap K[X] (RatFunc K) (4 : K[X]) = (4 : RatFunc K) :=
        map_natCast (algebraMap K[X] (RatFunc K)) 4
      rw [hfour]
      ring
    rw [heq]
    exact hfractionGeneric
  have hmonic : (cageOffDiagonalIteratedPolynomial xi eta d).Monic := by
    have hquadratic : IsMonicOfDegree
        (X ^ 2 - C (cagePulledRadicand xi d + cagePulledRadicand eta d) : K[X][X]) 2 :=
      (isMonicOfDegree_X_pow K[X] 2).sub (by simp)
    exact ((hquadratic.pow 2).sub (by
      have hpos : 0 < 2 * 2 := by norm_num
      simpa only [← C_mul, natDegree_C] using hpos)).monic
  exact hmonic.isPrimitive.irreducible_iff_irreducible_map_fraction_map.mpr
    hfraction

/-- Ground-field irreducibility of the off-diagonal bivariate polynomial. -/
lemma cageOffDiagonalPlanePolynomial_irreducible
    {xi eta : K} (hxi : xi ≠ 0) (heta : eta ≠ 0)
    (hXi : xi ^ 2 - 4 ≠ 0) (hEta : eta ^ 2 - 4 ≠ 0)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) {d : ℕ} (hd : 0 < d)
    (h2 : (2 : K) ≠ 0) (hdegree : (((2 * d : ℕ) : K)) ≠ 0) :
    Irreducible (cageOffDiagonalPlanePolynomial xi eta d) := by
  have hiterated := cageOffDiagonalIteratedPolynomial_irreducible
    hxi heta hXi hEta hoffDiagonal hd h2 hdegree
  have hback := hiterated.map (finTwoToIteratedPolynomial (K := K)).symm
  have heq :
      (finTwoToIteratedPolynomial (K := K)).symm
          (cageOffDiagonalIteratedPolynomial xi eta d) =
        cageOffDiagonalPlanePolynomial xi eta d := by
    rw [← finTwoToIteratedPolynomial_cageOffDiagonalPlanePolynomial]
    exact (finTwoToIteratedPolynomial (K := K)).symm_apply_apply _
  rw [heq] at hback
  exact hback

/-- Scalar extension commutes with the explicit pulled radicand. -/
lemma map_cagePulledRadicand
    {L : Type*} [Field L] (phi : K →+* L) (xi : K) (d : ℕ) :
    (cagePulledRadicand xi d).map phi = cagePulledRadicand (phi xi) d := by
  have h4 : phi (4 : K) = (4 : L) := map_natCast phi 4
  simp only [cagePulledRadicand, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_add, Polynomial.map_one,
    map_sub, map_pow, map_mul]
  rw [h4]

/-- The diagonal plane model is absolutely irreducible. -/
lemma cageDiagonalPlanePolynomial_absolutelyIrreducible
    {xi : K} (hxi : xi ≠ 0) (hXi : xi ^ 2 - 4 ≠ 0)
    {d : ℕ} (hd : 0 < d) (h2 : (2 : K) ≠ 0)
    (hdegree : (((2 * d : ℕ) : K)) ≠ 0) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (cageDiagonalPlanePolynomial xi d)) := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hxi' : phi xi ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr hxi
  have hXi' : (phi xi) ^ 2 - 4 ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr hXi
    rw [map_sub, map_pow] at hmapped
    have hfour : phi (4 : K) = (4 : AlgebraicClosure K) := map_natCast phi 4
    rw [hfour] at hmapped
    exact hmapped
  have h2' : (2 : AlgebraicClosure K) ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr h2
    have htwo : phi (2 : K) = (2 : AlgebraicClosure K) := map_natCast phi 2
    rw [htwo] at hmapped
    exact hmapped
  have hdegree' : (((2 * d : ℕ) : AlgebraicClosure K)) ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr hdegree
    have hcast : phi (((2 * d : ℕ) : K)) =
        (((2 * d : ℕ) : AlgebraicClosure K)) := map_natCast phi (2 * d)
    rw [hcast] at hmapped
    exact hmapped
  have hiterated := cageDiagonalIteratedPolynomial_irreducible
    hxi' hXi' hd h2' hdegree'
  have himage :
      finTwoToIteratedPolynomial (K := AlgebraicClosure K)
          (MvPolynomial.map phi (cageDiagonalPlanePolynomial xi d)) =
        cageDiagonalIteratedPolynomial (phi xi) d := by
    rw [finTwoToIteratedPolynomial_map]
    simp [finTwoToIteratedPolynomial_cageDiagonalPlanePolynomial,
      cageDiagonalIteratedPolynomial, adjoinSquarePolynomial,
      map_cagePulledRadicand]
  rw [← himage] at hiterated
  have hback := hiterated.map
    (finTwoToIteratedPolynomial (K := AlgebraicClosure K)).symm
  simpa [phi] using hback

/-- The off-diagonal primitive quartic is absolutely irreducible. -/
lemma cageOffDiagonalPlanePolynomial_absolutelyIrreducible
    {xi eta : K} (hxi : xi ≠ 0) (heta : eta ≠ 0)
    (hXi : xi ^ 2 - 4 ≠ 0) (hEta : eta ^ 2 - 4 ≠ 0)
    (hoffDiagonal : xi ^ 2 ≠ eta ^ 2) {d : ℕ} (hd : 0 < d)
    (h2 : (2 : K) ≠ 0) (hdegree : (((2 * d : ℕ) : K)) ≠ 0) :
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
        (cageOffDiagonalPlanePolynomial xi eta d)) := by
  let phi : K →+* AlgebraicClosure K := algebraMap K (AlgebraicClosure K)
  have hxi' : phi xi ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr hxi
  have heta' : phi eta ≠ 0 := (map_ne_zero_iff phi phi.injective).mpr heta
  have hXi' : (phi xi) ^ 2 - 4 ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr hXi
    rw [map_sub, map_pow] at hmapped
    have hfour : phi (4 : K) = (4 : AlgebraicClosure K) := map_natCast phi 4
    rw [hfour] at hmapped
    exact hmapped
  have hEta' : (phi eta) ^ 2 - 4 ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr hEta
    rw [map_sub, map_pow] at hmapped
    have hfour : phi (4 : K) = (4 : AlgebraicClosure K) := map_natCast phi 4
    rw [hfour] at hmapped
    exact hmapped
  have hoffDiagonal' : (phi xi) ^ 2 ≠ (phi eta) ^ 2 := by
    intro h
    apply hoffDiagonal
    apply phi.injective
    simpa only [map_pow] using h
  have h2' : (2 : AlgebraicClosure K) ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr h2
    have htwo : phi (2 : K) = (2 : AlgebraicClosure K) := map_natCast phi 2
    rw [htwo] at hmapped
    exact hmapped
  have hdegree' : (((2 * d : ℕ) : AlgebraicClosure K)) ≠ 0 := by
    have hmapped := (map_ne_zero_iff phi phi.injective).mpr hdegree
    have hcast : phi (((2 * d : ℕ) : K)) =
        (((2 * d : ℕ) : AlgebraicClosure K)) := map_natCast phi (2 * d)
    rw [hcast] at hmapped
    exact hmapped
  have hiterated := cageOffDiagonalIteratedPolynomial_irreducible
    hxi' heta' hXi' hEta' hoffDiagonal' hd h2' hdegree'
  have himage :
      finTwoToIteratedPolynomial (K := AlgebraicClosure K)
          (MvPolynomial.map phi (cageOffDiagonalPlanePolynomial xi eta d)) =
        cageOffDiagonalIteratedPolynomial (phi xi) (phi eta) d := by
    rw [finTwoToIteratedPolynomial_map]
    simp [finTwoToIteratedPolynomial_cageOffDiagonalPlanePolynomial,
      cageOffDiagonalIteratedPolynomial, map_cagePulledRadicand]
  rw [← himage] at hiterated
  have hback := hiterated.map
    (finTwoToIteratedPolynomial (K := AlgebraicClosure K)).symm
  simpa [phi] using hback

private lemma degreeOf_C_mul_X_one_pow_first_le (a : K) (n : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (MvPolynomial.C a * MvPolynomial.X 1 ^ n) ≤ 0 := by
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_C,
    MvPolynomial.degreeOf_X_pow_of_ne n (by decide : (0 : Fin 2) ≠ 1)]

private lemma degreeOf_C_mul_X_one_pow_second_le (a : K) (n : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (MvPolynomial.C a * MvPolynomial.X 1 ^ n) ≤ n := by
  refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
  rw [MvPolynomial.degreeOf_C, MvPolynomial.degreeOf_X_self_pow]
  omega

/-- Coordinate-degree bound for a pulled radicand: it is independent of the
root coordinate. -/
lemma cagePulledRadicandSecondCoordinate_degreeOf_first_le
    (xi : K) (d : ℕ) :
    MvPolynomial.degreeOf (0 : Fin 2)
      (cagePulledRadicandSecondCoordinate xi d) ≤ 0 := by
  unfold cagePulledRadicandSecondCoordinate
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · exact degreeOf_C_mul_X_one_pow_first_le _ _
    · exact degreeOf_C_mul_X_one_pow_first_le _ _
  · rw [MvPolynomial.degreeOf_C]

/-- Coordinate-degree bound for a pulled radicand in the power parameter. -/
lemma cagePulledRadicandSecondCoordinate_degreeOf_second_le
    (xi : K) (d : ℕ) :
    MvPolynomial.degreeOf (1 : Fin 2)
      (cagePulledRadicandSecondCoordinate xi d) ≤ 4 * d := by
  unfold cagePulledRadicandSecondCoordinate
  refine (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · exact degreeOf_C_mul_X_one_pow_second_le _ _
    · exact (degreeOf_C_mul_X_one_pow_second_le _ _).trans (by omega)
  · rw [MvPolynomial.degreeOf_C]
    omega

/-- The diagonal model has bidegree at most `(2,4d)`. -/
lemma cageDiagonalPlanePolynomial_hasBidegreeAtMost (xi : K) (d : ℕ) :
    BGS.External.HasBidegreeAtMost
      (cageDiagonalPlanePolynomial xi d) 2 (4 * d) := by
  have hfirst : MvPolynomial.degreeOf (0 : Fin 2)
      (cageDiagonalPlanePolynomial xi d) ≤ 2 := by
    unfold cageDiagonalPlanePolynomial
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · simp
    · exact (cagePulledRadicandSecondCoordinate_degreeOf_first_le xi d).trans
        (by omega)
  have hsecond : MvPolynomial.degreeOf (1 : Fin 2)
      (cageDiagonalPlanePolynomial xi d) ≤ 4 * d := by
    unfold cageDiagonalPlanePolynomial
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · rw [MvPolynomial.degreeOf_X_pow_of_ne 2 (by decide : (1 : Fin 2) ≠ 0)]
      omega
    · exact cagePulledRadicandSecondCoordinate_degreeOf_second_le xi d
  intro monomial hmonomial
  exact ⟨(MvPolynomial.degreeOf_le_iff.mp hfirst) monomial hmonomial,
    (MvPolynomial.degreeOf_le_iff.mp hsecond) monomial hmonomial⟩

/-- The primitive off-diagonal quartic has bidegree at most `(4,8d)`. -/
lemma cageOffDiagonalPlanePolynomial_hasBidegreeAtMost
    (xi eta : K) (d : ℕ) :
    BGS.External.HasBidegreeAtMost
      (cageOffDiagonalPlanePolynomial xi eta d) 4 (8 * d) := by
  have hfirst : MvPolynomial.degreeOf (0 : Fin 2)
      (cageOffDiagonalPlanePolynomial xi eta d) ≤ 4 := by
    unfold cageOffDiagonalPlanePolynomial
    have hsum : MvPolynomial.degreeOf (0 : Fin 2)
        (cagePulledRadicandSecondCoordinate xi d +
          cagePulledRadicandSecondCoordinate eta d) ≤ 0 :=
      (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le
        (cagePulledRadicandSecondCoordinate_degreeOf_first_le xi d)
        (cagePulledRadicandSecondCoordinate_degreeOf_first_le eta d))
    have hinside : MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.X 0 ^ 2 -
          (cagePulledRadicandSecondCoordinate xi d +
            cagePulledRadicandSecondCoordinate eta d)) ≤ 2 :=
      (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le (by simp) (hsum.trans (by omega)))
    have hsquare := MvPolynomial.degreeOf_pow_le (0 : Fin 2)
      (MvPolynomial.X 0 ^ 2 -
        (cagePulledRadicandSecondCoordinate xi d +
          cagePulledRadicandSecondCoordinate eta d)) 2
    have hproduct : MvPolynomial.degreeOf (0 : Fin 2)
        (MvPolynomial.C 4 * cagePulledRadicandSecondCoordinate xi d *
          cagePulledRadicandSecondCoordinate eta d) ≤ 0 := by
      have hleft : MvPolynomial.degreeOf (0 : Fin 2)
          (MvPolynomial.C 4 * cagePulledRadicandSecondCoordinate xi d) ≤ 0 := by
        refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
        rw [MvPolynomial.degreeOf_C]
        simpa using cagePulledRadicandSecondCoordinate_degreeOf_first_le xi d
      refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
      exact (add_le_add hleft
        (cagePulledRadicandSecondCoordinate_degreeOf_first_le eta d)).trans (by omega)
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · exact hsquare.trans (by omega)
    · exact hproduct.trans (by omega)
  have hsecond : MvPolynomial.degreeOf (1 : Fin 2)
      (cageOffDiagonalPlanePolynomial xi eta d) ≤ 8 * d := by
    unfold cageOffDiagonalPlanePolynomial
    have hsum : MvPolynomial.degreeOf (1 : Fin 2)
        (cagePulledRadicandSecondCoordinate xi d +
          cagePulledRadicandSecondCoordinate eta d) ≤ 4 * d :=
      (MvPolynomial.degreeOf_add_le _ _ _).trans (max_le
        (cagePulledRadicandSecondCoordinate_degreeOf_second_le xi d)
        (cagePulledRadicandSecondCoordinate_degreeOf_second_le eta d))
    have hinside : MvPolynomial.degreeOf (1 : Fin 2)
        (MvPolynomial.X 0 ^ 2 -
          (cagePulledRadicandSecondCoordinate xi d +
            cagePulledRadicandSecondCoordinate eta d)) ≤ 4 * d := by
      refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ hsum)
      rw [MvPolynomial.degreeOf_X_pow_of_ne 2 (by decide : (1 : Fin 2) ≠ 0)]
      omega
    refine (MvPolynomial.degreeOf_sub_le _ _ _).trans (max_le ?_ ?_)
    · exact (MvPolynomial.degreeOf_pow_le _ _ _).trans
        ((Nat.mul_le_mul_left 2 hinside).trans (by omega))
    · have hleft : MvPolynomial.degreeOf (1 : Fin 2)
          (MvPolynomial.C 4 * cagePulledRadicandSecondCoordinate xi d) ≤ 4 * d := by
        refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
        rw [MvPolynomial.degreeOf_C]
        simpa using cagePulledRadicandSecondCoordinate_degreeOf_second_le xi d
      refine (MvPolynomial.degreeOf_mul_le _ _ _).trans ?_
      exact (add_le_add hleft
        (cagePulledRadicandSecondCoordinate_degreeOf_second_le eta d)).trans (by omega)
  intro monomial hmonomial
  exact ⟨(MvPolynomial.degreeOf_le_iff.mp hfirst) monomial hmonomial,
    (MvPolynomial.degreeOf_le_iff.mp hsecond) monomial hmonomial⟩

/-- Evaluation of the embedded radicand is ordinary univariate evaluation
in the second coordinate. -/
lemma eval_cagePulledRadicandSecondCoordinate
    (xi : K) (d : ℕ) (root parameter : K) :
    MvPolynomial.eval ![root, parameter]
        (cagePulledRadicandSecondCoordinate xi d) =
      (cagePulledRadicand xi d).eval parameter := by
  rw [cagePulledRadicand_expanded]
  simp [cagePulledRadicandSecondCoordinate]

/-- Zeros of the diagonal plane model are exactly square roots of the
pulled radicand. -/
lemma eval_cageDiagonalPlanePolynomial_eq_zero_iff
    (xi : K) (d : ℕ) (root parameter : K) :
    MvPolynomial.eval ![root, parameter]
        (cageDiagonalPlanePolynomial xi d) = 0 ↔
      root ^ 2 = (cagePulledRadicand xi d).eval parameter := by
  simp [cageDiagonalPlanePolynomial,
    eval_cagePulledRadicandSecondCoordinate, sub_eq_zero]

/-- Evaluation of the off-diagonal plane model is the primitive quartic in
the two scalar radicand values. -/
lemma eval_cageOffDiagonalPlanePolynomial
    (xi eta : K) (d : ℕ) (sumRoot parameter : K) :
    MvPolynomial.eval ![sumRoot, parameter]
        (cageOffDiagonalPlanePolynomial xi eta d) =
      (sumRoot ^ 2 -
          ((cagePulledRadicand xi d).eval parameter +
            (cagePulledRadicand eta d).eval parameter)) ^ 2 -
        4 * (cagePulledRadicand xi d).eval parameter *
          (cagePulledRadicand eta d).eval parameter := by
  simp [cageOffDiagonalPlanePolynomial,
    eval_cagePulledRadicandSecondCoordinate]

/-- Away from the primitive-coordinate boundary `S = 0`, the quartic
equation is equivalent to retaining both quadratic roots.  The explicit
inverse is
`L = (S² + f - g)/(2S)`, `M = (S² - f + g)/(2S)`. -/
lemma primitiveQuarticEquation_iff_exists_rootPair
    (h2 : (2 : K) ≠ 0) {f g sumRoot : K} (hsum : sumRoot ≠ 0) :
    (sumRoot ^ 2 - (f + g)) ^ 2 - 4 * f * g = 0 ↔
      ∃ firstRoot secondRoot : K,
        firstRoot ^ 2 = f ∧ secondRoot ^ 2 = g ∧
          firstRoot + secondRoot = sumRoot := by
  constructor
  · intro hequation
    let firstRoot := (sumRoot ^ 2 + f - g) / (2 * sumRoot)
    let secondRoot := (sumRoot ^ 2 - f + g) / (2 * sumRoot)
    have hdenominator : 2 * sumRoot ≠ 0 := mul_ne_zero h2 hsum
    refine ⟨firstRoot, secondRoot, ?_, ?_, ?_⟩
    · dsimp [firstRoot]
      field_simp [hdenominator]
      linear_combination hequation
    · dsimp [secondRoot]
      field_simp [hdenominator]
      linear_combination hequation
    · dsimp [firstRoot, secondRoot]
      field_simp [hdenominator]
      ring
  · rintro ⟨firstRoot, secondRoot, hfirst, hsecond, hsumRoot⟩
    rw [← hfirst, ← hsecond, ← hsumRoot]
    ring

/-- The preceding primitive-element equivalence applied to the actual cage
plane equation. -/
lemma eval_cageOffDiagonalPlanePolynomial_eq_zero_iff_exists_rootPair
    (h2 : (2 : K) ≠ 0) (xi eta : K) (d : ℕ)
    {sumRoot parameter : K} (hsum : sumRoot ≠ 0) :
    MvPolynomial.eval ![sumRoot, parameter]
        (cageOffDiagonalPlanePolynomial xi eta d) = 0 ↔
      ∃ firstRoot secondRoot : K,
        firstRoot ^ 2 = (cagePulledRadicand xi d).eval parameter ∧
        secondRoot ^ 2 = (cagePulledRadicand eta d).eval parameter ∧
        firstRoot + secondRoot = sumRoot := by
  rw [eval_cageOffDiagonalPlanePolynomial]
  exact primitiveQuarticEquation_iff_exists_rootPair h2 hsum

end

end BGS.Markoff
