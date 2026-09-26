/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.OrderEscape
public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedIrreducibility
public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedNotSubtorus

/-!
# Nondegeneracy of the actual middle-game trace-curve coefficients

The geometric Corvaja--Zannier theorem needs more than a formal weighted equation.  This module
proves that the two weights coming from every nonzero nonparabolic Markoff fiber are nonzero and
that their product is not one.  These are the exact coefficient hypotheses used by the subsequent
absolute-irreducibility and non-subtorus proofs.
-/

@[expose] public section

namespace BGS.Markoff

/-- The explicit nonzero and nondegeneracy conditions imply every geometric
Corvaja--Zannier admissibility condition for the weighted trace curve. -/
theorem weightedTraceCurve_isCorvajaZannierAdmissible_of_nondegenerateWeights
    {K : Type*} [Field K] (alpha beta : K)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0)
    (hnondegenerate : alpha * beta ≠ 1) :
    WeightedTraceCurveIsCorvajaZannierAdmissible alpha beta := by
  apply weightedTraceCurve_isCorvajaZannierAdmissible_of_absoluteIrreducible
    alpha beta halpha hbeta hnondegenerate
  exact weightedTraceCurve_absolutelyIrreducible
    alpha beta halpha hbeta hnondegenerate

/-- The two weighted trace coefficients attached to a nonzero split-fiber trace are both nonzero,
and their product is the nondegenerate fiber invariant. -/
theorem splitFiberOrbit_weightedTraceCoefficients_nondegenerate
    {E : Type*} [Field E] (w s : Eˣ)
    (hw : (w : E) ^ 2 ≠ 1) (htrace : splitTorusTrace w ≠ 0)
    (hfour : (4 : E) ≠ 0) :
    (s : E) ≠ 0 ∧
      splitFiberProduct w * ((s⁻¹ : Eˣ) : E) ≠ 0 ∧
      (s : E) * (splitFiberProduct w * ((s⁻¹ : Eˣ) : E)) ≠ 1 := by
  refine ⟨Units.ne_zero s, ?_, ?_⟩
  · exact mul_ne_zero (splitFiberProduct_ne_zero w hw htrace) (Units.ne_zero (s⁻¹))
  · rw [splitFiberOrbit_weights_mul]
    exact splitFiberProduct_ne_one_of_four_ne_zero w hfour

/-- Four remains nonzero in the canonical quadratic extension of an odd prime field. -/
theorem four_ne_zero_quadraticFiniteField_of_prime_ne_two
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2) :
    (4 : quadraticFiniteField p) ≠ 0 := by
  apply (map_ne_zero (algebraMap (ZMod p) (quadraticFiniteField p))).mpr
  intro hzero
  have hpDvd : p ∣ 4 := (ZMod.natCast_eq_zero_iff 4 p).mp hzero
  have hpPrime := (Fact.out : p.Prime)
  have hpDvdPow : p ∣ 2 ^ 2 := by simpa using hpDvd
  have hpDvdTwo : p ∣ 2 := hpPrime.dvd_of_dvd_pow hpDvdPow
  have hpLeTwo : p ≤ 2 := Nat.le_of_dvd (by norm_num) hpDvdTwo
  exact hpTwo (Nat.le_antisymm hpLeTwo hpPrime.two_le)

/-- Concrete nondegeneracy for every diagonalized presentation of a nonzero nonparabolic
normalized Markoff fiber. -/
theorem diagonalizedFiber_weightedTraceCoefficients_nondegenerate
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (x : NormalizedPoint (ZMod p)) (hnonzero : x.u1 ≠ 0)
    (w s : (quadraticFiniteField p)ˣ)
    (hw : (w : quadraticFiniteField p) ^ 2 ≠ 1)
    (hpoint : algebraMapNormalizedPoint p x = splitFiberPoint w s) :
    (s : quadraticFiniteField p) ≠ 0 ∧
      splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
        quadraticFiniteField p) ≠ 0 ∧
      (s : quadraticFiniteField p) *
          (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
            quadraticFiniteField p)) ≠ 1 := by
  have htraceEq :
      algebraMap (ZMod p) (quadraticFiniteField p) x.u1 = splitTorusTrace w :=
    congrArg NormalizedPoint.u1 hpoint
  have htrace : splitTorusTrace w ≠ 0 := by
    rw [← htraceEq]
    exact (map_ne_zero (algebraMap (ZMod p) (quadraticFiniteField p))).mpr hnonzero
  exact splitFiberOrbit_weightedTraceCoefficients_nondegenerate
    w s hw htrace (four_ne_zero_quadraticFiniteField_of_prime_ne_two p hpTwo)

/-- Every actual diagonalized nonzero nonparabolic Markoff fiber supplies a
Corvaja--Zannier-admissible weighted trace curve; this is no longer an
independent geometric premise of the order-escape theorem. -/
theorem diagonalizedFiber_weightedTraceCurve_isCorvajaZannierAdmissible
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (x : NormalizedPoint (ZMod p)) (hnonzero : x.u1 ≠ 0)
    (w s : (quadraticFiniteField p)ˣ)
    (hw : (w : quadraticFiniteField p) ^ 2 ≠ 1)
    (hpoint : algebraMapNormalizedPoint p x = splitFiberPoint w s) :
    WeightedTraceCurveIsCorvajaZannierAdmissible
      (s : quadraticFiniteField p)
      (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
        quadraticFiniteField p)) := by
  obtain ⟨halpha, hbeta, hnondegenerate⟩ :=
    diagonalizedFiber_weightedTraceCoefficients_nondegenerate
      p hpTwo x hnonzero w s hw hpoint
  exact weightedTraceCurve_isCorvajaZannierAdmissible_of_nondegenerateWeights
    (s : quadraticFiniteField p)
    (splitFiberProduct w * ((s⁻¹ : (quadraticFiniteField p)ˣ) :
      quadraticFiniteField p)) halpha hbeta hnondegenerate

end BGS.Markoff
