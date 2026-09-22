/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Algebra.Polynomial.SpecificDegree
import LeanPool.MarkoffModP.BGS.Markoff.Cage.IncidenceGeometry

/-!
# The shifted cage trace cover

The off-diagonal cage base is the biquadratic incidence function field in the
common original coordinate `y`.  The next cover adjoins a root `R` of

`R^2 - (3y) * R + 1`.

This file proves the genuinely new branch calculation: the discriminant
`9y^2 - 4` is independent of both incidence square classes, remains a
nonsquare after the two quadratic adjunctions, and hence makes the trace
quadratic irreducible over the exact incidence function-field presentation.

It deliberately does not claim that `R` is not a `q`-th power.  That
place-at-infinity statement is the remaining Kummer obstruction for the
full shifted Laurent cover.
-/

namespace BGS.Markoff

open Polynomial

noncomputable section

variable {K : Type*} [Field K]

/-- The discriminant `9y² - 4` of the normalized trace quadratic. -/
def cageTraceBranchPolynomial : K[X] :=
  C 9 * X ^ 2 - C 4

/-- The quadratic whose root is a unit with prescribed trace. -/
def traceRootPolynomial {R : Type*} [CommRing R] (trace : R) : R[X] :=
  X ^ 2 - C trace * X + 1

/-- The prescribed-trace quadratic is monic. -/
lemma traceRootPolynomial_monic {R : Type*} [Nontrivial R] [CommRing R] (trace : R) :
    (traceRootPolynomial trace).Monic := by
  simpa [traceRootPolynomial] using isMonicOfDegree_sub_add_two trace (1 : R) |>.monic

/-- The prescribed-trace quadratic has degree two. -/
@[simp]
lemma traceRootPolynomial_natDegree {R : Type*} [Nontrivial R] [CommRing R] (trace : R) :
    (traceRootPolynomial trace).natDegree = 2 := by
  simpa [traceRootPolynomial] using
    isMonicOfDegree_sub_add_two trace (1 : R) |>.natDegree_eq

/-- A prescribed-trace quadratic over a domain is irreducible when its
discriminant is not a square. -/
lemma traceRootPolynomial_irreducible_of_discriminant_not_isSquare
    {R : Type*} [CommRing R] [IsDomain R]
    (trace : R) (hdisc : ¬ IsSquare (trace ^ 2 - 4)) :
    Irreducible (traceRootPolynomial trace) := by
  rw [(traceRootPolynomial_monic trace).irreducible_iff_roots_eq_zero_of_degree_le_three]
  · apply Multiset.eq_zero_of_forall_notMem
    intro root hroot
    have heval := (mem_roots (traceRootPolynomial_monic trace).ne_zero).mp hroot
    have heq : root ^ 2 - trace * root + 1 = 0 := by
      simpa [traceRootPolynomial] using heval
    apply hdisc
    refine ⟨2 * root - trace, ?_⟩
    calc
      trace ^ 2 - 4 =
          (2 * root - trace) * (2 * root - trace) -
            4 * (root ^ 2 - trace * root + 1) := by ring
      _ = (2 * root - trace) * (2 * root - trace) := by rw [heq]; ring
  · simp
  · simp

/-- The trace discriminant polynomial has degree two outside characteristic three. -/
lemma cageTraceBranchPolynomial_natDegree (h3 : (3 : K) ≠ 0) :
    (cageTraceBranchPolynomial : K[X]).natDegree = 2 := by
  rw [cageTraceBranchPolynomial, natDegree_sub_C,
    natDegree_C_mul_X_pow 2 (9 : K)]
  exact by
    convert mul_ne_zero h3 h3 using 1
    norm_num

/-- The trace discriminant polynomial is not a unit. -/
lemma cageTraceBranchPolynomial_not_isUnit (h3 : (3 : K) ≠ 0) :
    ¬ IsUnit (cageTraceBranchPolynomial : K[X]) :=
  not_isUnit_of_natDegree_pos _ <| by
    rw [cageTraceBranchPolynomial_natDegree h3]
    norm_num

/-- The two trace branch points are distinct outside characteristics two and three. -/
lemma cageTraceBranchPolynomial_separable
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) :
    (cageTraceBranchPolynomial : K[X]).Separable := by
  have h4 : (4 : K) ≠ 0 := by
    convert mul_ne_zero h2 h2 using 1
    norm_num
  have h9 : (9 : K) ≠ 0 := by
    convert mul_ne_zero h3 h3 using 1
    norm_num
  have hquot : (4 / 9 : K) ≠ 0 := div_ne_zero h4 h9
  have hsep : (X ^ 2 - C (4 / 9) : K[X]).Separable :=
    separable_X_pow_sub_C _ h2 hquot
  have hunit : IsUnit (C (9 : K) : K[X]) :=
    isUnit_C.mpr (isUnit_iff_ne_zero.mpr h9)
  have heq : (cageTraceBranchPolynomial : K[X]) =
      C (9 : K) * (X ^ 2 - C (4 / 9)) := by
    simp only [cageTraceBranchPolynomial, mul_sub]
    rw [← C_mul, mul_div_cancel₀ (4 : K) h9]
  rw [heq]
  exact hsep.unit_mul hunit

/-- An explicit constant Bezout combination of an incidence branch polynomial
and the trace discriminant polynomial. -/
lemma incidenceBranchPolynomial_cageTrace_linearCombination (a : K) :
    C (9 * a ^ 2 - 4) * cageTraceBranchPolynomial -
        C 9 * incidenceBranchPolynomial a = C 16 := by
  simp only [cageTraceBranchPolynomial, incidenceBranchPolynomial]
  ring_nf
  rw [← C_mul, ← C_neg, ← C_mul, ← C_add]
  congr 1
  ring

/-- Every nondegenerate incidence branch polynomial is coprime to the trace
discriminant polynomial; the Bezout constant is `16`. -/
lemma incidenceBranchPolynomial_isCoprime_cageTrace
    (h2 : (2 : K) ≠ 0) (a : K) :
    IsCoprime (incidenceBranchPolynomial a) cageTraceBranchPolynomial := by
  have h16 : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 2 ^ 4 by norm_num]
    exact pow_ne_zero 4 h2
  refine ⟨-(C (16 : K)⁻¹ * C 9),
    C (16 : K)⁻¹ * C (9 * a ^ 2 - 4), ?_⟩
  calc
    -(C (16 : K)⁻¹ * C 9) * incidenceBranchPolynomial a +
        (C (16 : K)⁻¹ * C (9 * a ^ 2 - 4)) * cageTraceBranchPolynomial =
      C (16 : K)⁻¹ *
        (C (9 * a ^ 2 - 4) * cageTraceBranchPolynomial -
          C 9 * incidenceBranchPolynomial a) := by ring
    _ = C (16 : K)⁻¹ * C 16 := by
      rw [incidenceBranchPolynomial_cageTrace_linearCombination]
    _ = 1 := by rw [← C_mul, inv_mul_cancel₀ h16, map_one]

/-- The trace discriminant and its products with either incidence branch
class are all nonsquares in the rational function field. -/
lemma cageTraceBranchSquareClasses_independent_ratFunc
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 9 * a ^ 2 - 4 ≠ 0) (hB : 9 * b ^ 2 - 4 ≠ 0)
    (hab : a ^ 2 ≠ b ^ 2) :
    ¬ IsSquare (algebraMap K[X] (RatFunc K) cageTraceBranchPolynomial) ∧
      ¬ IsSquare (algebraMap K[X] (RatFunc K)
        (incidenceBranchPolynomial a * cageTraceBranchPolynomial)) ∧
      ¬ IsSquare (algebraMap K[X] (RatFunc K)
        (incidenceBranchPolynomial b * cageTraceBranchPolynomial)) ∧
      ¬ IsSquare (algebraMap K[X] (RatFunc K)
        (incidenceBranchPolynomial a * incidenceBranchPolynomial b *
          cageTraceBranchPolynomial)) := by
  have hsepA := incidenceBranchPolynomial_separable h2 ha hA
  have hsepB := incidenceBranchPolynomial_separable h2 hb hB
  have hsepTrace := cageTraceBranchPolynomial_separable h2 h3
  have hcopAB := incidenceBranchPolynomial_isCoprime h2 hab
  have hcopATrace := incidenceBranchPolynomial_isCoprime_cageTrace h2 a
  have hcopBTrace := incidenceBranchPolynomial_isCoprime_cageTrace h2 b
  have hcopABTrace : IsCoprime
      (incidenceBranchPolynomial a * incidenceBranchPolynomial b)
      (cageTraceBranchPolynomial : K[X]) :=
    hcopATrace.mul_left hcopBTrace
  have hsqTrace := hsepTrace.squarefree
  have hsqATrace := (hsepA.mul hsepTrace hcopATrace).squarefree
  have hsqBTrace := (hsepB.mul hsepTrace hcopBTrace).squarefree
  have hsqABTrace :=
    ((hsepA.mul hsepB hcopAB).mul hsepTrace hcopABTrace).squarefree
  refine ⟨not_isSquare_algebraMap_of_squarefree_not_isUnit hsqTrace
      (cageTraceBranchPolynomial_not_isUnit h3),
    not_isSquare_algebraMap_of_squarefree_not_isUnit hsqATrace ?_,
    not_isSquare_algebraMap_of_squarefree_not_isUnit hsqBTrace ?_,
    not_isSquare_algebraMap_of_squarefree_not_isUnit hsqABTrace ?_⟩
  · intro hunit
    exact incidenceBranchPolynomial_not_isUnit hA (IsUnit.mul_iff.mp hunit).1
  · intro hunit
    exact incidenceBranchPolynomial_not_isUnit hB (IsUnit.mul_iff.mp hunit).1
  · intro hunit
    exact incidenceBranchPolynomial_not_isUnit hA
      (IsUnit.mul_iff.mp (IsUnit.mul_iff.mp hunit).1).1

/-- The discriminant of the trace quadratic remains nonsquare after adjoining
both incidence square roots. -/
theorem incidenceBiquadraticTraceBranch_not_isSquare
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 9 * a ^ 2 - 4 ≠ 0) (hB : 9 * b ^ 2 - 4 ≠ 0)
    (hab : a ^ 2 ≠ b ^ 2) :
    ¬ IsSquare
      (algebraMap (IncidenceFirstQuadraticRatFuncRing K a)
        (IncidenceBiquadraticRatFuncRing K a b)
        (algebraMap (RatFunc K) (IncidenceFirstQuadraticRatFuncRing K a)
          (algebraMap K[X] (RatFunc K) cageTraceBranchPolynomial))) := by
  let fA : RatFunc K :=
    algebraMap K[X] (RatFunc K) (incidenceBranchPolynomial a)
  let fB : RatFunc K :=
    algebraMap K[X] (RatFunc K) (incidenceBranchPolynomial b)
  let traceBranch : RatFunc K :=
    algebraMap K[X] (RatFunc K) cageTraceBranchPolynomial
  obtain ⟨hfA, hfB, hfAB⟩ :=
    incidenceBranchSquareClasses_independent_ratFunc h2 ha hb hA hB hab
  obtain ⟨hTrace, hATrace, hBTrace, hABTrace⟩ :=
    cageTraceBranchSquareClasses_independent_ratFunc h2 h3 ha hb hA hB hab
  have h2RatFunc : (2 : RatFunc K) ≠ 0 := by
    intro hzero
    apply h2
    apply FaithfulSMul.algebraMap_injective K (RatFunc K)
    simpa only [map_ofNat, map_zero] using hzero
  let : Fact
      (Irreducible
        (adjoinSquarePolynomial
          (algebraMap K[X] (RatFunc K) (incidenceBranchPolynomial a)))) :=
    ⟨adjoinSquarePolynomial_irreducible_of_not_isSquare hfA⟩
  let firstField := IncidenceFirstQuadraticRatFuncRing K a
  let secondField := IncidenceBiquadraticRatFuncRing K a b
  let fBFirst : firstField :=
    incidenceFirstQuadraticToRatFunc K a
      (algebraMap K[X] (IncidenceFirstQuadraticRing K a)
        (incidenceBranchPolynomial b))
  let traceFirst : firstField := algebraMap (RatFunc K) firstField traceBranch
  have h2First : (2 : firstField) ≠ 0 := by
    intro hzero
    apply h2RatFunc
    apply (algebraMap (RatFunc K) firstField).injective
    simpa only [map_ofNat, map_zero] using hzero
  have hfBFirst : ¬ IsSquare fBFirst := by
    change ¬ IsSquare
      (incidenceFirstQuadraticToRatFunc K a
        (algebraMap K[X] (IncidenceFirstQuadraticRing K a)
          (incidenceBranchPolynomial b)))
    rw [incidenceFirstQuadraticToRatFunc_algebraMap]
    apply not_isSquare_algebraMap_adjoinSquare_of_independent h2RatFunc hfA hfB
    simpa only [map_mul] using hfAB
  have hTraceFirst : ¬ IsSquare traceFirst := by
    apply not_isSquare_algebraMap_adjoinSquare_of_independent h2RatFunc hfA hTrace
    simpa only [map_mul] using hATrace
  have hBTraceFirst : ¬ IsSquare (fBFirst * traceFirst) := by
    have hMapped : ¬ IsSquare
        (algebraMap (RatFunc K) firstField (fB * traceBranch)) := by
      apply not_isSquare_algebraMap_adjoinSquare_of_independent h2RatFunc hfA
      · simpa only [fB, traceBranch, map_mul] using hBTrace
      · simpa only [fA, fB, traceBranch, map_mul, mul_assoc] using hABTrace
    rw [show fBFirst = algebraMap (RatFunc K) firstField fB by
      simp [fBFirst, fB, firstField,
        incidenceFirstQuadraticToRatFunc_algebraMap]]
    simpa only [traceFirst, map_mul] using hMapped
  change ¬ IsSquare (algebraMap firstField secondField traceFirst)
  exact not_isSquare_algebraMap_adjoinSquare_of_independent
    h2First hfBFirst hTraceFirst hBTraceFirst

/-- The normalized common coordinate `3y` inside the biquadratic incidence
function field. -/
def incidenceBiquadraticNormalizedTrace (a b : K) :
    IncidenceBiquadraticRatFuncRing K a b :=
  algebraMap (IncidenceFirstQuadraticRatFuncRing K a)
      (IncidenceBiquadraticRatFuncRing K a b)
    (algebraMap (RatFunc K) (IncidenceFirstQuadraticRatFuncRing K a)
      (RatFunc.C 3 * RatFunc.X))

/-- The discriminant of the normalized trace inside the biquadratic field is
the image of `9y² - 4`. -/
lemma incidenceBiquadraticNormalizedTrace_discriminant (a b : K) :
    incidenceBiquadraticNormalizedTrace a b ^ 2 - 4 =
      algebraMap (IncidenceFirstQuadraticRatFuncRing K a)
        (IncidenceBiquadraticRatFuncRing K a b)
        (algebraMap (RatFunc K) (IncidenceFirstQuadraticRatFuncRing K a)
          (algebraMap K[X] (RatFunc K) cageTraceBranchPolynomial)) := by
  simp only [incidenceBiquadraticNormalizedTrace, cageTraceBranchPolynomial,
    map_sub, map_mul, map_pow, map_ofNat, RatFunc.algebraMap_X]
  ring

/-- The normalized trace discriminant remains nonsquare in the complete
biquadratic incidence function field. -/
theorem incidenceBiquadraticNormalizedTrace_discriminant_not_isSquare
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 9 * a ^ 2 - 4 ≠ 0) (hB : 9 * b ^ 2 - 4 ≠ 0)
    (hab : a ^ 2 ≠ b ^ 2) :
    ¬ IsSquare (incidenceBiquadraticNormalizedTrace a b ^ 2 - 4) := by
  rw [incidenceBiquadraticNormalizedTrace_discriminant]
  exact incidenceBiquadraticTraceBranch_not_isSquare h2 h3 ha hb hA hB hab

/-- The trace quadratic over the exact incidence biquadratic field
presentation. -/
def incidenceBiquadraticTraceRootPolynomial (a b : K) :
    Polynomial (IncidenceBiquadraticRatFuncRing K a b) :=
  X ^ 2 - C (incidenceBiquadraticNormalizedTrace a b) * X + 1

/-- The trace quadratic is irreducible over the off-diagonal incidence
biquadratic function field. -/
theorem incidenceBiquadraticTraceRootPolynomial_irreducible
    (h2 : (2 : K) ≠ 0) (h3 : (3 : K) ≠ 0) {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : 9 * a ^ 2 - 4 ≠ 0) (hB : 9 * b ^ 2 - 4 ≠ 0)
    (hab : a ^ 2 ≠ b ^ 2) :
    Irreducible (incidenceBiquadraticTraceRootPolynomial a b) := by
  let : IsDomain (IncidenceBiquadraticRatFuncRing K a b) :=
    incidenceBiquadraticRatFuncRing_isDomain K h2 ha hb hA hB hab
  change Irreducible (traceRootPolynomial (incidenceBiquadraticNormalizedTrace a b))
  apply traceRootPolynomial_irreducible_of_discriminant_not_isSquare
  exact incidenceBiquadraticNormalizedTrace_discriminant_not_isSquare
    h2 h3 ha hb hA hB hab

/-- The quadratic trace extension of the cage incidence function field. -/
abbrev IncidenceTraceFunctionField (K : Type*) [Field K] (a b : K) :=
  AdjoinRoot (incidenceBiquadraticTraceRootPolynomial a b)

/-- The canonical unit-trace root in the quadratic trace extension. -/
def incidenceTraceRoot (a b : K) : IncidenceTraceFunctionField K a b :=
  AdjoinRoot.root (incidenceBiquadraticTraceRootPolynomial a b)

/-- The canonical trace root satisfies `R² - (3y)R + 1 = 0`. -/
lemma incidenceTraceRoot_quadratic_relation (a b : K) :
    incidenceTraceRoot a b ^ 2 -
        algebraMap (IncidenceBiquadraticRatFuncRing K a b)
          (IncidenceTraceFunctionField K a b)
          (incidenceBiquadraticNormalizedTrace a b) * incidenceTraceRoot a b + 1 = 0 := by
  have h := AdjoinRoot.eval₂_root (incidenceBiquadraticTraceRootPolynomial a b)
  rw [incidenceBiquadraticTraceRootPolynomial] at h
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_one] at h
  rw [← AdjoinRoot.algebraMap_eq] at h
  exact h

end

end BGS.Markoff
