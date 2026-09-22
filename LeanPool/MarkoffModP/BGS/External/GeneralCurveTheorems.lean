/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import Mathlib.Algebra.MvPolynomial.PDeriv
import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.CorvajaZannierSourceBound
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# General curve-theorem interfaces

These propositions are deliberately independent of the Markoff surface and
of every split, nonsplit, or cage family.  Downstream code must construct the
relevant plane curve, prove its geometric hypotheses and bidegree bounds, and
then apply one of these two general statements.  Both interfaces now have
in-repository inhabitants; keeping the propositions separate makes their
Markoff-specific applications explicit.
-/

namespace BGS.External

noncomputable section

/-- A bivariate polynomial has coordinate degrees bounded by `firstDegree`
and `secondDegree`. -/
def HasBidegreeAtMost {K : Type*} [CommSemiring K]
    (f : MvPolynomial (Fin 2) K) (firstDegree secondDegree : ℕ) : Prop :=
  ∀ monomial : Fin 2 →₀ ℕ, monomial ∈ f.support →
    monomial 0 ≤ firstDegree ∧ monomial 1 ≤ secondDegree

/-- Affine rational zeros of a bivariate polynomial. -/
noncomputable def affinePlaneCurveZeros
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) : Finset (K × K) := by
  classical
  exact Finset.univ.filter fun z =>
    MvPolynomial.eval ![z.1, z.2] f = 0

@[simp]
theorem mem_affinePlaneCurveZeros_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {z : K × K} :
    z ∈ affinePlaneCurveZeros K f ↔
      MvPolynomial.eval ![z.1, z.2] f = 0 := by
  classical
  simp [affinePlaneCurveZeros]

/-- A general affine plane-curve Hasse--Weil estimate with its coefficient
fixed in the type.  Keeping this layer separate from the existential wrapper
makes numerical specializations auditable. -/
def BivariateAffineHasseWeilBound (coefficient : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstDegree secondDegree : ℕ),
    0 < firstDegree →
    0 < secondDegree →
    HasBidegreeAtMost (K := K) f firstDegree secondDegree →
    Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f) →
    |((affinePlaneCurveZeros K f).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
        (firstDegree : ℝ) * (secondDegree : ℝ)

/-- The general affine plane-curve Hasse--Weil interface used by the Markoff
applications.

This is the standard bidegree corollary of Hasse--Weil: normalization and the
boundary of a geometrically irreducible curve of positive bidegree contribute
only a universal multiple of `firstDegree * secondDegree`. -/
def GeneralBivariateAffineHasseWeilTheorem : Prop :=
  ∃ coefficient : ℕ, 0 < coefficient ∧
    BivariateAffineHasseWeilBound coefficient

/-- Torsion points of a general bivariate torus curve. -/
noncomputable def torusCurveTorsionIntersection
    (K : Type*) [Field K] [Fintype K] [DecidableEq K]
    (f : MvPolynomial (Fin 2) K) (firstOrder secondOrder : ℕ) :
    Finset (Kˣ × Kˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    MvPolynomial.eval ![(z.1 : K), (z.2 : K)] f = 0 ∧
      z.1 ^ firstOrder = 1 ∧ z.2 ^ secondOrder = 1

@[simp]
theorem mem_torusCurveTorsionIntersection_iff
    {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    {f : MvPolynomial (Fin 2) K} {firstOrder secondOrder : ℕ}
    {z : Kˣ × Kˣ} :
    z ∈ torusCurveTorsionIntersection K f firstOrder secondOrder ↔
      MvPolynomial.eval ![(z.1 : K), (z.2 : K)] f = 0 ∧
        z.1 ^ firstOrder = 1 ∧ z.2 ^ secondOrder = 1 := by
  classical
  simp [torusCurveTorsionIntersection]

/-- No nontrivial character is constant on the geometric torus curve. -/
def TorusCurveNotSubtorusTranslate
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) : Prop :=
  ∀ (a b : ℤ), (a ≠ 0 ∨ b ≠ 0) →
    ∀ c : (AlgebraicClosure K)ˣ,
      ∃ x y : (AlgebraicClosure K)ˣ,
        MvPolynomial.eval ![(x : AlgebraicClosure K),
          (y : AlgebraicClosure K)]
            (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f) = 0 ∧
        x ^ a * y ^ b ≠ c

/-- A general plane torus curve satisfies the geometric hypotheses of the
Corvaja--Zannier theorem.  Nonzero partial derivatives express that both
coordinate functions are separating; prime-to-characteristic torsion orders
then retain nonzero differentials. -/
def IsCorvajaZannierPlaneCurve
    {K : Type*} [Field K] (f : MvPolynomial (Fin 2) K) : Prop :=
  Irreducible
      (MvPolynomial.map (algebraMap K (AlgebraicClosure K)) f) ∧
    TorusCurveNotSubtorusTranslate f ∧
      MvPolynomial.pderiv 0 f ≠ 0 ∧ MvPolynomial.pderiv 1 f ≠ 0

/-- A general bidegree-only upper bound for the Euler characteristic of the
normalization of a torus plane curve.  For bidegree `(d₁,d₂)`, genus is at
most `(d₁-1)(d₂-1)` and the toric boundary has at most `2d₁+2d₂` points. -/
def planeTorusEulerCharacteristicBound
    (firstDegree secondDegree : ℕ) : ℝ :=
  2 * firstDegree * secondDegree

/-- The Corvaja--Zannier plane-curve interface, stated for every admissible
bivariate torus curve rather than for the weighted Markoff trace family.  The
in-repository proof is `BGS.CorvajaZannier.generalCorvajaZannierPlaneCurveTheorem`;
the source proof and its formal dependency path are tracked in the dedicated
Blueprint chapter. -/
def GeneralCorvajaZannierPlaneCurveTheorem : Prop :=
  ∀ (p : ℕ) [Fact p.Prime]
    (K : Type) [Field K] [Fintype K] [DecidableEq K] [CharP K p]
    (f : MvPolynomial (Fin 2) K)
    (firstDegree secondDegree firstOrder secondOrder : ℕ),
    0 < firstDegree →
    0 < secondDegree →
    HasBidegreeAtMost (K := K) f firstDegree secondDegree →
    IsCorvajaZannierPlaneCurve f →
    0 < firstOrder →
    0 < secondOrder →
    ¬ p ∣ firstOrder →
    ¬ p ∣ secondOrder →
    ((torusCurveTorsionIntersection
        K f firstOrder secondOrder).card : ℝ) ≤
      BGS.Markoff.corvajaZannierCorollaryTwoNumericalBound
        p firstOrder secondOrder firstDegree secondDegree
          (planeTorusEulerCharacteristicBound firstDegree secondDegree)

end

end BGS.External
