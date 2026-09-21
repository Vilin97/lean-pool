/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.WeightedTraceEquation
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# The geometric Corvaja--Zannier interface for the middle game

Corvaja--Zannier, JEMS 15 (2013), Corollary 2, bounds torsion points on an
absolutely irreducible curve in a two-dimensional torus which is not a translate of a
subtorus.  The actual Markoff middle-game finset consists of solutions of

`alpha * h + beta * h⁻¹ = k + k⁻¹`, with `h ∈ H₁` and `k ∈ H₂`.

This module embeds that finset into the exact geometric torsion intersection of the
weighted trace curve.  It keeps all hypotheses of the cited result visible.  In particular,
`alpha * beta ≠ 1` is not silently identified with absolute irreducibility or with the
non-subtorus condition.

The constant `20` printed in the Markoff paper is not the direct specialization of
Corvaja--Zannier Corollary 2.  For the `(2,2)` trace curve, the `12 d₁ d₂ / p` term alone
gives `48 m₁ m₂ / p`.  Accordingly the source-backed envelope in this module has constant
`48`; obtaining `20` requires a separate argument.
-/

namespace BGS.Markoff

section GeometricCurve

variable {K : Type*} [Field K]

/-- The affine closure polynomial of the weighted trace curve after removing the boundary
monomial which appears when `beta = 0`.  Variable `0` is the right trace parameter `k` and
variable `1` is the left parameter `h`.

Removing this monomial is essential: Corvaja--Zannier concerns the curve in the torus, not
the extra coordinate-axis component introduced by clearing denominators. -/
noncomputable def weightedTraceTorusClosurePolynomial (alpha beta : K) :
    MvPolynomial (Fin 2) K := by
  classical
  exact if beta = 0 then
      MvPolynomial.C alpha * MvPolynomial.X 0 * MvPolynomial.X 1 -
        MvPolynomial.X 0 ^ 2 - 1
    else
      splitTraceCoverPolynomial alpha beta 1 1

/-- On nonzero coordinates, the reduced affine polynomial cuts out exactly the weighted
trace equation. -/
theorem eval_weightedTraceTorusClosurePolynomial_eq_zero_iff
    (alpha beta : K) (k h : Kˣ) :
    MvPolynomial.eval ![(k : K), (h : K)]
        (weightedTraceTorusClosurePolynomial alpha beta) = 0 ↔
      weightedSplitTorusTrace alpha beta h = splitTorusTrace k := by
  by_cases hbeta : beta = 0
  · subst beta
    simp only [weightedTraceTorusClosurePolynomial, if_pos, map_sub, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Matrix.cons_val_zero,
      Matrix.cons_val_one, map_pow, map_one, weightedSplitTorusTrace,
      splitTorusTrace, zero_mul, add_zero, Units.val_inv_eq_inv_val]
    have hk : (k : K) ≠ 0 := Units.ne_zero k
    field_simp [hk]
    constructor <;> intro heq <;> linear_combination heq
  · rw [weightedTraceTorusClosurePolynomial, if_neg hbeta]
    simpa [SplitTraceCurveEquation] using
      eval_splitTraceCoverPolynomial_eq_zero_iff alpha beta 1 1 k h

/-- Absolute irreducibility of the actual torus closure, expressed as irreducibility after
base change to an algebraic closure.  This is a proposition, not a typeclass. -/
def WeightedTraceCurveAbsolutelyIrreducible (alpha beta : K) : Prop :=
  Irreducible
    (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
      (weightedTraceTorusClosurePolynomial alpha beta))

/-- Exact geometric non-specialness: over an algebraic closure, no nontrivial character is
constant on the whole weighted trace curve.  For an irreducible curve in `G_m^2`, this is
equivalent to not being a translate of a one-dimensional subtorus. -/
def WeightedTraceCurveNotSubtorusTranslate (alpha beta : K) : Prop :=
  ∀ (a b : ℤ), (a ≠ 0 ∨ b ≠ 0) →
    ∀ c : (AlgebraicClosure K)ˣ,
      ∃ k h : (AlgebraicClosure K)ˣ,
        weightedSplitTorusTrace
            (algebraMap K (AlgebraicClosure K) alpha)
            (algebraMap K (AlgebraicClosure K) beta) h =
          splitTorusTrace k ∧
        k ^ a * h ^ b ≠ c

/-- The concrete curve hypotheses needed by the weighted-trace specialization of
Corvaja--Zannier Corollary 2.  Both weights are nonzero, the curve is nondegenerate and
absolutely irreducible, and it is not a translate of a subtorus.  These conditions are
kept separate from the external cardinal estimate. -/
def WeightedTraceCurveIsCorvajaZannierAdmissible (alpha beta : K) : Prop :=
  alpha ≠ 0 ∧
    beta ≠ 0 ∧
      alpha * beta ≠ 1 ∧
        WeightedTraceCurveAbsolutelyIrreducible alpha beta ∧
          WeightedTraceCurveNotSubtorusTranslate alpha beta

end GeometricCurve

section FiniteTorsionIntersection

variable {E : Type*} [Field E] [Fintype E]

/-- The geometric torsion intersection to which Corvaja--Zannier Corollary 2 applies.
Coordinates are ordered `(k, h)` to match `splitTraceCoverPolynomial`. -/
noncomputable def weightedTraceCurveTorsionIntersection
    (alpha beta : E) (leftOrder rightOrder : ℕ) : Finset (Eˣ × Eˣ) := by
  classical
  exact Finset.univ.filter fun z ↦
    weightedSplitTorusTrace alpha beta z.2 = splitTorusTrace z.1 ∧
      z.2 ^ leftOrder = 1 ∧ z.1 ^ rightOrder = 1

@[simp]
theorem mem_weightedTraceCurveTorsionIntersection_iff
    (alpha beta : E) (leftOrder rightOrder : ℕ) (z : Eˣ × Eˣ) :
    z ∈ weightedTraceCurveTorsionIntersection alpha beta leftOrder rightOrder ↔
      weightedSplitTorusTrace alpha beta z.2 = splitTorusTrace z.1 ∧
        z.2 ^ leftOrder = 1 ∧ z.1 ^ rightOrder = 1 := by
  classical
  simp [weightedTraceCurveTorsionIntersection]

/-- The same intersection stated with the explicit affine closure polynomial.  This is the
line-level bridge from the finite set to the algebraic curve consumed by Corollary 2. -/
theorem mem_weightedTraceCurveTorsionIntersection_iff_polynomial
    (alpha beta : E) (leftOrder rightOrder : ℕ) (z : Eˣ × Eˣ) :
    z ∈ weightedTraceCurveTorsionIntersection alpha beta leftOrder rightOrder ↔
      MvPolynomial.eval ![(z.1 : E), (z.2 : E)]
          (weightedTraceTorusClosurePolynomial alpha beta) = 0 ∧
        z.2 ^ leftOrder = 1 ∧ z.1 ^ rightOrder = 1 := by
  rw [mem_weightedTraceCurveTorsionIntersection_iff,
    eval_weightedTraceTorusClosurePolynomial_eq_zero_iff]

/-- Swap a subgroup solution into the geometric coordinate order `(k, h)`. -/
def weightedTraceSubgroupSolutionToCurvePoint
    (H₁ H₂ : Subgroup Eˣ) : H₁ × H₂ → Eˣ × Eˣ :=
  fun z ↦ ((z.2 : Eˣ), (z.1 : Eˣ))

omit [Fintype E] in
theorem weightedTraceSubgroupSolutionToCurvePoint_injective
    (H₁ H₂ : Subgroup Eˣ) :
    Function.Injective (weightedTraceSubgroupSolutionToCurvePoint H₁ H₂) := by
  intro x y hxy
  apply Prod.ext
  · apply Subtype.ext
    exact congrArg Prod.snd hxy
  · apply Subtype.ext
    exact congrArg Prod.fst hxy

/-- Every actual subgroup solution gives a point in the corresponding geometric torsion
intersection.  The subgroup cardinalities become the two root-of-unity exponents by
Lagrange's theorem. -/
theorem weightedTraceSubgroupSolutionToCurvePoint_mem_torsionIntersection
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ) (z : H₁ × H₂)
    (hz : z ∈ weightedTraceEquationSolutions alpha beta H₁ H₂) :
    weightedTraceSubgroupSolutionToCurvePoint H₁ H₂ z ∈
      weightedTraceCurveTorsionIntersection alpha beta (Nat.card H₁) (Nat.card H₂) := by
  letI := Fintype.ofFinite H₁
  letI := Fintype.ofFinite H₂
  rw [mem_weightedTraceCurveTorsionIntersection_iff]
  refine ⟨mem_weightedTraceEquationSolutions_iff.mp hz, ?_, ?_⟩
  · have hpow : z.1 ^ Fintype.card H₁ = 1 := pow_card_eq_one
    have hval := congrArg (fun u : H₁ ↦ (u : Eˣ)) hpow
    change ((z.1 : Eˣ) ^ Fintype.card H₁) = 1 at hval
    simpa only [weightedTraceSubgroupSolutionToCurvePoint,
      Fintype.card_eq_nat_card] using hval
  · have hpow : z.2 ^ Fintype.card H₂ = 1 := pow_card_eq_one
    have hval := congrArg (fun u : H₂ ↦ (u : Eˣ)) hpow
    change ((z.2 : Eˣ) ^ Fintype.card H₂) = 1 at hval
    simpa only [weightedTraceSubgroupSolutionToCurvePoint,
      Fintype.card_eq_nat_card] using hval

/-- The actual weighted solution count is bounded by the exact geometric torsion
intersection count.  This theorem contains no Corvaja--Zannier assumption. -/
theorem weightedTraceEquationSolutions_card_le_curveTorsionIntersection
    (alpha beta : E) (H₁ H₂ : Subgroup Eˣ) :
    (weightedTraceEquationSolutions alpha beta H₁ H₂).card ≤
      (weightedTraceCurveTorsionIntersection alpha beta
        (Nat.card H₁) (Nat.card H₂)).card := by
  classical
  exact Finset.card_le_card_of_injOn
    (weightedTraceSubgroupSolutionToCurvePoint H₁ H₂)
    (fun z hz ↦ weightedTraceSubgroupSolutionToCurvePoint_mem_torsionIntersection
      alpha beta H₁ H₂ z hz)
    (weightedTraceSubgroupSolutionToCurvePoint_injective H₁ H₂).injOn

end FiniteTorsionIntersection

end BGS.Markoff
