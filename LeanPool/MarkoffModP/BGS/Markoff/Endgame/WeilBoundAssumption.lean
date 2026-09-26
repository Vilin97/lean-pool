/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
module


public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedOddCoprimeIrreducibility
public import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Boundary
public import LeanPool.MarkoffModP.BGS.Markoff.Endgame.Nonsplit.SeededCover
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The explicit endgame Weil-bound assumption

The paper's endgame needs a point estimate for the weighted split trace covers

`alpha * (x^d + x^(-d)) = beta * (y^e + y^(-e))`.

The project accepts each relevant affine Hasse--Weil specialization as an ordinary theorem
parameter.  It is not a Lean axiom, a `sorry`, a typeclass, or a structure field.  The constant is
fixed before the finite field, the weights, and the covering exponents are chosen, so the
interface expresses the uniformity required by Theorem 1.

The assumption does not assert that a concrete Markoff trace cover is geometrically irreducible.
That hypothesis remains visible.  The application theorem at the end of this file discharges it
using the in-repository absolute-irreducibility proof.

Constructing a smooth projective normalization, bounding its genus and boundary, and applying the
classical projective Hasse--Weil theorem is one route to proving this assumption.  Those objects
are intentionally not part of the downstream interface: they belong to a proof of the accepted
external theorem, not to each use of it.
-/

@[expose] public section

namespace BGS.Markoff

noncomputable section

/-- The uniform weighted split trace-cover estimate accepted by the endgame.

`coefficient` is independent of the finite field, weights, and covering exponents.  Every
algebraic hypothesis needed to apply the estimate to a concrete cover is an explicit argument.
In particular, absolute irreducibility is stated as irreducibility after scalar extension to the
algebraic closure. -/
def WeightedSplitTraceWeilBoundAssumption (coefficient : ℕ) : Prop :=
  0 < coefficient ∧
    ∀ (K : Type) [Field K] [Fintype K] [DecidableEq K]
      (alpha beta : K) (d e : ℕ),
      alpha ≠ 0 →
        beta ≠ 0 →
          alpha * beta ≠ 1 →
            0 < d →
              0 < e →
                Irreducible
                    (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
                      (splitTraceCoverPolynomial alpha beta d e)) →
                  |((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
                      (Fintype.card K : ℝ)| ≤
                    (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
                      (d : ℝ) * (e : ℝ)

variable (K : Type) [Field K] [Fintype K] [DecidableEq K]

/-- Apply the accepted Weil estimate after supplying the concrete cover's absolute
irreducibility.  This theorem is the raw interface adapter; the next theorem proves that
irreducibility from the trace-cover hypotheses used in the paper. -/
theorem splitTraceCurveSolutions_count_error_le_of_weilBoundAssumption
    (coefficient : ℕ) (hWeil : WeightedSplitTraceWeilBoundAssumption coefficient)
    (alpha beta : K) (d e : ℕ)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hnondegenerate : alpha * beta ≠ 1)
    (hd : 0 < d) (he : 0 < e)
    (hirreducible :
      Irreducible
        (MvPolynomial.map (algebraMap K (AlgebraicClosure K))
          (splitTraceCoverPolynomial alpha beta d e))) :
    |((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
        (d : ℝ) * (e : ℝ) :=
  hWeil.2 K alpha beta d e halpha hbeta hnondegenerate hd he hirreducible

/-- The endgame-ready point estimate for a concrete weighted trace cover.

The only unproved mathematical input is `hWeil`.  Lean proves the required absolute
irreducibility from nonzero/nondegenerate weights, positive exponents, and the condition that the
second covering exponent is nonzero in the ground field.  For the paper's split endgame this last
condition follows because the exponent divides the prime-to-characteristic torus order. -/
theorem splitTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
    (coefficient : ℕ) (hWeil : WeightedSplitTraceWeilBoundAssumption coefficient)
    (alpha beta : K) (d e : ℕ)
    (halpha : alpha ≠ 0) (hbeta : beta ≠ 0) (hnondegenerate : alpha * beta ≠ 1)
    (hd : 0 < d) (he : 0 < e) (heChar : (e : K) ≠ 0) :
    |((splitTraceCurveSolutions K alpha beta d e).card : ℝ) -
        (Fintype.card K : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (Fintype.card K : ℝ) *
        (d : ℝ) * (e : ℝ) := by
  apply splitTraceCurveSolutions_count_error_le_of_weilBoundAssumption
    K coefficient hWeil alpha beta d e halpha hbeta hnondegenerate hd he
  exact splitTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
    alpha beta halpha hbeta hnondegenerate e d he hd heChar

/-! ## The seeded nonsplit branch -/

/-- Solutions of the paper's corrected nonsplit endgame equation on the norm-one torus and the
base-field multiplicative group.  Keeping this finite set over `ZMod p`, rather than replacing it
by all quadratic-field points of the scalar-extended split curve, preserves the actual count
needed by Theorem 1. -/
noncomputable def existingConicSeedNonsplitTraceCurveSolutions
    (p : ℕ) [Fact p.Prime]
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0))
    (d e : ℕ) : Finset (quadraticNormOneTorus p × (ZMod p)ˣ) := by
  classical
  exact Finset.univ.filter fun z =>
    ExistingConicSeedNonsplitTraceCoverEquation p t ht ht0 s d e z.1 z.2

@[simp]
theorem mem_existingConicSeedNonsplitTraceCurveSolutions_iff
    (p : ℕ) [Fact p.Prime]
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0))
    (d e : ℕ) (z : quadraticNormOneTorus p × (ZMod p)ˣ) :
    z ∈ existingConicSeedNonsplitTraceCurveSolutions p t ht ht0 s d e ↔
      ExistingConicSeedNonsplitTraceCoverEquation p t ht ht0 s d e z.1 z.2 := by
  classical
  simp [existingConicSeedNonsplitTraceCurveSolutions]

/-- The uniform affine Weil estimate accepted for the seeded nonsplit endgame family.

The conclusion counts the base-field solution set above, not every point of the scalar-extended
curve over the quadratic field.  The explicit irreducibility premise is the polynomial statement
already proved for the scalar extension of the corrected seeded equation. -/
def SeededNonsplitTraceWeilBoundAssumption (coefficient : ℕ) : Prop :=
  0 < coefficient ∧
    ∀ (p : ℕ) [Fact p.Prime],
      p ≠ 2 →
        ∀ (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
          (s : ↥(quadraticConicNormFiber p t ht ht0)) (d e : ℕ),
          0 < d →
            0 < e →
              Irreducible
                  (MvPolynomial.map
                    (algebraMap (quadraticFiniteField p)
                      (AlgebraicClosure (quadraticFiniteField p)))
                    (splitTraceCoverPolynomial
                      (s.1 : quadraticFiniteField p)
                      ((s.1 : quadraticFiniteField p) ^ p) e d)) →
                |((existingConicSeedNonsplitTraceCurveSolutions
                    p t ht ht0 s d e).card : ℝ) - (p : ℝ)| ≤
                  (coefficient : ℝ) * Real.sqrt (p : ℝ) * (d : ℝ) * (e : ℝ)

/-- Apply the accepted nonsplit Weil estimate after supplying the scalar-extended cover's
absolute irreducibility. -/
theorem existingConicSeedNonsplitTraceCurveSolutions_count_error_le_of_weilBoundAssumption
    (coefficient : ℕ) (hWeil : SeededNonsplitTraceWeilBoundAssumption coefficient)
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0))
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hirreducible :
      Irreducible
        (MvPolynomial.map
          (algebraMap (quadraticFiniteField p)
            (AlgebraicClosure (quadraticFiniteField p)))
          (splitTraceCoverPolynomial
            (s.1 : quadraticFiniteField p)
            ((s.1 : quadraticFiniteField p) ^ p) e d))) :
    |((existingConicSeedNonsplitTraceCurveSolutions
        p t ht ht0 s d e).card : ℝ) - (p : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (p : ℝ) * (d : ℝ) * (e : ℝ) :=
  hWeil.2 p hpTwo t ht ht0 s d e hd he hirreducible

/-- The endgame-ready point estimate for the corrected seeded nonsplit cover.

As in the split adapter, the only external input is `hWeil`.  Lean supplies the
scalar-extended absolute irreducibility theorem from the actual conic seed and the visible
prime-to-characteristic condition on the norm-one covering exponent. -/
theorem existingConicSeedNonsplitTraceCurveSolutions_count_error_le_of_weilBoundAssumption_and_positiveExponents
    (coefficient : ℕ) (hWeil : SeededNonsplitTraceWeilBoundAssumption coefficient)
    (p : ℕ) [Fact p.Prime] (hpTwo : p ≠ 2)
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0))
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hdChar : (d : quadraticFiniteField p) ≠ 0) :
    |((existingConicSeedNonsplitTraceCurveSolutions
        p t ht ht0 s d e).card : ℝ) - (p : ℝ)| ≤
      (coefficient : ℝ) * Real.sqrt (p : ℝ) * (d : ℝ) * (e : ℝ) := by
  apply existingConicSeedNonsplitTraceCurveSolutions_count_error_le_of_weilBoundAssumption
    coefficient hWeil p hpTwo t ht ht0 s d e hd he
  exact existingConicSeed_weightedCover_absolutelyIrreducible
    p hpTwo t ht ht0 s d e hd he hdChar

end

end BGS.Markoff
