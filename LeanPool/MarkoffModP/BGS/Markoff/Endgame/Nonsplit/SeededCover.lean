/-
Copyright (c) 2026 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/

import LeanPool.MarkoffModP.BGS.Markoff.MiddleGame.TraceCurveWeights
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.Geometry
import LeanPool.MarkoffModP.BGS.Markoff.TraceCurve.WeightedOddCoprimeIrreducibility

/-!
# The seeded nonsplit endgame cover

The endgame curve is not the trace of a bare norm-one element.  A fixed seed `s` in a
nontrivial norm fibre is multiplied by the varying norm-one coordinate.  After scalar extension
the two weights are `s` and `s^p`; their product is `Norm(s)`, not one.
-/

namespace BGS.Markoff

section GeneralSeed

variable (p : ℕ) [Fact p.Prime]

/-- A split base-field unit transported to the canonical quadratic extension. -/
noncomputable def seededBaseUnitInQuadraticField (u : (ZMod p)ˣ) :
    (quadraticFiniteField p)ˣ :=
  Units.map (algebraMap (ZMod p) (quadraticFiniteField p)).toMonoidHom u

/-- The actual seeded nonsplit cover.  The seed lies in the norm-`k` torsor and the varying
coordinate lies in the norm-one torus. -/
def SeededNonsplitTraceCoverEquation (k : (ZMod p)ˣ)
    (s : ↑(quadraticNormFiber p k)) (d e : ℕ)
    (w : quadraticNormOneTorus p) (u : (ZMod p)ˣ) : Prop :=
  Algebra.trace (ZMod p) (quadraticFiniteField p)
      ((s.1 : quadraticFiniteField p) *
        (((w ^ d : quadraticNormOneTorus p) : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p)) =
    splitTorusTrace (u ^ e)

/-- The scalar extension of the seeded trace is the weighted trace with coefficients
`alpha = s` and `beta = s^p`. -/
theorem algebraMap_seededQuadraticTrace_eq_weightedSplitTorusTrace
    (k : (ZMod p)ˣ) (s : ↑(quadraticNormFiber p k))
    (d : ℕ) (w : quadraticNormOneTorus p) :
    algebraMap (ZMod p) (quadraticFiniteField p)
        (Algebra.trace (ZMod p) (quadraticFiniteField p)
          ((s.1 : quadraticFiniteField p) *
            (((w ^ d : quadraticNormOneTorus p) : (quadraticFiniteField p)ˣ) :
              quadraticFiniteField p))) =
      weightedSplitTorusTrace
        (s.1 : quadraticFiniteField p)
        ((s.1 : quadraticFiniteField p) ^ p)
        ((w : (quadraticFiniteField p)ˣ) ^ d) := by
  have hwcoe :
      ((((w ^ d : quadraticNormOneTorus p) : (quadraticFiniteField p)ˣ) :
          quadraticFiniteField p)) =
        (((w : (quadraticFiniteField p)ˣ) : quadraticFiniteField p) ^ d) := rfl
  rw [algebraMap_quadraticTrace]
  unfold weightedSplitTorusTrace
  rw [mul_pow]
  rw [quadraticNormOne_frobenius_eq_inv p (w ^ d)]
  simp only [Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rw [hwcoe]

/-- The actual nonsplit cover is exactly the existing weighted split cover over the quadratic
field.  The exponent order in `SplitTraceCurveEquation` is `(e,d)`. -/
theorem seededNonsplitTraceCoverEquation_iff_weightedSplitTraceCover
    (k : (ZMod p)ˣ) (s : ↑(quadraticNormFiber p k))
    (d e : ℕ) (w : quadraticNormOneTorus p) (u : (ZMod p)ˣ) :
    SeededNonsplitTraceCoverEquation p k s d e w u ↔
      SplitTraceCurveEquation
        (s.1 : quadraticFiniteField p)
        ((s.1 : quadraticFiniteField p) ^ p) e d
        (seededBaseUnitInQuadraticField p u)
        (w : (quadraticFiniteField p)ˣ) := by
  unfold SeededNonsplitTraceCoverEquation SplitTraceCurveEquation
  have hleft := algebraMap_seededQuadraticTrace_eq_weightedSplitTorusTrace
    p k s d w
  constructor
  · intro h
    rw [← hleft, h]
    simp [seededBaseUnitInQuadraticField, splitTorusTrace]
  · intro h
    apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
    rw [hleft, h]
    simp [seededBaseUnitInQuadraticField, splitTorusTrace]

/-- The product of the scalar-extended weights is exactly the prescribed seed norm. -/
theorem seededNonsplitWeights_mul
    (k : (ZMod p)ˣ) (s : ↑(quadraticNormFiber p k)) :
    (s.1 : quadraticFiniteField p) * (s.1 : quadraticFiniteField p) ^ p =
      algebraMap (ZMod p) (quadraticFiniteField p) (k : ZMod p) := by
  rw [quadraticNormFiber_frobenius_eq_norm_mul_inv p k s]
  field_simp

/-- A seed of norm different from one supplies exactly the coefficient hypotheses required by
the weighted split-cover irreducibility theorem. -/
theorem seededNonsplitWeights_nondegenerate
    (k : (ZMod p)ˣ) (hk : k ≠ 1) (s : ↑(quadraticNormFiber p k)) :
    (s.1 : quadraticFiniteField p) ≠ 0 ∧
      (s.1 : quadraticFiniteField p) ^ p ≠ 0 ∧
      (s.1 : quadraticFiniteField p) * (s.1 : quadraticFiniteField p) ^ p ≠ 1 := by
  refine ⟨Units.ne_zero s.1, pow_ne_zero p (Units.ne_zero s.1), ?_⟩
  rw [seededNonsplitWeights_mul p k s]
  intro hmap
  apply hk
  apply Units.ext
  apply (algebraMap (ZMod p) (quadraticFiniteField p)).injective
  simpa using hmap

end GeneralSeed

section ExistingConicSeed

variable (p : ℕ) [Fact p.Prime]

/-- For an odd prime, the existing nonzero nonparabolic conic invariant
`kappa(t) = t^2/(t^2-4)` is not one. -/
theorem quadraticFiberProduct_ne_one_of_prime_ne_two
    (hpTwo : p ≠ 2) (t : ZMod p) (ht : t ^ 2 ≠ 4) :
    quadraticFiberProduct p t ≠ 1 := by
  have hfourE := four_ne_zero_quadraticFiniteField_of_prime_ne_two p hpTwo
  have hfour : (4 : ZMod p) ≠ 0 :=
    (map_ne_zero (algebraMap (ZMod p) (quadraticFiniteField p))).mp hfourE
  intro hkappa
  have hden : t ^ 2 - 4 ≠ 0 := sub_ne_zero.mpr ht
  have heq : t ^ 2 = 1 * (t ^ 2 - 4) := by
    exact (div_eq_iff hden).mp hkappa
  apply hfour
  linear_combination heq

/-- The unit indexing the existing conic norm fibre is nontrivial. -/
theorem quadraticFiberProductUnit_ne_one
    (hpTwo : p ≠ 2) (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0) :
    quadraticFiberProductUnit p t ht ht0 ≠ 1 := by
  intro h
  have hval := congrArg Units.val h
  apply quadraticFiberProduct_ne_one_of_prime_ne_two p hpTwo t ht
  change quadraticFiberProduct p t = 1 at hval
  exact hval

/-- Every seed from the existing nonsplit conic construction has nonzero weighted coefficients
whose product is the embedded invariant `kappa(t)`, and this product is not one. -/
theorem existingConicSeed_nonsplitWeights_nondegenerate
    (hpTwo : p ≠ 2) (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↑(quadraticConicNormFiber p t ht ht0)) :
    (s.1 : quadraticFiniteField p) ≠ 0 ∧
      (s.1 : quadraticFiniteField p) ^ p ≠ 0 ∧
      (s.1 : quadraticFiniteField p) * (s.1 : quadraticFiniteField p) ^ p ≠ 1 := by
  exact seededNonsplitWeights_nondegenerate p
    (quadraticFiberProductUnit p t ht ht0)
    (quadraticFiberProductUnit_ne_one p hpTwo t ht ht0) s

/-- The corrected nonsplit cover lands in the already-proved arbitrary positive-exponent
weighted-cover theorem after quadratic scalar extension.  In the polynomial convention the
base-field exponent `e` is the first exponent and the norm-one exponent `d` is the second, so
the characteristic hypothesis is required on `d`. -/
theorem existingConicSeed_weightedCover_absolutelyIrreducible
    (hpTwo : p ≠ 2) (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↥(quadraticConicNormFiber p t ht ht0))
    (d e : ℕ) (hd : 0 < d) (he : 0 < e)
    (hdChar : (d : quadraticFiniteField p) ≠ 0) :
    Irreducible
      (MvPolynomial.map
        (algebraMap (quadraticFiniteField p) (AlgebraicClosure (quadraticFiniteField p)))
        (splitTraceCoverPolynomial
          (s.1 : quadraticFiniteField p)
          ((s.1 : quadraticFiniteField p) ^ p) e d)) := by
  obtain ⟨halpha, hbeta, hproduct⟩ :=
    existingConicSeed_nonsplitWeights_nondegenerate p hpTwo t ht ht0 s
  exact splitTraceCoverPolynomial_absolutelyIrreducible_of_positiveExponents
    (s.1 : quadraticFiniteField p) ((s.1 : quadraticFiniteField p) ^ p)
    halpha hbeta hproduct d e hd he hdChar

/-- The endgame equation specialized to the seed type already constructed by the conic
parametrization module. -/
def ExistingConicSeedNonsplitTraceCoverEquation
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↑(quadraticConicNormFiber p t ht ht0))
    (d e : ℕ) (w : quadraticNormOneTorus p) (u : (ZMod p)ˣ) : Prop :=
  SeededNonsplitTraceCoverEquation p
    (quadraticFiberProductUnit p t ht ht0) s d e w u

theorem existingConicSeedNonsplitTraceCoverEquation_iff_weightedSplitTraceCover
    (t : ZMod p) (ht : t ^ 2 ≠ 4) (ht0 : t ≠ 0)
    (s : ↑(quadraticConicNormFiber p t ht ht0))
    (d e : ℕ) (w : quadraticNormOneTorus p) (u : (ZMod p)ˣ) :
    ExistingConicSeedNonsplitTraceCoverEquation p t ht ht0 s d e w u ↔
      SplitTraceCurveEquation
        (s.1 : quadraticFiniteField p)
        ((s.1 : quadraticFiniteField p) ^ p) e d
        (seededBaseUnitInQuadraticField p u)
        (w : (quadraticFiniteField p)ˣ) := by
  exact seededNonsplitTraceCoverEquation_iff_weightedSplitTraceCover p
    (quadraticFiberProductUnit p t ht ht0) s d e w u

end ExistingConicSeed

namespace DegenerateUnseededCountermodel

variable (p : ℕ) [Fact p.Prime]

/-- This is the tempting but incorrect unseeded model.  It is retained only to state the
degeneracy explicitly. -/
def UnseededNormOneTraceCountermodel (d e : ℕ)
    (w : quadraticNormOneTorus p) (u : (ZMod p)ˣ) : Prop :=
  quadraticNormOneTrace p (w ^ d) = splitTorusTrace (u ^ e)

theorem unseededCountermodel_weights_product_eq_one :
    (1 : quadraticFiniteField p) * 1 = 1 := by simp

end DegenerateUnseededCountermodel

end BGS.Markoff
