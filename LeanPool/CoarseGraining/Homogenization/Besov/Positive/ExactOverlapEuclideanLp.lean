/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpExponent
public import LeanPool.CoarseGraining.Homogenization.Multiscale.OverlapLp

/-!
# Exact finite-`p` Euclidean overlap Besov seminorm

The canonical positive overlap seminorm for vector fields uses Euclidean local
oscillations about `ScalarOverlap.cubeAverageVec`, with a single outer
`1 / p` root after summing all physical scales.
-/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

/-- The canonical positive Euclidean overlap Besov seminorm at finite `p`.
At running depth `j`, the physical scale is `Q.scale - j`; the outer root is
taken only after the complete weighted scale sum. -/
noncomputable def cubeEuclideanPositiveBesovOverlapESeminorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (g : Vec d → Vec d) : ℝ≥0∞ := by
  classical
  exact (∑' j : ℕ,
    ENNReal.ofReal
        (Real.rpow 3
          (-(s.1 * p.exponent.toReal *
            (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
      ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
        (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
          (MeasureTheory.eLpNorm
            (fun x => HilbertVec.ofVec
              (g x - ScalarOverlap.cubeAverageVec S.1 g))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
              p.exponent.toReal)) ^ (1 / p.exponent.toReal)

/-- Formula accessor for the canonical finite-`p` Euclidean overlap seminorm. -/
theorem cubeEuclideanPositiveBesovOverlapESeminorm_eq {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (g : Vec d → Vec d) :
    cubeEuclideanPositiveBesovOverlapESeminorm Q s p g =
      (∑' j : ℕ,
        ENNReal.ofReal
            (Real.rpow 3
              (-(s.1 * p.exponent.toReal *
                (((Q.scale - (j : ℤ) : ℤ) : ℝ))))) *
          ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
            (ScalarOverlap.centersAtDepth Q j).attach.sum (fun S =>
              (MeasureTheory.eLpNorm
                (fun x => HilbertVec.ofVec
                  (g x - ScalarOverlap.cubeAverageVec S.1 g))
                p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^
                  p.exponent.toReal)) ^ (1 / p.exponent.toReal) := rfl

theorem cubeEuclideanPositiveBesovOverlapESeminorm_nonneg {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (g : Vec d → Vec d) :
    0 ≤ cubeEuclideanPositiveBesovOverlapESeminorm Q s p g :=
  bot_le

end

end Homogenization
