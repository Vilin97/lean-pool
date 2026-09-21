/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePAveraging
import LeanPool.CoarseGraining.Homogenization.Besov.Duality.OverlapDefinitions

/-!
# Scalar homogeneity of exact overlap depth energies

The normalized overlap average and the resulting one-depth energy commute
exactly with multiplication by a real scalar.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem scalarOverlap_cubeAverageVec_const_smul {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} (q : FiniteLpExponent)
    (F : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) q.exponent
      (normalizedCubeMeasure Q))
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j) (c : ℝ) :
    ScalarOverlap.cubeAverageVec S (fun x => c • F x) =
      c • ScalarOverlap.cubeAverageVec S F := by
  funext i
  have hFcoord := hF
  rw [MeasureTheory.memLp_piLp_iff] at hFcoord
  have hFcoord' : MemLp (fun x => F x i) q.exponent
      (normalizedCubeMeasure Q) := by
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hFcoord i
  have hFlocal := ScalarOverlap.memLp_of_mem_centersAtDepth_of_memLp hS hFcoord'
  have hFlocal_int : Integrable (fun x => F x i)
      (ScalarOverlap.normalizedCubeMeasure S) :=
    hFlocal.integrable q.one_lt.le
  simp only [ScalarOverlap.cubeAverageVec, Pi.smul_apply]
  rw [ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure,
    ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure]
  simpa only [smul_eq_mul] using hFlocal_int.integral_smul c

private theorem scalarOverlap_residual_const_smul {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} (q : FiniteLpExponent)
    (F : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) q.exponent
      (normalizedCubeMeasure Q))
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j) (c : ℝ) :
    (fun x => HilbertVec.ofVec
      (c • F x - ScalarOverlap.cubeAverageVec S (fun y => c • F y))) =
      c • (fun x => HilbertVec.ofVec
        (F x - ScalarOverlap.cubeAverageVec S F)) := by
  have havg := scalarOverlap_cubeAverageVec_const_smul q F hF hS c
  funext x
  change (HilbertVec.ofVecL d)
      (c • F x - ScalarOverlap.cubeAverageVec S (fun y => c • F y)) =
    c • (HilbertVec.ofVecL d) (F x - ScalarOverlap.cubeAverageVec S F)
  simp only [havg, (HilbertVec.ofVecL d).map_sub,
    (HilbertVec.ofVecL d).map_smul, smul_sub]

/-- The exact powered overlap energy at a fixed depth is homogeneous under
real scalar multiplication, without a depth or cardinality loss. -/
theorem cubeEuclideanPositiveBesovOverlapDepthENorm_const_smul_rpow
    {d : ℕ} (Q : TriadicCube d) (q : FiniteLpExponent)
    (F : Vec d → Vec d)
    (c : ℝ)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) q.exponent
      (normalizedCubeMeasure Q)) (j : ℕ) :
    (cubeEuclideanPositiveBesovOverlapDepthENorm Q q (fun x => c • F x) j) ^
        q.exponent.toReal =
      ‖c‖ₑ ^ q.exponent.toReal *
        (cubeEuclideanPositiveBesovOverlapDepthENorm Q q F j) ^
          q.exponent.toReal := by
  classical
  rw [cubeEuclideanPositiveBesovOverlapDepthENorm_rpow,
    cubeEuclideanPositiveBesovOverlapDepthENorm_rpow]
  let D : Finset (TriadicCube d) := ScalarOverlap.centersAtDepth Q j
  have hlocal : ∀ S ∈ D,
      (eLpNorm (fun x => HilbertVec.ofVec
        (c • F x - ScalarOverlap.cubeAverageVec S (fun y => c • F y)))
        q.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ q.exponent.toReal =
      ‖c‖ₑ ^ q.exponent.toReal *
        (eLpNorm (fun x => HilbertVec.ofVec
          (F x - ScalarOverlap.cubeAverageVec S F))
          q.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ q.exponent.toReal := by
    intro S hS
    rw [scalarOverlap_residual_const_smul q F hF (by simpa [D] using hS) c,
      MeasureTheory.eLpNorm_const_smul,
      ENNReal.mul_rpow_of_nonneg _ _ ENNReal.toReal_nonneg]
  change ((D.card : ℝ≥0∞)⁻¹) * D.attach.sum (fun S =>
      (eLpNorm (fun x => HilbertVec.ofVec
        (c • F x - ScalarOverlap.cubeAverageVec S.1 (fun y => c • F y)))
        q.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ q.exponent.toReal) =
    ‖c‖ₑ ^ q.exponent.toReal *
      (((D.card : ℝ≥0∞)⁻¹) * D.attach.sum (fun S =>
        (eLpNorm (fun x => HilbertVec.ofVec
          (F x - ScalarOverlap.cubeAverageVec S.1 F))
          q.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ q.exponent.toReal))
  rw [show D.attach.sum (fun S =>
      (eLpNorm (fun x => HilbertVec.ofVec
        (c • F x - ScalarOverlap.cubeAverageVec S.1 (fun y => c • F y)))
        q.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ q.exponent.toReal) =
      D.attach.sum (fun S => ‖c‖ₑ ^ q.exponent.toReal *
        (eLpNorm (fun x => HilbertVec.ofVec
          (F x - ScalarOverlap.cubeAverageVec S.1 F))
          q.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ q.exponent.toReal) by
        exact Finset.sum_congr rfl fun S _ => hlocal S.1 S.2,
    ← Finset.mul_sum]
  ac_rfl

end

end Homogenization
