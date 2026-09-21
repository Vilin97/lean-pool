/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePAveraging

/-!
# Finite-`p` exact-overlap depth triangle inequality

At one overlap depth, the powered direct Euclidean energy is stable under
addition with the usual two-term finite-`p` constant.  The proof keeps the
average identity and the local Minkowski step on each overlap cube, before
summing, so no center-cardinality loss is introduced.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

private theorem memLp_hilbert_scalarOverlap_of_memLp {d : ℕ}
    {Q S : TriadicCube d} {j : ℕ} {F : Vec d → Vec d} {p : ℝ≥0∞}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p (normalizedCubeMeasure Q))
    (hS : S ∈ ScalarOverlap.centersAtDepth Q j) :
    MemLp (fun x => HilbertVec.ofVec (F x)) p (ScalarOverlap.normalizedCubeMeasure S) := by
  have hsub : ScalarOverlap.cubeSet S ⊆ cubeSet Q :=
    ScalarOverlap.cubeSet_subset_cubeSet_of_mem_centersAtDepth hS
  have hdom : ScalarOverlap.normalizedCubeMeasure S ≤
      (ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
        ENNReal.ofReal (cubeVolume Q)) • normalizedCubeMeasure Q := by
    rw [ScalarOverlap.normalizedCubeMeasure, normalizedCubeMeasure, smul_smul]
    have hvolQ : (0 : ℝ) < cubeVolume Q := cubeVolume_pos Q
    have hcancel : ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
        ENNReal.ofReal (cubeVolume Q) * ENNReal.ofReal (cubeVolume Q)⁻¹ =
          ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ := by
      rw [mul_assoc, ← ENNReal.ofReal_mul hvolQ.le,
        mul_inv_cancel₀ hvolQ.ne', ENNReal.ofReal_one, mul_one]
    rw [hcancel]
    refine Measure.le_iff'.2 fun A => ?_
    simp only [Measure.smul_apply, smul_eq_mul]
    refine mul_le_mul_right ?_ _
    rw [ScalarOverlap.cubeMeasure, cubeMeasure]
    exact Measure.le_iff'.1 (Measure.restrict_mono hsub le_rfl) A
  have hfin : (ENNReal.ofReal (ScalarOverlap.cubeVolume S)⁻¹ *
      ENNReal.ofReal (cubeVolume Q)) ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
  exact (hF.smul_measure hfin).mono_measure hdom

private theorem scalarOverlap_cubeAverageVec_add_of_memLp {d : ℕ}
    (S : TriadicCube d) (p : FiniteLpExponent) {F G : Vec d → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S))
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S)) :
    ScalarOverlap.cubeAverageVec S (fun x => F x + G x) =
      ScalarOverlap.cubeAverageVec S F + ScalarOverlap.cubeAverageVec S G := by
  funext i
  have hFi : MemLp (fun x => F x i) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S) := by
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF.eval_piLp i
  have hGi : MemLp (fun x => G x i) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S) := by
    simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hG.eval_piLp i
  have hFi_int : Integrable (fun x => F x i) (ScalarOverlap.normalizedCubeMeasure S) :=
    hFi.integrable p.one_lt.le
  have hGi_int : Integrable (fun x => G x i) (ScalarOverlap.normalizedCubeMeasure S) :=
    hGi.integrable p.one_lt.le
  show ScalarOverlap.cubeAverage S (fun x => (F x + G x) i) =
    ScalarOverlap.cubeAverage S (fun x => F x i) +
      ScalarOverlap.cubeAverage S (fun x => G x i)
  have hadd : (fun x => (F x + G x) i) = fun x => F x i + G x i := by
    funext x
    rfl
  rw [hadd, ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure,
    MeasureTheory.integral_add hFi_int hGi_int,
    ← ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure,
    ← ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure]

private theorem scalarOverlap_residual_add {d : ℕ}
    (S : TriadicCube d) (p : FiniteLpExponent) {F G : Vec d → Vec d}
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S))
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S)) :
    (fun x => HilbertVec.ofVec
      ((F x + G x) - ScalarOverlap.cubeAverageVec S (fun y => F y + G y))) =
      fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F) +
        HilbertVec.ofVec (G x - ScalarOverlap.cubeAverageVec S G) := by
  have havg := scalarOverlap_cubeAverageVec_add_of_memLp S p hF hG
  funext x
  rw [havg]
  change (HilbertVec.ofVecL d) ((F x + G x) -
      (ScalarOverlap.cubeAverageVec S F + ScalarOverlap.cubeAverageVec S G)) =
    (HilbertVec.ofVecL d) (F x - ScalarOverlap.cubeAverageVec S F) +
      (HilbertVec.ofVecL d) (G x - ScalarOverlap.cubeAverageVec S G)
  rw [← (HilbertVec.ofVecL d).map_add]
  congr 1
  ext i
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

private theorem scalarOverlap_residual_memLp {d : ℕ}
    (S : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S)) :
    MemLp (fun x => HilbertVec.ofVec
      (F x - ScalarOverlap.cubeAverageVec S F)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S) := by
  have hconst : MemLp (fun _ : Vec d => HilbertVec.ofVec
      (ScalarOverlap.cubeAverageVec S F)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S) :=
    memLp_const _
  simpa only [map_sub] using! hF.sub hconst

/-- The finite-`p` two-term constant after raising the Minkowski inequality to
the `p`-th power. -/
noncomputable def exactOverlapDepthTriangleConstant (p : FiniteLpExponent) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ (p.exponent.toReal - 1)

/-- The powered direct exact-overlap energy at one depth obeys a triangle
inequality with a constant depending only on the finite exponent. -/
theorem cubeEuclideanPositiveBesovOverlapDepthENorm_add_rpow_le {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (F G : Vec d → Vec d) (j : ℕ)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (normalizedCubeMeasure Q))
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) p.exponent
      (normalizedCubeMeasure Q)) :
    (cubeEuclideanPositiveBesovOverlapDepthENorm Q p (fun x => F x + G x) j) ^
        p.exponent.toReal ≤
      exactOverlapDepthTriangleConstant p *
        ((cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^ p.exponent.toReal +
          (cubeEuclideanPositiveBesovOverlapDepthENorm Q p G j) ^ p.exponent.toReal) := by
  classical
  let D : Finset (TriadicCube d) := ScalarOverlap.centersAtDepth Q j
  let r : ℝ := p.exponent.toReal
  have hr_one : 1 ≤ r := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono p.lt_top.ne p.one_lt.le
  have hlocal : ∀ S ∈ D,
      eLpNorm (fun x => HilbertVec.ofVec
          ((F x + G x) - ScalarOverlap.cubeAverageVec S (fun y => F y + G y)))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S) ≤
        eLpNorm (fun x => HilbertVec.ofVec
          (F x - ScalarOverlap.cubeAverageVec S F))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S) +
        eLpNorm (fun x => HilbertVec.ofVec
          (G x - ScalarOverlap.cubeAverageVec S G))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S) := by
    intro S hS
    have hFlocal := memLp_hilbert_scalarOverlap_of_memLp hF (by simpa [D] using hS)
    have hGlocal := memLp_hilbert_scalarOverlap_of_memLp hG (by simpa [D] using hS)
    rw [scalarOverlap_residual_add S p hFlocal hGlocal]
    exact eLpNorm_add_le
      (scalarOverlap_residual_memLp S p F hFlocal).aestronglyMeasurable
      (scalarOverlap_residual_memLp S p G hGlocal).aestronglyMeasurable p.one_lt.le
  have hlocal_power : ∀ S ∈ D,
      (eLpNorm (fun x => HilbertVec.ofVec
          ((F x + G x) - ScalarOverlap.cubeAverageVec S (fun y => F y + G y)))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ r ≤
        exactOverlapDepthTriangleConstant p *
          ((eLpNorm (fun x => HilbertVec.ofVec
            (F x - ScalarOverlap.cubeAverageVec S F))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ r +
            (eLpNorm (fun x => HilbertVec.ofVec
              (G x - ScalarOverlap.cubeAverageVec S G))
              p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ r) := by
    intro S hS
    calc
      (eLpNorm (fun x => HilbertVec.ofVec
          ((F x + G x) - ScalarOverlap.cubeAverageVec S (fun y => F y + G y)))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ r ≤
        (eLpNorm (fun x => HilbertVec.ofVec
          (F x - ScalarOverlap.cubeAverageVec S F))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S) +
          eLpNorm (fun x => HilbertVec.ofVec
            (G x - ScalarOverlap.cubeAverageVec S G))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ r :=
          ENNReal.rpow_le_rpow (hlocal S hS) (by positivity)
      _ ≤ exactOverlapDepthTriangleConstant p *
          ((eLpNorm (fun x => HilbertVec.ofVec
            (F x - ScalarOverlap.cubeAverageVec S F))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ r +
            (eLpNorm (fun x => HilbertVec.ofVec
              (G x - ScalarOverlap.cubeAverageVec S G))
              p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ r) := by
          exact ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hr_one
  rw [cubeEuclideanPositiveBesovOverlapDepthENorm_rpow,
    cubeEuclideanPositiveBesovOverlapDepthENorm_rpow,
    cubeEuclideanPositiveBesovOverlapDepthENorm_rpow]
  calc
    ((D.card : ℝ≥0∞)⁻¹) * D.attach.sum (fun S =>
        (eLpNorm (fun x => HilbertVec.ofVec
          ((F x + G x) - ScalarOverlap.cubeAverageVec S.1 (fun y => F y + G y)))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ r) ≤
      ((D.card : ℝ≥0∞)⁻¹) * D.attach.sum (fun S =>
        exactOverlapDepthTriangleConstant p *
          ((eLpNorm (fun x => HilbertVec.ofVec
            (F x - ScalarOverlap.cubeAverageVec S.1 F))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ r +
            (eLpNorm (fun x => HilbertVec.ofVec
              (G x - ScalarOverlap.cubeAverageVec S.1 G))
              p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ r)) := by
        refine mul_le_mul_right ?_ _
        apply Finset.sum_le_sum
        intro S _
        exact hlocal_power S.1 S.2
    _ = exactOverlapDepthTriangleConstant p *
        (((D.card : ℝ≥0∞)⁻¹) * D.attach.sum (fun S =>
          (eLpNorm (fun x => HilbertVec.ofVec
            (F x - ScalarOverlap.cubeAverageVec S.1 F))
            p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ r) +
          ((D.card : ℝ≥0∞)⁻¹) * D.attach.sum (fun S =>
            (eLpNorm (fun x => HilbertVec.ofVec
              (G x - ScalarOverlap.cubeAverageVec S.1 G))
              p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ r)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring

/-- The one-depth decomposition form of the finite-`p` triangle inequality. -/
theorem cubeEuclideanPositiveBesovOverlapDepthENorm_sub_add_rpow_le {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (F G : Vec d → Vec d) (j : ℕ)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (normalizedCubeMeasure Q))
    (hG : MemLp (fun x => HilbertVec.ofVec (G x)) p.exponent
      (normalizedCubeMeasure Q)) :
    (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^ p.exponent.toReal ≤
      exactOverlapDepthTriangleConstant p *
        ((cubeEuclideanPositiveBesovOverlapDepthENorm Q p (fun x => F x - G x) j) ^
            p.exponent.toReal +
          (cubeEuclideanPositiveBesovOverlapDepthENorm Q p G j) ^ p.exponent.toReal) := by
  have hsub : MemLp (fun x => HilbertVec.ofVec ((F x - G x))) p.exponent
      (normalizedCubeMeasure Q) := by
    simpa only [map_sub] using! hF.sub hG
  have hadd := cubeEuclideanPositiveBesovOverlapDepthENorm_add_rpow_le Q p
    (fun x => F x - G x) G j hsub hG
  simpa only [sub_add_cancel] using hadd

end

end Homogenization
