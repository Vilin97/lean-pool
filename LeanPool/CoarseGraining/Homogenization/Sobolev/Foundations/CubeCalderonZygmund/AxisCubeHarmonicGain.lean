/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.HarmonicGradientGainIteration
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.AxisCubeHarmonicCovariance

/-! # Axis Cube Harmonic Gain -/

namespace Homogenization

open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-!
# Axis-cube transport of the harmonic gradient gain

This file consumes the Euclidean harmonic gain on the centered unit triadic
cube and transports it to an arbitrary positive axis cube.  The coordinate to
Hilbert-vector comparison is kept here, so callers supply only harmonicity.
-/

private theorem harmonicPullback_grad_hilbert_memLp_two {d : ℕ} (z : Vec d) {L : ℝ}
    (hL : 0 < L) (u : H1Function (axisCube z L)) :
    MemLp (fun x => HilbertVec.ofVec ((axisCubeHarmonicPullback z hL u).grad x)) 2
      (normalizedCubeMeasure (originCube d 0)) := by
  rw [MeasureTheory.memLp_piLp_iff]
  intro i
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using
    (axisCubeHarmonicPullback z hL u).grad_memL2_normalizedCubeMeasure i

/-- The explicit finite-dimensional loss in the axis-cube transport remains
finite whenever the centered-cube gain constant is finite. -/
theorem axisCube_harmonicEuclideanGradientGain_coefficient_ne_top
    {d : ℕ} {r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth) :
    G.constant * (d : ℝ≥0∞) ≠ ∞ :=
  ENNReal.mul_ne_top G.constant_ne_top (ENNReal.natCast_ne_top d)

/-- The fixed-depth Euclidean harmonic-gradient gain transported to an
arbitrary positive axis cube.  The right side is its parent normalized
Hilbert-vector `L²` norm; the extra explicit factor is only the finite
coordinate count. -/
theorem axisCube_harmonicEuclideanGradientGain
    {d : ℕ} {r : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d r depth)
    (z : Vec d) (L : ℝ) (hL : 0 < L) (u : H1Function (axisCube z L))
    (hu : WeakPoissonEquationOn (axisCube z L) u 0) :
    MemLp (fun x => HilbertVec.ofVec (u.grad x)) r.exponent
        (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L depth)
          (axisCubeConcentricDepthSide L depth)) ∧
      eLpNorm (fun x => HilbertVec.ofVec (u.grad x)) r.exponent
          (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L depth)
            (axisCubeConcentricDepthSide L depth)) ≤
        (G.constant * (d : ℝ≥0∞)) *
          eLpNorm (fun x => HilbertVec.ofVec (u.grad x)) 2
            (axisCubeNormalizedMeasure z L) := by
  let v := axisCubeHarmonicPullback z hL u
  have hvharm : WeakPoissonEquationOn (openCubeSet (originCube d 0)) v 0 := by
    simpa only [v] using axisCubeHarmonicPullback_weakPoisson_zero z hL hu
  have hgain_mem : MemLp (fun x => HilbertVec.ofVec (v.grad x)) r.exponent
      (normalizedCubeMeasure (centralDescendant (originCube d 0) depth)) :=
    G.memLp (originCube d 0) v hvharm
  have hgain_bound : eLpNorm (fun x => HilbertVec.ofVec (v.grad x)) r.exponent
      (normalizedCubeMeasure (centralDescendant (originCube d 0) depth)) ≤
      G.constant * ∑ j : Fin d, eLpNorm (fun x => v.grad x j) 2
        (normalizedCubeMeasure (originCube d 0)) :=
    G.bound (originCube d 0) v hvharm
  rw [centralDescendant_originCube_zero_eq_originCube_neg_nat depth] at hgain_mem hgain_bound
  have hsource_mem : MemLp (fun x => HilbertVec.ofVec (u.grad (axisCubeAffine z L x)))
      r.exponent (normalizedCubeMeasure (originCube d (-(depth : ℤ)))) := by
    simpa only [v, axisCubeHarmonicPullback_grad] using hgain_mem
  have htarget_mem : MemLp (fun x => HilbertVec.ofVec (u.grad x)) r.exponent
      (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L depth)
        (axisCubeConcentricDepthSide L depth)) :=
    (memLp_axisCubeAffine_originCube_neg_nat_iff z hL.ne' depth r.exponent
      (fun x => HilbertVec.ofVec (u.grad x))).mp hsource_mem
  refine ⟨htarget_mem, ?_⟩
  have hdepth_transport := eLpNorm_axisCubeAffine_originCube_neg_nat_of_memLp
    z hL.ne' depth r.exponent (fun x => HilbertVec.ofVec (u.grad x)) hsource_mem
  have hparent_mem := harmonicPullback_grad_hilbert_memLp_two z hL u
  have hparent_transport := eLpNorm_axisCubeAffine_originCube_neg_nat_of_memLp
    z hL.ne' 0 2 (fun x => HilbertVec.ofVec (u.grad x)) (by
      simpa only [axisCubeHarmonicPullback_grad] using! hparent_mem)
  have hparent_transport' :
      eLpNorm (fun x => HilbertVec.ofVec (v.grad x)) 2
        (normalizedCubeMeasure (originCube d 0)) =
      eLpNorm (fun x => HilbertVec.ofVec (u.grad x)) 2
        (axisCubeNormalizedMeasure z L) := by
    calc
      _ = eLpNorm (fun x => HilbertVec.ofVec (u.grad (axisCubeAffine z L x))) 2
          (normalizedCubeMeasure (originCube d (-(0 : ℤ)))) := by
            simp only [v, axisCubeHarmonicPullback_grad, neg_zero]
      _ = eLpNorm (fun x => HilbertVec.ofVec (u.grad x)) 2
          (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L 0)
            (axisCubeConcentricDepthSide L 0)) := hparent_transport
      _ = _ := by simp
  have hsum_le :
      (∑ j : Fin d, eLpNorm (fun x => v.grad x j) 2
        (normalizedCubeMeasure (originCube d 0))) ≤
      (d : ℝ≥0∞) * eLpNorm (fun x => HilbertVec.ofVec (v.grad x)) 2
        (normalizedCubeMeasure (originCube d 0)) := by
    calc
      _ ≤ ∑ _j : Fin d, eLpNorm (fun x => HilbertVec.ofVec (v.grad x)) 2
          (normalizedCubeMeasure (originCube d 0)) := by
        exact Finset.sum_le_sum fun j _ =>
          coordinate_eLpNorm_le_euclidean (normalizedCubeMeasure (originCube d 0))
            FiniteLpExponent.two v.grad j
      _ = _ := by simp [nsmul_eq_mul]
  calc
    eLpNorm (fun x => HilbertVec.ofVec (u.grad x)) r.exponent
        (axisCubeNormalizedMeasure (axisCubeConcentricDepthCorner z L depth)
          (axisCubeConcentricDepthSide L depth)) =
        eLpNorm (fun x => HilbertVec.ofVec (v.grad x)) r.exponent
          (normalizedCubeMeasure (originCube d (-(depth : ℤ)))) := by
            rw [← hdepth_transport]
            simp only [v, axisCubeHarmonicPullback_grad]
    _ ≤ G.constant * ∑ j : Fin d, eLpNorm (fun x => v.grad x j) 2
          (normalizedCubeMeasure (originCube d 0)) := hgain_bound
    _ ≤ G.constant * ((d : ℝ≥0∞) * eLpNorm (fun x => HilbertVec.ofVec (v.grad x)) 2
          (normalizedCubeMeasure (originCube d 0))) := by gcongr
    _ = (G.constant * (d : ℝ≥0∞)) * eLpNorm (fun x => HilbertVec.ofVec (v.grad x)) 2
          (normalizedCubeMeasure (originCube d 0)) := by ring
    _ = (G.constant * (d : ℝ≥0∞)) *
        eLpNorm (fun x => HilbertVec.ofVec (u.grad x)) 2
          (axisCubeNormalizedMeasure z L) := by
      rw [hparent_transport']

end CubeCalderonZygmund

end

end Homogenization
