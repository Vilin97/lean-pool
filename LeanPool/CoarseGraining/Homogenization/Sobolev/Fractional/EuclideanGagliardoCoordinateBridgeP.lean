/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanWsp
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
import LeanPool.CoarseGraining.Homogenization.Sobolev.FiniteLpCoordinate

/-!
# Finite-`p` Euclidean-to-coordinate Gagliardo bridge

This module separates the two elementary changes which occur in the finite
exponent comparison: first replace the Euclidean distance in the vector
kernel by the project's ambient distance, and then compare that Hilbert-vector
kernel with its scalar coordinates.  Every displayed constant is independent
of the fractional order `s ∈ (0,1)`.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The intermediate ambient-distance, Euclidean-vector kernel.  Its scalar
coordinates are exactly the scalar Gagliardo kernels of the coordinates of
`F`; only its distance differs from `cubeEuclideanWspKernel`. -/
noncomputable def cubeAmbientHilbertWspKernel {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d) :
    Vec d × Vec d → HilbertVec d :=
  fun z =>
    (dist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
      HilbertVec.ofVec (F z.1 - F z.2)

@[simp] theorem cubeAmbientHilbertWspKernel_apply {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (z : Vec d × Vec d) :
    cubeAmbientHilbertWspKernel s p F z =
      (dist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) •
        HilbertVec.ofVec (F z.1 - F z.2) := rfl

/-- The finite-`p` seminorm of the intermediate ambient-distance vector
kernel. -/
noncomputable def cubeAmbientHilbertWspESeminorm {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  eLpNorm' (cubeAmbientHilbertWspKernel s p F) p.exponent.toReal
    (Gagliardo.gagliardoCubeMeasure Q)

theorem cubeAmbientHilbertWspESeminorm_eq_lintegral {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    cubeAmbientHilbertWspESeminorm Q s p F =
      (∫⁻ z, ‖cubeAmbientHilbertWspKernel s p F z‖ₑ ^ p.exponent.toReal
        ∂Gagliardo.gagliardoCubeMeasure Q) ^ (1 / p.exponent.toReal) := by
  unfold cubeAmbientHilbertWspESeminorm
  exact eLpNorm'_eq_lintegral_enorm _ _ _

/-- The scalar coordinates of the intermediate vector kernel are precisely
the scalar ambient-distance Gagliardo kernels. -/
theorem cubeAmbientHilbertWspKernel_coordinate {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (z : Vec d × Vec d) (i : Fin d) :
    (cubeAmbientHilbertWspKernel s p F z) i =
      Gagliardo.gagliardoKernel s.1 p.exponent (fun x => F x i) z := by
  rw [cubeAmbientHilbertWspKernel_apply, Gagliardo.gagliardoKernel_apply]
  simp only [Gagliardo.kernelExponent]
  rfl

/-- A direct Euclidean `L^p` field has scalar coordinate `L^p` fields on the
same cube. -/
theorem cubeEuclideanLp_coordinate_memLp {d : ℕ} {Q : TriadicCube d}
    {p : FiniteLpExponent} (F : CubeEuclideanLpField Q p) (i : Fin d) :
    MemLp (fun x => F x i) p.exponent (normalizedCubeMeasure Q) := by
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using F.euclideanMemLp.eval_piLp i

/-- Exact powered-kernel identity for the intermediate ambient-distance
Hilbert-vector kernel. -/
theorem cubeAmbientHilbertWspKernel_enorm_rpow {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (z : Vec d × Vec d) :
    ‖cubeAmbientHilbertWspKernel s p F z‖ₑ ^ p.exponent.toReal =
      ENNReal.ofReal (dist z.1 z.2 ^ (-(s.1 * p.exponent.toReal + d))) *
        ENNReal.ofReal (euclideanNorm (F z.1 - F z.2) ^ p.exponent.toReal) := by
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  rw [← ofReal_norm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  simp only [cubeAmbientHilbertWspKernel_apply, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg dist_nonneg _), ← euclideanNorm_eq_norm_ofVec]
  rw [Real.mul_rpow (Real.rpow_nonneg dist_nonneg _) (euclideanNorm_nonneg _)]
  calc
    ENNReal.ofReal
        ((dist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) ^
            p.exponent.toReal * euclideanNorm (F z.1 - F z.2) ^ p.exponent.toReal) =
        ENNReal.ofReal
          ((dist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) ^
            p.exponent.toReal) *
          ENNReal.ofReal (euclideanNorm (F z.1 - F z.2) ^ p.exponent.toReal) :=
      ENNReal.ofReal_mul
        (Real.rpow_nonneg (Real.rpow_nonneg dist_nonneg _) _)
    _ = ENNReal.ofReal (dist z.1 z.2 ^ (-(s.1 * p.exponent.toReal + d))) *
          ENNReal.ofReal (euclideanNorm (F z.1 - F z.2) ^ p.exponent.toReal) := by
      congr 2
      by_cases hxy : z.1 = z.2
      · rw [hxy]
        simp only [dist_self]
        have hfirst : 0 < s.1 + (d : ℝ) / p.exponent.toReal :=
          add_pos_of_pos_of_nonneg s.2.1
            (div_nonneg (Nat.cast_nonneg _) hp.le)
        have hsecond : 0 < s.1 * p.exponent.toReal + d :=
          add_pos_of_pos_of_nonneg (mul_pos s.2.1 hp) (Nat.cast_nonneg _)
        rw [Real.zero_rpow (neg_ne_zero.mpr hfirst.ne'),
          Real.zero_rpow hp.ne', Real.zero_rpow (neg_ne_zero.mpr hsecond.ne')]
      · have hdist : 0 < dist z.1 z.2 := dist_pos.mpr hxy
        rw [← Real.rpow_mul hdist.le]
        congr 1
        field_simp

/-- Exact powered-kernel identity for the Euclidean-distance vector kernel. -/
theorem cubeEuclideanWspKernel_enorm_rpow {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (z : Vec d × Vec d) :
    ‖cubeEuclideanWspKernel s p F z‖ₑ ^ p.exponent.toReal =
      ENNReal.ofReal (euclideanDist z.1 z.2 ^ (-(s.1 * p.exponent.toReal + d))) *
        ENNReal.ofReal (euclideanNorm (F z.1 - F z.2) ^ p.exponent.toReal) := by
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  rw [← ofReal_norm]
  rw [ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hp.le]
  simp only [norm_cubeEuclideanWspKernel]
  rw [Real.mul_rpow (Real.rpow_nonneg (euclideanDist_nonneg _ _) _)
    (euclideanNorm_nonneg _)]
  calc
    ENNReal.ofReal
        ((euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) ^
            p.exponent.toReal * euclideanNorm (F z.1 - F z.2) ^ p.exponent.toReal) =
        ENNReal.ofReal
          ((euclideanDist z.1 z.2 ^ (-(s.1 + (d : ℝ) / p.exponent.toReal))) ^
            p.exponent.toReal) *
          ENNReal.ofReal (euclideanNorm (F z.1 - F z.2) ^ p.exponent.toReal) :=
      ENNReal.ofReal_mul
        (Real.rpow_nonneg (Real.rpow_nonneg (euclideanDist_nonneg _ _) _) _)
    _ = ENNReal.ofReal (euclideanDist z.1 z.2 ^ (-(s.1 * p.exponent.toReal + d))) *
          ENNReal.ofReal (euclideanNorm (F z.1 - F z.2) ^ p.exponent.toReal) := by
      congr 2
      by_cases hxy : z.1 = z.2
      · rw [hxy]
        simp only [euclideanDist_self]
        have hfirst : 0 < s.1 + (d : ℝ) / p.exponent.toReal :=
          add_pos_of_pos_of_nonneg s.2.1
            (div_nonneg (Nat.cast_nonneg _) hp.le)
        have hsecond : 0 < s.1 * p.exponent.toReal + d :=
          add_pos_of_pos_of_nonneg (mul_pos s.2.1 hp) (Nat.cast_nonneg _)
        rw [Real.zero_rpow (neg_ne_zero.mpr hfirst.ne'),
          Real.zero_rpow hp.ne', Real.zero_rpow (neg_ne_zero.mpr hsecond.ne')]
      · have hdist : 0 < euclideanDist z.1 z.2 := by
          apply lt_of_le_of_ne (euclideanDist_nonneg _ _)
          intro hzero
          exact hxy (euclideanDist_eq_zero_iff.mp hzero.symm)
        rw [← Real.rpow_mul hdist.le]
        congr 1
        field_simp

/-- Pointwise, replacing the Euclidean distance by the ambient distance can
only increase the powered kernel. -/
theorem cubeEuclideanWspKernel_rpow_le_ambientHilbert {d : ℕ} [NeZero d]
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (z : Vec d × Vec d) :
    ‖cubeEuclideanWspKernel s p F z‖ₑ ^ p.exponent.toReal ≤
      ‖cubeAmbientHilbertWspKernel s p F z‖ₑ ^ p.exponent.toReal := by
  rw [cubeEuclideanWspKernel_enorm_rpow, cubeAmbientHilbertWspKernel_enorm_rpow]
  rcases z with ⟨x, y⟩
  let a : ℝ := s.1 * p.exponent.toReal + d
  let A : ℝ := euclideanNorm (F x - F y) ^ p.exponent.toReal
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have ha : 0 < a :=
    add_pos_of_pos_of_nonneg (mul_pos s.2.1 hp) (Nat.cast_nonneg _)
  change ENNReal.ofReal (euclideanDist x y ^ (-a)) * ENNReal.ofReal A ≤
    ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A
  by_cases hxy : x = y
  · subst y
    simp [a, A]
  · have hdist : 0 < dist x y := dist_pos.mpr hxy
    have heuclideanDist : 0 < euclideanDist x y := by
      apply lt_of_le_of_ne (euclideanDist_nonneg x y)
      intro hzero
      exact hxy (euclideanDist_eq_zero_iff.mp hzero.symm)
    have hpow :
        Real.rpow (euclideanDist x y) (-a) ≤ Real.rpow (dist x y) (-a) :=
      Real.rpow_le_rpow_of_nonpos hdist (dist_le_euclideanDist x y)
        (neg_nonpos.mpr ha.le)
    calc
      ENNReal.ofReal (euclideanDist x y ^ (-a)) * ENNReal.ofReal A =
          ENNReal.ofReal A * ENNReal.ofReal (euclideanDist x y ^ (-a)) := mul_comm _ _
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (dist x y ^ (-a)) :=
        mul_le_mul_right (ENNReal.ofReal_le_ofReal hpow) _
      _ = ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A := mul_comm _ _

/-- Pointwise reverse metric comparison, before replacing its `s`-dependent
factor by the uniform finite-`p` factor. -/
theorem ambientHilbertWspKernel_rpow_le_metric_factor_mul_euclidean
    {d : ℕ} [NeZero d] (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) (z : Vec d × Vec d) :
    ‖cubeAmbientHilbertWspKernel s p F z‖ₑ ^ p.exponent.toReal ≤
      ENNReal.ofReal ((d : ℝ) ^ (s.1 * p.exponent.toReal + d)) *
        ‖cubeEuclideanWspKernel s p F z‖ₑ ^ p.exponent.toReal := by
  rw [cubeAmbientHilbertWspKernel_enorm_rpow, cubeEuclideanWspKernel_enorm_rpow]
  rcases z with ⟨x, y⟩
  let a : ℝ := s.1 * p.exponent.toReal + d
  let A : ℝ := euclideanNorm (F x - F y) ^ p.exponent.toReal
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have ha : 0 < a :=
    add_pos_of_pos_of_nonneg (mul_pos s.2.1 hp) (Nat.cast_nonneg _)
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  change ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A ≤
    ENNReal.ofReal ((d : ℝ) ^ a) *
      (ENNReal.ofReal (euclideanDist x y ^ (-a)) * ENNReal.ofReal A)
  by_cases hxy : x = y
  · subst y
    have hne : -a ≠ 0 := neg_ne_zero.mpr ha.ne'
    rw [euclideanDist_self, dist_self, Real.zero_rpow hne]
    simp
  · have hdist : 0 < dist x y := dist_pos.mpr hxy
    have heuclideanDist : 0 < euclideanDist x y := by
      apply lt_of_le_of_ne (euclideanDist_nonneg x y)
      intro hzero
      exact hxy (euclideanDist_eq_zero_iff.mp hzero.symm)
    have hdenominator :
        Real.rpow (euclideanDist x y) a ≤
          Real.rpow (d : ℝ) a * Real.rpow (dist x y) a := by
      calc
        Real.rpow (euclideanDist x y) a ≤
            Real.rpow ((d : ℝ) * dist x y) a :=
          Real.rpow_le_rpow (euclideanDist_nonneg x y)
            (euclideanDist_le_dimension_mul_dist x y) ha.le
        _ = Real.rpow (d : ℝ) a * Real.rpow (dist x y) a :=
          Real.mul_rpow hd.le dist_nonneg
    have hA : 0 ≤ A := Real.rpow_nonneg (euclideanNorm_nonneg _) _
    have hdistPow : 0 < Real.rpow (dist x y) a :=
      Real.rpow_pos_of_pos hdist a
    have heuclideanDistPow : 0 < Real.rpow (euclideanDist x y) a :=
      Real.rpow_pos_of_pos heuclideanDist a
    have hreal :
        Real.rpow (dist x y) (-a) * A ≤
          Real.rpow (d : ℝ) a * (Real.rpow (euclideanDist x y) (-a) * A) := by
      have hdist_neg :
          Real.rpow (dist x y) (-a) = (Real.rpow (dist x y) a)⁻¹ :=
        Real.rpow_neg hdist.le a
      have heuclideanDist_neg :
          Real.rpow (euclideanDist x y) (-a) =
            (Real.rpow (euclideanDist x y) a)⁻¹ :=
        Real.rpow_neg heuclideanDist.le a
      rw [hdist_neg, heuclideanDist_neg]
      calc
        (Real.rpow (dist x y) a)⁻¹ * A =
            A / Real.rpow (dist x y) a := by rw [div_eq_mul_inv, mul_comm]
        _ ≤ (Real.rpow (d : ℝ) a * A) /
            Real.rpow (euclideanDist x y) a := by
          rw [div_le_div_iff₀ hdistPow heuclideanDistPow]
          calc
            A * Real.rpow (euclideanDist x y) a ≤
                A * (Real.rpow (d : ℝ) a * Real.rpow (dist x y) a) :=
              mul_le_mul_of_nonneg_left hdenominator hA
            _ = (Real.rpow (d : ℝ) a * A) * Real.rpow (dist x y) a := by ring
        _ = Real.rpow (d : ℝ) a *
            ((Real.rpow (euclideanDist x y) a)⁻¹ * A) := by
          rw [div_eq_mul_inv]
          ring
    calc
      ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A =
          ENNReal.ofReal (Real.rpow (dist x y) (-a) * A) :=
        (ENNReal.ofReal_mul (Real.rpow_nonneg dist_nonneg (-a))).symm
      _ ≤ ENNReal.ofReal
          (Real.rpow (d : ℝ) a *
            (Real.rpow (euclideanDist x y) (-a) * A)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((d : ℝ) ^ a) *
          (ENNReal.ofReal (euclideanDist x y ^ (-a)) * ENNReal.ofReal A) := by
        calc
          ENNReal.ofReal ((d : ℝ) ^ a *
              (euclideanDist x y ^ (-a) * A)) =
              ENNReal.ofReal ((d : ℝ) ^ a) *
                ENNReal.ofReal (euclideanDist x y ^ (-a) * A) :=
            ENNReal.ofReal_mul (Real.rpow_nonneg hd.le a)
          _ = ENNReal.ofReal ((d : ℝ) ^ a) *
              (ENNReal.ofReal (euclideanDist x y ^ (-a)) * ENNReal.ofReal A) := by
            rw [ENNReal.ofReal_mul
              (Real.rpow_nonneg (euclideanDist_nonneg _ _) _)]

/-- The coordinate scalar Gagliardo energies, each raised to the exact finite
`p` power before summation. -/
noncomputable def cubeCoordinateGagliardoPowerEnergy {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) : ℝ≥0∞ :=
  ∑ i : Fin d,
    (Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent (fun x => F x i)) ^
      p.exponent.toReal

private theorem scalar_gagliardoKernel_measurable {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (hF : Measurable F) (i : Fin d) :
    Measurable (Gagliardo.gagliardoKernel s.1 p.exponent (fun x => F x i)) := by
  unfold Gagliardo.gagliardoKernel
  have hf : Measurable fun z : Vec d × Vec d =>
      dist z.1 z.2 ^ (-Gagliardo.kernelExponent d s.1 p.exponent) :=
    measurable_dist.pow measurable_const
  have hg : Measurable fun z : Vec d × Vec d =>
      (fun x => F x i) z.1 - (fun x => F x i) z.2 :=
    ((continuous_apply i).measurable.comp (hF.comp measurable_fst)).sub
      ((continuous_apply i).measurable.comp (hF.comp measurable_snd))
  exact hf.smul hg

private theorem scalar_gagliardoKernel_enorm_rpow_measurable {d : ℕ}
    (s : FractionalOrder) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (hF : Measurable F) (i : Fin d) :
    Measurable (fun z =>
      ‖Gagliardo.gagliardoKernel s.1 p.exponent (fun x => F x i) z‖ₑ ^
        p.exponent.toReal) :=
  (scalar_gagliardoKernel_measurable s p F hF i).enorm.pow measurable_const

private theorem scalar_cubeGagliardoESeminorm_rpow_eq_lintegral {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (f : Vec d → ℝ) :
    (Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent f) ^
        p.exponent.toReal =
      ∫⁻ z, ‖Gagliardo.gagliardoKernel s.1 p.exponent f z‖ₑ ^
        p.exponent.toReal ∂Gagliardo.gagliardoCubeMeasure Q := by
  rw [Gagliardo.Internal.cubeGagliardoESeminorm_eq_lintegral
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne]
  rw [← ENNReal.rpow_mul]
  have hp : p.exponent.toReal ≠ 0 := (ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne).ne'
  have hmul : 1 / p.exponent.toReal * p.exponent.toReal = 1 := by
    field_simp
  rw [hmul, ENNReal.rpow_one]

/-- The finite coordinate energy is one product-measure integral of the sum
of the powered scalar kernels. -/
theorem cubeCoordinateGagliardoPowerEnergy_eq_lintegral_sum {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) (hF : Measurable F) :
    cubeCoordinateGagliardoPowerEnergy Q s p F =
  ∫⁻ z, ∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 p.exponent (fun x => F x i) z‖ₑ ^
          p.exponent.toReal ∂Gagliardo.gagliardoCubeMeasure Q := by
  unfold cubeCoordinateGagliardoPowerEnergy
  rw [Finset.sum_congr rfl fun i _ =>
    scalar_cubeGagliardoESeminorm_rpow_eq_lintegral Q s p (fun x => F x i)]
  rw [← lintegral_finsetSum' Finset.univ]
  intro i _
  exact (scalar_gagliardoKernel_enorm_rpow_measurable s p F hF i).aemeasurable

/-- The powered Euclidean seminorm is exactly its kernel integral. -/
theorem cubeEuclideanWspESeminorm_rpow_eq_lintegral {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal =
      ∫⁻ z, ‖cubeEuclideanWspKernel s p F z‖ₑ ^ p.exponent.toReal
        ∂Gagliardo.gagliardoCubeMeasure Q := by
  rw [cubeEuclideanWspESeminorm_eq_lintegral, ← ENNReal.rpow_mul]
  have hp : p.exponent.toReal ≠ 0 := (ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne).ne'
  have hmul : 1 / p.exponent.toReal * p.exponent.toReal = 1 := by
    field_simp
  rw [hmul, ENNReal.rpow_one]

/-- The powered intermediate seminorm is exactly its kernel integral. -/
theorem cubeAmbientHilbertWspESeminorm_rpow_eq_lintegral {d : ℕ}
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    (cubeAmbientHilbertWspESeminorm Q s p F) ^ p.exponent.toReal =
      ∫⁻ z, ‖cubeAmbientHilbertWspKernel s p F z‖ₑ ^ p.exponent.toReal
        ∂Gagliardo.gagliardoCubeMeasure Q := by
  rw [cubeAmbientHilbertWspESeminorm_eq_lintegral, ← ENNReal.rpow_mul]
  have hp : p.exponent.toReal ≠ 0 := (ENNReal.toReal_pos
    (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne).ne'
  have hmul : 1 / p.exponent.toReal * p.exponent.toReal = 1 := by
    field_simp
  rw [hmul, ENNReal.rpow_one]

/-- Powered Euclidean fractional energy is bounded by the intermediate
ambient-distance Hilbert energy. -/
theorem cubeEuclideanWspESeminorm_rpow_le_ambientHilbert {d : ℕ} [NeZero d]
    (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal ≤
      (cubeAmbientHilbertWspESeminorm Q s p F) ^ p.exponent.toReal := by
  rw [cubeEuclideanWspESeminorm_rpow_eq_lintegral,
    cubeAmbientHilbertWspESeminorm_rpow_eq_lintegral]
  exact lintegral_mono fun z =>
    cubeEuclideanWspKernel_rpow_le_ambientHilbert s p F z

/-- The uniform metric factor for the reverse comparison.  It depends only
on the dimension and finite exponent, never on `s`. -/
noncomputable def cubeEuclideanWspMetricComparisonConstant
    (d : ℕ) (p : FiniteLpExponent) : ℝ≥0∞ :=
  ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + p.exponent.toReal))

theorem cubeEuclideanWspMetricComparisonConstant_lt_top
    (d : ℕ) (p : FiniteLpExponent) :
    cubeEuclideanWspMetricComparisonConstant d p < ∞ :=
  ENNReal.ofReal_lt_top

private theorem metric_factor_le_uniform_metricComparisonConstant {d : ℕ} [NeZero d]
    (s : FractionalOrder) (p : FiniteLpExponent) :
    ENNReal.ofReal ((d : ℝ) ^ (s.1 * p.exponent.toReal + d)) ≤
      cubeEuclideanWspMetricComparisonConstant d p := by
  have hp : 0 < p.exponent.toReal :=
    ENNReal.toReal_pos (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
  have hd : 1 ≤ (d : ℝ) := by
    exact_mod_cast Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero (NeZero.ne d))
  apply ENNReal.ofReal_le_ofReal
  apply Real.rpow_le_rpow_of_exponent_le hd
  have hs : s.1 * p.exponent.toReal ≤ p.exponent.toReal := by
    calc
      s.1 * p.exponent.toReal ≤ 1 * p.exponent.toReal :=
        mul_le_mul_of_nonneg_right s.2.2.le hp.le
      _ = p.exponent.toReal := one_mul _
  linarith

/-- The intermediate ambient-distance energy is bounded by the Euclidean
energy with an explicit constant uniform in the fractional order. -/
theorem cubeAmbientHilbertWspESeminorm_rpow_le_metricComparisonConstant_mul
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (s : FractionalOrder)
    (p : FiniteLpExponent) (F : Vec d → Vec d) :
    (cubeAmbientHilbertWspESeminorm Q s p F) ^ p.exponent.toReal ≤
      cubeEuclideanWspMetricComparisonConstant d p *
        (cubeEuclideanWspESeminorm Q s p F) ^ p.exponent.toReal := by
  rw [cubeAmbientHilbertWspESeminorm_rpow_eq_lintegral,
    cubeEuclideanWspESeminorm_rpow_eq_lintegral]
  calc
    (∫⁻ z, ‖cubeAmbientHilbertWspKernel s p F z‖ₑ ^ p.exponent.toReal
        ∂Gagliardo.gagliardoCubeMeasure Q) ≤
      ∫⁻ z, ENNReal.ofReal ((d : ℝ) ^ (s.1 * p.exponent.toReal + d)) *
        ‖cubeEuclideanWspKernel s p F z‖ₑ ^ p.exponent.toReal
        ∂Gagliardo.gagliardoCubeMeasure Q := by
      refine lintegral_mono fun z => ?_
      exact ambientHilbertWspKernel_rpow_le_metric_factor_mul_euclidean s p F z
    _ ≤ ∫⁻ z, cubeEuclideanWspMetricComparisonConstant d p *
        ‖cubeEuclideanWspKernel s p F z‖ₑ ^ p.exponent.toReal
        ∂Gagliardo.gagliardoCubeMeasure Q := by
      refine lintegral_mono fun z => ?_
      exact mul_le_mul_left
        (metric_factor_le_uniform_metricComparisonConstant (d := d) s p) _
    _ = cubeEuclideanWspMetricComparisonConstant d p *
        ∫⁻ z, ‖cubeEuclideanWspKernel s p F z‖ₑ ^ p.exponent.toReal
        ∂Gagliardo.gagliardoCubeMeasure Q := by
      rw [lintegral_const_mul' _ _
        (cubeEuclideanWspMetricComparisonConstant_lt_top d p).ne]

/-- The sum of scalar coordinate Gagliardo `p`-energies is controlled by the
intermediate Hilbert-vector energy. -/
theorem cubeCoordinateGagliardoPowerEnergy_le_dimension_mul_ambientHilbert
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) :
    cubeCoordinateGagliardoPowerEnergy Q s p F ≤
      (d : ℝ≥0∞) *
        (cubeAmbientHilbertWspESeminorm Q s p F) ^ p.exponent.toReal := by
  unfold cubeCoordinateGagliardoPowerEnergy
  calc
    _ ≤ ∑ _i : Fin d,
        (cubeAmbientHilbertWspESeminorm Q s p F) ^ p.exponent.toReal := by
      apply Finset.sum_le_sum
      intro i _
      rw [scalar_cubeGagliardoESeminorm_rpow_eq_lintegral,
        cubeAmbientHilbertWspESeminorm_rpow_eq_lintegral]
      apply lintegral_mono
      intro z
      apply ENNReal.rpow_le_rpow _ ENNReal.toReal_nonneg
      rw [← cubeAmbientHilbertWspKernel_coordinate s p F z i]
      rw [← ofReal_norm, ← ofReal_norm]
      apply ENNReal.ofReal_le_ofReal
      simpa only [Real.norm_eq_abs] using
        HilbertVec.abs_apply_le_norm (cubeAmbientHilbertWspKernel s p F z) i
    _ = _ := by simp [nsmul_eq_mul]

/-- The explicit finite-dimensional coordinate factor in the reverse
Hilbert-vector comparison. -/
noncomputable def cubeCoordinateGagliardoComparisonConstant
    (d : ℕ) (p : FiniteLpExponent) : ℝ≥0∞ :=
  ‖(d : ℝ)‖ₑ ^ p.exponent.toReal *
    (d : ℝ≥0∞) ^ (p.exponent.toReal - 1)

theorem cubeCoordinateGagliardoComparisonConstant_lt_top
    (d : ℕ) (p : FiniteLpExponent) :
    cubeCoordinateGagliardoComparisonConstant d p < ∞ := by
  unfold cubeCoordinateGagliardoComparisonConstant
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg enorm_ne_top)
    (ENNReal.rpow_lt_top_of_nonneg
      (sub_nonneg.mpr (by
        rw [← ENNReal.toReal_one]
        exact ENNReal.toReal_mono p.lt_top.ne p.one_lt.le))
      (ENNReal.natCast_ne_top d))

/-- The intermediate Hilbert-vector `p`-energy is bounded by the finite sum
of scalar coordinate Gagliardo energies. -/
theorem cubeAmbientHilbertWspESeminorm_rpow_le_coordinateGagliardoPowerEnergy
    {d : ℕ} (Q : TriadicCube d) (s : FractionalOrder) (p : FiniteLpExponent)
    (F : Vec d → Vec d) (hF : Measurable F) :
    (cubeAmbientHilbertWspESeminorm Q s p F) ^ p.exponent.toReal ≤
      cubeCoordinateGagliardoComparisonConstant d p *
        cubeCoordinateGagliardoPowerEnergy Q s p F := by
  have hcoord : ∀ i : Fin d,
      AEStronglyMeasurable
        (fun z => (cubeAmbientHilbertWspKernel s p F z).toVec i)
        (Gagliardo.gagliardoCubeMeasure Q) := by
    intro i
    simpa only [HilbertVec.toVec, cubeAmbientHilbertWspKernel_coordinate] using
      (scalar_gagliardoKernel_measurable s p F hF i).aestronglyMeasurable
  have hkernel : AEStronglyMeasurable (cubeAmbientHilbertWspKernel s p F)
      (Gagliardo.gagliardoCubeMeasure Q) := by
    simpa only [HilbertVec.continuousLinearEquivVec_symm_apply,
      HilbertVec.ofVec_toVec] using
      ((HilbertVec.continuousLinearEquivVec d).symm.continuous.comp_aestronglyMeasurable
        (AEMeasurable.of_eval (fun i => (hcoord i).aemeasurable)).aestronglyMeasurable)
  have hscalar (i : Fin d) :
      Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent (fun x => F x i) =
        eLpNorm (Gagliardo.gagliardoKernel s.1 p.exponent (fun x => F x i))
          p.exponent (Gagliardo.gagliardoCubeMeasure Q) :=
    Gagliardo.Internal.cubeGagliardoESeminorm_def _ _ _ _
      (scalar_gagliardoKernel_measurable s p F hF i).aestronglyMeasurable
  have hambient : cubeAmbientHilbertWspESeminorm Q s p F =
      eLpNorm (cubeAmbientHilbertWspKernel s p F) p.exponent
        (Gagliardo.gagliardoCubeMeasure Q) :=
    (eLpNorm_eq_eLpNorm' (ne_of_gt (lt_trans zero_lt_one p.one_lt)) p.lt_top.ne
      hkernel).symm
  have hvector := euclidean_eLpNorm_rpow_le_dimension_rpow_mul_sum_rpow
    (Gagliardo.gagliardoCubeMeasure Q) p
    (fun z => (cubeAmbientHilbertWspKernel s p F z).toVec) hcoord
  have hpowerSum := finiteLpExponent_rpow_sum_le_card_rpow_mul_sum_rpow
    (fun i : Fin d =>
      Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent (fun x => F x i)) p
  calc
    (cubeAmbientHilbertWspESeminorm Q s p F) ^ p.exponent.toReal ≤
        ‖(d : ℝ)‖ₑ ^ p.exponent.toReal *
          (∑ i : Fin d,
            Gagliardo.cubeGagliardoESeminorm Q s.1 p.exponent (fun x => F x i)) ^
              p.exponent.toReal := by
      rw [hambient]
      simp_rw [hscalar]
      simpa only [HilbertVec.ofVec_toVec,
        HilbertVec.toVec, cubeAmbientHilbertWspKernel_coordinate] using! hvector
    _ ≤ ‖(d : ℝ)‖ₑ ^ p.exponent.toReal *
        ((d : ℝ≥0∞) ^ (p.exponent.toReal - 1) *
          cubeCoordinateGagliardoPowerEnergy Q s p F) := by
      apply mul_le_mul_right
      simpa only [cubeCoordinateGagliardoPowerEnergy, Fintype.card_fin] using hpowerSum
    _ = cubeCoordinateGagliardoComparisonConstant d p *
        cubeCoordinateGagliardoPowerEnergy Q s p F := by
      rw [cubeCoordinateGagliardoComparisonConstant]
      ring

end

end Homogenization
