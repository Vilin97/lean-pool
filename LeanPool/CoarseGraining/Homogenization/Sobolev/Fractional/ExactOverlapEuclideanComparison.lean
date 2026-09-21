/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapScalarComparison
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapEuclideanPoincare
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.CenteredCubeEuclideanH2
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.EuclideanGagliardoCoordinateBridge

/-!
# Exact Euclidean overlap Besov--Gagliardo comparison on centered cubes

This module compares the source-facing Euclidean overlap seminorm with the
literal physical Gagliardo seminorm on every centered triadic cube.  The
physical coordinate energy is kept over the physical product measure; scale
uniformity follows because all comparison constants are dimension/order
constants and do not depend on the centered-cube scale.
-/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

namespace CenteredCubeEuclideanL2Field

/-- The canonical exact-overlap integrability certificate carried by a
Euclidean `L²` field on an arbitrary centered triadic cube. -/
theorem exactOverlapEuclideanIntegrable {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) :
    ExactOverlapEuclideanIntegrable (originCube d m) F := by
  apply exactOverlapEuclideanIntegrable_of_euclidean_memLp
  simpa only [centeredCubeDomain,
    cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
      F.euclideanMemL2

end CenteredCubeEuclideanL2Field

/-- The physical finite-coordinate family of scalar ambient-distance
Gagliardo seminorms, squared before summation. -/
noncomputable def centeredCubeCoordinateGagliardoEnergy {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m) : ℝ≥0∞ :=
  ∑ i : Fin d,
    (Gagliardo.cubeGagliardoESeminorm (originCube d m) s.1 (2 : ℝ≥0∞)
      (fun x => F x i)) ^ (2 : ℝ)

/-- The squared Euclidean numerator is the sum of the squared coordinate
differences on every centered cube. -/
theorem centeredCubeEuclideanHs_numerator_eq_sum_coordinates {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) (z : Vec d × Vec d) :
    ‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 =
      ∑ i : Fin d, (F z.1 i - F z.2 i) ^ 2 := by
  simpa only [Pi.sub_apply, HilbertVec.ofVec, PiLp.toLp_apply] using
    HilbertVec.norm_sq_eq_sum_sq (HilbertVec.ofVec (F z.1 - F z.2))

/-- Both physical energies vanish in dimension zero. -/
theorem centeredCubeEuclideanHsEnergy_zero_dim {m : ℤ} (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field 0 m) : centeredCubeEuclideanHsEnergy s F = 0 := by
  rw [centeredCubeEuclideanHsEnergy_eq_lintegral]
  refine (lintegral_congr fun z => ?_).trans lintegral_zero
  have hfield : F z.1 = F z.2 := Subsingleton.elim _ _
  simp [hfield]

/-- The physical coordinate energy vanishes in dimension zero. -/
theorem centeredCubeCoordinateGagliardoEnergy_zero_dim {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field 0 m) :
    centeredCubeCoordinateGagliardoEnergy s F = 0 := by
  simp [centeredCubeCoordinateGagliardoEnergy]

private theorem sq_centeredCube_scalar_cubeGagliardoESeminorm_eq_lintegral
    {d : ℕ} {m : ℤ} (s : FractionalOrder) (f : Vec d → ℝ) :
    (Gagliardo.cubeGagliardoESeminorm (originCube d m) s.1 (2 : ℝ≥0∞) f) ^
        (2 : ℝ) =
      ∫⁻ z, ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) f z‖ₑ ^ (2 : ℝ)
        ∂Gagliardo.gagliardoCubeMeasure (originCube d m) := by
  rw [Gagliardo.Internal.cubeGagliardoESeminorm_eq_lintegral (by norm_num) (by norm_num)]
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem measurable_centeredCube_scalar_gagliardoKernel {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m)
    (hF : Measurable F) (i : Fin d) :
    Measurable (Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i)) := by
  unfold Gagliardo.gagliardoKernel
  exact (measurable_dist.pow measurable_const).smul
    (((continuous_apply i).measurable.comp (hF.comp measurable_fst)).sub
      ((continuous_apply i).measurable.comp (hF.comp measurable_snd)))

private theorem measurable_centeredCube_scalar_gagliardoKernel_enorm_sq
    {d : ℕ} {m : ℤ} (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) (hF : Measurable F) (i : Fin d) :
    Measurable (fun z =>
      ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)) :=
  (measurable_centeredCube_scalar_gagliardoKernel s F hF i).enorm.pow measurable_const

/-- The physical coordinate energy is one integral of the finite sum of
scalar kernels for a measurable representative. -/
private theorem centeredCubeCoordinateGagliardoEnergy_eq_lintegral_sum {d : ℕ} {m : ℤ}
    (s : FractionalOrder) (F : CenteredCubeEuclideanL2Field d m)
    (hF : Measurable F) :
    centeredCubeCoordinateGagliardoEnergy s F =
      ∫⁻ z, ∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)
          ∂Gagliardo.gagliardoCubeMeasure (originCube d m) := by
  unfold centeredCubeCoordinateGagliardoEnergy
  rw [Finset.sum_congr rfl fun i _ =>
    sq_centeredCube_scalar_cubeGagliardoESeminorm_eq_lintegral s (fun x => F x i)]
  rw [← lintegral_finsetSum' Finset.univ]
  intro i _
  exact (measurable_centeredCube_scalar_gagliardoKernel_enorm_sq s F hF i).aemeasurable

private theorem centeredCube_sum_enorm_sq_coordinate_diff_eq_ofReal_numerator
    {d : ℕ} {m : ℤ} (F : CenteredCubeEuclideanL2Field d m)
    (z : Vec d × Vec d) :
    (∑ i : Fin d, ‖F z.1 i - F z.2 i‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2) := by
  rw [centeredCubeEuclideanHs_numerator_eq_sum_coordinates]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg (F z.1 i - F z.2 i))]
  apply Finset.sum_congr rfl
  intro i _
  norm_num
  rw [Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg (F z.1 i - F z.2 i)), sq_abs]

private theorem centeredCube_sum_scalar_gagliardoKernel_eq_distance_mul_numerator
    {d : ℕ} {m : ℤ} (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) (z : Vec d × Vec d) :
    (∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal (dist z.1 z.2 ^ (-(s.1 * 2 + (d : ℝ)))) *
        ENNReal.ofReal (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2) := by
  calc
    (∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)) =
      ∑ i : Fin d,
        ENNReal.ofReal (dist z.1 z.2 ^ (-(s.1 * 2 + (d : ℝ)))) *
          ‖F z.1 i - F z.2 i‖ₑ ^ (2 : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa using
        Gagliardo.enorm_gagliardoKernel_rpow s.1
          (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (fun x => F x i) z
    _ = ENNReal.ofReal (dist z.1 z.2 ^ (-(s.1 * 2 + (d : ℝ)))) *
        ∑ i : Fin d, ‖F z.1 i - F z.2 i‖ₑ ^ (2 : ℝ) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal (dist z.1 z.2 ^ (-(s.1 * 2 + (d : ℝ)))) *
        ENNReal.ofReal (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2) := by
      rw [centeredCube_sum_enorm_sq_coordinate_diff_eq_ofReal_numerator]

private theorem centeredCubeEuclideanHsIntegrand_le_sum_scalar_gagliardoKernel
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) (z : Vec d × Vec d) :
    centeredCubeEuclideanHsIntegrand s F z ≤
      ∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ) := by
  rw [centeredCube_sum_scalar_gagliardoKernel_eq_distance_mul_numerator]
  rcases z with ⟨x, y⟩
  let a : ℝ := s.1 * 2 + (d : ℝ)
  let A : ℝ := ‖HilbertVec.ofVec (F x - F y)‖ ^ 2
  have ha : 0 < a := by
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    dsimp [a]
    nlinarith [s.2.1, hd_nonneg]
  change ENNReal.ofReal
      (A / Real.rpow (euclideanDist x y) ((d : ℝ) + 2 * s.1)) ≤
    ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A
  rw [show (d : ℝ) + 2 * s.1 = a by simp [a, add_comm, mul_comm]]
  by_cases hxy : x = y
  · subst y
    simp [A]
  · have hdist : 0 < dist x y := dist_pos.mpr hxy
    have heuclideanDist : 0 < euclideanDist x y := by
      apply lt_of_le_of_ne (euclideanDist_nonneg x y)
      intro hzero
      exact hxy (euclideanDist_eq_zero_iff.mp hzero.symm)
    have hpow :
        Real.rpow (euclideanDist x y) (-a) ≤ Real.rpow (dist x y) (-a) :=
      Real.rpow_le_rpow_of_nonpos hdist (dist_le_euclideanDist x y) (neg_nonpos.mpr ha.le)
    have hA : 0 ≤ A := sq_nonneg _
    have hreal :
        A / Real.rpow (euclideanDist x y) a ≤ Real.rpow (dist x y) (-a) * A := by
      have hneg :
          Real.rpow (euclideanDist x y) (-a) =
            (Real.rpow (euclideanDist x y) a)⁻¹ :=
        Real.rpow_neg heuclideanDist.le a
      calc
        A / Real.rpow (euclideanDist x y) a =
            Real.rpow (euclideanDist x y) (-a) * A := by
          rw [div_eq_mul_inv, hneg]
          ring
        _ ≤ Real.rpow (dist x y) (-a) * A :=
          mul_le_mul_of_nonneg_right hpow hA
    calc
      ENNReal.ofReal (A / Real.rpow (euclideanDist x y) a) ≤
          ENNReal.ofReal (Real.rpow (dist x y) (-a) * A) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A := by
        exact ENNReal.ofReal_mul (Real.rpow_nonneg dist_nonneg (-a))

private theorem centeredCube_sum_scalar_gagliardoKernel_le_mul_euclideanHsIntegrand
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) (z : Vec d × Vec d) :
    (∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) *
        centeredCubeEuclideanHsIntegrand s F z := by
  rw [centeredCube_sum_scalar_gagliardoKernel_eq_distance_mul_numerator]
  rcases z with ⟨x, y⟩
  let a : ℝ := s.1 * 2 + (d : ℝ)
  let A : ℝ := ‖HilbertVec.ofVec (F x - F y)‖ ^ 2
  have ha : 0 < a := by
    have hd_nonneg : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
    dsimp [a]
    nlinarith [s.2.1, hd_nonneg]
  have hd : 0 < (d : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne d)
  change ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A ≤
    ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) *
      ENNReal.ofReal (A / Real.rpow (euclideanDist x y) ((d : ℝ) + 2 * s.1))
  rw [show (d : ℝ) + 2 * s.1 = a by simp [a, add_comm, mul_comm]]
  by_cases hxy : x = y
  · subst y
    simp [A]
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
        _ = Real.rpow (d : ℝ) a * Real.rpow (dist x y) a := by
          exact Real.mul_rpow hd.le dist_nonneg
    have hA : 0 ≤ A := sq_nonneg _
    have hdistPow : 0 < Real.rpow (dist x y) a :=
      Real.rpow_pos_of_pos hdist a
    have heuclideanDistPow : 0 < Real.rpow (euclideanDist x y) a :=
      Real.rpow_pos_of_pos heuclideanDist a
    have hreal :
        Real.rpow (dist x y) (-a) * A ≤
          Real.rpow (d : ℝ) a * (A / Real.rpow (euclideanDist x y) a) := by
      have hdist_neg :
          Real.rpow (dist x y) (-a) = (Real.rpow (dist x y) a)⁻¹ :=
        Real.rpow_neg hdist.le a
      calc
        Real.rpow (dist x y) (-a) * A = A / Real.rpow (dist x y) a := by
          rw [hdist_neg, div_eq_mul_inv]
          ring
        _ ≤ (Real.rpow (d : ℝ) a * A) /
            Real.rpow (euclideanDist x y) a := by
          rw [div_le_div_iff₀ hdistPow heuclideanDistPow]
          calc
            A * Real.rpow (euclideanDist x y) a ≤
                A * (Real.rpow (d : ℝ) a * Real.rpow (dist x y) a) :=
              mul_le_mul_of_nonneg_left hdenominator hA
            _ = (Real.rpow (d : ℝ) a * A) * Real.rpow (dist x y) a := by
              ring
        _ = Real.rpow (d : ℝ) a *
            (A / Real.rpow (euclideanDist x y) a) := by
          ring
    calc
      ENNReal.ofReal (dist x y ^ (-a)) * ENNReal.ofReal A =
          ENNReal.ofReal (Real.rpow (dist x y) (-a) * A) := by
        exact (ENNReal.ofReal_mul (Real.rpow_nonneg dist_nonneg (-a))).symm
      _ ≤ ENNReal.ofReal
          (Real.rpow (d : ℝ) a * (A / Real.rpow (euclideanDist x y) a)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((d : ℝ) ^ a) *
          ENNReal.ofReal (A / Real.rpow (euclideanDist x y) a) := by
        exact ENNReal.ofReal_mul (Real.rpow_nonneg hd.le a)

/-- The physical Euclidean energy is bounded by the physical coordinate
Gagliardo energy, with no scale factor. -/
private theorem centeredCubeEuclideanHsEnergy_le_coordinateGagliardoEnergy
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) (hF : Measurable F) :
    centeredCubeEuclideanHsEnergy s F ≤ centeredCubeCoordinateGagliardoEnergy s F := by
  rw [centeredCubeEuclideanHsEnergy_eq_lintegral,
    centeredCubeEuclideanHsProductMeasure_eq_gagliardoCubeMeasure,
    centeredCubeCoordinateGagliardoEnergy_eq_lintegral_sum s F hF]
  apply lintegral_mono
  intro z
  simpa only [centeredCubeEuclideanHsIntegrand] using
    centeredCubeEuclideanHsIntegrand_le_sum_scalar_gagliardoKernel s F z

/-- The physical coordinate Gagliardo energy is bounded by the physical
Euclidean energy with the same explicit metric-comparison factor as on the
unit cube. -/
private theorem centeredCubeCoordinateGagliardoEnergy_le_mul_euclideanHsEnergy
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) (hF : Measurable F) :
    centeredCubeCoordinateGagliardoEnergy s F ≤
      ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) *
        centeredCubeEuclideanHsEnergy s F := by
  rw [centeredCubeCoordinateGagliardoEnergy_eq_lintegral_sum s F hF,
    centeredCubeEuclideanHsEnergy_eq_lintegral,
    centeredCubeEuclideanHsProductMeasure_eq_gagliardoCubeMeasure]
  calc
    (∫⁻ z, ∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)
        ∂Gagliardo.gagliardoCubeMeasure (originCube d m)) ≤
      ∫⁻ z, ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) *
        ENNReal.ofReal
          (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
            Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
        ∂Gagliardo.gagliardoCubeMeasure (originCube d m) := by
      apply lintegral_mono
      intro z
      simpa only [centeredCubeEuclideanHsIntegrand] using
        centeredCube_sum_scalar_gagliardoKernel_le_mul_euclideanHsIntegrand s F z
    _ = ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) *
        ∫⁻ z, ENNReal.ofReal
          (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
            Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
          ∂Gagliardo.gagliardoCubeMeasure (originCube d m) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem exactOverlapEuclideanSeminormTwo_sq_eq_sum {d : ℕ}
    (s : FractionalOrder) (Q : TriadicCube d) (F : Vec d → Vec d)
    (hF : ExactOverlapEuclideanIntegrable Q F) :
    (exactOverlapEuclideanSeminormTwo s Q F hF) ^ (2 : ℝ) =
      ∑ i : Fin d,
        (exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) Q
          (fun x => F x i) (hF.coordinate i)) ^ 2 := by
  rw [exactOverlapEuclideanSeminormTwo_eq]
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem centeredCube_coordinate_memLp {d : ℕ} {m : ℤ}
    (F : CenteredCubeEuclideanL2Field d m) (i : Fin d) :
    MemLp (fun x => F x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) := by
  have hF : MemLp (fun x => HilbertVec.ofVec (F x)) (2 : ℝ≥0∞)
      (normalizedCubeMeasure (originCube d m)) := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
        F.euclideanMemL2
  simpa only [HilbertVec.ofVec, PiLp.toLp_apply] using hF.eval_piLp i

/-- Coordinatewise scalar comparison bounds the squared exact Euclidean
overlap seminorm by the physical coordinate Gagliardo energy. -/
private theorem exactOverlapEuclideanSeminormTwo_sq_le_mul_coordinateGagliardoEnergy
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) (hF : Measurable F) :
    (exactOverlapEuclideanSeminormTwo s (originCube d m) F
      F.exactOverlapEuclideanIntegrable) ^ (2 : ℝ) ≤
        (2 * 3 ^ d : ℝ≥0∞) * centeredCubeCoordinateGagliardoEnergy s F := by
  rw [exactOverlapEuclideanSeminormTwo_sq_eq_sum]
  unfold centeredCubeCoordinateGagliardoEnergy
  calc
    (∑ i : Fin d,
        (exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) (originCube d m)
          (fun x => F x i) (F.exactOverlapEuclideanIntegrable.coordinate i)) ^ 2) ≤
      ∑ i : Fin d, (2 * 3 ^ d : ℝ≥0∞) *
        (Gagliardo.cubeGagliardoESeminorm (originCube d m) s.1 (2 : ℝ≥0∞)
          (fun x => F x i)) ^ (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [exactOverlapTwoParameters, exactOverlapScalarTwoParameters,
        ENNReal.rpow_two] using
          exactOverlapScalarSeminormTwo_sq_le_gagliardo s (originCube d m)
            (fun x => F x i) (F.exactOverlapEuclideanIntegrable.coordinate i)
            ((measurable_pi_apply i).comp hF) (centeredCube_coordinate_memLp F i)
    _ = (2 * 3 ^ d : ℝ≥0∞) *
        ∑ i : Fin d,
          (Gagliardo.cubeGagliardoESeminorm (originCube d m) s.1 (2 : ℝ≥0∞)
            (fun x => F x i)) ^ (2 : ℝ) := by
      rw [Finset.mul_sum]

/-- The reverse coordinatewise scalar comparison bounds the physical
coordinate Gagliardo energy by the squared exact Euclidean overlap seminorm. -/
private theorem centeredCubeCoordinateGagliardoEnergy_le_mul_exactOverlapEuclideanSeminormTwo_sq
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) (hF : Measurable F) :
    centeredCubeCoordinateGagliardoEnergy s F ≤
      (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
        (exactOverlapEuclideanSeminormTwo s (originCube d m) F
          F.exactOverlapEuclideanIntegrable) ^ (2 : ℝ) := by
  unfold centeredCubeCoordinateGagliardoEnergy
  rw [exactOverlapEuclideanSeminormTwo_sq_eq_sum]
  calc
    (∑ i : Fin d,
        (Gagliardo.cubeGagliardoESeminorm (originCube d m) s.1 (2 : ℝ≥0∞)
          (fun x => F x i)) ^ (2 : ℝ)) ≤
      ∑ i : Fin d, (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
        (exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) (originCube d m)
          (fun x => F x i) (F.exactOverlapEuclideanIntegrable.coordinate i)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [exactOverlapTwoParameters, exactOverlapScalarTwoParameters,
        ENNReal.rpow_two] using
          gagliardo_sq_le_exactOverlapScalarSeminormTwo s (originCube d m)
            (fun x => F x i) (F.exactOverlapEuclideanIntegrable.coordinate i)
            ((measurable_pi_apply i).comp hF) (centeredCube_coordinate_memLp F i)
    _ = (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
        ∑ i : Fin d,
          (exactOverlapFiniteSeminorm (exactOverlapTwoParameters s) (originCube d m)
            (fun x => F x i) (F.exactOverlapEuclideanIntegrable.coordinate i)) ^ 2 := by
      rw [Finset.mul_sum]

private theorem centeredCube_ae_eq_measurableRepresentative_on_overlap
    {d : ℕ} {m : ℤ} (F : CenteredCubeEuclideanL2Field d m) :
    ∀ (j : ℕ) (S : TriadicCube d),
      S ∈ ScalarOverlap.centersAtDepth (originCube d m) j →
        F =ᵐ[ScalarOverlap.normalizedCubeMeasure S] F.measurableRepresentative := by
  have hroot :
      F =ᵐ[normalizedCubeMeasure (originCube d m)] F.measurableRepresentative := by
    simpa only [centeredCubeDomain,
      cubeBoundedMeasurableDomain_normalizedVolume_eq_normalizedCubeMeasure] using
        F.ae_eq_measurableRepresentative
  intro j S hS
  rw [ScalarOverlap.normalizedCubeMeasure_eq_smul_restrict_of_mem_centersAtDepth hS]
  have hc : (ENNReal.ofReal (cubeVolume (originCube d m) / ScalarOverlap.cubeVolume S)) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2
      (div_pos (cubeVolume_pos (originCube d m)) (ScalarOverlap.cubeVolume_pos S))
  exact (Measure.ae_ennreal_smul_measure_iff hc).2 (ae_restrict_of_ae hroot)

/-- The exact Euclidean overlap seminorm is unchanged by passage to the
canonical globally measurable representative. -/
private theorem exactOverlapEuclideanSeminormTwo_eq_measurableRepresentative
    {d : ℕ} {m : ℤ} (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) :
    exactOverlapEuclideanSeminormTwo s (originCube d m) F
        F.exactOverlapEuclideanIntegrable =
      exactOverlapEuclideanSeminormTwo s (originCube d m) F.measurableRepresentative
        F.measurableRepresentative.exactOverlapEuclideanIntegrable := by
  apply exactOverlapEuclideanSeminormTwo_congr_ae
  intro i j S hS
  have hvector := centeredCube_ae_eq_measurableRepresentative_on_overlap F j S hS
  filter_upwards [hvector] with x hx
  rw [hx]

private theorem ennreal_rpow_two_rpow_half (a : ℝ≥0∞) :
    (a ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) = a := by
  rw [← ENNReal.rpow_mul]
  norm_num

/-- The physical Euclidean Gagliardo seminorm is controlled by the exact
Euclidean overlap seminorm, with no representative or integrability binder. -/
theorem centeredCubeEuclideanHsESeminorm_le_mul_exactOverlapEuclideanSeminormTwo
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) :
    centeredCubeEuclideanHsESeminorm s F ≤
      Gagliardo.gagliardoBesovLowerConstant d *
        exactOverlapEuclideanSeminormTwo s (originCube d m) F
          F.exactOverlapEuclideanIntegrable := by
  let G : CenteredCubeEuclideanL2Field d m := F.measurableRepresentative
  let B : ℝ≥0∞ := exactOverlapEuclideanSeminormTwo s (originCube d m) G
    G.exactOverlapEuclideanIntegrable
  have hGmeas : Measurable G := by
    simpa only [G] using F.measurable_measurableRepresentative
  have henergy : centeredCubeEuclideanHsEnergy s G ≤
      centeredCubeCoordinateGagliardoEnergy s G :=
    centeredCubeEuclideanHsEnergy_le_coordinateGagliardoEnergy s G hGmeas
  have hcoordinate : centeredCubeCoordinateGagliardoEnergy s G ≤
      (Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) * B ^ (2 : ℝ) := by
    simpa only [B] using
      centeredCubeCoordinateGagliardoEnergy_le_mul_exactOverlapEuclideanSeminormTwo_sq
        s G hGmeas
  rw [centeredCubeEuclideanHsESeminorm_congr_ae F.ae_eq_measurableRepresentative]
  change centeredCubeEuclideanHsEnergy s G ^ ((2 : ℝ)⁻¹) ≤
    Gagliardo.gagliardoBesovLowerConstant d *
      exactOverlapEuclideanSeminormTwo s (originCube d m) F
        F.exactOverlapEuclideanIntegrable
  calc
    centeredCubeEuclideanHsEnergy s G ^ ((2 : ℝ)⁻¹) ≤
        centeredCubeCoordinateGagliardoEnergy s G ^ ((2 : ℝ)⁻¹) := by
      exact ENNReal.rpow_le_rpow henergy (by norm_num)
    _ ≤ ((Gagliardo.gagliardoBesovLowerConstant d) ^ (2 : ℝ) *
        B ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) := by
      exact ENNReal.rpow_le_rpow hcoordinate (by norm_num)
    _ = Gagliardo.gagliardoBesovLowerConstant d * B := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num),
        ennreal_rpow_two_rpow_half, ennreal_rpow_two_rpow_half]
    _ = Gagliardo.gagliardoBesovLowerConstant d *
        exactOverlapEuclideanSeminormTwo s (originCube d m) F
          F.exactOverlapEuclideanIntegrable := by
      rw [exactOverlapEuclideanSeminormTwo_eq_measurableRepresentative]

/-- The exact Euclidean overlap seminorm is controlled by the physical
Euclidean Gagliardo seminorm.  The explicit constant contains both the scalar
overlap factor and the Euclidean/product-metric factor. -/
theorem exactOverlapEuclideanSeminormTwo_le_mul_centeredCubeEuclideanHsESeminorm
    {d : ℕ} {m : ℤ} [NeZero d] (s : FractionalOrder)
    (F : CenteredCubeEuclideanL2Field d m) :
    exactOverlapEuclideanSeminormTwo s (originCube d m) F
        F.exactOverlapEuclideanIntegrable ≤
      ((2 * 3 ^ d : ℝ≥0∞) *
        ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))) ^ ((2 : ℝ)⁻¹) *
          centeredCubeEuclideanHsESeminorm s F := by
  let G : CenteredCubeEuclideanL2Field d m := F.measurableRepresentative
  let B : ℝ≥0∞ := exactOverlapEuclideanSeminormTwo s (originCube d m) G
    G.exactOverlapEuclideanIntegrable
  let K : ℝ≥0∞ := (2 * 3 ^ d : ℝ≥0∞) *
    ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))
  have hGmeas : Measurable G := by
    simpa only [G] using F.measurable_measurableRepresentative
  have hoverlap : B ^ (2 : ℝ) ≤
      (2 * 3 ^ d : ℝ≥0∞) * centeredCubeCoordinateGagliardoEnergy s G := by
    simpa only [B] using
      exactOverlapEuclideanSeminormTwo_sq_le_mul_coordinateGagliardoEnergy
        s G hGmeas
  have hmetric : centeredCubeCoordinateGagliardoEnergy s G ≤
      ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) *
        centeredCubeEuclideanHsEnergy s G :=
    centeredCubeCoordinateGagliardoEnergy_le_mul_euclideanHsEnergy
      s G hGmeas
  have hsq : B ^ (2 : ℝ) ≤ K * centeredCubeEuclideanHsEnergy s G := by
    calc
      B ^ (2 : ℝ) ≤
          (2 * 3 ^ d : ℝ≥0∞) * centeredCubeCoordinateGagliardoEnergy s G := hoverlap
      _ ≤ (2 * 3 ^ d : ℝ≥0∞) *
          (ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) *
            centeredCubeEuclideanHsEnergy s G) := by
        gcongr
      _ = K * centeredCubeEuclideanHsEnergy s G := by
        simp only [K]
        ring
  rw [exactOverlapEuclideanSeminormTwo_eq_measurableRepresentative]
  change B ≤ K ^ ((2 : ℝ)⁻¹) * centeredCubeEuclideanHsESeminorm s F
  calc
    B = (B ^ (2 : ℝ)) ^ ((2 : ℝ)⁻¹) :=
      (ennreal_rpow_two_rpow_half B).symm
    _ ≤ (K * centeredCubeEuclideanHsEnergy s G) ^ ((2 : ℝ)⁻¹) := by
      exact ENNReal.rpow_le_rpow hsq (by norm_num)
    _ = K ^ ((2 : ℝ)⁻¹) *
        centeredCubeEuclideanHsEnergy s G ^ ((2 : ℝ)⁻¹) := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
    _ = K ^ ((2 : ℝ)⁻¹) * centeredCubeEuclideanHsESeminorm s F := by
      rw [centeredCubeEuclideanHsESeminorm_congr_ae F.ae_eq_measurableRepresentative]
      rfl

/-- One scale-independent constant for both directions of the physical
Euclidean Gagliardo/exact-overlap comparison. -/
noncomputable def centeredCubeExactOverlapEuclideanComparisonConstant
    (d : ℕ) (s : FractionalOrder) : ℝ≥0∞ :=
  max (Gagliardo.gagliardoBesovLowerConstant d)
    (((2 * 3 ^ d : ℝ≥0∞) *
      ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))) ^ ((2 : ℝ)⁻¹))

/-- The common physical comparison constant is finite. -/
theorem centeredCubeExactOverlapEuclideanComparisonConstant_lt_top
    (d : ℕ) (s : FractionalOrder) :
    centeredCubeExactOverlapEuclideanComparisonConstant d s < ∞ := by
  unfold centeredCubeExactOverlapEuclideanComparisonConstant
  rw [max_lt_iff]
  constructor
  · rw [Gagliardo.gagliardoBesovLowerConstant]
    exact lt_top_iff_ne_top.2 (by finiteness)
  · apply ENNReal.rpow_lt_top_of_nonneg (by norm_num)
    exact ENNReal.mul_ne_top (by finiteness) ENNReal.ofReal_ne_top

/-- Uniform source-facing equivalence between the exact physical Euclidean
Gagliardo seminorm and the exact Euclidean overlap Besov seminorm on every
centered triadic cube.  The finite constant is chosen before the scale and
field, and all measurability, `L²`, representative, and scalar-comparison
obligations are discharged internally. -/
theorem exists_centeredCubeEuclideanHs_exactOverlapEuclideanSeminormTwo_comparison
    (d : ℕ) [NeZero d] (s : FractionalOrder) :
    ∃ C : ℝ≥0∞, C < ∞ ∧
      ∀ (m : ℤ) (F : CenteredCubeEuclideanL2Field d m),
        centeredCubeEuclideanHsESeminorm s F ≤
            C * exactOverlapEuclideanSeminormTwo s (originCube d m) F
              F.exactOverlapEuclideanIntegrable ∧
          exactOverlapEuclideanSeminormTwo s (originCube d m) F
              F.exactOverlapEuclideanIntegrable ≤
            C * centeredCubeEuclideanHsESeminorm s F := by
  let C := centeredCubeExactOverlapEuclideanComparisonConstant d s
  refine ⟨C, centeredCubeExactOverlapEuclideanComparisonConstant_lt_top d s, ?_⟩
  intro m F
  constructor
  · calc
      centeredCubeEuclideanHsESeminorm s F ≤
          Gagliardo.gagliardoBesovLowerConstant d *
            exactOverlapEuclideanSeminormTwo s (originCube d m) F
              F.exactOverlapEuclideanIntegrable :=
        centeredCubeEuclideanHsESeminorm_le_mul_exactOverlapEuclideanSeminormTwo s F
      _ ≤ C * exactOverlapEuclideanSeminormTwo s (originCube d m) F
          F.exactOverlapEuclideanIntegrable := by
        exact mul_le_mul_left
          (le_max_left (Gagliardo.gagliardoBesovLowerConstant d)
            (((2 * 3 ^ d : ℝ≥0∞) *
              ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))) ^ ((2 : ℝ)⁻¹))) _
  · calc
      exactOverlapEuclideanSeminormTwo s (originCube d m) F
          F.exactOverlapEuclideanIntegrable ≤
        (((2 * 3 ^ d : ℝ≥0∞) *
          ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))) ^ ((2 : ℝ)⁻¹)) *
            centeredCubeEuclideanHsESeminorm s F :=
        exactOverlapEuclideanSeminormTwo_le_mul_centeredCubeEuclideanHsESeminorm s F
      _ ≤ C * centeredCubeEuclideanHsESeminorm s F := by
        exact mul_le_mul_left
          (le_max_right (Gagliardo.gagliardoBesovLowerConstant d)
            (((2 * 3 ^ d : ℝ≥0∞) *
              ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1))) ^ ((2 : ℝ)⁻¹))) _

end

end Homogenization
