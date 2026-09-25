/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.UnitCubeGeometry
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.EuclideanH2
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.DefinitionsAPI
public import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.AssemblyPieces

/-!
# Euclidean-to-coordinate Gagliardo bridge

This module fixes the exact product measure and the finite-coordinate
numerator decomposition needed to compare the Euclidean `H^s` energy with
the scalar ambient-distance Gagliardo energies.
-/

@[expose] public section

namespace Homogenization

open scoped BigOperators ENNReal
open MeasureTheory

noncomputable section

/-- The finite-coordinate family of scalar ambient-distance Gagliardo
seminorms at exponent two, squared before summation. -/
noncomputable def coordinateGagliardoEnergy {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) : ℝ≥0∞ :=
  ∑ i : Fin d,
    (Gagliardo.cubeGagliardoESeminorm (originCube d 0) s.1 (2 : ℝ≥0∞)
      (fun x => F x i)) ^ (2 : ℝ)

/-- The exact Euclidean product measure is the scalar Gagliardo product
measure on the origin unit cube. -/
theorem euclideanHsProductMeasure_eq_gagliardoCubeMeasure_originCube_zero (d : ℕ) :
    euclideanHsProductMeasure d = Gagliardo.gagliardoCubeMeasure (originCube d 0) := by
  unfold euclideanHsProductMeasure Gagliardo.gagliardoCubeMeasure
  rw [unitCenteredCubeDomain_normalizedVolume_eq_normalizedCubeMeasure,
    unitCenteredCubeDomain_restrictedVolume_eq_cubeMeasure]

/-- The squared Euclidean target magnitude is the finite sum of squared
coordinate differences. -/
theorem euclideanHs_numerator_eq_sum_coordinates {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) (z : Vec d × Vec d) :
    ‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 =
      ∑ i : Fin d, (F z.1 i - F z.2 i) ^ 2 := by
  simpa only [Pi.sub_apply, HilbertVec.ofVec, PiLp.toLp_apply] using
    HilbertVec.norm_sq_eq_sum_sq (HilbertVec.ofVec (F z.1 - F z.2))

/-- At zero dimension both the exact Euclidean energy and the finite
coordinate family vanish, with no positive-dimension instance. -/
theorem euclideanHsEnergy_zero_dim (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field 0) : euclideanHsEnergy s F = 0 := by
  rw [euclideanHsEnergy_eq_lintegral]
  refine (lintegral_congr fun z => ?_).trans lintegral_zero
  have hfield : F z.1 = F z.2 := Subsingleton.elim _ _
  simp [hfield]

theorem coordinateGagliardoEnergy_zero_dim (s : FractionalOrder)
    (F : UnitCubeEuclideanL2Field 0) : coordinateGagliardoEnergy s F = 0 := by
  simp [coordinateGagliardoEnergy]

private theorem sq_scalar_cubeGagliardoESeminorm_eq_lintegral {d : ℕ}
    (s : FractionalOrder) (f : Vec d → ℝ) :
    (Gagliardo.cubeGagliardoESeminorm (originCube d 0) s.1 (2 : ℝ≥0∞) f) ^ (2 : ℝ) =
      ∫⁻ z, ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) f z‖ₑ ^ (2 : ℝ)
        ∂Gagliardo.gagliardoCubeMeasure (originCube d 0) := by
  rw [Gagliardo.Internal.cubeGagliardoESeminorm_eq_lintegral (by norm_num) (by norm_num)]
  rw [← ENNReal.rpow_mul]
  norm_num

private theorem measurable_scalar_gagliardoKernel {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (hF : Measurable F)
    (i : Fin d) :
    Measurable (Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i)) := by
  unfold Gagliardo.gagliardoKernel
  have hf : Measurable fun z : Vec d × Vec d =>
      dist z.1 z.2 ^ (-Gagliardo.kernelExponent d s.1 (2 : ℝ≥0∞)) :=
    measurable_dist.pow measurable_const
  have hg : Measurable fun z : Vec d × Vec d =>
      (fun x => F x i) z.1 - (fun x => F x i) z.2 :=
    ((continuous_apply i).measurable.comp (hF.comp measurable_fst)).sub
      ((continuous_apply i).measurable.comp (hF.comp measurable_snd))
  exact hf.smul hg

private theorem measurable_scalar_gagliardoKernel_enorm_sq {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (hF : Measurable F)
    (i : Fin d) :
    Measurable (fun z =>
      ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)) :=
  (measurable_scalar_gagliardoKernel s F hF i).enorm.pow measurable_const

/-- The coordinate energy is one product-measure lintegral of the finite
sum of scalar ambient-distance kernels when the chosen representative is
measurable. -/
theorem coordinateGagliardoEnergy_eq_lintegral_sum {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (hF : Measurable F) :
    coordinateGagliardoEnergy s F =
      ∫⁻ z, ∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)
          ∂Gagliardo.gagliardoCubeMeasure (originCube d 0) := by
  unfold coordinateGagliardoEnergy
  rw [Finset.sum_congr rfl fun i _ =>
    sq_scalar_cubeGagliardoESeminorm_eq_lintegral s (fun x => F x i)]
  rw [← lintegral_finsetSum' Finset.univ]
  intro i _
  exact (measurable_scalar_gagliardoKernel_enorm_sq s F hF i).aemeasurable

private theorem sum_enorm_sq_coordinate_diff_eq_ofReal_numerator {d : ℕ}
    (F : UnitCubeEuclideanL2Field d) (z : Vec d × Vec d) :
    (∑ i : Fin d, ‖F z.1 i - F z.2 i‖ₑ ^ (2 : ℝ)) =
      ENNReal.ofReal (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2) := by
  rw [euclideanHs_numerator_eq_sum_coordinates]
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _hi => sq_nonneg (F z.1 i - F z.2 i))]
  refine Finset.sum_congr rfl ?_
  intro i _hi
  norm_num
  rw [Real.enorm_eq_ofReal_abs,
    ← ENNReal.ofReal_pow (abs_nonneg (F z.1 i - F z.2 i)), sq_abs]

private theorem sum_scalar_gagliardoKernel_eq_distance_mul_numerator {d : ℕ}
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (z : Vec d × Vec d) :
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
      refine Finset.sum_congr rfl ?_
      intro i _hi
      simpa only [ENNReal.toReal_ofNat] using
        Gagliardo.enorm_gagliardoKernel_rpow s.1
          (p := (2 : ℝ≥0∞)) (by norm_num) (by norm_num) (fun x => F x i) z
    _ = ENNReal.ofReal (dist z.1 z.2 ^ (-(s.1 * 2 + (d : ℝ)))) *
        ∑ i : Fin d, ‖F z.1 i - F z.2 i‖ₑ ^ (2 : ℝ) := by
      rw [Finset.mul_sum]
    _ = ENNReal.ofReal (dist z.1 z.2 ^ (-(s.1 * 2 + (d : ℝ)))) *
        ENNReal.ofReal (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2) := by
      rw [sum_enorm_sq_coordinate_diff_eq_ofReal_numerator]

private theorem euclideanHsIntegrand_le_sum_scalar_gagliardoKernel {d : ℕ}
    [NeZero d] (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (z : Vec d × Vec d) :
    euclideanHsIntegrand s F z ≤
      ∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ) := by
  rw [sum_scalar_gagliardoKernel_eq_distance_mul_numerator]
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
    have hA : 0 ≤ A := by
      exact sq_nonneg _
    have hreal :
        A / Real.rpow (euclideanDist x y) a ≤
          Real.rpow (dist x y) (-a) * A := by
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

private theorem sum_scalar_gagliardoKernel_le_mul_euclideanHsIntegrand {d : ℕ}
    [NeZero d] (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d)
    (z : Vec d × Vec d) :
    (∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)) ≤
      ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) * euclideanHsIntegrand s F z := by
  rw [sum_scalar_gagliardoKernel_eq_distance_mul_numerator]
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
      ENNReal.ofReal
        (A / Real.rpow (euclideanDist x y) ((d : ℝ) + 2 * s.1))
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
          Real.rpow (d : ℝ) a *
            (A / Real.rpow (euclideanDist x y) a) := by
      have hdist_neg :
          Real.rpow (dist x y) (-a) = (Real.rpow (dist x y) a)⁻¹ :=
        Real.rpow_neg hdist.le a
      calc
        Real.rpow (dist x y) (-a) * A =
            A / Real.rpow (dist x y) a := by
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
          (Real.rpow (d : ℝ) a *
            (A / Real.rpow (euclideanDist x y) a)) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = ENNReal.ofReal ((d : ℝ) ^ a) *
          ENNReal.ofReal (A / Real.rpow (euclideanDist x y) a) := by
        exact ENNReal.ofReal_mul (Real.rpow_nonneg hd.le a)

/-- The explicit metric-comparison constant is finite in every dimension and fractional order. -/
theorem coordinateGagliardoEnergy_euclideanHsConstant_lt_top (d : ℕ)
    (s : FractionalOrder) :
    ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) < ∞ :=
  ENNReal.ofReal_lt_top

/-- Proof-internal positive-dimensional producer: the exact Euclidean energy is bounded by the
finite family of scalar ambient-distance Gagliardo energies. -/
theorem euclideanHsEnergy_le_coordinateGagliardoEnergy {d : ℕ} [NeZero d]
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (hF : Measurable F) :
    euclideanHsEnergy s F ≤ coordinateGagliardoEnergy s F := by
  rw [euclideanHsEnergy_eq_lintegral,
    euclideanHsProductMeasure_eq_gagliardoCubeMeasure_originCube_zero,
    coordinateGagliardoEnergy_eq_lintegral_sum s F hF]
  refine lintegral_mono fun z => ?_
  simpa only [euclideanHsIntegrand] using
    euclideanHsIntegrand_le_sum_scalar_gagliardoKernel s F z

/-- Proof-internal positive-dimensional producer: the coordinate Gagliardo energy is bounded by
the exact Euclidean energy with an explicit metric-comparison factor. -/
theorem coordinateGagliardoEnergy_le_mul_euclideanHsEnergy {d : ℕ} [NeZero d]
    (s : FractionalOrder) (F : UnitCubeEuclideanL2Field d) (hF : Measurable F) :
    coordinateGagliardoEnergy s F ≤
      ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) * euclideanHsEnergy s F := by
  rw [coordinateGagliardoEnergy_eq_lintegral_sum s F hF,
    euclideanHsEnergy_eq_lintegral,
    euclideanHsProductMeasure_eq_gagliardoCubeMeasure_originCube_zero]
  calc
    (∫⁻ z, ∑ i : Fin d,
        ‖Gagliardo.gagliardoKernel s.1 (2 : ℝ≥0∞) (fun x => F x i) z‖ₑ ^ (2 : ℝ)
        ∂Gagliardo.gagliardoCubeMeasure (originCube d 0)) ≤
      ∫⁻ z, ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) *
        ENNReal.ofReal
          (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
            Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
        ∂Gagliardo.gagliardoCubeMeasure (originCube d 0) := by
      refine lintegral_mono fun z => ?_
      simpa only [euclideanHsIntegrand] using
        sum_scalar_gagliardoKernel_le_mul_euclideanHsIntegrand s F z
    _ = ENNReal.ofReal ((d : ℝ) ^ ((d : ℝ) + 2 * s.1)) *
        ∫⁻ z, ENNReal.ofReal
          (‖HilbertVec.ofVec (F z.1 - F z.2)‖ ^ 2 /
            Real.rpow (euclideanDist z.1 z.2) ((d : ℝ) + 2 * s.1))
          ∂Gagliardo.gagliardoCubeMeasure (originCube d 0) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end

end Homogenization
