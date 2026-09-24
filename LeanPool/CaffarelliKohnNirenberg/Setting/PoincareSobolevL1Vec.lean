/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.GradientNorm

/-!
# Poincare Sobolev L1 Vec

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators ENNReal
open CKN.Foundation.Parabolic

namespace CKN

noncomputable section

private theorem vec3Ball_eq_euclideanBall {x₀ : Vec3} {r : ℝ} (hr : 0 < r) :
    vec3Ball x₀ r = euclideanBall x₀ r := by
  ext x
  change vec3EuclideanNorm (x - x₀) < r ↔ x ∈ euclideanBall x₀ r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
    using (mem_euclideanBall_iff_vecEuclideanNorm_lt (d := 3) hr).symm

/-- Explicit constant for the vector-valued ball inequality. -/
noncomputable def poincareSobolevL1VectorConstant : ℝ :=
  2 * Real.sqrt 3 * poincareSobolevL1Constant.toReal

private theorem contDiff_coord {u : Vec3 → Vec3} (hu : ContDiff ℝ 1 u) (i : Fin 3) :
    ContDiff ℝ 1 (fun x => u x i) := by
  exact contDiff_apply ℝ ℝ i |>.comp hu

private theorem vec3_square_eq_sum {v : Vec3} :
    (vec3EuclideanNorm v) ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
  rw [vec3EuclideanNorm]
  exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))

private theorem contDiff_vec3_square {u : Vec3 → Vec3} (hu : ContDiff ℝ 1 u) :
    ContDiff ℝ 1 (fun x => (vec3EuclideanNorm (u x)) ^ 2) := by
  have hfun : (fun x => (vec3EuclideanNorm (u x)) ^ 2) =
      fun x => ∑ i : Fin 3, (u x i) ^ 2 := by
    funext x
    rw [vec3_square_eq_sum]
  rw [hfun]
  apply ContDiff.sum
  intro i hi
  exact (contDiff_coord hu i).pow 2

private theorem fderiv_vec3_square_apply {u : Vec3 → Vec3}
    (hu : ContDiff ℝ 1 u) (x z : Vec3) :
    (fderiv ℝ (fun y => (vec3EuclideanNorm (u y)) ^ 2) x) z =
      2 * ∑ i : Fin 3, u x i *
        (fderiv ℝ (fun y => u y i) x) z := by
  have hfun : (fun y => (vec3EuclideanNorm (u y)) ^ 2) =
      ∑ i : Fin 3, (fun y => (u y i) ^ 2) := by
    funext y
    rw [vec3_square_eq_sum]
    simp only [Finset.sum_apply]
  rw [hfun, fderiv_sum]
  · change ∑ i : Fin 3,
      (fderiv ℝ (fun y => (u y i) ^ 2) x) z = _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hcoord := (contDiff_coord hu i).differentiable (by norm_num) x
    have hmul := fderiv_mul hcoord hcoord
    have hpow : (fun y => (u y i) ^ 2) =
        (fun y => u y i) * (fun y => u y i) := by
      funext y
      simp [pow_two]
    rw [hpow, hmul]
    change u x i * (fderiv ℝ (fun y => u y i) x) z +
        u x i * (fderiv ℝ (fun y => u y i) x) z = _
    ring
  · intro i hi
    exact ((contDiff_coord hu i).pow 2).differentiable (by norm_num) x

private theorem fderiv_vec3_square_basis_apply {u : Vec3 → Vec3}
    (hu : ContDiff ℝ 1 u) (x : Vec3) (j : Fin 3) :
    (fderiv ℝ (fun y => (vec3EuclideanNorm (u y)) ^ 2) x) (basisVec j) =
      2 * ∑ i : Fin 3, u x i *
        (fderiv ℝ (fun y => u y i) x) (basisVec j) := by
  exact fderiv_vec3_square_apply hu x (basisVec j)

private theorem gradient_column_cauchy {u : Vec3 → Vec3}
    (x : Vec3) (j : Fin 3) :
    |∑ i : Fin 3, u x i *
        (fderiv ℝ (fun y => u y i) x) (basisVec j)| ≤
      vec3EuclideanNorm (u x) *
        Real.sqrt (∑ i : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) := by
  calc
    |∑ i : Fin 3, u x i *
        (fderiv ℝ (fun y => u y i) x) (basisVec j)| ≤
        ∑ i : Fin 3, |u x i| *
          |(fderiv ℝ (fun y => u y i) x) (basisVec j)| := by
      simpa only [abs_mul] using
        (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin 3)))
          (f := fun i : Fin 3 => u x i *
            (fderiv ℝ (fun y => u y i) x) (basisVec j)))
    _ ≤ Real.sqrt (∑ i : Fin 3, |u x i| ^ 2) *
        Real.sqrt (∑ i : Fin 3,
          |(fderiv ℝ (fun y => u y i) x) (basisVec j)| ^ 2) := by
      simpa only using
        (Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3))
          (fun i : Fin 3 => |u x i|)
          (fun i : Fin 3 =>
            |(fderiv ℝ (fun y => u y i) x) (basisVec j)|))
    _ = vec3EuclideanNorm (u x) *
        Real.sqrt (∑ i : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) := by
      have hu_sq : Real.sqrt (∑ i : Fin 3, |u x i| ^ 2) =
          vec3EuclideanNorm (u x) := by
        unfold vec3EuclideanNorm
        congr 1
        exact Finset.sum_congr rfl (fun i _ => sq_abs _)
      have hd_sq : Real.sqrt (∑ i : Fin 3,
          |(fderiv ℝ (fun y => u y i) x) (basisVec j)| ^ 2) =
          Real.sqrt (∑ i : Fin 3,
            ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) := by
        congr 1
        exact Finset.sum_congr rfl (fun i _ => sq_abs _)
      rw [hu_sq, hd_sq]

private theorem gradient_column_sum_le {u : Vec3 → Vec3}
    (x : Vec3) :
    ∑ j : Fin 3, Real.sqrt (∑ i : Fin 3,
        ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ≤
      Real.sqrt 3 * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
        ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3))
    (fun _ : Fin 3 => (1 : ℝ))
    (fun j : Fin 3 => Real.sqrt (∑ i : Fin 3,
      ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2))
  calc
    ∑ j : Fin 3, Real.sqrt (∑ i : Fin 3,
        ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) =
        ∑ j : Fin 3, (1 : ℝ) * Real.sqrt (∑ i : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) := by
            simp
    _ ≤ Real.sqrt (∑ j : Fin 3, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ j : Fin 3, (Real.sqrt (∑ i : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2)) ^ 2) := hcs
    _ = Real.sqrt 3 * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
        ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) := by
      have hfirst : (∑ j : Fin 3, (1 : ℝ) ^ 2) = 3 := by norm_num
      have hsecond :
          (∑ j : Fin 3, (Real.sqrt (∑ i : Fin 3,
            ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2)) ^ 2) =
            ∑ i : Fin 3, ∑ j : Fin 3,
              ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2 := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))]
      rw [hfirst, hsecond]

private theorem fderiv_vec3_square_norm_le {u : Vec3 → Vec3}
    (hu : ContDiff ℝ 1 u) (x : Vec3) :
    ‖fderiv ℝ (fun y => (vec3EuclideanNorm (u y)) ^ 2) x‖ ≤
      2 * Real.sqrt 3 * vec3EuclideanNorm (u x) *
        Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) := by
  rw [opNorm_eq_sum_abs_basis]
  calc
    ∑ j : Fin 3, |(fderiv ℝ (fun y => (vec3EuclideanNorm (u y)) ^ 2) x)
        (basisVec j)| =
        ∑ j : Fin 3, |2 * ∑ i : Fin 3, u x i *
          (fderiv ℝ (fun y => u y i) x) (basisVec j)| := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [fderiv_vec3_square_basis_apply hu x j]
    _ = ∑ j : Fin 3, 2 * |∑ i : Fin 3, u x i *
          (fderiv ℝ (fun y => u y i) x) (basisVec j)| := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [abs_mul]
            norm_num
    _ = 2 * ∑ j : Fin 3, |∑ i : Fin 3, u x i *
          (fderiv ℝ (fun y => u y i) x) (basisVec j)| := by
            rw [Finset.mul_sum]
    _ ≤ 2 * vec3EuclideanNorm (u x) *
        ∑ j : Fin 3, Real.sqrt (∑ i : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) := by
      have hsum :
          ∑ j : Fin 3, |∑ i : Fin 3, u x i *
              (fderiv ℝ (fun y => u y i) x) (basisVec j)| ≤
            vec3EuclideanNorm (u x) * ∑ j : Fin 3, Real.sqrt (∑ i : Fin 3,
              ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) := by
        calc
          _ ≤ ∑ j : Fin 3, vec3EuclideanNorm (u x) * Real.sqrt (∑ i : Fin 3,
              ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) :=
            Finset.sum_le_sum (s := (Finset.univ : Finset (Fin 3)))
              (fun j _ => gradient_column_cauchy (u := u) x j)
          _ = _ := by rw [Finset.mul_sum]
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left hsum (by norm_num : (0 : ℝ) ≤ 2))
    _ ≤ 2 * vec3EuclideanNorm (u x) * (Real.sqrt 3 *
        Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2)) := by
      exact mul_le_mul_of_nonneg_left (gradient_column_sum_le (u := u) x)
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (vec3EuclideanNorm_nonneg (u x)))
    _ = _ := by ring

private theorem memLp_euclideanBall_of_continuous
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) {f : Vec3 → ℝ}
    (hf : Continuous f) (p : ℝ≥0∞) :
    MemLp f p (volume.restrict (euclideanBall x₀ r)) := by
  let B : Set Vec3 := euclideanBall x₀ r
  let K : Set Vec3 := euclideanClosedBall x₀ r
  have hK : IsCompact K := isCompact_euclideanClosedBall x₀ hr.le
  have hBK : B ⊆ K := by
    intro x hx
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).le
  have hBopen : IsOpen B := by
    change IsOpen {x : Vec3 | euclideanSqDist x x₀ < r ^ 2}
    exact isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  let _ : IsFiniteMeasure (volume.restrict B) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]
    exact (measure_mono hBK).trans_lt hK.measure_lt_top
  obtain ⟨M, hM⟩ := hK.bddAbove_image hf.continuousOn
  obtain ⟨m, hm⟩ := hK.bddBelow_image hf.continuousOn
  refine memLp_of_bounded (a := m) (b := M) ?_ ?_ p
  · filter_upwards [ae_restrict_mem hBopen.measurableSet] with x hx
    have hxK : x ∈ K := hBK hx
    have hfx : f x ∈ f '' K := ⟨x, hxK, rfl⟩
    exact ⟨hm hfx, hM hfx⟩
  · exact hf.aestronglyMeasurable.restrict

private theorem vec3_norm_continuous {u : Vec3 → Vec3} (hu : ContDiff ℝ 1 u) :
    Continuous (fun x => vec3EuclideanNorm (u x)) := by
  change Continuous (fun x => Real.sqrt (∑ i : Fin 3, (u x i) ^ 2))
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i hi
  exact (((continuous_apply i).comp hu.continuous).pow 2)

private theorem vec3_gradient_norm_continuous {u : Vec3 → Vec3}
    (hu : ContDiff ℝ 1 u) :
    Continuous (fun x => Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2)) := by
  apply Continuous.sqrt
  apply continuous_finsetSum
  intro i hi
  apply continuous_finsetSum
  intro j hj
  exact (((contDiff_coord hu i).continuous_fderiv (by norm_num)).clm_apply
    continuous_const).pow 2

/-- Vector-valued Poincare–Sobolev inequality for a continuously differentiable map. -/
theorem poincareSobolevL1_vec3_ball
    (x₀ : Vec3) {r : ℝ} (hr : 0 < r)
    (u : Vec3 → Vec3) (hu : ContDiff ℝ 1 u) :
    (∫ x in vec3Ball x₀ r,
        |(vec3EuclideanNorm (u x)) ^ 2 -
          ⨍ y in vec3Ball x₀ r, (vec3EuclideanNorm (u y)) ^ 2| ^
            (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≤
      poincareSobolevL1VectorConstant *
        (∫ x in vec3Ball x₀ r, (vec3EuclideanNorm (u x)) ^ 2 ∂volume) ^
          (1 / 2 : ℝ) *
        (∫ x in vec3Ball x₀ r, ∑ i : Fin 3, ∑ j : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2 ∂volume) ^
            (1 / 2 : ℝ) := by
  rw [vec3Ball_eq_euclideanBall hr]
  let g : Vec3 → ℝ := fun x => (vec3EuclideanNorm (u x)) ^ 2
  have hg : ContDiff ℝ 1 g := contDiff_vec3_square hu
  have hPS := poincareSobolevL1_ball x₀ hr g hg
  have hderiv :
      ∫ x in euclideanBall x₀ r, ‖fderiv ℝ g x‖ ∂volume ≤
        2 * Real.sqrt 3 * ∫ x in euclideanBall x₀ r,
          vec3EuclideanNorm (u x) * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
            ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ∂volume := by
    have hleft : IntegrableOn (fun x => ‖fderiv ℝ g x‖)
        (euclideanBall x₀ r) volume := by
      exact ((hg.continuous_fderiv (by norm_num)).norm.continuousOn.integrableOn_compact
        (isCompact_euclideanClosedBall x₀ hr.le)).mono_set (by
          intro x hx
          exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
            ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).le)
    have hright : IntegrableOn
        (fun x => 2 * Real.sqrt 3 * (vec3EuclideanNorm (u x) *
          Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
            ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2)))
        (euclideanBall x₀ r) volume := by
      exact (((vec3_norm_continuous hu).mul (vec3_gradient_norm_continuous hu)).const_mul
        (2 * Real.sqrt 3)).continuousOn.integrableOn_compact
        (isCompact_euclideanClosedBall x₀ hr.le) |>.mono_set (by
          intro x hx
          exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
            ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).le)
    calc
      ∫ x in euclideanBall x₀ r, ‖fderiv ℝ g x‖ ∂volume ≤
          ∫ x in euclideanBall x₀ r,
            2 * Real.sqrt 3 * (vec3EuclideanNorm (u x) *
              Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
                ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2)) ∂volume := by
            refine integral_mono_ae hleft hright ?_
            filter_upwards [ae_restrict_mem
              (isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous
                continuous_const).measurableSet] with x hx
            simpa only [g, mul_assoc] using fderiv_vec3_square_norm_le hu x
      _ = 2 * Real.sqrt 3 * ∫ x in euclideanBall x₀ r,
          vec3EuclideanNorm (u x) * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
            ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ∂volume := by
            rw [integral_const_mul]
  have hPS' :
      (∫ x in euclideanBall x₀ r,
          |(vec3EuclideanNorm (u x)) ^ 2 -
            ⨍ y in euclideanBall x₀ r, (vec3EuclideanNorm (u y)) ^ 2| ^
              (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≤
        poincareSobolevL1Constant.toReal *
          ∫ x in euclideanBall x₀ r,
            ‖fderiv ℝ (fun y => (vec3EuclideanNorm (u y)) ^ 2) x‖ ∂volume := by
    convert hPS using 1
    all_goals simp [g, integralAverage]
  have hPS'' :
      (∫ x in euclideanBall x₀ r,
          |(vec3EuclideanNorm (u x)) ^ 2 -
            ⨍ y in euclideanBall x₀ r, (vec3EuclideanNorm (u y)) ^ 2| ^
              (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≤
        poincareSobolevL1Constant.toReal *
          (2 * Real.sqrt 3 * ∫ x in euclideanBall x₀ r,
            vec3EuclideanNorm (u x) * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
              ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ∂volume) := by
    calc
      _ ≤ poincareSobolevL1Constant.toReal *
          ∫ x in euclideanBall x₀ r,
            ‖fderiv ℝ (fun y => (vec3EuclideanNorm (u y)) ^ 2) x‖ ∂volume := hPS'
      _ ≤ _ := mul_le_mul_of_nonneg_left hderiv ENNReal.toReal_nonneg
  have hUmem : MemLp (fun x => vec3EuclideanNorm (u x))
      (ENNReal.ofReal (2 : ℝ)) (volume.restrict (euclideanBall x₀ r)) := by
    simpa using memLp_euclideanBall_of_continuous hr (vec3_norm_continuous hu)
      (2 : ℝ≥0∞)
  have hGmem : MemLp (fun x => Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2))
      (ENNReal.ofReal (2 : ℝ)) (volume.restrict (euclideanBall x₀ r)) := by
    simpa using memLp_euclideanBall_of_continuous hr
      (vec3_gradient_norm_continuous hu) (2 : ℝ≥0∞)
  have hholder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (p := (2 : ℝ)) (q := (2 : ℝ))
    (μ := volume.restrict (euclideanBall x₀ r))
    ((Real.holderConjugate_iff).2 ⟨by norm_num, by norm_num⟩)
    (Filter.Eventually.of_forall (fun x => vec3EuclideanNorm_nonneg (u x)))
    (Filter.Eventually.of_forall (fun x => Real.sqrt_nonneg _))
    hUmem hGmem
  have hholder' :
      ∫ x in euclideanBall x₀ r, vec3EuclideanNorm (u x) *
          Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
            ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ∂volume ≤
        (∫ x in euclideanBall x₀ r, (vec3EuclideanNorm (u x)) ^ 2 ∂volume) ^
            (1 / 2 : ℝ) *
          (∫ x in euclideanBall x₀ r, ∑ i : Fin 3, ∑ j : Fin 3,
            ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2 ∂volume) ^
            (1 / 2 : ℝ) := by
    have hgrad_integral :
        (∫ x in euclideanBall x₀ r, Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) *
          Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
            ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ∂volume) =
        ∫ x in euclideanBall x₀ r, ∑ i : Fin 3, ∑ j : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2 ∂volume := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [← pow_two, Real.sq_sqrt]
      positivity
    calc
      _ ≤ (∫ x in euclideanBall x₀ r, (vec3EuclideanNorm (u x)) ^ 2 ∂volume) ^
            (1 / 2 : ℝ) *
          (∫ x in euclideanBall x₀ r,
            Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
              ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) *
              Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
                ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ∂volume) ^
            (1 / 2 : ℝ) := by
        simpa [pow_two] using hholder
      _ = _ := by rw [hgrad_integral]
  calc
          (∫ x in euclideanBall x₀ r,
        |(vec3EuclideanNorm (u x)) ^ 2 -
          ⨍ y in euclideanBall x₀ r, (vec3EuclideanNorm (u y)) ^ 2| ^
            (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≤
      poincareSobolevL1Constant.toReal *
        (2 * Real.sqrt 3 * ∫ x in euclideanBall x₀ r,
          vec3EuclideanNorm (u x) * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ∂volume) := hPS''
    _ ≤ poincareSobolevL1VectorConstant *
        (∫ x in euclideanBall x₀ r, (vec3EuclideanNorm (u x)) ^ 2 ∂volume) ^
          (1 / 2 : ℝ) *
        (∫ x in euclideanBall x₀ r, ∑ i : Fin 3, ∑ j : Fin 3,
          ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2 ∂volume) ^
            (1 / 2 : ℝ) := by
      rw [poincareSobolevL1VectorConstant]
      have hC : 0 ≤ poincareSobolevL1Constant.toReal := ENNReal.toReal_nonneg
      have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
      have hmul : 0 ≤ 2 * Real.sqrt 3 := by positivity
      calc
        poincareSobolevL1Constant.toReal *
            (2 * Real.sqrt 3 * ∫ x in euclideanBall x₀ r,
              vec3EuclideanNorm (u x) * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
                ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ∂volume) =
            2 * Real.sqrt 3 * poincareSobolevL1Constant.toReal *
              (∫ x in euclideanBall x₀ r,
                vec3EuclideanNorm (u x) * Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
                  ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2) ∂volume) := by ring
        _ ≤ 2 * Real.sqrt 3 * poincareSobolevL1Constant.toReal *
            ((∫ x in euclideanBall x₀ r, (vec3EuclideanNorm (u x)) ^ 2 ∂volume) ^
              (1 / 2 : ℝ) *
              (∫ x in euclideanBall x₀ r, ∑ i : Fin 3, ∑ j : Fin 3,
                ((fderiv ℝ (fun y => u y i) x) (basisVec j)) ^ 2 ∂volume) ^
                (1 / 2 : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hholder' (mul_nonneg hmul hC)
        _ = _ := by ring


end
end CKN
