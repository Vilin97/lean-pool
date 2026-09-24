/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.SobolevPoincareBallWeak
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.BallDisplays
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import Mathlib.MeasureTheory.SpecificCodomains.Pi

/-!
# Sobolev Poincare Bridge

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

/-- Volume-normalization coefficient for the full ball Sobolev estimate. -/
noncomputable def sobolevPoincareBallFullConstant : ℝ≥0∞ :=
  ENNReal.ofReal (Real.pi * 4 / 3) ^ (-(1 / 3 : ℝ))

private lemma euclideanBall_volume_pos {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) :
    0 < volume (euclideanBall x₀ r) := by
  change 0 < volume {x | euclideanSqDist x x₀ < r ^ 2}
  have hopen : IsOpen {x : Vec 3 | euclideanSqDist x x₀ < r ^ 2} :=
    isOpen_lt (contDiff_euclideanSqDist_left x₀).continuous continuous_const
  exact hopen.measure_pos volume ⟨x₀, by simp [hr]⟩

private lemma euclideanBall_volume_lt_top {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) :
    volume (euclideanBall x₀ r) < ∞ := by
  change volume {x | euclideanSqDist x x₀ < r ^ 2} < ∞
  have hsub : {x : Vec 3 | euclideanSqDist x x₀ < r ^ 2} ⊆ Metric.ball x₀ r := by
    intro x hx
    rw [Metric.mem_ball, dist_eq_norm]
    have hnorm : ‖x - x₀‖ ≤ vecEuclideanNorm (x - x₀) := by
      rw [Pi.norm_def]
      have hnn : Finset.univ.sup (fun i => ‖(x - x₀) i‖₊) ≤
          ⟨vecEuclideanNorm (x - x₀), vecEuclideanNorm_nonneg _⟩ := by
        apply Finset.sup_le
        intro i hi
        exact_mod_cast abs_apply_le_vecEuclideanNorm (x - x₀) i
      exact_mod_cast hnn
    exact hnorm.trans_lt
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx)
  exact (measure_mono hsub).trans_lt (measure_ball_lt_top (μ := volume) (x := x₀) (r := r))

private lemma euclideanBall_eq_vec3Ball {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) :
    euclideanBall x₀ r = vec3Ball x₀ r := by
  ext x
  change (x ∈ euclideanBall x₀ r) ↔ vec3EuclideanNorm (x - x₀) < r
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
    (mem_euclideanBall_iff_vecEuclideanNorm_lt hr)

private lemma native_norm_le_sum_abs (v : Vec 3) :
    ‖v‖ ≤ ∑ i : Fin 3, |v i| := by
  rw [Pi.norm_def]
  have hsup : Finset.univ.sup (fun i : Fin 3 => ‖v i‖₊) ≤
      ∑ i : Fin 3, ‖v i‖₊ := by
    apply Finset.sup_le
    intro i hi
    exact Finset.single_le_sum (fun j _ => (show (0 : ℝ≥0) ≤ ‖v j‖₊ from bot_le)
      ) (Finset.mem_univ i)
  exact_mod_cast hsup

private lemma vec3EuclideanNorm_le_sqrt_three_native (v : Vec 3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    have hv : vec3EuclideanNorm v ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
      unfold vec3EuclideanNorm
      exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    rw [hv]
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      ∑ i : Fin 3, v i ^ 2 ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2

private lemma row_abs_sum_le_sqrt_three_row_norm (v : Vec3) :
    ∑ j : Fin 3, |v j| ≤ Real.sqrt 3 * vec3EuclideanNorm v := by
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin 3))
    (fun _ : Fin 3 => (1 : ℝ)) (fun j : Fin 3 => |v j|)
  calc
    ∑ j : Fin 3, |v j| = ∑ j : Fin 3, (1 : ℝ) * |v j| := by simp
    _ ≤ Real.sqrt (∑ j : Fin 3, (1 : ℝ) ^ 2) *
        Real.sqrt (∑ j : Fin 3, |v j| ^ 2) := hcs
    _ = Real.sqrt 3 * vec3EuclideanNorm v := by
      rw [show (∑ j : Fin 3, (1 : ℝ) ^ 2) = 3 by norm_num]
      congr 2
      change (∑ j : Fin 3, |v j| ^ 2) = ∑ j : Fin 3, v j ^ 2
      exact Finset.sum_congr rfl (fun j _ => sq_abs _)

private lemma vec3EuclideanNorm_le_sum_abs (v : Vec3) :
    vec3EuclideanNorm v ≤ ∑ i : Fin 3, |v i| := by
  rw [vec3EuclideanNorm]
  apply Real.sqrt_le_iff.mpr
  constructor
  · exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  · simp only [Fin.sum_univ_succ]
    simp only [Fin.sum_univ_zero, add_zero]
    change v 0 ^ 2 + (v 1 ^ 2 + v 2 ^ 2) ≤
      (|v 0| + (|v 1| + |v 2|)) ^ 2
    nlinarith only [sq_abs (v 0), sq_abs (v 1), sq_abs (v 2),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 1)),
      mul_nonneg (abs_nonneg (v 0)) (abs_nonneg (v 2)),
      mul_nonneg (abs_nonneg (v 1)) (abs_nonneg (v 2))]

private lemma vector_h1_sobolev_ball_integral_hWi_1 :
    ∀ {x₀ : Vec3} {r : ℝ} (u : Vec3 → Vec3) (hu : Fin 3 → H1Function (euclideanBall x₀ r)),
      let B : Set Vec3 := euclideanBall x₀ r;
      let μ : Measure Vec3 := Measure.restrict volume B;
      let W : Vec3 → Vec3 := fun y i => u y i - ⨍ (z : Vec3), u z i ∂μ;
      (∀ (i : Fin 3),
          eLpNorm (ε := ℝ) (fun y => W y i) 6 μ ≤
            sobolevPoincareL6Constant * eLpNorm ((hu i).grad (U := euclideanBall x₀ r)) 2 μ) →
        (∀ (i : Fin 3), MemLp ((hu i).grad (U := euclideanBall x₀ r)) 2 μ) →
          ∀ (i : Fin 3), MemLp (ε := ℝ) (fun y => W y i) 6 μ
    := by
  intro x₀ r u hu B μ W hscalar hgradmem i
  have hgradtop : eLpNorm ((hu i).grad) 2 μ < ∞ := by
    exact (hgradmem i).eLpNorm_lt_top
  exact lt_of_le_of_lt (hscalar i)
    (ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (by
      unfold sobolevPoincareL6Constant
      dsimp
      unfold localSobolevConstant
      apply ENNReal.mul_ne_top
      · finiteness
      · apply ENNReal.add_ne_top.mpr
        constructor
        · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
          apply ENNReal.add_ne_top.mpr
          constructor
          · norm_num
          · apply ENNReal.mul_ne_top
            · norm_num
            · simp [euclideanBallPoincareConstant]
        · apply ENNReal.mul_ne_top
          · norm_num
          · apply ENNReal.mul_ne_top
            · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
              norm_num
            · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
              simp [euclideanBallPoincareConstant])) hgradtop)

private lemma vector_h1_sobolev_ball_integral_hWbound_2 :
    ∀ {x₀ : Vec3} {r : ℝ} (u : Vec3 → Vec3),
      let B : Set Vec3 := euclideanBall x₀ r;
      let μ : Measure Vec3 := Measure.restrict volume B;
      let W : Vec3 → Vec3 := fun y i => u y i - ⨍ (z : Vec3), u z i ∂μ;
      (∀ (i : Fin 3), MemLp (ε := ℝ) (fun y => W y i) 6 μ) →
        AEStronglyMeasurable W μ →
          eLpNorm W 6 μ ≤ ∑ i : Fin 3, eLpNorm (ε := ℝ) (fun y => W y i) 6 μ
    := by
  intro x₀ r u B μ W hWi hWmeas
  calc
    eLpNorm W 6 μ ≤ eLpNorm (fun y => ∑ i : Fin 3, |W y i|) 6 μ := by
      apply eLpNorm_mono_ae_real hWmeas
      filter_upwards [] with y
      exact native_norm_le_sum_abs (W y)
    _ = eLpNorm (∑ i : Fin 3, (fun y => |W y i|)) 6 μ := by rfl
    _ ≤ ∑ i : Fin 3, eLpNorm (fun y => |W y i|) 6 μ := by
      simpa using (eLpNorm_sum_le (p := (6 : ℝ≥0∞))
        (s := (Finset.univ : Finset (Fin 3)))
        (f := fun i : Fin 3 => (fun y => |W y i|)) (by norm_num))
    _ = ∑ i : Fin 3, eLpNorm (fun y => W y i) 6 μ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← eLpNorm_norm (fun y => W y i) (hWi i).aestronglyMeasurable]
      rfl

private lemma vector_h1_sobolev_ball_integral_hrow_3 :
    ∀ {x₀ : Vec3} {r : ℝ} (D : Vec3 → Fin 3 → Vec3)
      (hu : Fin 3 → H1Function (euclideanBall x₀ r)),
      (∀ (i : Fin 3), (hu i).grad (U := euclideanBall x₀ r) = fun x => D x i) →
        let B : Set Vec3 := euclideanBall x₀ r;
        let μ : Measure Vec3 := Measure.restrict volume B;
        let H : Vec3 → ℝ := fun y => √(∑ i : Fin 3, ∑ j : Fin 3, D y i j ^ 2);
        (∀ (i : Fin 3), MemLp ((hu i).grad (U := euclideanBall x₀ r)) 2 μ) →
          ∀ (i : Fin 3),
            eLpNorm (ε := ℝ) (fun y => ∑ j : Fin 3, |D y i j|) 2 μ ≤
              ENNReal.ofReal √3 * eLpNorm H 2 μ
    := by
  intro x₀ r D hu hgrad B μ H hgradmem i
  have hrowm : AEStronglyMeasurable (fun y => ∑ j : Fin 3, |D y i j|) μ := by
    have hDij (j : Fin 3) : AEMeasurable (fun y => D y i j) μ := by
      simpa only [hgrad i] using ((hgradmem i).eval j).aemeasurable
    have hrowm' := Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun j _ => (hDij j).norm)
    have heq : (∑ j : Fin 3, (fun y => |D y i j|)) =
        (fun y => ∑ j : Fin 3, |D y i j|) := by
      funext y
      simp
    rw [← heq]
    simpa only [Real.norm_eq_abs] using hrowm'.aestronglyMeasurable
  apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hrowm
  filter_upwards [] with y
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun j _ => abs_nonneg _))]
  rw [Real.norm_of_nonneg (by dsimp [H]; positivity)]
  calc
    ∑ j : Fin 3, |D y i j| ≤ Real.sqrt 3 * vec3EuclideanNorm (D y i) :=
      row_abs_sum_le_sqrt_three_row_norm (D y i)
    _ ≤ Real.sqrt 3 * H y := by
      gcongr
      unfold H
      have hle : ∑ j : Fin 3, (D y i j) ^ (2 : ℕ) ≤
          ∑ k : Fin 3, ∑ j : Fin 3, (D y k j) ^ (2 : ℕ) := by
        exact Finset.single_le_sum (fun k _ =>
          Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Finset.mem_univ i)
      exact Real.sqrt_le_sqrt hle

private lemma vector_h1_sobolev_ball_integral_hH_4 :
    ∀ {x₀ : Vec3} {r : ℝ} (D : Vec3 → Fin 3 → Vec3)
      (hu : Fin 3 → H1Function (euclideanBall x₀ r)),
      (∀ (i : Fin 3), (hu i).grad (U := euclideanBall x₀ r) = fun x => D x i) →
        let B : Set Vec3 := euclideanBall x₀ r;
        let μ : Measure Vec3 := Measure.restrict volume B;
        let H : Vec3 → ℝ := fun y => √(∑ i : Fin 3, ∑ j : Fin 3, D y i j ^ 2);
        (∀ (i : Fin 3), MemLp ((hu i).grad (U := euclideanBall x₀ r)) 2 μ) →
          AEStronglyMeasurable H μ → MemLp H 2 μ
    := by
  intro x₀ r D hu hgrad B μ H hgradmem hHm
  have hrowmem (i : Fin 3) : MemLp (fun y => ∑ j : Fin 3, |D y i j|) 2 μ := by
    have hDij (j : Fin 3) : MemLp (fun y => D y i j) 2 μ := by
      simpa only [hgrad i] using (hgradmem i).eval j
    apply memLp_finsetSum
    intro j hj
    exact (hDij j).abs
  have htotal : MemLp (fun y => ∑ i : Fin 3, ∑ j : Fin 3, |D y i j|) 2 μ := by
    apply memLp_finsetSum
    intro i hi
    exact hrowmem i
  apply htotal.of_le hHm
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (by dsimp [H]; positivity),
    Real.norm_of_nonneg (Finset.sum_nonneg
      (fun i _ => Finset.sum_nonneg (fun j _ => abs_nonneg _)))]
  calc
    H y = vec3EuclideanNorm (fun i : Fin 3 => vec3EuclideanNorm (D y i)) := by
      unfold H vec3EuclideanNorm
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      exact (Real.sq_sqrt (Finset.sum_nonneg (fun j _ => sq_nonneg _))).symm
    _ ≤ ∑ i : Fin 3, vec3EuclideanNorm (D y i) :=
      by simpa only [abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using
        vec3EuclideanNorm_le_sum_abs (fun i : Fin 3 => vec3EuclideanNorm (D y i))
    _ ≤ ∑ i : Fin 3, ∑ j : Fin 3, |D y i j| := by
      apply Finset.sum_le_sum
      intro i hi
      exact vec3EuclideanNorm_le_sum_abs (D y i)

private lemma vector_h1_sobolev_ball_integral_hGbound_5 :
    ∀ {x₀ : Vec3} {r : ℝ} (u : Vec3 → Vec3) (D : Vec3 → Fin 3 → Vec3),
      let B : Set Vec3 := euclideanBall x₀ r;
      let μ : Measure Vec3 := Measure.restrict volume B;
      let W : Vec3 → Vec3 := fun y i => u y i - ⨍ (z : Vec3), u z i ∂μ;
      let H : Vec3 → ℝ := fun y => √(∑ i : Fin 3, ∑ j : Fin 3, D y i j ^ 2);
      ∑ i : Fin 3, eLpNorm (ε := ℝ) (fun y => ∑ j : Fin 3, |D y i j|) 2 μ ≤
          3 * ENNReal.ofReal √3 * eLpNorm H 2 μ →
        eLpNorm W 6 μ ≤
            sobolevPoincareL6Constant *
              ∑ i : Fin 3, eLpNorm (ε := ℝ) (fun y => ∑ j : Fin 3, |D y i j|) 2 μ →
          let G : Vec3 → ℝ := fun y => vec3EuclideanNorm (W y);
          AEStronglyMeasurable G μ → eLpNorm G 6 μ ≤ 9 * sobolevPoincareL6Constant * eLpNorm H 2 μ
    := by
  intro x₀ r u D B μ W H hrow_sum hWbound' G hGm
  have hmono : eLpNorm G 6 μ ≤
      ENNReal.ofReal (Real.sqrt 3) * eLpNorm W 6 μ := by
    apply eLpNorm_le_mul_eLpNorm_of_ae_le_mul hGm
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg (W y))]
    exact vec3EuclideanNorm_le_sqrt_three_native (W y)
  calc
    eLpNorm G 6 μ ≤ ENNReal.ofReal (Real.sqrt 3) * eLpNorm W 6 μ := hmono
    _ ≤ ENNReal.ofReal (Real.sqrt 3) *
        (sobolevPoincareL6Constant *
          (∑ i : Fin 3, eLpNorm (fun y => ∑ j : Fin 3, |D y i j|) 2 μ)) :=
      mul_le_mul_of_nonneg_left hWbound' (by positivity)
    _ ≤ ENNReal.ofReal (Real.sqrt 3) *
        (sobolevPoincareL6Constant *
          (3 * ENNReal.ofReal (Real.sqrt 3) * eLpNorm H 2 μ)) := by
      gcongr
    _ = 9 * sobolevPoincareL6Constant * eLpNorm H 2 μ := by
      have hsqrt : ENNReal.ofReal (Real.sqrt 3) * ENNReal.ofReal (Real.sqrt 3) =
          3 := by
        rw [← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ Real.sqrt 3)]
        rw [Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      rw [show ENNReal.ofReal (Real.sqrt 3) *
          (sobolevPoincareL6Constant *
            (3 * ENNReal.ofReal (Real.sqrt 3) * eLpNorm H 2 μ)) =
          3 * (ENNReal.ofReal (Real.sqrt 3) * ENNReal.ofReal (Real.sqrt 3)) *
            sobolevPoincareL6Constant * eLpNorm H 2 μ by ring, hsqrt]
      ring

private lemma vector_h1_sobolev_ball_integral_hS_top_6 :
    sobolevPoincareL6Constant ≠ ∞
    := by
  unfold sobolevPoincareL6Constant
  apply ENNReal.mul_ne_top
  · unfold localSobolevConstant
    finiteness
  · apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
      apply ENNReal.add_ne_top.mpr
      constructor
      · norm_num
      · apply ENNReal.mul_ne_top
        · norm_num
        · simp [euclideanBallPoincareConstant]
    · apply ENNReal.mul_ne_top
      · norm_num
      · apply ENNReal.mul_ne_top
        · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
          norm_num
        · apply ENNReal.rpow_ne_top_of_nonneg (by positivity)
          simp [euclideanBallPoincareConstant]

/-- The scalar weak Sobolev estimate aggregated over the three velocity components. -/
theorem vector_h1_sobolev_ball_integral
    {x₀ : Vec3} {r : ℝ} (hr : 0 < r) (u : Vec3 → Vec3)
    (D : Vec3 → Fin 3 → Vec3)
    (hu : ∀ _i : Fin 3, H1Function (euclideanBall x₀ r))
    (hcomp : ∀ i : Fin 3, (hu i).toFun = fun x => u x i)
    (hgrad : ∀ i : Fin 3, (hu i).grad = fun x => D x i) :
    MemLp (fun y : Vec3 => vec3EuclideanNorm (fun i : Fin 3 =>
      u y i - average (volume.restrict (vec3Ball x₀ r))
        (fun z => u z i))) 6 (volume.restrict (vec3Ball x₀ r)) ∧
    (∫ y in vec3Ball x₀ r,
        (vec3EuclideanNorm (fun i : Fin 3 =>
          u y i - average (volume.restrict (vec3Ball x₀ r))
            (fun z => u z i))) ^ (6 : ℕ)) ^ (1 / 6 : ℝ) ≤
      9 * sobolevPoincareL6Constant.toReal *
        (∫ y in vec3Ball x₀ r,
          ∑ i : Fin 3, ∑ j : Fin 3, (D y i j) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) := by
  let B : Set Vec3 := euclideanBall x₀ r
  let μ : Measure Vec3 := volume.restrict B
  let W : Vec3 → Vec3 := fun y i =>
    u y i - average μ (fun z => u z i)
  let H : Vec3 → ℝ := fun y =>
    Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3, (D y i j) ^ (2 : ℕ))
  have hB : B = vec3Ball x₀ r := euclideanBall_eq_vec3Ball hr
  have hμfin : IsFiniteMeasure μ := by
    change IsFiniteMeasure (volume.restrict B)
    rw [isFiniteMeasure_restrict]
    have hBtop : volume B < ∞ := by
      rw [hB, volume_vec3Ball_eq]
      exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
        ENNReal.ofReal_lt_top
    exact hBtop.ne
  have : IsFiniteMeasure μ := hμfin
  have hscalar (i : Fin 3) :
      eLpNorm (fun y => W y i) 6 μ ≤
        sobolevPoincareL6Constant * eLpNorm ((hu i).grad) 2 μ := by
    have h := sobolevPoincare_L6_ball_weak x₀ hr (hu i)
    simpa [lpNormOn, W, μ, B, hB, hcomp i, weakGradientLpNormOn] using h
  have hgradmem (i : Fin 3) : MemLp ((hu i).grad) 2 μ := by
    apply (memLp_pi_iff).2
    intro j
    simpa [μ, B] using (hu i).grad_memL2 j
  have hWi (i : Fin 3) := @vector_h1_sobolev_ball_integral_hWi_1 x₀ r u hu hscalar hgradmem i
  have hW : MemLp W 6 μ := (memLp_pi_iff).2 hWi
  have hWmeas : AEStronglyMeasurable W μ := hW.aestronglyMeasurable
  have hWbound := @vector_h1_sobolev_ball_integral_hWbound_2 x₀ r u hWi hWmeas
  have hrow (i : Fin 3) := @vector_h1_sobolev_ball_integral_hrow_3 x₀ r D hu hgrad hgradmem i
  have hHm : AEStronglyMeasurable H μ := by
    have hD (i j : Fin 3) : AEMeasurable (fun y => D y i j) μ := by
      simpa only [hgrad i] using (hgradmem i).eval j |>.aemeasurable
    have hs : AEMeasurable (fun y => ∑ i : Fin 3, ∑ j : Fin 3,
        (D y i j) ^ (2 : ℕ)) μ := by
      exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun i _ => by
        exact Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3)) (fun j _ => by
          have hpow : AEMeasurable (fun y => (D y i j) ^ (2 : ℕ)) μ := by
            convert (hD i j).pow_const (2 : ℝ) using 1
            funext y
            exact (Real.rpow_natCast _ _).symm
          exact hpow))
    exact (Real.continuous_sqrt.measurable.comp_aemeasurable hs).aestronglyMeasurable
  have hH := @vector_h1_sobolev_ball_integral_hH_4 x₀ r D hu hgrad hgradmem hHm
  have hrow_sum :
      ∑ i : Fin 3, eLpNorm (fun y => ∑ j : Fin 3, |D y i j|) 2 μ ≤
        3 * ENNReal.ofReal (Real.sqrt 3) * eLpNorm H 2 μ := by
    calc
      ∑ i : Fin 3, eLpNorm (fun y => ∑ j : Fin 3, |D y i j|) 2 μ ≤
          ∑ i : Fin 3, ENNReal.ofReal (Real.sqrt 3) * eLpNorm H 2 μ :=
        Finset.sum_le_sum (fun i _ => hrow i)
      _ = 3 * ENNReal.ofReal (Real.sqrt 3) * eLpNorm H 2 μ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hgradrow (i : Fin 3) :
      eLpNorm ((hu i).grad) 2 μ ≤
        eLpNorm (fun y => ∑ j : Fin 3, |D y i j|) 2 μ := by
    apply eLpNorm_mono_ae_real (hgradmem i).aestronglyMeasurable
    filter_upwards [] with y
    simpa only [hgrad i] using native_norm_le_sum_abs (D y i)
  have hWbound' : eLpNorm W 6 μ ≤
      sobolevPoincareL6Constant *
        (∑ i : Fin 3, eLpNorm (fun y => ∑ j : Fin 3, |D y i j|) 2 μ) := by
    calc
      eLpNorm W 6 μ ≤ ∑ i : Fin 3, eLpNorm (fun y => W y i) 6 μ := hWbound
      _ ≤ ∑ i : Fin 3, sobolevPoincareL6Constant * eLpNorm ((hu i).grad) 2 μ :=
        Finset.sum_le_sum (fun i _ => hscalar i)
      _ ≤ ∑ i : Fin 3, sobolevPoincareL6Constant *
          eLpNorm (fun y => ∑ j : Fin 3, |D y i j|) 2 μ := by
        exact Finset.sum_le_sum (fun i _ =>
          mul_le_mul_of_nonneg_left (hgradrow i) (by positivity))
      _ = sobolevPoincareL6Constant *
          (∑ i : Fin 3, eLpNorm (fun y => ∑ j : Fin 3, |D y i j|) 2 μ) := by
        rw [Finset.mul_sum]
  let G : Vec3 → ℝ := fun y => vec3EuclideanNorm (W y)
  have hGm : AEStronglyMeasurable G μ := by
    have hs' := Finset.aemeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => (hWi i).aemeasurable.pow_const 2)
    have hs : AEMeasurable (fun y => ∑ i : Fin 3, (W y i) ^ (2 : ℕ)) μ := by
      have heq : (∑ i : Fin 3, (fun y => (W y i) ^ (2 : ℕ))) =
          (fun y => ∑ i : Fin 3, (W y i) ^ (2 : ℕ)) := by
        funext y
        simp
      rw [← heq]
      exact hs'
    have hroot := Real.continuous_sqrt.measurable.comp_aemeasurable hs
    simpa [Function.comp_def, G, vec3EuclideanNorm] using hroot.aestronglyMeasurable
  have hG : MemLp G 6 μ := by
    apply hW.of_le_mul hGm
    on_goal 1 => filter_upwards [] with y
    on_goal 1 => rw [Real.norm_of_nonneg (vec3EuclideanNorm_nonneg (W y))]
    exact vec3EuclideanNorm_le_sqrt_three_native (W y)
  have hGbound := @vector_h1_sobolev_ball_integral_hGbound_5 x₀ r u D hrow_sum hWbound' hGm
  have hS_top := @vector_h1_sobolev_ball_integral_hS_top_6
  have hGformula := hG.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (6 : ℝ≥0∞) ≠ 0) (by norm_num : (6 : ℝ≥0∞) ≠ ∞)
  have hHformula := hH.eLpNorm_eq_integral_rpow_norm
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have hrighttop :
      9 * sobolevPoincareL6Constant * eLpNorm H 2 μ ≠ ∞ := by
    exact (ENNReal.mul_lt_top
      (ENNReal.mul_lt_top (by norm_num) (lt_top_iff_ne_top.mpr hS_top))
      hH.eLpNorm_lt_top).ne
  have hGnonneg : ∀ x, 0 ≤ G x := by
    intro x
    dsimp [G]
    exact vec3EuclideanNorm_nonneg _
  have hGint : (∫ x, |G x| ^ (6 : ℝ) ∂μ) =
      ∫ x, G x ^ (6 : ℕ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [abs_of_nonneg (hGnonneg x)]
    exact Real.rpow_natCast _ _
  have hGformula'' : eLpNorm G 6 μ =
      ENNReal.ofReal ((∫ x, |G x| ^ (6 : ℝ) ∂μ) ^ (1 / 6 : ℝ)) := by
    simpa [Real.norm_eq_abs] using hGformula
  rw [hGint] at hGformula''
  have hGformula' : eLpNorm G 6 μ =
      ENNReal.ofReal ((∫ x, G x ^ (6 : ℕ) ∂μ) ^ (1 / 6 : ℝ)) := hGformula''
  have hHnonneg : ∀ x, 0 ≤ H x := by
    intro x
    dsimp [H]
    positivity
  have hHint : (∫ x, |H x| ^ (2 : ℝ) ∂μ) =
      ∫ x, H x ^ (2 : ℕ) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with x
    rw [abs_of_nonneg (hHnonneg x)]
    exact Real.rpow_natCast _ _
  have hHformula'' : eLpNorm H 2 μ =
      ENNReal.ofReal ((∫ x, |H x| ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) := by
    simpa [Real.norm_eq_abs] using hHformula
  rw [hHint] at hHformula''
  have hHformula' : eLpNorm H 2 μ =
      ENNReal.ofReal ((∫ x, H x ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ)) := hHformula''
  have hto := ENNReal.toReal_mono hrighttop hGbound
  rw [hGformula', hHformula'] at hto
  have hGroot : 0 ≤ (∫ x, (G x) ^ (6 : ℕ) ∂μ) ^ (1 / 6 : ℝ) := by positivity
  have hHroot : 0 ≤ (∫ x, (H x) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by positivity
  rw [ENNReal.toReal_ofReal hGroot] at hto
  simp only [ENNReal.toReal_mul] at hto
  rw [ENNReal.toReal_ofReal hHroot] at hto
  have hmean :
      (∫ x, (G x) ^ (6 : ℕ) ∂μ) ^ (1 / 6 : ℝ) ≤
        9 * sobolevPoincareL6Constant.toReal *
          (∫ x, (H x) ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
    simpa [G, H, Real.rpow_natCast] using hto
  have hHsq : (fun x => H x ^ (2 : ℕ)) =
      (fun x => ∑ i : Fin 3, ∑ j : Fin 3, (D x i j) ^ (2 : ℕ)) := by
    funext x
    dsimp [H]
    rw [Real.sq_sqrt]
    exact Finset.sum_nonneg (fun i _ =>
      Finset.sum_nonneg (fun j _ => sq_nonneg _))
  rw [hHsq] at hmean
  have hmem : MemLp (fun y : Vec3 => vec3EuclideanNorm (fun i : Fin 3 =>
      u y i - average (volume.restrict (vec3Ball x₀ r))
        (fun z => u z i))) 6 (volume.restrict (vec3Ball x₀ r)) := by
    simpa [G, W, μ, B, hB] using hG
  exact ⟨hmem, by simpa [G, W, μ, B, hB] using hmean⟩

private lemma average_norm_mul_volume_half_le
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) (u : H1Function (euclideanBall x₀ r)) :
    ENNReal.ofReal (|average (volume.restrict (euclideanBall x₀ r)) u.toFun|) *
        volume (euclideanBall x₀ r) ^ (1 / 2 : ℝ) ≤
      eLpNorm u.toFun 2 (volume.restrict (euclideanBall x₀ r)) := by
  let μ : Measure (Vec 3) := volume.restrict (euclideanBall x₀ r)
  have hμpos : 0 < μ Set.univ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      euclideanBall_volume_pos hr
  have hμtop : μ Set.univ < ∞ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      euclideanBall_volume_lt_top (x₀ := x₀) (r := r) hr
  have : IsFiniteMeasure μ := ⟨hμtop⟩
  have hu2 : MemLp u.toFun 2 μ := by
    simpa [μ, volumeOn] using u.memL2
  have hconst : MemLp (fun _ : Vec 3 => (1 : ℝ)) 2 μ := memLp_const 1
  have hu2r : MemLp u.toFun (ENNReal.ofReal (2 : ℝ)) μ := by simpa using hu2
  have hconstr : MemLp (fun _ : Vec 3 => (1 : ℝ)) (ENNReal.ofReal (2 : ℝ)) μ := by
    simpa using hconst
  have h22 : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have hholder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) h22 hu2r hconstr
  have hnorm_integral :
      ENNReal.ofReal (∫ x, |u.toFun x| ∂μ) ≤
        eLpNorm u.toFun 2 μ * μ Set.univ ^ (1 / 2 : ℝ) := by
    have hholder' := ENNReal.ofReal_le_ofReal hholder
    rw [ENNReal.ofReal_mul (by positivity)] at hholder'
    have hholder'' :
        ENNReal.ofReal (∫ x, |u.toFun x| ∂μ) ≤
          ENNReal.ofReal ((∫ x, ‖u.toFun x‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) *
            ENNReal.ofReal ((∫ x, ‖(1 : ℝ)‖ ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) := by
      simpa only [Real.norm_eq_abs, norm_one, mul_one] using hholder'
    have hu2norm := hu2.eLpNorm_eq_integral_rpow_norm
      (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
    have hu2norm' :
        eLpNorm u.toFun 2 μ =
          ENNReal.ofReal ((∫ x, u.toFun x ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ)) := by
      simpa [Real.rpow_natCast, ENNReal.toReal_ofNat, Real.norm_eq_abs] using hu2norm
    norm_num [Real.rpow_natCast] at hholder''
    rw [← hu2norm'] at hholder''
    calc
      ENNReal.ofReal (∫ x, |u.toFun x| ∂μ) ≤
          eLpNorm u.toFun 2 μ * ENNReal.ofReal ((μ Set.univ).toReal ^ (1 / 2 : ℝ)) :=
        hholder''
      _ = eLpNorm u.toFun 2 μ * μ Set.univ ^ (1 / 2 : ℝ) := by
        have hpow : ENNReal.ofReal ((μ Set.univ).toReal ^ (1 / 2 : ℝ)) =
          ENNReal.ofReal (μ Set.univ).toReal ^ (1 / 2 : ℝ) :=
          (ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity)).symm
        rw [hpow]
        rw [ENNReal.ofReal_toReal hμtop.ne]
  have havg := MeasureTheory.average_eq μ u.toFun
  have hintnorm :
      |∫ x, u.toFun x ∂μ| ≤ ∫ x, |u.toFun x| ∂μ := by
    simpa [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm u.toFun
  have hfinal : ENNReal.ofReal |average μ u.toFun| * μ Set.univ ^ (1 / 2 : ℝ) ≤
      eLpNorm u.toFun 2 μ := by
    rw [havg]
    rw [smul_eq_mul]
    have hμreal : 0 < μ.real Set.univ := ENNReal.toReal_pos hμpos.ne' hμtop.ne
    have hreal :
        |(μ.real Set.univ)⁻¹ * ∫ x, u.toFun x ∂μ| ≤
          (μ.real Set.univ)⁻¹ * ∫ x, |u.toFun x| ∂μ := by
      calc
        |(μ.real Set.univ)⁻¹ * ∫ x, u.toFun x ∂μ| =
            |(μ.real Set.univ)⁻¹| * |∫ x, u.toFun x ∂μ| := abs_mul _ _
        _ = (μ.real Set.univ)⁻¹ * |∫ x, u.toFun x ∂μ| := by
          rw [abs_of_pos (inv_pos.mpr hμreal)]
        _ ≤ (μ.real Set.univ)⁻¹ * ∫ x, |u.toFun x| ∂μ :=
          mul_le_mul_of_nonneg_left hintnorm (le_of_lt (inv_pos.mpr hμreal))
    have hof := ENNReal.ofReal_le_ofReal hreal
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_inv_of_pos hμreal] at hof
    have hμof : ENNReal.ofReal (μ.real Set.univ) = μ Set.univ :=
      ENNReal.ofReal_toReal hμtop.ne
    rw [hμof] at hof
    calc
      ENNReal.ofReal |(μ.real Set.univ)⁻¹ * ∫ x, u.toFun x ∂μ| *
          μ Set.univ ^ (1 / 2 : ℝ) ≤
        (μ Set.univ)⁻¹ * ENNReal.ofReal (∫ x, |u.toFun x| ∂μ) *
          μ Set.univ ^ (1 / 2 : ℝ) := by
            exact mul_le_mul_of_nonneg_right hof (by positivity)
      _ ≤ (μ Set.univ)⁻¹ *
          (eLpNorm u.toFun 2 μ * μ Set.univ ^ (1 / 2 : ℝ)) *
            μ Set.univ ^ (1 / 2 : ℝ) := by
            have hb : 0 ≤ μ Set.univ ^ (1 / 2 : ℝ) := by positivity
            have hinvnonneg : 0 ≤ (μ Set.univ)⁻¹ := by positivity
            have hinner :
                ENNReal.ofReal (∫ x, |u.toFun x| ∂μ) *
                    μ Set.univ ^ (1 / 2 : ℝ) ≤
                  (eLpNorm u.toFun 2 μ * μ Set.univ ^ (1 / 2 : ℝ)) *
                    μ Set.univ ^ (1 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right hnorm_integral hb
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hinner hinvnonneg
      _ = eLpNorm u.toFun 2 μ := by
        have hinv : (μ Set.univ)⁻¹ = (μ Set.univ) ^ (-(1 : ℝ)) := by
          rw [ENNReal.rpow_neg, ENNReal.rpow_one]
        have hhalf :
            μ Set.univ ^ (1 / 2 : ℝ) * μ Set.univ ^ (1 / 2 : ℝ) =
              μ Set.univ ^ (1 : ℝ) := by
          rw [← ENNReal.rpow_add_of_nonneg (x := μ Set.univ)
            (y := (1 / 2 : ℝ)) (z := (1 / 2 : ℝ)) (by positivity) (by positivity)]
          norm_num
        have hzero :
            (μ Set.univ)⁻¹ * μ Set.univ ^ (1 / 2 : ℝ) *
                μ Set.univ ^ (1 / 2 : ℝ) = 1 := by
          calc
            (μ Set.univ)⁻¹ * μ Set.univ ^ (1 / 2 : ℝ) *
                μ Set.univ ^ (1 / 2 : ℝ) =
              (μ Set.univ)⁻¹ *
                (μ Set.univ ^ (1 / 2 : ℝ) * μ Set.univ ^ (1 / 2 : ℝ)) := by ac_rfl
            _ = (μ Set.univ)⁻¹ * μ Set.univ ^ (1 : ℝ) := by rw [hhalf]
            _ = μ Set.univ ^ (-(1 : ℝ)) * μ Set.univ ^ (1 : ℝ) := by rw [hinv]
            _ = μ Set.univ ^ ((-(1 : ℝ)) + 1) := by
              rw [ENNReal.rpow_add (y := (-(1 : ℝ))) (z := (1 : ℝ))
                hμpos.ne' hμtop.ne]
            _ = 1 := by norm_num
        calc
          (μ Set.univ)⁻¹ *
              (eLpNorm u.toFun 2 μ * μ Set.univ ^ (1 / 2 : ℝ)) *
                μ Set.univ ^ (1 / 2 : ℝ) =
              eLpNorm u.toFun 2 μ *
                ((μ Set.univ)⁻¹ * μ Set.univ ^ (1 / 2 : ℝ) *
                  μ Set.univ ^ (1 / 2 : ℝ)) := by ac_rfl
          _ = eLpNorm u.toFun 2 μ := by rw [hzero, mul_one]
  simpa [μ] using hfinal

theorem h1SobolevBall_of_sobolevPoincare
    {x₀ : Vec 3} {r : ℝ} (hr : 0 < r) (u : H1Function (euclideanBall x₀ r)) :
    lpNormOn 6 (euclideanBall x₀ r) u.toFun ≤
      (2 * sobolevPoincareL6Constant + 2 * sobolevPoincareBallFullConstant) *
        (weakGradientLpNormOn 2 (euclideanBall x₀ r) u.grad +
          (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) u.toFun) := by
  let μ : Measure (Vec 3) := volume.restrict (euclideanBall x₀ r)
  let c : ℝ := average μ u.toFun
  let K : ℝ≥0∞ := sobolevPoincareBallFullConstant
  have hμpos : 0 < μ Set.univ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      euclideanBall_volume_pos hr
  have hμtop : μ Set.univ < ∞ := by
    simpa [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter] using
      euclideanBall_volume_lt_top hr
  have : IsFiniteMeasure μ := ⟨hμtop⟩
  have hweak := sobolevPoincare_L6_ball_weak x₀ hr u
  have hmean : ENNReal.ofReal |c| * μ Set.univ ^ (1 / 2 : ℝ) ≤
      eLpNorm u.toFun 2 μ := by
      simpa [c, μ] using average_norm_mul_volume_half_le hr u
  have hconst : MemLp (fun _ : Vec 3 => c) 6 μ := memLp_const c
  have hconstnorm :
    eLpNorm (fun _ : Vec 3 => c) 6 μ =
        ENNReal.ofReal |c| * μ Set.univ ^ (1 / 6 : ℝ) := by
    have hc : ‖c‖ₑ = ENNReal.ofReal |c| := by
      rw [← ofReal_norm]
      simp [Real.norm_eq_abs]
    calc
      eLpNorm (fun _ : Vec 3 => c) 6 μ = ‖c‖ₑ * μ Set.univ ^ (1 / 6 : ℝ) :=
        eLpNorm_const' c (by norm_num) (by norm_num)
      _ = ENNReal.ofReal |c| * μ Set.univ ^ (1 / 6 : ℝ) := by rw [hc]
  have hvol : μ Set.univ = ENNReal.ofReal r ^ (3 : ℝ) *
      ENNReal.ofReal (Real.pi * 4 / 3) := by
    simp only [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [euclideanBall_eq_vec3Ball hr, volume_vec3Ball_eq]
    norm_num
  have hscale : μ Set.univ ^ (-(1 / 3 : ℝ)) =
      K * (ENNReal.ofReal r)⁻¹ := by
    rw [hvol, ENNReal.mul_rpow_of_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top]
    dsimp [K]
    have hrpow : (ENNReal.ofReal r ^ (3 : ℝ)) ^ (-(1 / 3 : ℝ)) =
        (ENNReal.ofReal r)⁻¹ := by
      calc
        (ENNReal.ofReal r ^ (3 : ℝ)) ^ (-(1 / 3 : ℝ)) =
            (ENNReal.ofReal r) ^ ((3 : ℝ) * (-(1 / 3 : ℝ))) := by
              exact (ENNReal.rpow_mul (ENNReal.ofReal r) (3 : ℝ)
                (-(1 / 3 : ℝ))).symm
        _ = (ENNReal.ofReal r) ^ (-(1 : ℝ)) := by norm_num
        _ = (ENNReal.ofReal r)⁻¹ := by
              rw [ENNReal.rpow_neg, ENNReal.rpow_one]
    calc
      (ENNReal.ofReal r ^ (3 : ℝ)) ^ (-(1 / 3 : ℝ)) *
          ENNReal.ofReal (Real.pi * 4 / 3) ^ (-(1 / 3 : ℝ)) =
          (ENNReal.ofReal r)⁻¹ *
            ENNReal.ofReal (Real.pi * 4 / 3) ^ (-(1 / 3 : ℝ)) := by
              rw [hrpow]
      _ = K * (ENNReal.ofReal r)⁻¹ := by
        dsimp [K, sobolevPoincareBallFullConstant]
        ac_rfl
  have hmean6 :
      ENNReal.ofReal |c| * μ Set.univ ^ (1 / 6 : ℝ) ≤
        K * (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) u.toFun := by
    have hpow : μ Set.univ ^ (1 / 2 : ℝ) * μ Set.univ ^ (-(1 / 3 : ℝ)) =
        μ Set.univ ^ (1 / 6 : ℝ) := by
      calc
        μ Set.univ ^ (1 / 2 : ℝ) * μ Set.univ ^ (-(1 / 3 : ℝ)) =
            μ Set.univ ^ ((1 / 2 : ℝ) + (-(1 / 3 : ℝ))) := by
              rw [ENNReal.rpow_add (y := (1 / 2 : ℝ)) (z := (-(1 / 3 : ℝ)))
                hμpos.ne' hμtop.ne]
        _ = μ Set.univ ^ (1 / 6 : ℝ) := by norm_num
    calc
      ENNReal.ofReal |c| * μ Set.univ ^ (1 / 6 : ℝ) =
          ENNReal.ofReal |c| *
            (μ Set.univ ^ (1 / 2 : ℝ) * μ Set.univ ^ (-(1 / 3 : ℝ))) := by
              rw [hpow]
      _ = (ENNReal.ofReal |c| * μ Set.univ ^ (1 / 2 : ℝ)) *
            μ Set.univ ^ (-(1 / 3 : ℝ)) := by ac_rfl
      _ ≤ eLpNorm u.toFun 2 μ * μ Set.univ ^ (-(1 / 3 : ℝ)) :=
        mul_le_mul_of_nonneg_right hmean (by positivity)
      _ = K * (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) u.toFun := by
        rw [hscale]
        simp [lpNormOn, μ]
        ac_rfl
  have hsum :
      lpNormOn 6 (euclideanBall x₀ r) u.toFun ≤
        sobolevPoincareL6Constant * weakGradientLpNormOn 2
            (euclideanBall x₀ r) u.grad +
          K * (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) u.toFun := by
    have hdecomp : u.toFun = (fun _ : Vec 3 => c) +
        (fun x => u.toFun x - c) := by
      funext x
      change u.toFun x = c + (u.toFun x - c)
      ring
    calc
      lpNormOn 6 (euclideanBall x₀ r) u.toFun =
          eLpNorm ((fun _ : Vec 3 => c) + (fun x => u.toFun x - c)) 6 μ := by
            rw [← hdecomp]
            rfl
      _ ≤
          eLpNorm (fun _ : Vec 3 => c) 6 μ +
            eLpNorm (fun x => u.toFun x - c) 6 μ :=
        eLpNorm_add_le (p := (6 : ℝ≥0∞)) (by norm_num)
      _ ≤ K * (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) u.toFun +
          sobolevPoincareL6Constant * weakGradientLpNormOn 2
            (euclideanBall x₀ r) u.grad := by
        rw [hconstnorm]
        have hw : eLpNorm (fun x => u.toFun x - c) 6 μ ≤
            sobolevPoincareL6Constant * weakGradientLpNormOn 2
              (euclideanBall x₀ r) u.grad := by
          simpa [c, μ, lpNormOn, weakGradientLpNormOn] using hweak
        exact add_le_add hmean6 hw
      _ = sobolevPoincareL6Constant * weakGradientLpNormOn 2
            (euclideanBall x₀ r) u.grad +
          K * (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) u.toFun := by
        ac_rfl
  calc
    lpNormOn 6 (euclideanBall x₀ r) u.toFun ≤
        sobolevPoincareL6Constant * weakGradientLpNormOn 2
            (euclideanBall x₀ r) u.grad +
          K * (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) u.toFun := hsum
    _ ≤ (2 * sobolevPoincareL6Constant + 2 * K) *
        (weakGradientLpNormOn 2 (euclideanBall x₀ r) u.grad +
          (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) u.toFun) := by
      have hG : 0 ≤ weakGradientLpNormOn 2 (euclideanBall x₀ r) u.grad := by positivity
      have hL : 0 ≤ (ENNReal.ofReal r)⁻¹ *
          lpNormOn 2 (euclideanBall x₀ r) u.toFun := by positivity
      let G := weakGradientLpNormOn 2 (euclideanBall x₀ r) u.grad
      let B := (ENNReal.ofReal r)⁻¹ * lpNormOn 2 (euclideanBall x₀ r) u.toFun
      have hCG : sobolevPoincareL6Constant * G ≤
          (2 * sobolevPoincareL6Constant + 2 * K) * G := by
        apply mul_le_mul_of_nonneg_right _ hG
        calc
          sobolevPoincareL6Constant ≤ 2 * sobolevPoincareL6Constant := by
            have h := (le_add_self : sobolevPoincareL6Constant ≤
              sobolevPoincareL6Constant + sobolevPoincareL6Constant)
            rw [two_mul]
            exact h
          _ ≤ 2 * sobolevPoincareL6Constant + 2 * K := le_add_of_nonneg_right (by positivity)
      have hKB : K * B ≤
          (2 * sobolevPoincareL6Constant + 2 * K) * B := by
        apply mul_le_mul_of_nonneg_right _ hL
        calc
          K ≤ 2 * K := by
            have h := (le_add_self : K ≤ K + K)
            rw [two_mul]
            exact h
          _ ≤ 2 * sobolevPoincareL6Constant + 2 * K :=
            le_add_of_nonneg_left (by positivity)
      have hadd := add_le_add hCG hKB
      have htarget :
          sobolevPoincareL6Constant * G + K * B ≤
            (2 * sobolevPoincareL6Constant + 2 * K) * (G + B) := by
        calc
          sobolevPoincareL6Constant * G + K * B ≤
              (2 * sobolevPoincareL6Constant + 2 * K) * G +
                (2 * sobolevPoincareL6Constant + 2 * K) * B := hadd
          _ = (2 * sobolevPoincareL6Constant + 2 * K) * (G + B) := by
            rw [mul_add]
      simpa [G, B, mul_assoc] using htarget

end CKN
