/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/
module


public import LeanPool.CoarseGraining.Homogenization.Book.Ch03.Theorems.CoarseCaccioppoliRHS.Prefactors

/-! # Zero Trace Value -/

@[expose] public section

namespace Homogenization
namespace Book
namespace Ch03

/-!
# Zero-Trace Value Estimates for Coarse Caccioppoli with RHS

This file is split mechanically out of `CoarseCaccioppoliRHS.lean`.

## Audit tag

Claim: relate normalized open-cube `L²` squares for the zero-trace corrector
to cube norms and the public forced Caccioppoli value terms.

Downstream target: `CoarseCaccioppoliRHS/PublicRHSScalar.lean`.  This file
should remain value/norm comparison infrastructure.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

/-- Normalized `L²` squares are nonnegative. -/
theorem normalizedL2SqOnSet_nonneg
    {d : ℕ} (V : Set (Vec d)) (u : Vec d → ℝ) :
    MeasurableSet V → 0 ≤ normalizedL2SqOnSet V u := by
  intro hV
  unfold normalizedL2SqOnSet normalizedSetAverage
  exact volumeAverage_nonneg_of_nonneg_on hV
    (fun x _hx => sq_nonneg (u x))

/-- On a parent open cube, the normalized `L²` square is the square of the
normalized cube `L²` norm. -/
theorem normalizedL2SqOnSet_openCubeSet_eq_cubeLpNorm_two_sq
    {d : ℕ} (Q : TriadicCube d) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    normalizedL2SqOnSet (openCubeSet Q) u =
      (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
  have hsq_integral :
      ∫ y in openCubeSet Q, u y ^ (2 : ℕ) ∂MeasureTheory.volume =
        cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
    have hmul :=
      setIntegral_openCubeSet_sq_eq_cubeVolume_mul_cubeLpNorm_two_rpow
        Q u hu
    calc
      ∫ y in openCubeSet Q, u y ^ (2 : ℕ) ∂MeasureTheory.volume =
          ∫ y in openCubeSet Q, u y * u y ∂MeasureTheory.volume := by
        apply MeasureTheory.setIntegral_congr_fun (measurableSet_openCubeSet Q)
        intro y hy
        ring
      _ =
          cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℝ) := hmul
      _ =
          cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
        rw [Real.rpow_two]
  have hvol_ne : cubeVolume Q ≠ 0 := (cubeVolume_pos Q).ne'
  unfold normalizedL2SqOnSet normalizedSetAverage volumeAverage
  calc
    (MeasureTheory.volume (openCubeSet Q)).toReal⁻¹ *
        ∫ y in openCubeSet Q, u y ^ (2 : ℕ) ∂MeasureTheory.volume =
      (cubeVolume Q)⁻¹ *
        ∫ y in openCubeSet Q, u y ^ (2 : ℕ) ∂MeasureTheory.volume := by
        simp
    _ =
      (cubeVolume Q)⁻¹ *
        (cubeVolume Q * (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ)) := by
        rw [hsq_integral]
    _ = (cubeLpNorm Q (2 : ℝ≥0∞) u) ^ (2 : ℕ) := by
        rw [← mul_assoc, inv_mul_cancel₀ hvol_ne, one_mul]

/-- Depth zero of the scalar positive Besov seminorm of a fluctuation is the
top-scale normalized `L²` norm. -/
theorem cubeBesovDepthSeminorm_two_depth_zero_fluctuation_eq
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (cubeFluctuation Q u) 0 =
      cubeBesovScaleWeight s Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) := by
  have hfluct : cubeFluctuation Q (cubeFluctuation Q u) = cubeFluctuation Q u :=
    cubeFluctuation_cubeFluctuation_of_memLp_two Q Q hu
  have hnonneg : 0 ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) :=
    cubeLpNorm_nonneg Q (2 : ℝ≥0∞) (cubeFluctuation Q u)
  have hsq :
      (cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) =
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) := by
    simpa using sq_rpow_half_eq_of_nonneg hnonneg
  calc
    cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (cubeFluctuation Q u) 0
        =
          cubeBesovScaleWeight s Q *
            ((cubeLpNorm Q (2 : ℝ≥0∞)
              (cubeFluctuation Q (cubeFluctuation Q u))) ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) := by
            simp [cubeBesovDepthSeminorm, cubeBesovDepthAverage, descendantsAverage,
              cubeBesovOscillation]
    _ =
          cubeBesovScaleWeight s Q *
            ((cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)) ^ (2 : ℕ)) ^ ((2 : ℝ)⁻¹) := by
            rw [hfluct]
    _ = cubeBesovScaleWeight s Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) := by
            rw [hsq]

/-- Any positive-Besov finite top norm contains the depth-zero fluctuation
`L²` contribution. -/
theorem cubeBesovScaleWeight_mul_cubeLpNorm_fluctuation_le_partialNormTop
    {d : ℕ} (Q : TriadicCube d) (s : ℝ) (M : ℕ) (u : Vec d → ℝ)
    (hu : MeasureTheory.MemLp u (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeBesovScaleWeight s Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u) ≤
      cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) := by
  calc
    cubeBesovScaleWeight s Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q u)
        = cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (cubeFluctuation Q u) 0 := by
          rw [cubeBesovDepthSeminorm_two_depth_zero_fluctuation_eq Q s u hu]
    _ ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M (cubeFluctuation Q u) := by
          calc
            cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞) (cubeFluctuation Q u) 0
                ≤ cubeBesovPartialSeminormTop Q s (2 : ℝ≥0∞) M
                    (cubeFluctuation Q u) := by
                  unfold cubeBesovPartialSeminormTop
                  exact Finset.le_sup'
                    (s := Finset.range (M + 1))
                    (f := fun k =>
                      cubeBesovDepthSeminorm Q s (2 : ℝ≥0∞)
                        (cubeFluctuation Q u) k)
                    (by simp : 0 ∈ Finset.range (M + 1))
            _ ≤ cubeBesovPartialNormTop Q s (2 : ℝ≥0∞) M
                    (cubeFluctuation Q u) := by
                  unfold cubeBesovPartialNormTop
                  exact le_add_of_nonneg_right
                    (mul_nonneg (cubeBesovScaleWeight_nonneg s Q) (norm_nonneg _))

/-- The fluctuation half of the zero-trace value bridge: the top-scale
fluctuation `L²` norm is controlled by the public `q = 2` negative-Besov norm
of the gradient, with the geometric exponent-gap loss left explicit. -/
theorem cubeBesovScaleWeight_one_mul_cubeLpNorm_fluctuation_le_grad_negativeBesovTwo
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {t : ℝ}
    (u : H1Function (openCubeSet Q))
    (ht : 0 < t) (ht_lt : t < 1 / 2) :
    cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun x => u x)) ≤
      ((Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((d : ℝ) *
            Real.sqrt
              ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹))) *
        cubeBesovNegativeVectorSeminormTwo Q (2 * t) (fun x => u.grad x) := by
  let s0 : ℝ := (1 / 2 : ℝ) - t
  let a : ℝ := 1 - s0
  let N : ℝ := cubeBesovNegativeVectorSeminormTwo Q (2 * t) (fun x => u.grad x)
  let G : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * s0))⁻¹)
  let C : ℝ := Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)
  have hs0_pos : 0 < s0 := by
    dsimp [s0]
    linarith
  have hs0_lt_one : s0 < 1 := by
    dsimp [s0]
    linarith
  have ha_gap : 0 < a - 2 * t := by
    dsimp [a, s0]
    linarith
  have ha_eq : a = (1 / 2 : ℝ) + t := by
    dsimp [a, s0]
    ring
  have hgap_eq : a - 2 * t = s0 := by
    dsimp [a, s0]
    ring
  have hC_nonneg : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (Ch01.Legacy.fullVectorPoincareConstant_nonneg Q)
      (Real.rpow_nonneg (by norm_num : 0 ≤ (3 : ℝ)) _)
  have hdepth :
      cubeBesovScaleWeight s0 Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun x => u x)) ≤
        cubeBesovPartialNormTop Q s0 (2 : ℝ≥0∞) 1
          (cubeFluctuation Q (fun x => u x)) :=
    cubeBesovScaleWeight_mul_cubeLpNorm_fluctuation_le_partialNormTop
      Q s0 1 (fun x => u x) u.memL2_normalizedCubeMeasure
  have hpoinc :
      cubeBesovPartialNormTop Q s0 (2 : ℝ≥0∞) 1
          (cubeFluctuation Q (fun x => u x)) ≤
        C *
          ∑ i : Fin d,
            cubeBesovCircNorm Q a (2 : ℝ≥0∞) (1 : ℝ≥0∞)
              (fun x => u.grad x i) := by
    have hp :=
      Ch01.Legacy.h1_fluctuation_partialNormTop_two_le_sum_grad_circNorm
        (Q := Q) (s := s0) (M := 1) u hs0_pos hs0_lt_one
    simpa [C, a] using hp
  have hBdd :
      BddAbove (Set.range fun M : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q (2 * t) M (fun x => u.grad x)) :=
    by
      have hgrad :
          MeasureTheory.MemLp (fun x => u.grad x) (2 : ℝ≥0∞)
            (normalizedCubeMeasure Q) := by
        simpa using
          (MeasureTheory.MemLp.of_eval
            (fun i : Fin d => u.grad_memL2_normalizedCubeMeasure i))
      exact cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp
        Q (by nlinarith) (fun x => u.grad x) hgrad
  have hcirc :
      ∀ i : Fin d,
        cubeBesovCircNorm Q a (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i) ≤
          cubeBesovScaleWeight (-a) Q * (G * N) := by
    intro i
    have hraw :=
      cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_gap_geometric_of_bddAbove
        (Q := Q) (a := a) (b := 2 * t) ha_gap
        (u := fun x => u.grad x) i hBdd
    simpa [G, N, hgap_eq] using hraw
  have hsum :
      (∑ i : Fin d,
          cubeBesovCircNorm Q a (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i)) ≤
        (d : ℝ) * (cubeBesovScaleWeight (-a) Q * (G * N)) := by
    calc
      (∑ i : Fin d,
          cubeBesovCircNorm Q a (2 : ℝ≥0∞) (1 : ℝ≥0∞)
            (fun x => u.grad x i))
          ≤ ∑ _i : Fin d, cubeBesovScaleWeight (-a) Q * (G * N) := by
            exact Finset.sum_le_sum fun i _ => hcirc i
      _ = (d : ℝ) * (cubeBesovScaleWeight (-a) Q * (G * N)) := by
            simp
  have hfinite :
      cubeBesovScaleWeight s0 Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun x => u x)) ≤
        C * ((d : ℝ) * (cubeBesovScaleWeight (-a) Q * (G * N))) := by
    exact hdepth.trans (hpoinc.trans (mul_le_mul_of_nonneg_left hsum hC_nonneg))
  have hscale_nonneg : 0 ≤ cubeBesovScaleWeight a Q :=
    cubeBesovScaleWeight_nonneg a Q
  calc
    cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun x => u x))
        =
      cubeBesovScaleWeight a Q *
        (cubeBesovScaleWeight s0 Q *
          cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q (fun x => u x))) := by
        rw [← mul_assoc, cubeBesovScaleWeight_mul_eq_scaleWeight_add]
        congr 1
        dsimp [a, s0]
        ring_nf
    _ ≤ cubeBesovScaleWeight a Q *
        (C * ((d : ℝ) * (cubeBesovScaleWeight (-a) Q * (G * N)))) := by
        exact mul_le_mul_of_nonneg_left hfinite hscale_nonneg
    _ =
      (C * ((d : ℝ) * G)) * N := by
        have hcancel :
            cubeBesovScaleWeight a Q * cubeBesovScaleWeight (-a) Q = 1 := by
          rw [cubeBesovScaleWeight_mul_eq_scaleWeight_add]
          simp [cubeBesovScaleWeight]
        calc
          cubeBesovScaleWeight a Q *
              (C * ((d : ℝ) * (cubeBesovScaleWeight (-a) Q * (G * N))))
              =
            C * ((d : ℝ) *
              ((cubeBesovScaleWeight a Q * cubeBesovScaleWeight (-a) Q) * (G * N))) := by
              ring
          _ = C * ((d : ℝ) * (1 * (G * N))) := by
              rw [hcancel]
          _ = (C * ((d : ℝ) * G)) * N := by
              ring
    _ =
      ((Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          ((d : ℝ) *
            Real.sqrt
              ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹))) *
        cubeBesovNegativeVectorSeminormTwo Q (2 * t) (fun x => u.grad x) := by
        dsimp [C, G, N, s0]

/-- The scalar average of a zero-trace function is controlled by the public
negative-Besov norm of its gradient.  The proof uses the zero-trace identity
`∫ u = -∫ ∂ᵢu (xᵢ - centerᵢ)` and tests the gradient component against the
centered coordinate. -/
theorem cubeBesovScaleWeight_one_mul_abs_cubeAverage_h10_le_grad_negativeBesovTwo
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {t : ℝ}
    (u : H10Function (cubeSet Q))
    (ht : 0 < t) (ht_lt : t < 1 / 2) :
    cubeBesovScaleWeight (1 : ℝ) Q *
        ‖cubeAverage Q (fun x => u.toH1Function.toFun x)‖ ≤
      ((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (1 - 2 * t)))⁻¹)) *
        cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (fun x => u.toH1Function.grad x) := by
  let i0 : Fin d := 0
  let φ : Vec d → ℝ := fun x => x i0 - cubeCenter Q i0
  let G : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (1 - 2 * t)))⁻¹)
  let N : ℝ :=
    cubeBesovNegativeVectorSeminormTwo Q (2 * t)
      (fun x => u.toH1Function.grad x)
  have hφ_cont : Continuous φ := by
    dsimp [φ]
    fun_prop
  have hφ_smooth : ContDiff ℝ (⊤ : ℕ∞) φ := by
    dsimp [φ]
    fun_prop
  have hradius_le_scale : cubeRadius Q ≤ cubeScaleFactor Q := by
    have hEq := cubeScaleFactor_eq_two_mul_cubeRadius Q
    have hr := cubeRadius_nonneg Q
    nlinarith
  have hφ_bound : ∀ x ∈ cubeSet Q, ‖φ x‖ ≤ cubeScaleFactor Q := by
    intro x hx
    have hxball : x ∈ Metric.closedBall (cubeCenter Q) (cubeRadius Q) :=
      cubeSet_subset_closedBall Q hx
    have hdist : ‖x - cubeCenter Q‖ ≤ cubeRadius Q := by
      simpa [Metric.mem_closedBall, dist_eq_norm] using hxball
    have hcoord : ‖(x - cubeCenter Q) i0‖ ≤ ‖x - cubeCenter Q‖ :=
      norm_le_pi_norm (x - cubeCenter Q) i0
    calc
      ‖φ x‖ = ‖(x - cubeCenter Q) i0‖ := by
        simp [φ, Pi.sub_apply]
      _ ≤ ‖x - cubeCenter Q‖ := hcoord
      _ ≤ cubeRadius Q := hdist
      _ ≤ cubeScaleFactor Q := hradius_le_scale
  have hφLpTop : MeasureTheory.MemLp φ ∞ (normalizedCubeMeasure Q) := by
    have hbound_ae_cube : ∀ᵐ x ∂ cubeMeasure Q, ‖φ x‖ ≤ cubeScaleFactor Q := by
      exact (MeasureTheory.ae_restrict_iff' (measurableSet_cubeSet Q)).2 <|
        Filter.Eventually.of_forall hφ_bound
    have hbound_ae : ∀ᵐ x ∂ normalizedCubeMeasure Q, ‖φ x‖ ≤ cubeScaleFactor Q := by
      simpa [normalizedCubeMeasure] using
        (MeasureTheory.Measure.ae_smul_measure hbound_ae_cube
          (ENNReal.ofReal ((cubeVolume Q)⁻¹)))
    exact MeasureTheory.memLp_top_of_bound hφ_cont.aestronglyMeasurable
      (cubeScaleFactor Q) hbound_ae
  have hφLp2 : MeasureTheory.MemLp φ (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    hφLpTop.mono_exponent (by norm_num : (2 : ℝ≥0∞) ≤ ∞)
  have hφ_linf_le : cubeLpNorm Q ∞ φ ≤ cubeScaleFactor Q :=
    cubeLpNorm_infty_le_of_bound_on_cubeSet Q φ
      (cubeScaleFactor_nonneg Q) hφ_bound
  have hprod : cubeBesovScaleWeight (1 : ℝ) Q * cubeScaleFactor Q = 1 := by
    have hmul := cubeBesovScaleWeight_neg_one_mul_cubeBesovScaleWeight_one_eq_one Q
    have hneg := cubeBesovScaleWeight_neg_one_eq_cubeScaleFactor Q
    calc
      cubeBesovScaleWeight (1 : ℝ) Q * cubeScaleFactor Q =
          cubeBesovScaleWeight (-1 : ℝ) Q * cubeBesovScaleWeight (1 : ℝ) Q := by
            rw [hneg]
            ring
      _ = 1 := hmul
  have htest :
      ∀ M : ℕ,
        cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M φ ≤ 2 := by
    intro M
    have hraw := cubeBesovDualTestNorm_one_two_le_of_contDiff_bound
      Q φ M (by norm_num : (0 : ℝ) ≤ 1) hφLpTop hφ_smooth
      (fun z _hz => norm_fderiv_coord_sub_const_le_one i0 (cubeCenter Q) z)
    calc
      cubeBesovDualTestNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞) M φ
          ≤ 1 + cubeBesovScaleWeight 1 Q * cubeLpNorm Q ∞ φ := hraw
      _ ≤ 1 + cubeBesovScaleWeight 1 Q * cubeScaleFactor Q := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_left hφ_linf_le
              (cubeBesovScaleWeight_nonneg 1 Q))
      _ = 2 := by
          rw [hprod]
          norm_num
  have hmem : CubeBesovDualLocalMemLpGlobal Q (2 : ℝ≥0∞) φ :=
    cubeBesovDualLocalMemLpGlobal_of_memLp_two Q φ hφLp2
  have hgrad_i :
      MeasureTheory.MemLp (fun x => u.toH1Function.grad x i0)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using u.toOpenCubeSet.toH1Function.grad_memL2_normalizedCubeMeasure i0
  have hgrad_vec :
      MeasureTheory.MemLp (fun x => u.toH1Function.grad x)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    simpa using
      (MeasureTheory.MemLp.of_eval
        (fun i : Fin d => u.toOpenCubeSet.toH1Function.grad_memL2_normalizedCubeMeasure i))
  have hBdd :
      BddAbove (Set.range fun M : ℕ =>
        cubeBesovNegativeVectorPartialSeminormTwo Q (2 * t) M
          (fun x => u.toH1Function.grad x)) :=
    cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp
      Q (by nlinarith : 0 < 2 * t) (fun x => u.toH1Function.grad x) hgrad_vec
  have hcirc :
      cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) (1 : ℝ≥0∞)
          (fun x => u.toH1Function.grad x i0) ≤
        cubeBesovScaleWeight (-1 : ℝ) Q * (G * N) := by
    have hraw :=
      cubeBesovCircNorm_two_one_component_le_scaleWeight_neg_mul_gap_geometric_of_bddAbove
        (Q := Q) (a := 1) (b := 2 * t)
        (by linarith : 0 < (1 : ℝ) - 2 * t)
        (u := fun x => u.toH1Function.grad x) i0 hBdd
    simpa [G, N] using hraw
  have hpair :=
    abs_cubeBesovPairing_le_note_constant_mul_of_uniform_bound_two_one_of_nonneg
      Q 1 (fun x => u.toH1Function.grad x i0) φ
      (by norm_num) hgrad_i (by norm_num : (0 : ℝ) ≤ 2) htest hmem
  have hpair' :
      |cubeBesovPairing Q (fun x => u.toH1Function.grad x i0) φ| ≤
        ((3 : ℝ) ^ ((d : ℝ) + 1) *
          (cubeBesovScaleWeight (-1 : ℝ) Q * (G * N))) * 2 := by
    exact hpair.trans
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hcirc
          (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 3) _))
        (by norm_num : (0 : ℝ) ≤ 2))
  have hid := cubeAverage_eq_neg_cubeAverage_grad_mul_centeredCoord_of_h10OnCube Q u i0
  have havg_pair :
      ‖cubeAverage Q (fun x => u.toH1Function.toFun x)‖ =
        |cubeBesovPairing Q (fun x => u.toH1Function.grad x i0) φ| := by
    rw [hid]
    unfold cubeBesovPairing
    simp [φ, Real.norm_eq_abs]
  calc
    cubeBesovScaleWeight (1 : ℝ) Q *
        ‖cubeAverage Q (fun x => u.toH1Function.toFun x)‖
        =
      cubeBesovScaleWeight (1 : ℝ) Q *
        |cubeBesovPairing Q (fun x => u.toH1Function.grad x i0) φ| := by
        rw [havg_pair]
    _ ≤
      cubeBesovScaleWeight (1 : ℝ) Q *
        (((3 : ℝ) ^ ((d : ℝ) + 1) *
          (cubeBesovScaleWeight (-1 : ℝ) Q * (G * N))) * 2) := by
        exact mul_le_mul_of_nonneg_left hpair'
          (cubeBesovScaleWeight_nonneg 1 Q)
    _ = ((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) * G) * N := by
        have hcancel : cubeBesovScaleWeight (1 : ℝ) Q *
            cubeBesovScaleWeight (-1 : ℝ) Q = 1 := by
          have h := cubeBesovScaleWeight_neg_one_mul_cubeBesovScaleWeight_one_eq_one Q
          nlinarith [h]
        calc
          cubeBesovScaleWeight (1 : ℝ) Q *
            (((3 : ℝ) ^ ((d : ℝ) + 1) *
              (cubeBesovScaleWeight (-1 : ℝ) Q * (G * N))) * 2)
              =
            (2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              ((cubeBesovScaleWeight (1 : ℝ) Q *
                cubeBesovScaleWeight (-1 : ℝ) Q) * (G * N)) := by
              ring
          _ = (2 * (3 : ℝ) ^ ((d : ℝ) + 1)) * (1 * (G * N)) := by
              rw [hcancel]
          _ = ((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) * G) * N := by
              ring
    _ =
      ((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (1 - 2 * t)))⁻¹)) *
        cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (fun x => u.toH1Function.grad x) := by
        rfl

/-- The geometric loss with exponent `2r` is no larger than the corresponding
loss with exponent `r`. -/
theorem sqrt_inv_one_sub_rpow_three_neg_two_mul_le_sqrt_inv_one_sub_rpow_three_neg
    {r : ℝ} (hr : 0 < r) :
    Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * r))⁻¹) ≤
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-r))⁻¹) := by
  let r₁ : ℝ := Real.rpow (3 : ℝ) (-r)
  let r₂ : ℝ := Real.rpow (3 : ℝ) (-2 * r)
  have hr₁_lt_one : r₁ < 1 := by
    dsimp [r₁]
    simpa [Real.rpow_eq_pow] using
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by linarith : -r < 0)
  have hr₂_lt_one : r₂ < 1 := by
    dsimp [r₂]
    simpa [Real.rpow_eq_pow] using
      Real.rpow_lt_one_of_one_lt_of_neg
        (by norm_num : (1 : ℝ) < 3) (by nlinarith : -2 * r < 0)
  have hr₂_le_r₁ : r₂ ≤ r₁ := by
    dsimp [r₁, r₂]
    simpa [Real.rpow_eq_pow] using
      Real.rpow_le_rpow_of_exponent_le
        (by norm_num : (1 : ℝ) ≤ 3) (by linarith : -2 * r ≤ -r)
  have hden₁_pos : 0 < 1 - r₁ := by linarith
  have hden₂_pos : 0 < 1 - r₂ := by linarith
  have hden_order : 1 - r₁ ≤ 1 - r₂ := by linarith
  have hinv_order : (1 - r₂)⁻¹ ≤ (1 - r₁)⁻¹ :=
    (inv_le_inv₀ hden₂_pos hden₁_pos).2 hden_order
  simpa [r₁, r₂] using Real.sqrt_le_sqrt hinv_order

/-- The normalized `L²` norm is bounded by the fluctuation part plus the
absolute scalar average. -/
theorem cubeLpNorm_two_le_cubeLpNorm_fluctuation_add_norm_cubeAverage
    {d : ℕ} (Q : TriadicCube d) (v : Vec d → ℝ)
    (hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q)) :
    cubeLpNorm Q (2 : ℝ≥0∞) v ≤
      cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v) + ‖cubeAverage Q v‖ := by
  have hv_fluct :
      MeasureTheory.MemLp (cubeFluctuation Q v) (2 : ℝ≥0∞)
        (normalizedCubeMeasure Q) :=
    hv.sub (MeasureTheory.memLp_const (cubeAverage Q v))
  have hconst :
      MeasureTheory.MemLp (fun _ : Vec d => cubeAverage Q v)
        (2 : ℝ≥0∞) (normalizedCubeMeasure Q) :=
    MeasureTheory.memLp_const (cubeAverage Q v)
  calc
    cubeLpNorm Q (2 : ℝ≥0∞) v =
        cubeLpNorm Q (2 : ℝ≥0∞)
          (fun x => cubeFluctuation Q v x +
            (fun _ : Vec d => cubeAverage Q v) x) := by
        congr 1
        funext x
        simp [cubeFluctuation]
    _ ≤ cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v) +
        cubeLpNorm Q (2 : ℝ≥0∞) (fun _ : Vec d => cubeAverage Q v) := by
        exact cubeLpNorm_add_le Q (2 : ℝ≥0∞) (cubeFluctuation Q v)
          (fun _ : Vec d => cubeAverage Q v) hv_fluct hconst (by norm_num)
    _ = cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v) +
        ‖cubeAverage Q v‖ := by
        rw [cubeLpNorm_const (Q := Q) (p := (2 : ℝ≥0∞))
          (c := cubeAverage Q v) (by norm_num)]

/-- Full parent-cube zero-trace value estimate: the top-scale normalized
`L²` norm is controlled by the public negative-Besov norm of the gradient. -/
theorem cubeBesovScaleWeight_one_mul_cubeLpNorm_h10_le_grad_negativeBesovTwo
    {d : ℕ} [NeZero d] (Q : TriadicCube d) {t : ℝ}
    (u : H10Function (cubeSet Q))
    (ht : 0 < t) (ht_lt : t < 1 / 2) :
    cubeBesovScaleWeight (1 : ℝ) Q *
        cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.toH1Function.toFun x) ≤
      ((((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)) +
          2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹)) *
        cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (fun x => u.toH1Function.grad x) := by
  let v : Vec d → ℝ := fun x => u.toH1Function.toFun x
  let F : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (cubeFluctuation Q v)
  let Aavg : ℝ := ‖cubeAverage Q v‖
  let W : ℝ := cubeBesovScaleWeight (1 : ℝ) Q
  let G : ℝ := Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹)
  let N : ℝ :=
    cubeBesovNegativeVectorSeminormTwo Q (2 * t)
      (fun x => u.toH1Function.grad x)
  let Kfl : ℝ := (d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
      (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)
  let Kav : ℝ := 2 * (3 : ℝ) ^ ((d : ℝ) + 1)
  have hv : MeasureTheory.MemLp v (2 : ℝ≥0∞) (normalizedCubeMeasure Q) := by
    dsimp [v]
    simpa using u.toOpenCubeSet.toH1Function.memL2_normalizedCubeMeasure
  have htri : cubeLpNorm Q (2 : ℝ≥0∞) v ≤ F + Aavg := by
    dsimp [F, Aavg, v]
    exact cubeLpNorm_two_le_cubeLpNorm_fluctuation_add_norm_cubeAverage Q v hv
  have hW_nonneg : 0 ≤ W := by
    dsimp [W]
    exact cubeBesovScaleWeight_nonneg 1 Q
  have hfluct_raw :=
    cubeBesovScaleWeight_one_mul_cubeLpNorm_fluctuation_le_grad_negativeBesovTwo
      (Q := Q) (t := t) u.toOpenCubeSet.toH1Function ht ht_lt
  have hfluct0 :
      W * F ≤
        (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
          (3 : ℝ) ^ ((d : ℝ) + 1)) * ((d : ℝ) * G)) * N := by
    dsimp [W, F, G, N]
    simpa [v, H10Function.toOpenCubeSet_toH1Function_toFun,
      H10Function.toOpenCubeSet_toH1Function_grad,
      Ch01.Legacy.fullVectorPoincareConstant,
      fullVectorPoincareCubeConstant_eq_dimensionConstant] using hfluct_raw
  have hfluct : W * F ≤ (Kfl * G) * N := by
    calc
      W * F ≤
          (((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
            (3 : ℝ) ^ ((d : ℝ) + 1)) * ((d : ℝ) * G)) * N := hfluct0
      _ = (Kfl * G) * N := by
          dsimp [Kfl]
          ring
  have havg_raw :=
    cubeBesovScaleWeight_one_mul_abs_cubeAverage_h10_le_grad_negativeBesovTwo
      (Q := Q) (t := t) u ht ht_lt
  have hGavg_le :
      Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (1 - 2 * t)))⁻¹) ≤ G := by
    dsimp [G]
    have h := sqrt_inv_one_sub_rpow_three_neg_two_mul_le_sqrt_inv_one_sub_rpow_three_neg
      (by linarith : 0 < 1 - 2 * t)
    simpa [show -(1 - 2 * t) = -2 * ((1 / 2 : ℝ) - t) by ring] using h
  have hN_nonneg : 0 ≤ N := by
    dsimp [N]
    exact cubeBesovNegativeVectorSeminormTwo_nonneg_of_bddAbove Q (2 * t)
      (fun x => u.toH1Function.grad x)
      (cubeBesovNegativeVectorPartialSeminormTwo_bddAbove_of_memLp
        Q (by nlinarith : 0 < 2 * t) (fun x => u.toH1Function.grad x)
        (by
          simpa using
            (MeasureTheory.MemLp.of_eval
              (fun i : Fin d =>
                u.toOpenCubeSet.toH1Function.grad_memL2_normalizedCubeMeasure i))))
  have hKav_nonneg : 0 ≤ Kav := by
    dsimp [Kav]
    positivity
  have havg : W * Aavg ≤ (Kav * G) * N := by
    dsimp [W, Aavg, Kav, N] at havg_raw ⊢
    have hstep :
        ((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
            Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (1 - 2 * t)))⁻¹)) *
          cubeBesovNegativeVectorSeminormTwo Q (2 * t)
            (fun x => u.toH1Function.grad x) ≤
        ((2 * (3 : ℝ) ^ ((d : ℝ) + 1)) * G) *
          cubeBesovNegativeVectorSeminormTwo Q (2 * t)
            (fun x => u.toH1Function.grad x) := by
      have hcoef :
          (2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
              Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * (1 - 2 * t)))⁻¹) ≤
            (2 * (3 : ℝ) ^ ((d : ℝ) + 1)) * G := by
        exact mul_le_mul_of_nonneg_left hGavg_le hKav_nonneg
      exact mul_le_mul_of_nonneg_right hcoef hN_nonneg
    exact havg_raw.trans hstep
  calc
    W * cubeLpNorm Q (2 : ℝ≥0∞) v ≤ W * (F + Aavg) :=
      mul_le_mul_of_nonneg_left htri hW_nonneg
    _ = W * F + W * Aavg := by ring
    _ ≤ (Kfl * G) * N + (Kav * G) * N := add_le_add hfluct havg
    _ = (((Kfl + Kav) * G) * N) := by ring
    _ =
      ((((d : ℝ) * Legacy.cubeNeumannW22CalderonZygmundConstant d *
            (3 : ℝ) ^ ((d : ℝ) + 1) * (d : ℝ)) +
          2 * (3 : ℝ) ^ ((d : ℝ) + 1)) *
          Real.sqrt ((1 - Real.rpow (3 : ℝ) (-2 * ((1 / 2 : ℝ) - t)))⁻¹)) *
        cubeBesovNegativeVectorSeminormTwo Q (2 * t)
          (fun x => u.toH1Function.grad x) := by
        rfl


end

end Ch03
end Book
end Homogenization
