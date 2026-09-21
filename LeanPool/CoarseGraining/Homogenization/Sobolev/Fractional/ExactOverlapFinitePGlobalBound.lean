/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ExactOverlapFinitePAveraging
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ContinuousInterpolation.OverlapCoordinateBridge

/-! # Exact Overlap Finite PGlobal Bound -/

namespace Homogenization

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- A finite dimension-only constant for the global bound on one exact-overlap
depth energy. -/
noncomputable def exactOverlapDepthGlobalBoundConstant (d : ℕ) : ℝ≥0∞ :=
  2 * (3 ^ d : ℝ≥0∞)

private theorem memLp_hilbert_overlap_of_memLp {d : ℕ}
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

private theorem eLpNorm_overlap_residual_le_two_mul {d : ℕ}
    (S : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S)) :
    eLpNorm (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
        p.exponent (ScalarOverlap.normalizedCubeMeasure S) ≤
      2 * eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
        (ScalarOverlap.normalizedCubeMeasure S) := by
  let μ : Measure (Vec d) := ScalarOverlap.normalizedCubeMeasure S
  let f : Vec d → HilbertVec d := fun x => HilbertVec.ofVec (F x)
  let m : HilbertVec d := HilbertVec.ofVec (ScalarOverlap.cubeAverageVec S F)
  let : IsProbabilityMeasure μ := ⟨by simp [μ]⟩
  have hp_one : 1 ≤ p.exponent := p.one_lt.le
  have hp0 : p.exponent ≠ 0 := (zero_lt_one.trans p.one_lt).ne'
  have htop : p.exponent ≠ ∞ := p.lt_top.ne
  have hF' : MemLp f p.exponent μ := by
    simpa [f, μ] using hF
  have hint : Integrable f μ := by
    exact hF'.integrable hp_one
  have hmean : m = ∫ x, f x ∂μ := by
    apply HilbertVec.ext
    intro i
    simp only [m, f, μ, HilbertVec.ofVec]
    rw [ScalarOverlap.cubeAverageVec, ScalarOverlap.cubeAverage_eq_integral_normalizedCubeMeasure]
    exact (eval_integral_piLp (fun j => hint.eval_piLp j) i).symm
  have hm_le : ‖m‖ₑ ≤ eLpNorm f p.exponent μ := by
    calc
      ‖m‖ₑ = ‖∫ x, f x ∂μ‖ₑ := by rw [hmean]
      _ ≤ ∫⁻ x, ‖f x‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
      _ = eLpNorm f 1 μ := eLpNorm_one_eq_lintegral_enorm.symm
      _ ≤ eLpNorm f p.exponent μ :=
        eLpNorm_le_eLpNorm_of_exponent_le hp_one hF.aestronglyMeasurable
  have hconst : eLpNorm (fun _ : Vec d => m) p.exponent μ = ‖m‖ₑ := by
    rw [eLpNorm_const' m hp0 htop]
    simp
  have htri : eLpNorm (fun x => f x - m) p.exponent μ ≤
      eLpNorm f p.exponent μ + eLpNorm (fun _ : Vec d => m) p.exponent μ :=
    eLpNorm_sub_le hF.aestronglyMeasurable aestronglyMeasurable_const hp_one
  have hfun : (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F)) =
      fun x => f x - m := by
    funext x
    simp [f, m]
  rw [hfun]
  calc
    eLpNorm (fun x => f x - m) p.exponent μ ≤
        eLpNorm f p.exponent μ + eLpNorm (fun _ : Vec d => m) p.exponent μ := htri
    _ ≤ eLpNorm f p.exponent μ + eLpNorm f p.exponent μ := by rw [hconst]; gcongr
    _ = 2 * eLpNorm f p.exponent μ := by ring

private theorem eLpNorm_rpow_eq_lintegral_enorm {α E : Type*}
    [MeasurableSpace α] [NormedAddCommGroup E] {μ : Measure α}
    {f : α → E} (p : FiniteLpExponent) :
    (eLpNorm f p.exponent μ) ^ p.exponent.toReal =
      ∫⁻ x, ‖f x‖ₑ ^ p.exponent.toReal ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne, ← ENNReal.rpow_mul]
  have hp : p.exponent.toReal ≠ 0 :=
    ENNReal.toReal_pos (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne |>.ne'
  rw [one_div, inv_mul_cancel₀ hp, ENNReal.rpow_one]

private theorem aemeasurable_hilbert_enorm_rpow_of_memLp {d : ℕ}
    {Q : TriadicCube d} {F : Vec d → Vec d} (p : FiniteLpExponent)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (normalizedCubeMeasure Q)) :
    AEMeasurable (fun x => ‖HilbertVec.ofVec (F x)‖ₑ ^ p.exponent.toReal)
      (volume.restrict (cubeSet Q)) := by
  let μ : Measure (Vec d) := volume.restrict (cubeSet Q)
  have hcoeff : ENNReal.ofReal ((cubeVolume Q)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (cubeVolume_pos Q))
  have hF_vol : AEMeasurable (fun x => HilbertVec.ofVec (F x)) μ := by
    have hF_norm : AEMeasurable (fun x => HilbertVec.ofVec (F x))
        (normalizedCubeMeasure Q) := hF.aestronglyMeasurable.aemeasurable
    simpa [μ, normalizedCubeMeasure, cubeMeasure] using
      (aemeasurable_smul_measure_iff
        (μ := volume.restrict (cubeSet Q))
        (f := fun x => HilbertVec.ofVec (F x)) hcoeff).1 hF_norm
  have hmap : Measurable (fun v : HilbertVec d => ‖v‖ₑ ^ p.exponent.toReal) := by
    fun_prop
  exact hmap.comp_aemeasurable hF_vol

private theorem aemeasurable_hilbert_enorm_rpow_scalarOverlap_of_memLp {d : ℕ}
    {S : TriadicCube d} {F : Vec d → Vec d} (p : FiniteLpExponent)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (ScalarOverlap.normalizedCubeMeasure S)) :
    AEMeasurable (fun x => ‖HilbertVec.ofVec (F x)‖ₑ ^ p.exponent.toReal)
      (volume.restrict (ScalarOverlap.cubeSet S)) := by
  let μ : Measure (Vec d) := volume.restrict (ScalarOverlap.cubeSet S)
  have hcoeff : ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (inv_pos.mpr (ScalarOverlap.cubeVolume_pos S))
  have hF_vol : AEMeasurable (fun x => HilbertVec.ofVec (F x)) μ := by
    have hF_norm : AEMeasurable (fun x => HilbertVec.ofVec (F x))
        (ScalarOverlap.normalizedCubeMeasure S) := hF.aestronglyMeasurable.aemeasurable
    simpa [μ, ScalarOverlap.normalizedCubeMeasure, ScalarOverlap.cubeMeasure] using
      (aemeasurable_smul_measure_iff
        (μ := volume.restrict (ScalarOverlap.cubeSet S))
        (f := fun x => HilbertVec.ofVec (F x)) hcoeff).1 hF_norm
  have hmap : Measurable (fun v : HilbertVec d => ‖v‖ₑ ^ p.exponent.toReal) := by
    fun_prop
  exact hmap.comp_aemeasurable hF_vol

/-- At each retained depth, exact Euclidean overlap oscillation is bounded by
a finite dimension-only multiple of the parent normalized `L^p` norm. -/
theorem cubeEuclideanPositiveBesovOverlapDepthENorm_le_global {d : ℕ}
    (Q : TriadicCube d) (p : FiniteLpExponent) (F : Vec d → Vec d) (j : ℕ)
    (hF : MemLp (fun x => HilbertVec.ofVec (F x)) p.exponent
      (normalizedCubeMeasure Q)) :
    cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j ≤
      exactOverlapDepthGlobalBoundConstant d *
        eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
          (normalizedCubeMeasure Q) := by
  classical
  let D : Finset (TriadicCube d) := ScalarOverlap.centersAtDepth Q j
  let r : ℝ := p.exponent.toReal
  let g : Vec d → ℝ≥0∞ := fun x => ‖HilbertVec.ofVec (F x)‖ₑ ^ r
  have hr_pos : 0 < r :=
    ENNReal.toReal_pos (zero_lt_one.trans p.one_lt).ne' p.lt_top.ne
  have hr_one : 1 ≤ r := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono p.lt_top.ne p.one_lt.le
  have hlocal : ∀ S ∈ D,
      eLpNorm (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S) ≤
        2 * eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
          (ScalarOverlap.normalizedCubeMeasure S) := by
    intro S hS
    exact eLpNorm_overlap_residual_le_two_mul S p F
      (memLp_hilbert_overlap_of_memLp hF (by simpa [D] using hS))
  have hlocal_rpow : ∀ S ∈ D,
      (eLpNorm (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ r ≤
        (2 : ℝ≥0∞) ^ r *
          ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S := by
    intro S hS
    have hpow := ENNReal.rpow_le_rpow (hlocal S hS) hr_pos.le
    rw [eLpNorm_rpow_eq_lintegral_enorm] at hpow
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr_pos.le] at hpow
    calc
      (eLpNorm (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F))
          p.exponent (ScalarOverlap.normalizedCubeMeasure S)) ^ r =
          ∫⁻ x, ‖HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S F)‖ₑ ^ r
            ∂ScalarOverlap.normalizedCubeMeasure S := eLpNorm_rpow_eq_lintegral_enorm p
      _ ≤ (2 : ℝ≥0∞) ^ r *
          (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
            (ScalarOverlap.normalizedCubeMeasure S)) ^ r := by
            exact hpow
      _ = (2 : ℝ≥0∞) ^ r *
          ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S := by
            rw [eLpNorm_rpow_eq_lintegral_enorm]
  have hassembly :
      ((D.card : ℝ≥0∞)⁻¹) *
        D.sum (fun S => ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S) ≤
      (3 ^ d : ℝ≥0∞) * ∫⁻ x, g x ∂normalizedCubeMeasure Q := by
    simpa [D, g] using!
      overlapCentersAtDepth_average_lintegral_normalizedOverlapCubeMeasure_le
        Q j
        (aemeasurable_hilbert_enorm_rpow_of_memLp (Q := Q) p hF)
        (fun S hS =>
          by
            simpa only [ScalarOverlap.cubeSet_eq_overlapCubeSet] using
              aemeasurable_hilbert_enorm_rpow_scalarOverlap_of_memLp p
                (memLp_hilbert_overlap_of_memLp (Q := Q) (S := S) (j := j)
                  (p := p.exponent) hF hS))
  have hpower :
      (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^ r ≤
        (2 : ℝ≥0∞) ^ r * (3 ^ d : ℝ≥0∞) *
          (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
            (normalizedCubeMeasure Q)) ^ r := by
    rw [cubeEuclideanPositiveBesovOverlapDepthENorm_rpow]
    calc
      ((D.card : ℝ≥0∞)⁻¹) *
          D.attach.sum (fun S =>
            (eLpNorm
              (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S.1 F))
              p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ r) ≤
          ((D.card : ℝ≥0∞)⁻¹) *
            D.sum (fun S => (2 : ℝ≥0∞) ^ r *
              ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S) := by
            apply mul_le_mul_right
            calc
              D.attach.sum (fun S =>
                (eLpNorm
                  (fun x => HilbertVec.ofVec (F x - ScalarOverlap.cubeAverageVec S.1 F))
                  p.exponent (ScalarOverlap.normalizedCubeMeasure S.1)) ^ r) ≤
                  D.attach.sum (fun S => (2 : ℝ≥0∞) ^ r *
                    ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S.1) := by
                    exact Finset.sum_le_sum fun S hS => hlocal_rpow S.1 S.2
              _ = D.sum (fun S => (2 : ℝ≥0∞) ^ r *
                    ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S) :=
                    by
                      simpa using (Finset.sum_attach D
                        (fun S => (2 : ℝ≥0∞) ^ r *
                          ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S))
      _ = (2 : ℝ≥0∞) ^ r *
          (((D.card : ℝ≥0∞)⁻¹) *
            D.sum (fun S => ∫⁻ x, g x ∂ScalarOverlap.normalizedCubeMeasure S)) := by
            rw [← Finset.mul_sum]
            ac_rfl
      _ ≤ (2 : ℝ≥0∞) ^ r *
          ((3 ^ d : ℝ≥0∞) * ∫⁻ x, g x ∂normalizedCubeMeasure Q) := by
            gcongr
      _ = (2 : ℝ≥0∞) ^ r * (3 ^ d : ℝ≥0∞) *
          (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
            (normalizedCubeMeasure Q)) ^ r := by
            rw [eLpNorm_rpow_eq_lintegral_enorm]
            ring
  have hK : (3 ^ d : ℝ≥0∞) ≤ (3 ^ d : ℝ≥0∞) ^ r := by
    have hthree : (1 : ℝ≥0∞) ≤ 3 := by norm_num
    simpa only [ENNReal.rpow_one] using
      ENNReal.rpow_le_rpow_of_exponent_le (one_le_pow₀ hthree (n := d)) hr_one
  have htarget_power :
      (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^ r ≤
        (exactOverlapDepthGlobalBoundConstant d *
          eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
            (normalizedCubeMeasure Q)) ^ r := by
    calc
      (cubeEuclideanPositiveBesovOverlapDepthENorm Q p F j) ^ r ≤
          (2 : ℝ≥0∞) ^ r * (3 ^ d : ℝ≥0∞) *
            (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
              (normalizedCubeMeasure Q)) ^ r := hpower
      _ ≤ (2 : ℝ≥0∞) ^ r * (3 ^ d : ℝ≥0∞) ^ r *
            (eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
              (normalizedCubeMeasure Q)) ^ r := by gcongr
      _ = (exactOverlapDepthGlobalBoundConstant d *
          eLpNorm (fun x => HilbertVec.ofVec (F x)) p.exponent
            (normalizedCubeMeasure Q)) ^ r := by
          rw [exactOverlapDepthGlobalBoundConstant,
            ENNReal.mul_rpow_of_nonneg _ _ hr_pos.le,
            ENNReal.mul_rpow_of_nonneg _ _ hr_pos.le]
  have hroot := ENNReal.rpow_le_rpow htarget_power (show 0 ≤ r⁻¹ by positivity)
  have hrr : r * r⁻¹ = 1 := mul_inv_cancel₀ hr_pos.ne'
  simpa only [← ENNReal.rpow_mul, hrr, ENNReal.rpow_one] using hroot

end

end Homogenization
