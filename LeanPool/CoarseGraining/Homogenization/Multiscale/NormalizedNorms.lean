/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Multiscale.Projection
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Normalized Norms -/

namespace Homogenization

open scoped ENNReal

/-!
Normalized cube `L^p` and `W^{1,p}` quantities used later in the Besov layer.

The normalization is packaged through a probability measure on `cubeSet Q`, so
the underlined norms match the note conventions without repeatedly rederiving
factors of `cubeVolume Q`.
-/

noncomputable def cubeMeasure {d : ℕ} (Q : TriadicCube d) : MeasureTheory.Measure (Vec d) :=
  MeasureTheory.volume.restrict (cubeSet Q)

noncomputable def normalizedCubeMeasure {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.Measure (Vec d) :=
  ENNReal.ofReal ((cubeVolume Q)⁻¹) • cubeMeasure Q

@[simp] theorem cubeMeasure_apply_univ {d : ℕ} (Q : TriadicCube d) :
    cubeMeasure Q Set.univ = MeasureTheory.volume (cubeSet Q) := by
  rw [cubeMeasure, MeasureTheory.Measure.restrict_apply_univ]

@[simp] theorem cubeMeasure_apply_univ_toReal {d : ℕ} (Q : TriadicCube d) :
    (cubeMeasure Q Set.univ).toReal = cubeVolume Q := by
  simp [cubeMeasure]

theorem cubeMeasure_apply_univ_ne_top {d : ℕ} (Q : TriadicCube d) :
    cubeMeasure Q Set.univ ≠ ∞ := by
  intro htop
  have hzero : (cubeMeasure Q Set.univ).toReal = 0 := by
    simp [htop]
  have hvol : (cubeMeasure Q Set.univ).toReal = cubeVolume Q :=
    cubeMeasure_apply_univ_toReal Q
  have : cubeVolume Q = 0 := by
    simpa [hvol] using hzero
  exact (cubeVolume_pos Q).ne' this

@[simp] theorem cubeMeasure_apply_univ_eq {d : ℕ} (Q : TriadicCube d) :
    cubeMeasure Q Set.univ = ENNReal.ofReal (cubeVolume Q) := by
  exact (ENNReal.toReal_eq_toReal_iff' (cubeMeasure_apply_univ_ne_top Q)
    ENNReal.ofReal_ne_top).1 (by
      rw [cubeMeasure_apply_univ_toReal Q, ENNReal.toReal_ofReal (cubeVolume_nonneg Q)])

@[simp] theorem normalizedCubeMeasure_apply_univ {d : ℕ} (Q : TriadicCube d) :
    normalizedCubeMeasure Q Set.univ = 1 := by
  rw [normalizedCubeMeasure, MeasureTheory.Measure.smul_apply, cubeMeasure_apply_univ_eq Q]
  rw [ENNReal.ofReal_inv_of_pos (cubeVolume_pos Q)]
  have hvol : ENNReal.ofReal (cubeVolume Q) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.2 (cubeVolume_pos Q)
  exact ENNReal.inv_mul_cancel hvol ENNReal.ofReal_ne_top

instance normalizedCubeMeasure.instIsFiniteMeasure {d : ℕ} (Q : TriadicCube d) :
    MeasureTheory.IsFiniteMeasure (normalizedCubeMeasure Q) where
  measure_univ_lt_top := by
    simp [normalizedCubeMeasure_apply_univ Q]

theorem normalizedCubeMeasure_ne_zero {d : ℕ} (Q : TriadicCube d) :
    normalizedCubeMeasure Q ≠ 0 := by
  intro hzero
  have huniv : normalizedCubeMeasure Q Set.univ = 0 := by
    simp [hzero]
  simp at huniv

theorem cubeAverage_eq_integral_normalizedCubeMeasure {d : ℕ} (Q : TriadicCube d)
    (f : Vec d → ℝ) :
    cubeAverage Q f = ∫ x, f x ∂ normalizedCubeMeasure Q := by
  rw [cubeAverage, normalizedCubeMeasure, cubeMeasure, MeasureTheory.integral_smul_measure]
  simp [smul_eq_mul, ENNReal.toReal_ofReal, inv_nonneg, cubeVolume_nonneg]

noncomputable def cubeLpNorm {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → E) : ℝ :=
  (MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q)).toReal

noncomputable def cubeFluctuation {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    Vec d → ℝ :=
  fun x => f x - cubeAverage Q f

theorem cubeAverage_sub_const_of_memLp_two {d : ℕ} (Q : TriadicCube d)
    {f : Vec d → ℝ} (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (c : ℝ) :
    cubeAverage Q (fun x => f x - c) = cubeAverage Q f - c := by
  rw [cubeAverage_eq_integral_normalizedCubeMeasure,
    cubeAverage_eq_integral_normalizedCubeMeasure]
  have hf_int : MeasureTheory.Integrable f (normalizedCubeMeasure Q) :=
    hf.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hc_int : MeasureTheory.Integrable (fun _ : Vec d => c) (normalizedCubeMeasure Q) :=
    MeasureTheory.integrable_const c
  have hreal_univ : (normalizedCubeMeasure Q).real Set.univ = 1 := by
    rw [MeasureTheory.Measure.real_def, normalizedCubeMeasure_apply_univ]
    norm_num
  rw [MeasureTheory.integral_sub hf_int hc_int, MeasureTheory.integral_const,
    hreal_univ]
  simp

theorem cubeFluctuation_sub_const_of_memLp_two {d : ℕ} (Q : TriadicCube d)
    {f : Vec d → ℝ} (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure Q))
    (c : ℝ) :
    cubeFluctuation Q (fun x => f x - c) = cubeFluctuation Q f := by
  funext x
  calc
    cubeFluctuation Q (fun x => f x - c) x
        = (f x - c) - (cubeAverage Q f - c) := by
            simp [cubeFluctuation, cubeAverage_sub_const_of_memLp_two Q hf c]
    _ = f x - cubeAverage Q f := by ring
    _ = cubeFluctuation Q f x := by simp [cubeFluctuation]

theorem cubeFluctuation_cubeFluctuation_of_memLp_two {d : ℕ} (R Q : TriadicCube d)
    {f : Vec d → ℝ} (hf : MeasureTheory.MemLp f (2 : ℝ≥0∞) (normalizedCubeMeasure R)) :
    cubeFluctuation R (cubeFluctuation Q f) = cubeFluctuation R f := by
  simpa [cubeFluctuation] using!
    cubeFluctuation_sub_const_of_memLp_two R hf (cubeAverage Q f)

noncomputable def cubeW1pSeminorm {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (Du : Vec d → Vec d) : ℝ :=
  cubeLpNorm Q p Du

noncomputable def cubeW1InfinityNorm {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (Du : Vec d → Vec d) : ℝ :=
  max (cubeLpNorm Q ∞ Du) ((cubeScaleFactor Q)⁻¹ * cubeLpNorm Q ∞ u)

noncomputable def cubeW1pNorm {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (Du : Vec d → Vec d) : ℝ :=
  if p = 0 then
    0
  else if p = ∞ then
    cubeW1InfinityNorm Q u Du
  else
    ((cubeW1pSeminorm Q p Du) ^ p.toReal
      + (cubeScaleFactor Q) ^ (-p.toReal) * (cubeLpNorm Q p u) ^ p.toReal) ^ (1 / p.toReal)

theorem cubeLpNorm_nonneg {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → E) :
    0 ≤ cubeLpNorm Q p f :=
  ENNReal.toReal_nonneg

@[simp] theorem cubeLpNorm_zero {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) :
    cubeLpNorm Q p (fun _ => (0 : E)) = 0 := by
  simp [cubeLpNorm]

theorem cubeLpNorm_const {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (p : ℝ≥0∞) (c : E) (hp : p ≠ 0) :
    cubeLpNorm Q p (fun _ => c) = ‖c‖ := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_const c hp (normalizedCubeMeasure_ne_zero Q),
    normalizedCubeMeasure_apply_univ]
  simp

theorem cubeLpNorm_one_eq_integral_norm {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    (Q : TriadicCube d) (f : Vec d → E)
    (hf : MeasureTheory.AEStronglyMeasurable f (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 1 f = ∫ x, ‖f x‖ ∂ normalizedCubeMeasure Q := by
  unfold cubeLpNorm
  rw [MeasureTheory.eLpNorm_one_eq_lintegral_enorm hf,
    ← MeasureTheory.integral_norm_eq_lintegral_enorm hf]

theorem cubeLpNorm_rpow_eq_cubeAverage_norm_rpow {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (Q : TriadicCube d) (p : ℝ≥0∞) (f : Vec d → E)
    (hp0 : p ≠ 0) (hpTop : p ≠ ∞)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q)) :
    (cubeLpNorm Q p f) ^ p.toReal =
      cubeAverage Q (fun x => ‖f x‖ ^ p.toReal) := by
  have hpPos : 0 < p.toReal := ENNReal.toReal_pos hp0 hpTop
  have hnonneg :
      0 ≤ᵐ[normalizedCubeMeasure Q] fun x => ‖f x‖ ^ p.toReal :=
    Filter.Eventually.of_forall fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hmeas :
      MeasureTheory.AEStronglyMeasurable (fun x => ‖f x‖ ^ p.toReal)
        (normalizedCubeMeasure Q) :=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow aemeasurable_const).aestronglyMeasurable
  calc
    (cubeLpNorm Q p f) ^ p.toReal
        = ((MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q)) ^ p.toReal).toReal := by
            rw [cubeLpNorm, ← ENNReal.toReal_rpow]
    _ = (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂ normalizedCubeMeasure Q).toReal := by
          rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpTop hf.aestronglyMeasurable]
          let A : ℝ≥0∞ := ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂ normalizedCubeMeasure Q
          change ((A ^ (1 / p.toReal)) ^ p.toReal).toReal = A.toReal
          rw [← ENNReal.rpow_mul, one_div, inv_mul_cancel₀ hpPos.ne', ENNReal.rpow_one]
    _ = ∫ x, ‖f x‖ ^ p.toReal ∂ normalizedCubeMeasure Q := by
          symm
          rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hnonneg hmeas]
          refine congrArg ENNReal.toReal ?_
          apply MeasureTheory.lintegral_congr_ae
          filter_upwards with x
          rw [← ENNReal.ofReal_rpow_of_nonneg (norm_nonneg (f x)) ENNReal.toReal_nonneg]
          simp
    _ = cubeAverage Q (fun x => ‖f x‖ ^ p.toReal) := by
          symm
          rw [cubeAverage_eq_integral_normalizedCubeMeasure]

theorem cubeLpNorm_mul_le_mul_cubeLpNorm_of_holderConjugate {d : ℕ}
    (Q : TriadicCube d) (p q : ℝ≥0∞) (f g : Vec d → ℝ)
    [ENNReal.HolderConjugate p q]
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g q (normalizedCubeMeasure Q)) :
    cubeLpNorm Q 1 (fun x => f x * g x) ≤
      cubeLpNorm Q p f * cubeLpNorm Q q g := by
  have hmul :
      MeasureTheory.eLpNorm (fun x => f x * g x) 1 (normalizedCubeMeasure Q) ≤
        1 * MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q) *
          MeasureTheory.eLpNorm g q (normalizedCubeMeasure Q) := by
    simpa using
      (MeasureTheory.eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm
        (fun a b : ℝ => a * b) 1 (continuous_fst.mul continuous_snd)
        hf.aestronglyMeasurable hg.aestronglyMeasurable
        (Filter.Eventually.of_forall fun x => by
          simp))
  have hf_top : MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q) ≠ ∞ := ne_of_lt hf.eLpNorm_lt_top
  have hg_top : MeasureTheory.eLpNorm g q (normalizedCubeMeasure Q) ≠ ∞ :=
    ne_of_lt hg.eLpNorm_lt_top
  have hmul_top :
      1 * MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q) *
        MeasureTheory.eLpNorm g q (normalizedCubeMeasure Q) ≠ ∞ := by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.one_ne_top hf_top) hg_top
  have htoReal :
      (MeasureTheory.eLpNorm (fun x => f x * g x) 1 (normalizedCubeMeasure Q)).toReal ≤
        (1 * MeasureTheory.eLpNorm f p (normalizedCubeMeasure Q) *
          MeasureTheory.eLpNorm g q (normalizedCubeMeasure Q)).toReal :=
    ENNReal.toReal_mono hmul_top hmul
  simpa [cubeLpNorm, hf_top, hg_top, mul_assoc] using htoReal

theorem cubeLpNorm_mul_le_mul_cubeLpNorm_conjExponent {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (ENNReal.conjExponent p) (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) :
    cubeLpNorm Q 1 (fun x => f x * g x) ≤
      cubeLpNorm Q p f * cubeLpNorm Q (ENNReal.conjExponent p) g := by
  let : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent hp
  simpa using cubeLpNorm_mul_le_mul_cubeLpNorm_of_holderConjugate
    Q p (ENNReal.conjExponent p) f g hf hg

theorem abs_cubeAverage_mul_le_mul_cubeLpNorm_of_holderConjugate {d : ℕ}
    (Q : TriadicCube d) (p q : ℝ≥0∞) (f g : Vec d → ℝ)
    [ENNReal.HolderConjugate p q]
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g q (normalizedCubeMeasure Q)) :
    |cubeAverage Q (fun x => f x * g x)| ≤
      cubeLpNorm Q p f * cubeLpNorm Q q g := by
  have hfg_meas : MeasureTheory.AEStronglyMeasurable (fun x => f x * g x) (normalizedCubeMeasure Q) :=
    hf.aestronglyMeasurable.mul hg.aestronglyMeasurable
  calc
    |cubeAverage Q (fun x => f x * g x)|
      = |∫ x, f x * g x ∂ normalizedCubeMeasure Q| := by
          rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    _ ≤ ∫ x, |f x * g x| ∂ normalizedCubeMeasure Q := MeasureTheory.abs_integral_le_integral_abs
    _ = cubeLpNorm Q 1 (fun x => f x * g x) := by
          symm
          simpa using cubeLpNorm_one_eq_integral_norm Q (fun x => f x * g x) hfg_meas
    _ ≤ cubeLpNorm Q p f * cubeLpNorm Q q g :=
          cubeLpNorm_mul_le_mul_cubeLpNorm_of_holderConjugate Q p q f g hf hg

theorem abs_cubeAverage_mul_le_mul_cubeLpNorm_conjExponent {d : ℕ}
    (Q : TriadicCube d) (p : ℝ≥0∞) (f g : Vec d → ℝ)
    (hf : MeasureTheory.MemLp f p (normalizedCubeMeasure Q))
    (hg : MeasureTheory.MemLp g (ENNReal.conjExponent p) (normalizedCubeMeasure Q))
    (hp : 1 ≤ p) :
    |cubeAverage Q (fun x => f x * g x)| ≤
      cubeLpNorm Q p f * cubeLpNorm Q (ENNReal.conjExponent p) g := by
  let : ENNReal.HolderConjugate p (ENNReal.conjExponent p) :=
    ENNReal.HolderConjugate.conjExponent hp
  simpa using abs_cubeAverage_mul_le_mul_cubeLpNorm_of_holderConjugate
    Q p (ENNReal.conjExponent p) f g hf hg

@[simp] theorem cubeFluctuation_apply {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) (x : Vec d) :
    cubeFluctuation Q f x = f x - cubeAverage Q f :=
  rfl

@[simp] theorem cubeFluctuation_const {d : ℕ} (Q : TriadicCube d) (c : ℝ) :
    cubeFluctuation Q (fun _ => c) = 0 := by
  funext x
  simp [cubeFluctuation, cubeAverage_const]

@[simp] theorem cubeFluctuation_zero {d : ℕ} (Q : TriadicCube d) :
    cubeFluctuation Q (fun _ => (0 : ℝ)) = 0 := by
  simp

@[simp] theorem cubeAverage_cubeFluctuation {d : ℕ} (Q : TriadicCube d) (f : Vec d → ℝ) :
    cubeAverage Q (cubeFluctuation Q f) = 0 := by
  by_cases hf : MeasureTheory.Integrable f (normalizedCubeMeasure Q)
  · rw [cubeAverage_eq_integral_normalizedCubeMeasure]
    unfold cubeFluctuation
    have hconst :
        MeasureTheory.Integrable (fun _ : Vec d => cubeAverage Q f) (normalizedCubeMeasure Q) :=
      MeasureTheory.integrable_const _
    have hreal_univ : (normalizedCubeMeasure Q).real Set.univ = 1 := by
      rw [MeasureTheory.Measure.real_def, normalizedCubeMeasure_apply_univ]
      norm_num
    rw [MeasureTheory.integral_sub hf hconst, cubeAverage_eq_integral_normalizedCubeMeasure,
      MeasureTheory.integral_const, hreal_univ]
    simp
  · have havg : cubeAverage Q f = 0 := by
      rw [cubeAverage_eq_integral_normalizedCubeMeasure, MeasureTheory.integral_undef hf]
    have hfluct : cubeFluctuation Q f = f := by
      funext x
      simp [cubeFluctuation, havg]
    rw [hfluct, havg]

theorem cubeW1pSeminorm_nonneg {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (Du : Vec d → Vec d) :
    0 ≤ cubeW1pSeminorm Q p Du :=
  cubeLpNorm_nonneg Q p Du

@[simp] theorem cubeW1pSeminorm_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) :
    cubeW1pSeminorm Q p (fun _ => 0) = 0 := by
  simp [cubeW1pSeminorm]

@[simp] theorem cubeW1pNorm_top {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    cubeW1pNorm Q ∞ u Du = cubeW1InfinityNorm Q u Du := by
  simp [cubeW1pNorm]

theorem cubeW1InfinityNorm_nonneg {d : ℕ} (Q : TriadicCube d)
    (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    0 ≤ cubeW1InfinityNorm Q u Du := by
  exact le_trans (cubeLpNorm_nonneg Q ∞ Du) (le_max_left _ _)

@[simp] theorem cubeW1InfinityNorm_zero {d : ℕ} (Q : TriadicCube d) :
    cubeW1InfinityNorm Q (fun _ => 0) (fun _ => 0) = 0 := by
  simp [cubeW1InfinityNorm]

theorem cubeW1pNorm_nonneg {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞)
    (u : Vec d → ℝ) (Du : Vec d → Vec d) :
    0 ≤ cubeW1pNorm Q p u Du := by
  unfold cubeW1pNorm
  split_ifs with hp0 hp
  · positivity
  · exact cubeW1InfinityNorm_nonneg Q u Du
  · have hgrad : 0 ≤ (cubeW1pSeminorm Q p Du) ^ p.toReal :=
      Real.rpow_nonneg (cubeW1pSeminorm_nonneg Q p Du) _
    have hscale : 0 ≤ (cubeScaleFactor Q) ^ (-p.toReal) :=
      Real.rpow_nonneg (le_of_lt (by
        simpa [cubeScaleFactor] using (zpow_pos (show (0 : ℝ) < 3 by norm_num) Q.scale))) _
    have hu : 0 ≤ (cubeLpNorm Q p u) ^ p.toReal :=
      Real.rpow_nonneg (cubeLpNorm_nonneg Q p u) _
    apply Real.rpow_nonneg
    exact add_nonneg hgrad (mul_nonneg hscale hu)

@[simp] theorem cubeW1pNorm_zero {d : ℕ} (Q : TriadicCube d) (p : ℝ≥0∞) :
    cubeW1pNorm Q p (fun _ => 0) (fun _ => 0) = 0 := by
  by_cases hp0 : p = 0
  · simp [cubeW1pNorm, hp0]
  by_cases hp : p = ∞
  · simp [cubeW1pNorm, hp]
  have hpPos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp [cubeW1pNorm, hp0, hp, hpPos.ne']

end Homogenization
