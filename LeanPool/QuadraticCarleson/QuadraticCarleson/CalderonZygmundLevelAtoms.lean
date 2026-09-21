/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.CalderonZygmundBadPart
import LeanPool.QuadraticCarleson.QuadraticCarleson.PositiveLevelIntegration
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# Calderón--Zygmund atoms on magnitude levels

This file isolates the algebraic and measure-theoretic facts about the atoms

`1_I (f 1_{F_k} - average_I (f 1_{F_k}))`

used in the positive-endpoint argument.  It does not assert the existence of
a Calderón--Zygmund decomposition: the interval (or a disjoint family of
intervals) is supplied explicitly.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators Function

namespace QuadraticCarleson
namespace CalderonZygmundLevelAtoms

open PositiveEndpointOptimization PositiveLevelIntegration


noncomputable section

/-- The part of `f` lying in the magnitude band `F_k`. -/
def levelRestricted (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) : ℝ → ℂ :=
  (magnitudeLevelSet A f k).indicator f

/-- The average of the level-restricted function over the centered interval. -/
def levelAverage (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℂ :=
  ⨍ x in centeredInterval z R, levelRestricted A f k x

/-- The level atom attached to a centered interval. -/
def levelAtom (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℝ → ℂ :=
  (centeredInterval z R).indicator
    (fun x ↦ levelRestricted A f k x - levelAverage A f k z R)

/-- The `L¹` mass of the `k`th magnitude level inside a centered interval. -/
def levelMassOnInterval (A : ℕ → ℝ) (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℝ :=
  ∫ x in centeredInterval z R, ‖levelRestricted A f k x‖

theorem measurable_levelRestricted {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) (k : ℕ) : Measurable (levelRestricted A f k) :=
  hf.indicator (measurableSet_magnitudeLevelSet hf k)

@[simp] theorem volume_centeredInterval (z R : ℝ) :
    volume (centeredInterval z R) = ENNReal.ofReal R := by
  simp [centeredInterval, Real.volume_Ico]

theorem volume_centeredInterval_lt_top (z R : ℝ) :
    volume (centeredInterval z R) < ∞ := by
  rw [volume_centeredInterval]
  exact ENNReal.ofReal_lt_top

theorem volumeReal_centeredInterval {z R : ℝ} (hR : 0 ≤ R) :
    volume.real (centeredInterval z R) = R := by
  simp [Measure.real, volume_centeredInterval, hR]

theorem levelRestricted_apply_of_mem {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} {x : ℝ} (hx : x ∈ magnitudeLevelSet A f k) :
    levelRestricted A f k x = f x := by
  simp [levelRestricted, hx]

theorem levelRestricted_apply_of_not_mem {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} {x : ℝ} (hx : x ∉ magnitudeLevelSet A f k) :
    levelRestricted A f k x = 0 := by
  simp [levelRestricted, hx]

/-- The upper endpoint in the definition of `F_k` is an exact pointwise bound. -/
theorem norm_levelRestricted_le {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} (hAk : 0 ≤ A k) (x : ℝ) :
    ‖levelRestricted A f k x‖ ≤ A k := by
  by_cases hx : x ∈ magnitudeLevelSet A f k
  · rw [levelRestricted_apply_of_mem hx]
    by_cases hk : k = 0
    · simp only [mem_magnitudeLevelSet, InMagnitudeLevel, hk, ↓reduceIte] at hx
      simpa [hk] using hx.2
    · simp only [mem_magnitudeLevelSet, InMagnitudeLevel, hk, ↓reduceIte] at hx
      exact hx.2
  · rw [levelRestricted_apply_of_not_mem hx, norm_zero]
    exact hAk

/-- A magnitude level is locally integrable on every finite centered interval. -/
theorem integrableOn_levelRestricted {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) {k : ℕ} (hAk : 0 ≤ A k) (z R : ℝ) :
    IntegrableOn (levelRestricted A f k) (centeredInterval z R) := by
  apply Integrable.mono' (integrableOn_const (C := A k) (by
    simp [centeredInterval, Real.volume_Ico]))
  · exact (measurable_levelRestricted hf k).aestronglyMeasurable.restrict
  · filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg hAk] using norm_levelRestricted_le hAk x

theorem levelMassOnInterval_eq {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) (k : ℕ) (z R : ℝ) :
    levelMassOnInterval A f k z R =
      ∫ x in centeredInterval z R ∩ magnitudeLevelSet A f k, ‖f x‖ := by
  rw [levelMassOnInterval]
  simp only [levelRestricted, norm_indicator_eq_indicator_norm]
  exact setIntegral_indicator (measurableSet_magnitudeLevelSet hf k)

/-- The average of the level-restricted function retains the exact upper
endpoint `A k` of the magnitude level. -/
theorem norm_levelAverage_le {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) :
    ‖levelAverage A f k z R‖ ≤ A k := by
  have hI : volume (centeredInterval z R) < ∞ := volume_centeredInterval_lt_top z R
  have hInt :
      ‖∫ x in centeredInterval z R, levelRestricted A f k x‖ ≤
        A k * volume.real (centeredInterval z R) :=
    norm_setIntegral_le_of_norm_le_const_ae hI
      (Filter.Eventually.of_forall fun x ↦ norm_levelRestricted_le hAk x)
  rw [levelAverage, setAverage_eq, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.2 measureReal_nonneg)]
  calc
    (volume.real (centeredInterval z R))⁻¹ *
          ‖∫ x in centeredInterval z R, levelRestricted A f k x‖ ≤
        (volume.real (centeredInterval z R))⁻¹ *
          (A k * volume.real (centeredInterval z R)) :=
      mul_le_mul_of_nonneg_left hInt (inv_nonneg.2 measureReal_nonneg)
    _ = A k := by
      rw [volumeReal_centeredInterval hR.le]
      field_simp

theorem measurable_levelAtom {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) (k : ℕ) (z R : ℝ) :
    Measurable (levelAtom A f k z R) := by
  exact ((measurable_levelRestricted hf k).sub measurable_const).indicator measurableSet_Ico

theorem integrable_levelAtom {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) {k : ℕ} (hAk : 0 ≤ A k) (z R : ℝ) :
    Integrable (levelAtom A f k z R) := by
  apply IntegrableOn.integrable_indicator
    ((integrableOn_levelRestricted hf hAk z R).sub
      (integrableOn_const (C := levelAverage A f k z R)
        (volume_centeredInterval_lt_top z R).ne))
    measurableSet_Ico

/-- The atom has exact mean zero. -/
theorem integral_levelAtom_eq_zero {A : ℕ → ℝ} {f : ℝ → ℂ}
    (k : ℕ) (z R : ℝ) :
    ∫ x, levelAtom A f k z R x = 0 := by
  rw [levelAtom, integral_indicator
    (show MeasurableSet (centeredInterval z R) by exact measurableSet_Ico)]
  exact setAverage_sub_setAverage (volume_centeredInterval_lt_top z R).ne
    (levelRestricted A f k)

/-- The atom is pointwise bounded by twice the upper endpoint of its
magnitude level. -/
theorem norm_levelAtom_le_two_mul {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) (x : ℝ) :
    ‖levelAtom A f k z R x‖ ≤ 2 * A k := by
  by_cases hx : x ∈ centeredInterval z R
  · rw [levelAtom, indicator_of_mem hx]
    calc
      ‖levelRestricted A f k x - levelAverage A f k z R‖ ≤
          ‖levelRestricted A f k x‖ + ‖levelAverage A f k z R‖ := norm_sub_le _ _
      _ ≤ A k + A k := add_le_add (norm_levelRestricted_le hAk x)
        (norm_levelAverage_le hAk hR)
      _ = 2 * A k := by ring
  · rw [levelAtom, indicator_of_notMem hx, norm_zero]
    exact mul_nonneg (by norm_num) hAk

/-- Essential-supremum formulation of the pointwise size estimate. -/
theorem eLpNormEssSup_levelAtom_le {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) :
    eLpNormEssSup (levelAtom A f k z R) volume ≤ ENNReal.ofReal (2 * A k) :=
  eLpNormEssSup_le_of_ae_bound
    (Filter.Eventually.of_forall fun x ↦ norm_levelAtom_le_two_mul hAk hR x)

/-- The standard factor-two `L¹` estimate for a mean-zero atom. -/
theorem integral_norm_levelAtom_le_two_mul_levelMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) (z R : ℝ) :
    (∫ x, ‖levelAtom A f k z R x‖) ≤ 2 * levelMassOnInterval A f k z R := by
  let I := centeredInterval z R
  let g := levelRestricted A f k
  let c := levelAverage A f k z R
  have hI : MeasurableSet I := measurableSet_Ico
  have hIfin : volume I ≠ ∞ := (volume_centeredInterval_lt_top z R).ne
  have hg : IntegrableOn g I := integrableOn_levelRestricted hf hAk z R
  have hc : IntegrableOn (fun _ : ℝ ↦ c) I := integrableOn_const hIfin
  have hnormavg : volume.real I * ‖c‖ ≤ ∫ x in I, ‖g x‖ := by
    calc
      volume.real I * ‖c‖ = ‖volume.real I • c‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      _ = ‖∫ x in I, g x‖ := by
        change ‖volume.real I • (⨍ x in I, g x)‖ = ‖∫ x in I, g x‖
        rw [measure_smul_setAverage g hIfin]
      _ ≤ ∫ x in I, ‖g x‖ := by
        simpa using (norm_integral_le_integral_norm (f := g) (μ := volume.restrict I))
  have htriangle :
      (∫ x in I, ‖g x - c‖) ≤ ∫ x in I, ‖g x‖ + ‖c‖ := by
    exact setIntegral_mono_on (hg.sub hc).norm (hg.norm.add hc.norm) hI
      (fun x _ ↦ norm_sub_le _ _)
  have hatom :
      (∫ x, ‖levelAtom A f k z R x‖) = ∫ x in I, ‖g x - c‖ := by
    simp only [levelAtom, I, g, c, norm_indicator_eq_indicator_norm]
    exact integral_indicator hI
  rw [hatom]
  calc
    (∫ x in I, ‖g x - c‖) ≤ ∫ x in I, ‖g x‖ + ‖c‖ := htriangle
    _ = (∫ x in I, ‖g x‖) + volume.real I * ‖c‖ := by
      rw [integral_add hg.norm hc.norm, setIntegral_const, smul_eq_mul]
    _ ≤ (∫ x in I, ‖g x‖) + ∫ x in I, ‖g x‖ :=
      add_le_add le_rfl hnormavg
    _ = 2 * levelMassOnInterval A f k z R := by
      simp only [levelMassOnInterval, I, g]
      ring

/-- Squared `L²` mass is controlled by essential size times `L¹` mass. -/
theorem integral_sq_norm_levelAtom_le_two_mul_integral_norm
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) :
    (∫ x, ‖levelAtom A f k z R x‖ ^ 2) ≤
      2 * A k * ∫ x, ‖levelAtom A f k z R x‖ := by
  let b := levelAtom A f k z R
  have hb : Integrable b := integrable_levelAtom hf hAk z R
  have hbmeas : Measurable b := measurable_levelAtom hf k z R
  have hmajor : Integrable (fun x ↦ (2 * A k) * ‖b x‖) :=
    hb.norm.const_mul (2 * A k)
  have hsq : Integrable (fun x ↦ ‖b x‖ ^ 2) := by
    apply Integrable.mono' hmajor
      ((hbmeas.norm.pow_const 2).aestronglyMeasurable)
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖b x‖)]
    simpa [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right (norm_levelAtom_le_two_mul hAk hR x) (norm_nonneg (b x))
  have hmono :
      (∫ x, ‖b x‖ ^ 2) ≤ ∫ x, (2 * A k) * ‖b x‖ := by
    apply integral_mono hsq hmajor
    intro x
    simpa [pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_right (norm_levelAtom_le_two_mul hAk hR x) (norm_nonneg (b x))
  simpa only [integral_const_mul, b] using hmono

/-- Combining the factor-two `L¹` estimate with the essential-size bound
gives the explicit squared `L²` estimate used in the high/low split. -/
theorem integral_sq_norm_levelAtom_le_four_mul_levelMass
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) :
    (∫ x, ‖levelAtom A f k z R x‖ ^ 2) ≤
      4 * A k * levelMassOnInterval A f k z R := by
  calc
    (∫ x, ‖levelAtom A f k z R x‖ ^ 2) ≤
        2 * A k * ∫ x, ‖levelAtom A f k z R x‖ :=
      integral_sq_norm_levelAtom_le_two_mul_integral_norm hf hAk hR
    _ ≤ 2 * A k * (2 * levelMassOnInterval A f k z R) := by
      gcongr
      exact integral_norm_levelAtom_le_two_mul_levelMass hf hAk z R
    _ = 4 * A k * levelMassOnInterval A f k z R := by ring

/-- The corresponding `L²` seminorm bound, written as the square root of
the squared-norm integral. -/
theorem sqrt_integral_sq_norm_levelAtom_le
    {A : ℕ → ℝ} {f : ℝ → ℂ} (hf : Measurable f)
    {k : ℕ} (hAk : 0 ≤ A k) {z R : ℝ} (hR : 0 < R) :
    Real.sqrt (∫ x, ‖levelAtom A f k z R x‖ ^ 2) ≤
      Real.sqrt (4 * A k * levelMassOnInterval A f k z R) :=
  Real.sqrt_le_sqrt (integral_sq_norm_levelAtom_le_four_mul_levelMass hf hAk hR)

/-- For a countable disjoint interval family, the extended total of the atom
`L¹` masses is at most twice the global mass of the magnitude level.  The
extended formulation avoids any global integrability hypothesis on `f`. -/
theorem tsum_atomL1Mass_le_two_mul_global_level_mass
    {ι : Type*} [Countable ι] {A : ℕ → ℝ} {f : ℝ → ℂ}
    (hf : Measurable f) {k : ℕ} (hAk : 0 ≤ A k)
    (z R : ι → ℝ)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i, ENNReal.ofReal (∫ x, ‖levelAtom A f k (z i) (R i) x‖)) ≤
      2 * ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖ := by
  let I : ι → Set ℝ := fun i ↦ centeredInterval (z i) (R i)
  let g := levelRestricted A f k
  have hI : ∀ i, MeasurableSet (I i) := fun _ ↦ measurableSet_Ico
  have hg : ∀ i, IntegrableOn g (I i) := fun i ↦
    integrableOn_levelRestricted hf hAk (z i) (R i)
  have hlocal : ∀ i,
      ENNReal.ofReal (∫ x, ‖levelAtom A f k (z i) (R i) x‖) ≤
        2 * ∫⁻ x in I i, ENNReal.ofReal ‖g x‖ := by
    intro i
    calc
      ENNReal.ofReal (∫ x, ‖levelAtom A f k (z i) (R i) x‖) ≤
          ENNReal.ofReal (2 * levelMassOnInterval A f k (z i) (R i)) :=
        ENNReal.ofReal_le_ofReal
          (integral_norm_levelAtom_le_two_mul_levelMass hf hAk (z i) (R i))
      _ = 2 * ENNReal.ofReal (levelMassOnInterval A f k (z i) (R i)) := by
        rw [ENNReal.ofReal_mul (by positivity)]
        norm_num
      _ = 2 * ∫⁻ x in I i, ENNReal.ofReal ‖g x‖ := by
        congr 1
        rw [levelMassOnInterval]
        exact ofReal_integral_eq_lintegral_ofReal (hg i).norm
          (Filter.Eventually.of_forall fun x ↦ norm_nonneg (g x))
  calc
    (∑' i, ENNReal.ofReal (∫ x, ‖levelAtom A f k (z i) (R i) x‖)) ≤
        ∑' i, 2 * ∫⁻ x in I i, ENNReal.ofReal ‖g x‖ :=
      ENNReal.tsum_le_tsum hlocal
    _ = 2 * ∑' i, ∫⁻ x in I i, ENNReal.ofReal ‖g x‖ := ENNReal.tsum_mul_left
    _ = 2 * ∫⁻ x in ⋃ i, I i, ENNReal.ofReal ‖g x‖ := by
      rw [lintegral_iUnion hI hdisj]
    _ ≤ 2 * ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
      have hmono : (∫⁻ x in ⋃ i, I i, ENNReal.ofReal ‖g x‖) ≤
          ∫⁻ x, ENNReal.ofReal ‖g x‖ := by
        simpa only [Measure.restrict_univ] using
          (lintegral_mono_set (μ := volume) (f := fun x ↦ ENNReal.ofReal ‖g x‖)
            (subset_univ (⋃ i, I i)))
      exact mul_right_mono hmono
    _ = 2 * ∫⁻ x in magnitudeLevelSet A f k, ENNReal.ofReal ‖f x‖ := by
      congr 1
      have heq : (fun x ↦ ENNReal.ofReal ‖g x‖) =
          (magnitudeLevelSet A f k).indicator (fun x ↦ ENNReal.ofReal ‖f x‖) := by
        funext x
        by_cases hx : x ∈ magnitudeLevelSet A f k <;>
          simp [g, levelRestricted, hx]
      rw [heq, lintegral_indicator (measurableSet_magnitudeLevelSet hf k)]

/-! ### Paper-specific full and lacunary atoms -/

/-- The atom built from the full-operator magnitude level. -/
abbrev fullLevelAtom (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℝ → ℂ :=
  levelAtom fullAmplitude f k z R

/-- The atom built from the lacunary magnitude level. -/
abbrev lacunaryLevelAtom (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℝ → ℂ :=
  levelAtom lacunaryAmplitude f k z R

abbrev fullLevelMassOnInterval (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℝ :=
  levelMassOnInterval fullAmplitude f k z R

abbrev lacunaryLevelMassOnInterval (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) : ℝ :=
  levelMassOnInterval lacunaryAmplitude f k z R

theorem integrable_fullLevelAtom {f : ℝ → ℂ} (hf : Measurable f)
    (k : ℕ) (z R : ℝ) : Integrable (fullLevelAtom f k z R) :=
  integrable_levelAtom hf (fullAmplitude_pos k).le z R

theorem integrable_lacunaryLevelAtom {f : ℝ → ℂ} (hf : Measurable f)
    (k : ℕ) (z R : ℝ) : Integrable (lacunaryLevelAtom f k z R) :=
  integrable_levelAtom hf (lacunaryAmplitude_pos k).le z R

theorem integral_fullLevelAtom_eq_zero (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) :
    ∫ x, fullLevelAtom f k z R x = 0 :=
  integral_levelAtom_eq_zero k z R

theorem integral_lacunaryLevelAtom_eq_zero (f : ℝ → ℂ) (k : ℕ) (z R : ℝ) :
    ∫ x, lacunaryLevelAtom f k z R x = 0 :=
  integral_levelAtom_eq_zero k z R

theorem norm_fullLevelAtom_le {f : ℝ → ℂ} (k : ℕ)
    {z R : ℝ} (hR : 0 < R) (x : ℝ) :
    ‖fullLevelAtom f k z R x‖ ≤ 2 * fullAmplitude k :=
  norm_levelAtom_le_two_mul (fullAmplitude_pos k).le hR x

theorem norm_lacunaryLevelAtom_le {f : ℝ → ℂ} (k : ℕ)
    {z R : ℝ} (hR : 0 < R) (x : ℝ) :
    ‖lacunaryLevelAtom f k z R x‖ ≤ 2 * lacunaryAmplitude k :=
  norm_levelAtom_le_two_mul (lacunaryAmplitude_pos k).le hR x

theorem eLpNormEssSup_fullLevelAtom_le {f : ℝ → ℂ} (k : ℕ)
    {z R : ℝ} (hR : 0 < R) :
    eLpNormEssSup (fullLevelAtom f k z R) volume ≤
      ENNReal.ofReal (2 * fullAmplitude k) :=
  eLpNormEssSup_levelAtom_le (fullAmplitude_pos k).le hR

theorem eLpNormEssSup_lacunaryLevelAtom_le {f : ℝ → ℂ} (k : ℕ)
    {z R : ℝ} (hR : 0 < R) :
    eLpNormEssSup (lacunaryLevelAtom f k z R) volume ≤
      ENNReal.ofReal (2 * lacunaryAmplitude k) :=
  eLpNormEssSup_levelAtom_le (lacunaryAmplitude_pos k).le hR

theorem integral_norm_fullLevelAtom_le {f : ℝ → ℂ} (hf : Measurable f)
    (k : ℕ) (z R : ℝ) :
    (∫ x, ‖fullLevelAtom f k z R x‖) ≤ 2 * fullLevelMassOnInterval f k z R :=
  integral_norm_levelAtom_le_two_mul_levelMass hf (fullAmplitude_pos k).le z R

theorem integral_norm_lacunaryLevelAtom_le {f : ℝ → ℂ} (hf : Measurable f)
    (k : ℕ) (z R : ℝ) :
    (∫ x, ‖lacunaryLevelAtom f k z R x‖) ≤
      2 * lacunaryLevelMassOnInterval f k z R :=
  integral_norm_levelAtom_le_two_mul_levelMass hf (lacunaryAmplitude_pos k).le z R

theorem integral_sq_norm_fullLevelAtom_le {f : ℝ → ℂ} (hf : Measurable f)
    (k : ℕ) {z R : ℝ} (hR : 0 < R) :
    (∫ x, ‖fullLevelAtom f k z R x‖ ^ 2) ≤
      4 * fullAmplitude k * fullLevelMassOnInterval f k z R :=
  integral_sq_norm_levelAtom_le_four_mul_levelMass hf (fullAmplitude_pos k).le hR

theorem integral_sq_norm_lacunaryLevelAtom_le {f : ℝ → ℂ} (hf : Measurable f)
    (k : ℕ) {z R : ℝ} (hR : 0 < R) :
    (∫ x, ‖lacunaryLevelAtom f k z R x‖ ^ 2) ≤
      4 * lacunaryAmplitude k * lacunaryLevelMassOnInterval f k z R :=
  integral_sq_norm_levelAtom_le_four_mul_levelMass hf (lacunaryAmplitude_pos k).le hR

theorem tsum_fullAtomL1Mass_le_global_level_mass
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (k : ℕ)
    (z R : ι → ℝ)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i, ENNReal.ofReal (∫ x, ‖fullLevelAtom f k (z i) (R i) x‖)) ≤
      2 * ∫⁻ x in fullMagnitudeLevelSet f k, ENNReal.ofReal ‖f x‖ := by
  simpa [fullMagnitudeLevelSet] using
    tsum_atomL1Mass_le_two_mul_global_level_mass hf (fullAmplitude_pos k).le z R hdisj

theorem tsum_lacunaryAtomL1Mass_le_global_level_mass
    {ι : Type*} [Countable ι] {f : ℝ → ℂ} (hf : Measurable f) (k : ℕ)
    (z R : ι → ℝ)
    (hdisj : Pairwise (Disjoint on fun i ↦ centeredInterval (z i) (R i))) :
    (∑' i, ENNReal.ofReal (∫ x, ‖lacunaryLevelAtom f k (z i) (R i) x‖)) ≤
      2 * ∫⁻ x in lacunaryMagnitudeLevelSet f k, ENNReal.ofReal ‖f x‖ := by
  simpa [lacunaryMagnitudeLevelSet] using
    tsum_atomL1Mass_le_two_mul_global_level_mass hf (lacunaryAmplitude_pos k).le z R hdisj

theorem levelAtom_eq_zero_of_not_mem {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} {z R x : ℝ} (hx : x ∉ centeredInterval z R) :
    levelAtom A f k z R x = 0 := by
  simp [levelAtom, hx]

theorem support_levelAtom_subset {A : ℕ → ℝ} {f : ℝ → ℂ}
    {k : ℕ} {z R : ℝ} :
    Function.support (levelAtom A f k z R) ⊆ centeredInterval z R := by
  intro x hx
  by_contra hnot
  exact hx (levelAtom_eq_zero_of_not_mem hnot)

end
end CalderonZygmundLevelAtoms
end QuadraticCarleson
