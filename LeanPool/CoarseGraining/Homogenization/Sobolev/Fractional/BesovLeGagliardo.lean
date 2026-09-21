/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.ENNRealBridge
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.JensenStep
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.TailSummation
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.OverlapIntegral
import LeanPool.CoarseGraining.Homogenization.Sobolev.Fractional.AssemblyPieces
import LeanPool.CoarseGraining.Homogenization.Besov.Positive.Full

/-!
# Besov-to-Gagliardo comparison: the partial overlap Besov seminorm is
controlled by the fractional Sobolev seminorm

Main result (`ofReal_partialSeminorm_rpow_le_gagliardo`): for every depth
truncation `N`, the `p`-th power of the diagonal overlap Besov partial
seminorm is at most `2 * 3^d` times the `p`-th power of the volume-normalized
Gagliardo seminorm.  The constant is purely dimensional.

Proof skeleton: the `ℝ≥0∞` bridge (`ENNRealBridge`) rewrites the partial
seminorm power as a sum of depth pieces; Jensen (`JensenStep`) bounds each
per-cube oscillation by a doubled difference integral; the depth coefficient
collapses (scale bookkeeping + the `3^{dj}` center count); the per-pair
backwards geometric tail (`TailSummation`) and the bounded-overlap count
(`OverlapIntegral`) convert the depth sum into the Gagliardo kernel integral
(`AssemblyPieces`).
-/

namespace Homogenization
namespace Gagliardo

noncomputable section

open MeasureTheory ScalarOverlap
open scoped ENNReal BigOperators

variable {d : ℕ}

/-- Measurability of the pairwise difference enorm power. -/
theorem measurable_pair_diff_enorm_rpow {u : Vec d → ℝ} (humeas : Measurable u)
    (pr : ℝ) :
    Measurable fun z : Vec d × Vec d => ‖u z.1 - u z.2‖ₑ ^ pr :=
  ENNReal.continuous_rpow_const.measurable.comp
    (((humeas.comp measurable_fst).sub (humeas.comp measurable_snd)).enorm)

/-- Multiplying by a `0/1` indicator inside a lintegral restricts the domain. -/
theorem lintegral_indicator_one_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {A : Set α} (hA : MeasurableSet A) (G : α → ℝ≥0∞) :
    (∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z * G z ∂μ) = ∫⁻ z in A, G z ∂μ := by
  rw [← lintegral_indicator hA]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ A <;> simp [hz]

/-- Unnormalization: the doubled lintegral against the normalized enlarged-cube
measure is the volume-normalized product set-lintegral. -/
theorem double_lintegral_normalized_eq (S : TriadicCube d) {pr : ℝ}
    {u : Vec d → ℝ} (humeas : Measurable u) :
    (∫⁻ x, ∫⁻ y, ‖u x - u y‖ₑ ^ pr ∂(ScalarOverlap.normalizedCubeMeasure S)
        ∂(ScalarOverlap.normalizedCubeMeasure S)) =
      ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
        (ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
          ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
            ‖u z.1 - u z.2‖ₑ ^ pr ∂(volume.prod volume)) := by
  have hF : Measurable fun z : Vec d × Vec d => ‖u z.1 - u z.2‖ₑ ^ pr :=
    measurable_pair_diff_enorm_rpow humeas pr
  have hTonelli :
      (∫⁻ x in ScalarOverlap.cubeSet S, ∫⁻ y in ScalarOverlap.cubeSet S,
          ‖u x - u y‖ₑ ^ pr ∂volume ∂volume) =
        ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
          ‖u z.1 - u z.2‖ₑ ^ pr ∂(volume.prod volume) := by
    rw [← Measure.prod_restrict]
    exact (MeasureTheory.lintegral_prod _ hF.aemeasurable).symm
  calc (∫⁻ x, ∫⁻ y, ‖u x - u y‖ₑ ^ pr ∂(ScalarOverlap.normalizedCubeMeasure S)
        ∂(ScalarOverlap.normalizedCubeMeasure S))
      = ∫⁻ x, ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
          ∫⁻ y in ScalarOverlap.cubeSet S, ‖u x - u y‖ₑ ^ pr ∂volume
          ∂(ScalarOverlap.normalizedCubeMeasure S) :=
        lintegral_congr fun x =>
          ScalarOverlap.lintegral_normalizedCubeMeasure_eq S _
    _ = ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
          ∫⁻ x, (∫⁻ y in ScalarOverlap.cubeSet S, ‖u x - u y‖ₑ ^ pr ∂volume)
            ∂(ScalarOverlap.normalizedCubeMeasure S) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
          (ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
            ∫⁻ x in ScalarOverlap.cubeSet S, ∫⁻ y in ScalarOverlap.cubeSet S,
              ‖u x - u y‖ₑ ^ pr ∂volume ∂volume) := by
        rw [ScalarOverlap.lintegral_normalizedCubeMeasure_eq S]
    _ = ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
          (ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
            ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
              ‖u z.1 - u z.2‖ₑ ^ pr ∂(volume.prod volume)) := by
        rw [hTonelli]

/-- Per-center bound (U1 + U2): the `p`-th power of the overlap oscillation is
controlled by the volume-normalized product set-lintegral of differences. -/
theorem ofReal_oscillation_rpow_le_setProd (S : TriadicCube d) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞) {u : Vec d → ℝ} (humeas : Measurable u)
    (hu : MemLp u p (ScalarOverlap.normalizedCubeMeasure S)) :
    ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) ≤
      ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
        (ENNReal.ofReal ((ScalarOverlap.cubeVolume S)⁻¹) *
          ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
            ‖u z.1 - u z.2‖ₑ ^ p.toReal ∂(volume.prod volume)) :=
  (ofReal_oscillation_rpow_le S p u).trans
    ((eLpNorm_sub_average_rpow_le_double_lintegral S hp hpt hu).trans
      (double_lintegral_normalized_eq S humeas).le)

/-- Real coefficient identity for one depth: weight power times the depth
count inverse times the squared volume inverse collapses to the parent volume
inverse times the kernel scale power. -/
theorem depth_coeff_identity {cQ : ℝ} (hc : 0 < cQ) (d j : ℕ) (t : ℝ) :
    (cQ / 3 ^ j) ^ (-t) *
        (((3 : ℝ) ^ (d * j))⁻¹ *
          (((cQ / 3 ^ j) ^ d)⁻¹ * ((cQ / 3 ^ j) ^ d)⁻¹)) =
      (cQ ^ d)⁻¹ * (cQ / 3 ^ j) ^ (-(t + (d : ℝ))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have he : (0 : ℝ) < cQ / 3 ^ j := div_pos hc (pow_pos h3 j)
  have hlog : Real.log (cQ / 3 ^ j) = Real.log cQ - j * Real.log 3 := by
    rw [Real.log_div hc.ne' (pow_ne_zero j h3.ne'), Real.log_pow]
  rw [← Real.rpow_natCast (cQ / 3 ^ j) d, ← Real.rpow_natCast (3 : ℝ) (d * j),
    ← Real.rpow_natCast cQ d]
  simp only [Real.rpow_def_of_pos he, Real.rpow_def_of_pos hc,
    Real.rpow_def_of_pos h3, ← Real.exp_neg, ← Real.exp_add]
  rw [Real.exp_eq_exp, hlog]
  push_cast
  ring

/-- Depth coefficient bound: weight power times center-count inverse times the
squared per-cube volume normalization is at most the parent volume inverse
times the kernel scale power. -/
theorem depth_coefficient_le (Q : TriadicCube d) (j : ℕ) (s pr : ℝ) :
    ENNReal.ofReal (cubeBesovOverlapDepthWeight Q s j ^ pr) *
        (((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal (((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹) *
            ENNReal.ofReal (((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹))) ≤
      ENNReal.ofReal ((cubeVolume Q)⁻¹) *
        ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr + (d : ℝ)))) := by
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hcQ : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  have he : (0 : ℝ) < cubeScaleFactor Q / 3 ^ j := div_pos hcQ (pow_pos h3 j)
  -- the center count dominates `3^(d*j)`
  have hcard_nat : 3 ^ (d * j) ≤ (ScalarOverlap.centersAtDepth Q j).card := by
    calc 3 ^ (d * j) = (3 ^ d) ^ j := by rw [pow_mul]
      _ = (descendantsAtDepth Q j).card := (descendantsAtDepth_card Q j).symm
      _ ≤ (ScalarOverlap.centersAtDepth Q j).card :=
          ScalarOverlap.descendantsAtDepth_card_le_centersAtDepth_card Q j
  have hcard : ((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ ≤
      ENNReal.ofReal (((3 : ℝ) ^ (d * j))⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos (pow_pos h3 _)]
    refine ENNReal.inv_le_inv' ?_
    have hcast : ENNReal.ofReal ((3 : ℝ) ^ (d * j)) =
        ((3 ^ (d * j) : ℕ) : ℝ≥0∞) := by
      rw [← ENNReal.ofReal_natCast]
      congr 1
      push_cast
      ring
    rw [hcast]
    exact_mod_cast hcard_nat
  -- unfold the weight power
  have hw : cubeBesovOverlapDepthWeight Q s j ^ pr =
      (cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr)) := by
    unfold cubeBesovOverlapDepthWeight cubeBesovDepthWeight
    rw [← Real.rpow_mul he.le, neg_mul]
  -- nonnegativity facts for `ofReal` multiplication
  have hw0 : (0 : ℝ) ≤ (cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr)) :=
    Real.rpow_nonneg he.le _
  have h30 : (0 : ℝ) ≤ ((3 : ℝ) ^ (d * j))⁻¹ :=
    inv_nonneg.2 (pow_nonneg h3.le _)
  have hv0 : (0 : ℝ) ≤ ((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹ :=
    inv_nonneg.2 (pow_nonneg he.le _)
  calc ENNReal.ofReal (cubeBesovOverlapDepthWeight Q s j ^ pr) *
        (((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          (ENNReal.ofReal (((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹) *
            ENNReal.ofReal (((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹)))
      ≤ ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr))) *
        (ENNReal.ofReal (((3 : ℝ) ^ (d * j))⁻¹) *
          (ENNReal.ofReal (((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹) *
            ENNReal.ofReal (((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹))) := by
        rw [hw]
        exact mul_le_mul_right (mul_le_mul_left hcard _) _
    _ = ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr)) *
          (((3 : ℝ) ^ (d * j))⁻¹ *
            (((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹ *
              ((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹))) := by
        rw [ENNReal.ofReal_mul hw0, ENNReal.ofReal_mul h30,
          ENNReal.ofReal_mul hv0]
    _ = ENNReal.ofReal (((cubeScaleFactor Q) ^ d)⁻¹ *
          (cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr + (d : ℝ)))) := by
        rw [depth_coeff_identity hcQ d j (s * pr)]
    _ = ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * pr + (d : ℝ)))) := by
        rw [cubeVolume_eq_scaleFactor_pow,
          ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg hcQ.le d))]

/-- Per-depth bound: the `p`-th power of one depth seminorm is controlled by
the kernel-scale-weighted sum of product set-lintegrals over the centers. -/
theorem ofReal_depthSeminorm_rpow_le_sum (Q : TriadicCube d) {s : ℝ}
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) {u : Vec d → ℝ}
    (humeas : Measurable u) (hu : MemLp u p (normalizedCubeMeasure Q))
    (j : ℕ) :
    ENNReal.ofReal (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal) ≤
      ENNReal.ofReal ((cubeVolume Q)⁻¹) *
        (ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * p.toReal + (d : ℝ)))) *
          ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
            ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
              ‖u z.1 - u z.2‖ₑ ^ p.toReal ∂(volume.prod volume)) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  set v : ℝ≥0∞ := ENNReal.ofReal (((cubeScaleFactor Q / 3 ^ j) ^ d)⁻¹) with hv_def
  set I : TriadicCube d → ℝ≥0∞ := fun S =>
    ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
      ‖u z.1 - u z.2‖ₑ ^ p.toReal ∂(volume.prod volume) with hI_def
  -- per-center bound with the constant volume factor
  have hper : ∀ S ∈ ScalarOverlap.centersAtDepth Q j,
      ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal) ≤
        v * (v * I S) := by
    intro S hS
    have hvol : ScalarOverlap.cubeVolume S =
        (cubeScaleFactor Q / 3 ^ j) ^ d := by
      unfold ScalarOverlap.cubeVolume
      rw [ScalarOverlap.scaleFactor_eq_cubeScaleFactor_div_pow_of_mem_centersAtDepth hS]
    have h := ofReal_oscillation_rpow_le_setProd S hp hpt humeas
      (memLp_overlap_of_memLp hu hS)
    rwa [hvol] at h
  rw [ofReal_depthSeminorm_rpow_eq Q s hp0 hpt u j,
    ofReal_depthAverage_eq Q j p u]
  calc ENNReal.ofReal (cubeBesovOverlapDepthWeight Q s j ^ p.toReal) *
        (((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
            ENNReal.ofReal (cubeBesovOverlapOscillation S p u ^ p.toReal))
      ≤ ENNReal.ofReal (cubeBesovOverlapDepthWeight Q s j ^ p.toReal) *
        (((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ *
          ∑ S ∈ ScalarOverlap.centersAtDepth Q j, v * (v * I S)) :=
        mul_le_mul_right
          (mul_le_mul_right (Finset.sum_le_sum hper) _) _
    _ = (ENNReal.ofReal (cubeBesovOverlapDepthWeight Q s j ^ p.toReal) *
          (((ScalarOverlap.centersAtDepth Q j).card : ℝ≥0∞)⁻¹ * (v * v))) *
          ∑ S ∈ ScalarOverlap.centersAtDepth Q j, I S := by
        rw [← Finset.mul_sum]
        have : (∑ S ∈ ScalarOverlap.centersAtDepth Q j, v * I S) =
            v * ∑ S ∈ ScalarOverlap.centersAtDepth Q j, I S := by
          rw [← Finset.mul_sum]
        rw [this]
        ring
    _ ≤ (ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * p.toReal + (d : ℝ))))) *
          ∑ S ∈ ScalarOverlap.centersAtDepth Q j, I S :=
        mul_le_mul_left (depth_coefficient_le Q j s p.toReal) _
    _ = ENNReal.ofReal ((cubeVolume Q)⁻¹) *
        (ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * p.toReal + (d : ℝ)))) *
          ∑ S ∈ ScalarOverlap.centersAtDepth Q j, I S) := by
        rw [mul_assoc]

/-- Sum of product set-lintegrals over the depth-`j` centers as one lintegral
against the pointwise overlap count. -/
theorem sum_setLIntegral_eq_lintegral_count (Q : TriadicCube d) (j : ℕ)
    {F : Vec d × Vec d → ℝ≥0∞} (hF : Measurable F) :
    (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
        ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S, F z
          ∂(volume.prod volume)) =
      ∫⁻ z, (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
            (fun _ => (1 : ℝ≥0∞)) z) * F z ∂(volume.prod volume) := by
  classical
  have hstep1 :
      (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S, F z
            ∂(volume.prod volume)) =
        ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          ∫⁻ z, (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
              (fun _ => (1 : ℝ≥0∞)) z * F z ∂(volume.prod volume) :=
    Finset.sum_congr rfl fun S _hS =>
      (lintegral_indicator_one_mul (measurableSet_overlap_prod S) F).symm
  have hstep2 :
      (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          ∫⁻ z, (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
              (fun _ => (1 : ℝ≥0∞)) z * F z ∂(volume.prod volume)) =
        ∫⁻ z, ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
            (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
                (fun _ => (1 : ℝ≥0∞)) z * F z ∂(volume.prod volume) :=
    (lintegral_finsetSum (ScalarOverlap.centersAtDepth Q j) fun S _hS =>
      (measurable_const.indicator (measurableSet_overlap_prod S)).mul hF).symm
  rw [hstep1, hstep2]
  exact lintegral_congr fun z => (Finset.sum_mul _ _ _).symm

/-- Backwards geometric tail: over depths whose enlarged side dominates a fixed
positive distance `D`, the kernel scale powers sum to at most `2 * D^(-a)`. -/
theorem filtered_scale_sum_le (Q : TriadicCube d) {a : ℝ} (ha : 1 ≤ a)
    {D : ℝ} (hD : 0 < D) (N : ℕ) :
    (∑ j ∈ (Finset.range (N + 1)).filter
        (fun j => D ≤ cubeScaleFactor Q / 3 ^ j),
      ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-a))) ≤
      2 * ENNReal.ofReal (D ^ (-a)) := by
  classical
  have h3 : (0 : ℝ) < 3 := by norm_num
  have hcQ : 0 < cubeScaleFactor Q := cubeScaleFactor_pos' Q
  set q : ℝ≥0∞ := ENNReal.ofReal ((3 : ℝ) ^ a) with hq_def
  set M : ℝ≥0∞ := ENNReal.ofReal ((cubeScaleFactor Q / D) ^ a) with hM_def
  -- exponent swap for the two `3`-power readings
  have hswap : ∀ j : ℕ, ((3 : ℝ) ^ j) ^ a = ((3 : ℝ) ^ a) ^ j := by
    intro j
    rw [← Real.rpow_natCast_mul h3.le j a, ← Real.rpow_mul_natCast h3.le a j,
      mul_comm]
  -- split each scale power into the parent factor times a geometric term
  have hsplit : ∀ j : ℕ,
      ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-a)) =
        ENNReal.ofReal (cubeScaleFactor Q ^ (-a)) * q ^ j := by
    intro j
    have h1 : (cubeScaleFactor Q / 3 ^ j : ℝ) ^ (-a) =
        cubeScaleFactor Q ^ (-a) * ((3 : ℝ) ^ a) ^ j := by
      rw [Real.div_rpow hcQ.le (pow_nonneg h3.le j),
        Real.rpow_neg (pow_nonneg h3.le j), div_inv_eq_mul, hswap j]
    rw [h1, ENNReal.ofReal_mul (Real.rpow_nonneg hcQ.le _),
      ENNReal.ofReal_pow (Real.rpow_nonneg h3.le _)]
  -- ratio facts
  have hq3 : (3 : ℝ≥0∞) ≤ q := by
    have h33 : ((3 : ℝ≥0∞)) = ENNReal.ofReal (3 : ℝ) := by simp
    rw [h33]
    refine ENNReal.ofReal_le_ofReal ?_
    calc (3 : ℝ) = 3 ^ (1 : ℝ) := (Real.rpow_one 3).symm
      _ ≤ 3 ^ a := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha
  have hqt : q ≠ ∞ := ENNReal.ofReal_ne_top
  -- each retained geometric term is bounded by `M`
  have hM : ∀ j ∈ (Finset.range (N + 1)).filter
      (fun j => D ≤ cubeScaleFactor Q / 3 ^ j), q ^ j ≤ M := by
    intro j hj
    have hd : D ≤ cubeScaleFactor Q / 3 ^ j := (Finset.mem_filter.mp hj).2
    have h3j : (3 : ℝ) ^ j ≤ cubeScaleFactor Q / D := by
      rw [le_div_iff₀ hD]
      have h1 : D * 3 ^ j ≤ cubeScaleFactor Q :=
        (le_div_iff₀ (pow_pos h3 j)).1 hd
      calc (3 : ℝ) ^ j * D = D * 3 ^ j := mul_comm _ _
        _ ≤ cubeScaleFactor Q := h1
    have hpow : ((3 : ℝ) ^ j) ^ a ≤ (cubeScaleFactor Q / D) ^ a :=
      Real.rpow_le_rpow (pow_nonneg h3.le j) h3j (by linarith)
    calc q ^ j = ENNReal.ofReal (((3 : ℝ) ^ a) ^ j) :=
          (ENNReal.ofReal_pow (Real.rpow_nonneg h3.le _) j).symm
      _ = ENNReal.ofReal (((3 : ℝ) ^ j) ^ a) := by rw [hswap j]
      _ ≤ M := ENNReal.ofReal_le_ofReal hpow
  have htail := sum_pow_le_two_mul_of_forall_le hq3 hqt hM
  calc (∑ j ∈ (Finset.range (N + 1)).filter
        (fun j => D ≤ cubeScaleFactor Q / 3 ^ j),
      ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-a)))
      = ∑ j ∈ (Finset.range (N + 1)).filter
          (fun j => D ≤ cubeScaleFactor Q / 3 ^ j),
        ENNReal.ofReal (cubeScaleFactor Q ^ (-a)) * q ^ j :=
        Finset.sum_congr rfl fun j _ => hsplit j
    _ = ENNReal.ofReal (cubeScaleFactor Q ^ (-a)) *
        ∑ j ∈ (Finset.range (N + 1)).filter
          (fun j => D ≤ cubeScaleFactor Q / 3 ^ j), q ^ j :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ ENNReal.ofReal (cubeScaleFactor Q ^ (-a)) * (2 * M) :=
        mul_le_mul_right htail _
    _ = 2 * (ENNReal.ofReal (cubeScaleFactor Q ^ (-a)) * M) := by ring
    _ = 2 * ENNReal.ofReal (D ^ (-a)) := by
        rw [hM_def, ← ENNReal.ofReal_mul (Real.rpow_nonneg hcQ.le _)]
        congr 1
        rw [Real.div_rpow hcQ.le hD.le, Real.rpow_neg hcQ.le,
          Real.rpow_neg hD.le, div_eq_mul_inv, ← mul_assoc,
          inv_mul_cancel₀ (Real.rpow_pos_of_pos hcQ a).ne', one_mul]

/-- Pointwise pair bound: for each pair `z`, the depth sum of kernel-scale
powers times overlap counts times the difference power is controlled by the
distance power on the parent product cube, with constant `2 * 3^d`. -/
theorem pointwise_pair_sum_le (Q : TriadicCube d) {a pr : ℝ} (ha : 1 ≤ a)
    (hpr : 0 < pr) (u : Vec d → ℝ) (N : ℕ) (z : Vec d × Vec d) :
    (∑ j ∈ Finset.range (N + 1),
        ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-a)) *
          ((∑ S ∈ ScalarOverlap.centersAtDepth Q j,
              (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
                (fun _ => (1 : ℝ≥0∞)) z) *
            ‖u z.1 - u z.2‖ₑ ^ pr)) ≤
      2 * 3 ^ d *
        ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
            (fun _ => (1 : ℝ≥0∞)) z *
          (ENNReal.ofReal (dist z.1 z.2 ^ (-a)) * ‖u z.1 - u z.2‖ₑ ^ pr)) := by
  classical
  by_cases hz : z.1 = z.2
  · -- diagonal: the difference power vanishes
    have hFz : ‖u z.1 - u z.2‖ₑ ^ pr = 0 := by
      rw [hz, sub_self, enorm_zero]
      exact ENNReal.zero_rpow_of_pos hpr
    simp [hFz]
  · have hdist : 0 < dist z.1 z.2 := dist_pos.2 hz
    -- per-depth bound, filtered by the scale capture condition
    have hterm : ∀ j ∈ Finset.range (N + 1),
        ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-a)) *
          ((∑ S ∈ ScalarOverlap.centersAtDepth Q j,
              (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
                (fun _ => (1 : ℝ≥0∞)) z) *
            ‖u z.1 - u z.2‖ₑ ^ pr) ≤
          (if dist z.1 z.2 ≤ cubeScaleFactor Q / 3 ^ j then
              ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-a))
            else 0) *
            ((3 : ℝ≥0∞) ^ d *
              ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
                  (fun _ => (1 : ℝ≥0∞)) z *
                ‖u z.1 - u z.2‖ₑ ^ pr)) := by
      intro j _hj
      by_cases hcnt : (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
          (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
            (fun _ => (1 : ℝ≥0∞)) z) = 0
      · rw [hcnt, zero_mul, mul_zero]
        exact zero_le
      · -- a nonzero count produces a capturing center
        obtain ⟨S, hS, hSne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hcnt
        have hzS : z ∈ ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S := by
          by_contra hmem
          exact hSne (Set.indicator_of_notMem hmem _)
        have hd : dist z.1 z.2 ≤ cubeScaleFactor Q / 3 ^ j := by
          calc dist z.1 z.2 ≤ 3 * cubeScaleFactor S :=
                dist_le_of_mem_overlapCubeSet hzS.1 hzS.2
            _ = ScalarOverlap.scaleFactor S := rfl
            _ = cubeScaleFactor Q / 3 ^ j :=
                ScalarOverlap.scaleFactor_eq_cubeScaleFactor_div_pow_of_mem_centersAtDepth hS
        rw [if_pos hd]
        refine mul_le_mul_right ?_ _
        calc (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
              (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
                (fun _ => (1 : ℝ≥0∞)) z) * ‖u z.1 - u z.2‖ₑ ^ pr
            ≤ ((3 : ℝ≥0∞) ^ d *
                (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
                  (fun _ => (1 : ℝ≥0∞)) z) * ‖u z.1 - u z.2‖ₑ ^ pr :=
              mul_le_mul_left (sum_indicator_overlap_prod_le Q j z) _
          _ = (3 : ℝ≥0∞) ^ d *
              ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
                  (fun _ => (1 : ℝ≥0∞)) z * ‖u z.1 - u z.2‖ₑ ^ pr) :=
              mul_assoc _ _ _
    -- sum the per-depth bounds and run the geometric tail
    calc (∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-a)) *
            ((∑ S ∈ ScalarOverlap.centersAtDepth Q j,
                (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
                  (fun _ => (1 : ℝ≥0∞)) z) *
              ‖u z.1 - u z.2‖ₑ ^ pr))
        ≤ ∑ j ∈ Finset.range (N + 1),
            (if dist z.1 z.2 ≤ cubeScaleFactor Q / 3 ^ j then
                ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-a))
              else 0) *
              ((3 : ℝ≥0∞) ^ d *
                ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
                    (fun _ => (1 : ℝ≥0∞)) z *
                  ‖u z.1 - u z.2‖ₑ ^ pr)) :=
          Finset.sum_le_sum hterm
      _ = (∑ j ∈ (Finset.range (N + 1)).filter
            (fun j => dist z.1 z.2 ≤ cubeScaleFactor Q / 3 ^ j),
            ENNReal.ofReal ((cubeScaleFactor Q / 3 ^ j) ^ (-a))) *
            ((3 : ℝ≥0∞) ^ d *
              ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
                  (fun _ => (1 : ℝ≥0∞)) z *
                ‖u z.1 - u z.2‖ₑ ^ pr)) := by
          rw [Finset.sum_filter, Finset.sum_mul]
      _ ≤ (2 * ENNReal.ofReal (dist z.1 z.2 ^ (-a))) *
            ((3 : ℝ≥0∞) ^ d *
              ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
                  (fun _ => (1 : ℝ≥0∞)) z *
                ‖u z.1 - u z.2‖ₑ ^ pr)) :=
          mul_le_mul_left (filtered_scale_sum_le Q ha hdist N) _
      _ = 2 * 3 ^ d *
            ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
                (fun _ => (1 : ℝ≥0∞)) z *
              (ENNReal.ofReal (dist z.1 z.2 ^ (-a)) *
                ‖u z.1 - u z.2‖ₑ ^ pr)) := by
          ring

/-- **Besov-to-Gagliardo comparison** (truncated form): the `p`-th power of
the diagonal overlap Besov partial seminorm is at most `2 * 3^d` times the
`p`-th power of the volume-normalized Gagliardo seminorm, uniformly in the
truncation depth `N`. -/
theorem ofReal_partialSeminorm_rpow_le_gagliardo [NeZero d]
    (Q : TriadicCube d) {s : ℝ} (hs : 0 ≤ s) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) {u : Vec d → ℝ} (humeas : Measurable u)
    (hu : MemLp u p (normalizedCubeMeasure Q)) (N : ℕ) :
    ENNReal.ofReal (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal) ≤
      2 * 3 ^ d * cubeGagliardoESeminorm Q s p u ^ p.toReal := by
  classical
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have ha1 : 1 ≤ s * p.toReal + (d : ℝ) := by
    have := mul_nonneg hs hpr.le
    linarith
  have hF : Measurable fun z : Vec d × Vec d => ‖u z.1 - u z.2‖ₑ ^ p.toReal :=
    measurable_pair_diff_enorm_rpow humeas _
  have hQQ : MeasurableSet
      (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q) :=
    (Homogenization.measurableSet_cubeSet Q).prod
      (Homogenization.measurableSet_cubeSet Q)
  have h23top : (2 * 3 ^ d : ℝ≥0∞) ≠ ∞ :=
    ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp))
  calc ENNReal.ofReal (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal)
      = ∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal (cubeBesovOverlapDepthSeminorm Q s p u j ^ p.toReal) :=
        ofReal_partialSeminorm_rpow_eq Q s hp0 hpt N u
    _ ≤ ∑ j ∈ Finset.range (N + 1),
          ENNReal.ofReal ((cubeVolume Q)⁻¹) *
            (ENNReal.ofReal
                ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * p.toReal + (d : ℝ)))) *
              ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
                ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
                  ‖u z.1 - u z.2‖ₑ ^ p.toReal ∂(volume.prod volume)) :=
        Finset.sum_le_sum fun j _hj =>
          ofReal_depthSeminorm_rpow_le_sum Q hp hpt humeas hu j
    _ = ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ∑ j ∈ Finset.range (N + 1),
            ENNReal.ofReal
                ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * p.toReal + (d : ℝ)))) *
              ∑ S ∈ ScalarOverlap.centersAtDepth Q j,
                ∫⁻ z in ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S,
                  ‖u z.1 - u z.2‖ₑ ^ p.toReal ∂(volume.prod volume) :=
        (Finset.mul_sum _ _ _).symm
    _ = ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ∑ j ∈ Finset.range (N + 1),
            ENNReal.ofReal
                ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * p.toReal + (d : ℝ)))) *
              ∫⁻ z, (∑ S ∈ ScalarOverlap.centersAtDepth Q j,
                  (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
                    (fun _ => (1 : ℝ≥0∞)) z) *
                ‖u z.1 - u z.2‖ₑ ^ p.toReal ∂(volume.prod volume) := by
        congr 1
        refine Finset.sum_congr rfl fun j _hj => ?_
        rw [sum_setLIntegral_eq_lintegral_count Q j hF]
    _ = ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ∑ j ∈ Finset.range (N + 1),
            ∫⁻ z, ENNReal.ofReal
                ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * p.toReal + (d : ℝ)))) *
              ((∑ S ∈ ScalarOverlap.centersAtDepth Q j,
                  (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
                    (fun _ => (1 : ℝ≥0∞)) z) *
                ‖u z.1 - u z.2‖ₑ ^ p.toReal) ∂(volume.prod volume) := by
        congr 1
        refine Finset.sum_congr rfl fun j _hj => ?_
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ∫⁻ z, ∑ j ∈ Finset.range (N + 1),
            ENNReal.ofReal
                ((cubeScaleFactor Q / 3 ^ j) ^ (-(s * p.toReal + (d : ℝ)))) *
              ((∑ S ∈ ScalarOverlap.centersAtDepth Q j,
                  (ScalarOverlap.cubeSet S ×ˢ ScalarOverlap.cubeSet S).indicator
                    (fun _ => (1 : ℝ≥0∞)) z) *
                ‖u z.1 - u z.2‖ₑ ^ p.toReal) ∂(volume.prod volume) := by
        congr 1
        exact (lintegral_finsetSum (Finset.range (N + 1)) fun j _hj =>
          measurable_const.mul
            ((Finset.measurable_sum _ fun S _hS =>
              measurable_const.indicator (measurableSet_overlap_prod S)).mul hF)).symm
    _ ≤ ENNReal.ofReal ((cubeVolume Q)⁻¹) *
          ∫⁻ z, 2 * 3 ^ d *
            ((Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
                (fun _ => (1 : ℝ≥0∞)) z *
              (ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + (d : ℝ)))) *
                ‖u z.1 - u z.2‖ₑ ^ p.toReal)) ∂(volume.prod volume) :=
        mul_le_mul_right
          (lintegral_mono fun z => pointwise_pair_sum_le Q ha1 hpr u N z) _
    _ = 2 * 3 ^ d *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) *
            ∫⁻ z, (Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q).indicator
                (fun _ => (1 : ℝ≥0∞)) z *
              (ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + (d : ℝ)))) *
                ‖u z.1 - u z.2‖ₑ ^ p.toReal) ∂(volume.prod volume)) := by
        rw [lintegral_const_mul' (2 * 3 ^ d : ℝ≥0∞) _ h23top]
        ring
    _ = 2 * 3 ^ d *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) *
            ∫⁻ z in Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q,
              ENNReal.ofReal (dist z.1 z.2 ^ (-(s * p.toReal + (d : ℝ)))) *
                ‖u z.1 - u z.2‖ₑ ^ p.toReal ∂(volume.prod volume)) := by
        rw [lintegral_indicator_one_mul hQQ]
    _ = 2 * 3 ^ d *
          (ENNReal.ofReal ((cubeVolume Q)⁻¹) *
            ∫⁻ z in Homogenization.cubeSet Q ×ˢ Homogenization.cubeSet Q,
              ‖gagliardoKernel s p u z‖ₑ ^ p.toReal ∂(volume.prod volume)) := by
        congr 2
        exact lintegral_congr fun z =>
          (enorm_gagliardoKernel_rpow s hp0 hpt u z).symm
    _ = 2 * 3 ^ d *
          ∫⁻ z, ‖gagliardoKernel s p u z‖ₑ ^ p.toReal
            ∂gagliardoCubeMeasure Q := by
        rw [lintegral_gagliardoCubeMeasure_eq Q]
    _ = 2 * 3 ^ d * cubeGagliardoESeminorm Q s p u ^ p.toReal := by
        congr 1
        rw [Internal.cubeGagliardoESeminorm_eq_lintegral hp0 hpt,
          ← ENNReal.rpow_mul, one_div_mul_cancel hpr.ne', ENNReal.rpow_one]

/-- Corollary: when the Gagliardo seminorm is finite, the set of partial
overlap Besov seminorm values is bounded above (uniformly in the depth). -/
theorem besovOverlapSeminormValueSet_bddAbove_of_gagliardo [NeZero d]
    (Q : TriadicCube d) {s : ℝ} (hs : 0 ≤ s) {p : ℝ≥0∞} (hp : 1 ≤ p)
    (hpt : p ≠ ∞) {u : Vec d → ℝ} (humeas : Measurable u)
    (hu : MemLp u p (normalizedCubeMeasure Q))
    (hfin : cubeGagliardoESeminorm Q s p u ≠ ∞) :
    BddAbove (cubeBesovOverlapSeminormValueSet Q s p p u) := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans_le hp).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hpt
  have hBt : (2 * 3 ^ d * cubeGagliardoESeminorm Q s p u ^ p.toReal : ℝ≥0∞)
      ≠ ∞ :=
    ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (by simp) (ENNReal.pow_ne_top (by simp)))
      (ENNReal.rpow_ne_top_of_nonneg hpr.le hfin)
  refine ⟨(2 * 3 ^ d * cubeGagliardoESeminorm Q s p u ^ p.toReal
      : ℝ≥0∞).toReal ^ (p.toReal)⁻¹, ?_⟩
  rintro x ⟨N, rfl⟩
  have hmain := ofReal_partialSeminorm_rpow_le_gagliardo Q hs hp hpt humeas hu N
  have hreal : cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal ≤
      (2 * 3 ^ d * cubeGagliardoESeminorm Q s p u ^ p.toReal : ℝ≥0∞).toReal :=
    (ENNReal.ofReal_le_iff_le_toReal hBt).1 hmain
  have hnn : 0 ≤ cubeBesovOverlapPartialSeminorm Q s p p N u :=
    cubeBesovOverlapPartialSeminorm_nonneg Q s p p N u
  calc cubeBesovOverlapPartialSeminorm Q s p p N u
      = (cubeBesovOverlapPartialSeminorm Q s p p N u ^ p.toReal)
          ^ (p.toReal)⁻¹ :=
        (Real.rpow_rpow_inv hnn hpr.ne').symm
    _ ≤ ((2 * 3 ^ d * cubeGagliardoESeminorm Q s p u ^ p.toReal
          : ℝ≥0∞).toReal) ^ (p.toReal)⁻¹ :=
        Real.rpow_le_rpow (Real.rpow_nonneg hnn _) hreal (inv_nonneg.2 hpr.le)

end

end Gagliardo
end Homogenization
