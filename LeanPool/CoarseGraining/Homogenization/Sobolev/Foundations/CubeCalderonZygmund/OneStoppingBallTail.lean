/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.OneStoppingBallComparison
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.OneBallTailAlgebra
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.OneBallScaleFactor

/-! # One Stopping Ball Tail -/

namespace Homogenization

open scoped ENNReal

noncomputable section

namespace CubeCalderonZygmund

open Filter MeasureTheory Set

/-!
# Geometric and measure-local preparation for the one-stopping-ball tail

The final tail comparison is made on the open depth descendant.  These lemmas
keep the two nontrivial localisation facts explicit: that descendant is inside
the PDE comparison parent, and its boundary can be changed to the closed
stopping ball for any square-weighted measure based on volume.
-/

/-- The open depth descendant lies in its comparison parent. -/
theorem stoppingComparison_descendant_subset_parent {d : ℕ}
    (x : Vec d) {r : ℝ} (hr : 0 < r) (depth : ℕ) :
    axisCube
        (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth) depth)
        (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth) ⊆
      axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) := by
  rw [stoppingComparison_concentricDepth_axisCube_eq_ball x hr depth,
    stoppingComparisonParent_axisCube_eq_ball x hr depth]
  intro y hy
  apply Metric.mem_ball.mpr
  have hy' : dist y x < 5 * r := Metric.mem_ball.mp hy
  calc
    dist y x < 5 * r := hy'
    _ ≤ stoppingComparisonParentMultiplier depth * r := by
      rw [stoppingComparisonParentMultiplier]
      have hp : 1 ≤ (3 : ℝ) ^ depth := one_le_pow₀ (by norm_num)
      nlinarith

/-- The final square-weighted tail may cross from the open harmonic-gain
descendant to the closed stopping ball without a comparison loss. -/
theorem sqWeightedMeasure_tail_descendant_eq_closedBall
    {d : ℕ} [NeZero d] {E : Type*} [NormedAddCommGroup E]
    (f : Vec d → E) (x : Vec d) {r : ℝ} (hr : 0 < r) (depth : ℕ)
    (T : Set (Vec d)) :
    sqWeightedMeasure f volume
        (T ∩ axisCube
          (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth) depth)
          (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth)) =
      sqWeightedMeasure f volume (T ∩ Metric.closedBall x (5 * r)) := by
  have hae := stoppingComparison_concentricDepth_axisCube_ae_eq_closedBall
    (d := d) x hr depth
  have hsq_ac : sqWeightedMeasure f volume ≪ volume :=
    MeasureTheory.withDensity_absolutelyContinuous volume _
  have hae_sq : axisCube
      (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) depth)
      (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth) =ᵐ[
        sqWeightedMeasure f volume] Metric.closedBall x (5 * r) :=
    hsq_ac.ae_eq hae
  let child : Set (Vec d) := axisCube
    (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
      (stoppingComparisonParentSide r depth) depth)
    (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth)
  have hchild_meas : MeasurableSet child := by
    rw [show child = Metric.ball x (5 * r) by
      simpa only [child] using
        (stoppingComparison_concentricDepth_axisCube_eq_ball x hr depth)]
    exact measurableSet_ball
  change (sqWeightedMeasure f volume) (T ∩ child) =
    (sqWeightedMeasure f volume) (T ∩ Metric.closedBall x (5 * r))
  rw [← Measure.restrict_apply' hchild_meas,
    ← Measure.restrict_apply' measurableSet_closedBall]
  exact congrArg (fun μ : Measure (Vec d) => μ T) (Measure.restrict_congr_set hae_sq)

/-- The depth descendant used by the harmonic gain has side `10 r`. -/
theorem stoppingComparison_descendant_side_eq {r : ℝ} (depth : ℕ) :
    axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth = 10 * r := by
  simp only [axisCubeConcentricDepthSide, stoppingComparisonParentSide,
    stoppingAxisCubeSide, stoppingComparisonParentMultiplier, zpow_neg,
    zpow_natCast]
  field_simp [pow_ne_zero depth (by norm_num : (3 : ℝ) ≠ 0)]
  ring

/-- The parent side is `10 * 3^n * r`, the raw volume factor used for the
correction-energy contribution. -/
theorem stoppingComparison_parent_side_eq {r : ℝ} (depth : ℕ) :
    stoppingComparisonParentSide r depth = 10 * (3 : ℝ) ^ depth * r := by
  simp only [stoppingComparisonParentSide, stoppingAxisCubeSide,
    stoppingComparisonParentMultiplier]
  ring

/-- On the comparison descendant, replacing the global field by the weak
solution gradient turns the comparison error into the zero-trace correction.
This is the restricted-a.e. transport used in the correction tail. -/
theorem local_lintegral_error_eq_harmonicCorrection
    {d : ℕ} {E : Type*} [NormedAddCommGroup E]
    {B : Set (Vec d)} {f v w : Vec d → E}
    (hfu : f =ᵐ[volume.restrict B] v + w) :
    (∫⁻ y in B, ENNReal.ofReal (‖f y - v y‖ ^ (2 : ℕ)) ∂volume) =
      ∫⁻ y in B, ENNReal.ofReal (‖w y‖ ^ (2 : ℕ)) ∂volume := by
  have hsub : f - v =ᵐ[volume.restrict B] w := by
    filter_upwards [hfu] with y hy
    change f y - v y = w y
    change f y = v y + w y at hy
    rw [hy]
    abel
  apply lintegral_congr_ae
  filter_upwards [hsub] with y hy
  change ENNReal.ofReal (‖(f - v) y‖ ^ (2 : ℕ)) = _
  rw [hy]

/-- The correction integral on the descendant is bounded by its exact raw
parent-cube energy. -/
theorem stoppingComparison_correction_descendant_le_parent
    {d : ℕ} [NeZero d] (x : Vec d) {r : ℝ} (hr : 0 < r) (depth : ℕ)
    (w : H10Function (axisCube (stoppingComparisonParentCorner x r depth)
      (stoppingComparisonParentSide r depth))) {B : ℝ≥0∞}
    (hB : eLpNorm (hilbertifyVecField w.toH1Function.grad) 2
      (axisCubeNormalizedMeasure (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth)) ≤ B) :
    (∫⁻ y in axisCube
      (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) depth)
      (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth),
      ENNReal.ofReal (‖hilbertifyVecField w.toH1Function.grad y‖ ^ (2 : ℕ)) ∂volume) ≤
      ENNReal.ofReal ((stoppingComparisonParentSide r depth) ^ d) * B ^ (2 : ℝ) := by
  calc
    _ ≤ ∫⁻ y in axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth),
        ENNReal.ofReal (‖hilbertifyVecField w.toH1Function.grad y‖ ^ (2 : ℕ)) ∂volume := by
          exact MeasureTheory.lintegral_mono'
            (Measure.restrict_mono
              (stoppingComparison_descendant_subset_parent x hr depth) le_rfl)
            (by intro y; rfl)
    _ ≤ _ := axisCube_lintegral_ofReal_norm_sq_le_volume_mul
      (stoppingComparisonParentCorner x r depth)
      (by
        rw [stoppingComparison_parent_side_eq]
        positivity) (hilbertifyVecField w.toH1Function.grad) hB

/-- The harmonic gain gives its raw descendant `L^q` integral with precisely
the side-`10r` volume factor. -/
theorem stoppingComparison_harmonic_raw_bound
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} (x : Vec d) {r : ℝ}
    (hr : 0 < r) (depth : ℕ) (v : Vec d → HilbertVec d) {B : ℝ≥0∞}
    (hB : eLpNorm v q.exponent (axisCubeNormalizedMeasure
      (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) depth)
      (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth)) ≤ B) :
    (∫⁻ y in axisCube
      (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) depth)
      (axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth),
      ENNReal.ofReal (‖v y‖ ^ q.exponent.toReal) ∂volume) ≤
      ENNReal.ofReal ((10 * r) ^ d) * B ^ q.exponent.toReal := by
  have h := axisCube_lintegral_ofReal_norm_rpow_le_volume_mul
    (axisCubeConcentricDepthCorner (stoppingComparisonParentCorner x r depth)
      (stoppingComparisonParentSide r depth) depth)
    (by rw [stoppingComparison_descendant_side_eq]; positivity) q v hB
  rw [stoppingComparison_descendant_side_eq] at h
  simpa only [stoppingComparison_descendant_side_eq] using h

/-- The complete one-stopping-ball weighted comparison estimate.  The
harmonic comparison is constructed from the weak equation, rather than
supplied as a hypothesis. -/
theorem sqWeightedMeasure_oneStoppingBall_le
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} {depth : ℕ}
    (G : INTERNAL.HarmonicEuclideanGradientGain d q depth)
    (hq : 2 < q.exponent.toReal) (x : Vec d)
    {r R sigma0 eps M level : ℝ}
    (hr : 0 < r) (hsigma0 : 0 < sigma0) (heps : 0 < eps)
    (heps_one : eps ≤ 1) (hM : 0 < M) (hlevel : 0 < level)
    (hcutoff : r ≤ R / (10 * (3 : ℝ) ^ depth))
    (f : Vec d → HilbertVec d) (H : Vec d → Vec d)
    (hf : MemLp f 2 volume) (hH : MemLp (hilbertifyVecField H) 2 volume)
    (u : H1Function (axisCube (stoppingComparisonParentCorner x r depth)
      (stoppingComparisonParentSide r depth)))
    (hfu : f =ᵐ[volume.restrict
      (axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth))] hilbertifyVecField u.grad)
    (hweak : ∀ phi : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) phi → HasCompactSupport phi →
      tsupport phi ⊆ axisCube (stoppingComparisonParentCorner x r depth)
        (stoppingComparisonParentSide r depth) →
      sigma0 * ∫ y in axisCube (stoppingComparisonParentCorner x r depth)
          (stoppingComparisonParentSide r depth),
        vecDot (u.grad y) (euclideanGradient phi y) ∂volume =
          -∫ y in axisCube (stoppingComparisonParentCorner x r depth)
            (stoppingComparisonParentSide r depth),
            vecDot (H y) (euclideanGradient phi y) ∂volume)
    (hstop : goodLambdaCombinedEnergy f (sigma0⁻¹ • hilbertifyVecField H)
      eps x r = level)
    (hlast : ∀ s ∈ Icc r R,
      goodLambdaCombinedEnergy f (sigma0⁻¹ • hilbertifyVecField H) eps x s ≤ level) :
    sqWeightedMeasure f volume ({y | M * level < ‖f y‖} ∩ Metric.closedBall x (5 * r)) ≤
      oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure f volume ({y | level / 2 < ‖f y‖} ∩ Metric.closedBall x r) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField H) volume
              ({y | eps * level / 2 < ‖(sigma0⁻¹ • hilbertifyVecField H) y‖} ∩
                Metric.closedBall x r)) := by
  let parent : Set (Vec d) := axisCube (stoppingComparisonParentCorner x r depth)
    (stoppingComparisonParentSide r depth)
  let z : Vec d := axisCubeConcentricDepthCorner
    (stoppingComparisonParentCorner x r depth) (stoppingComparisonParentSide r depth) depth
  let L : ℝ := axisCubeConcentricDepthSide (stoppingComparisonParentSide r depth) depth
  let child : Set (Vec d) := axisCube z L
  obtain ⟨w, hwHarm, hwL2, hvMem, hvBound⟩ :=
    exists_stoppingComparison_harmonic_remainder G x hr hsigma0 heps heps_one
      hcutoff f H hf hH u hfu hweak hlast
  let v : Vec d → HilbertVec d := hilbertifyVecField (u - w.toH1Function).grad
  have hchild_subset : child ⊆ parent := by
    simpa only [child, z, L, parent] using
      stoppingComparison_descendant_subset_parent x hr depth
  have hfu_child : f =ᵐ[volume.restrict child] hilbertifyVecField u.grad :=
    Filter.Eventually.filter_mono
      (MeasureTheory.ae_mono (Measure.restrict_mono hchild_subset le_rfl)) hfu
  have hL : 0 < L := by
    rw [show L = 10 * r by simpa only [L] using
      stoppingComparison_descendant_side_eq (r := r) depth]
    positivity
  have hnormc : ENNReal.ofReal (L ^ d)⁻¹ ≠ 0 :=
    ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos hL _)))
  have hvMem' : MemLp v q.exponent (axisCubeNormalizedMeasure z L) := by
    simpa only [v, z, L] using hvMem
  have hvBound' : eLpNorm v q.exponent (axisCubeNormalizedMeasure z L) ≤
      (2 * (G.constant * (d : ℝ≥0∞))) * ENNReal.ofReal level := by
    simpa only [v, z, L] using hvBound
  have hvmeas : AEStronglyMeasurable v (volume.restrict child) := by
    rw [axisCubeNormalizedMeasure_eq_smul_volume_restrict z L hL] at hvMem'
    exact hvMem'.aestronglyMeasurable.mono_ac
      (Measure.absolutelyContinuous_smul hnormc)
  have htail := sqWeightedMeasure_tail_le_comparison_restrict
    (μ := volume) (B := child) (by
      rw [show child = Metric.ball x (5 * r) by
        simpa only [child, z, L] using
          stoppingComparison_concentricDepth_axisCube_eq_ball x hr depth]
      exact measurableSet_ball)
    (hf.aestronglyMeasurable.restrict) hvmeas hq (mul_pos hM hlevel)
  rw [sqWeightedMeasure_tail_descendant_eq_closedBall f x hr depth
    {y | M * level < ‖f y‖}] at htail
  have hfvw : f =ᵐ[volume.restrict child]
      v + hilbertifyVecField w.toH1Function.grad := by
    filter_upwards [hfu_child] with y hy
    rw [hy]
    change HilbertVec.ofVec (u.grad y) =
      HilbertVec.ofVec ((u - w.toH1Function).grad y) +
        HilbertVec.ofVec (w.toH1Function.grad y)
    rw [H1Function.sub_grad]
    change WithLp.toLp 2 (u.grad y) =
      WithLp.toLp 2 (u.grad y - w.toH1Function.grad y) +
        WithLp.toLp 2 (w.toH1Function.grad y)
    rw [WithLp.toLp_sub]
    abel
  have herror :
      (∫⁻ y in child, ENNReal.ofReal (‖f y - v y‖ ^ (2 : ℕ)) ∂volume) =
        ∫⁻ y in child,
          ENNReal.ofReal (‖hilbertifyVecField w.toH1Function.grad y‖ ^ (2 : ℕ)) ∂volume :=
    local_lintegral_error_eq_harmonicCorrection hfvw
  have hcorrection_raw :
      (∫⁻ y in child,
        ENNReal.ofReal (‖hilbertifyVecField w.toH1Function.grad y‖ ^ (2 : ℕ)) ∂volume) ≤
        ENNReal.ofReal ((stoppingComparisonParentSide r depth) ^ d) *
          (ENNReal.ofReal (eps * level)) ^ (2 : ℝ) := by
    simpa only [child, z, L] using
      (stoppingComparison_correction_descendant_le_parent x hr depth w hwL2)
  have hcorrection_scale :
      6 * (∫⁻ y in child,
        ENNReal.ofReal (‖f y - v y‖ ^ (2 : ℕ)) ∂volume) ≤
        6 * (5 * (3 : ℝ≥0∞) ^ depth) ^ d * ENNReal.ofReal (eps ^ (2 : ℕ)) *
          ENNReal.ofReal (level ^ (2 : ℕ)) * volume (Metric.closedBall x r) := by
    rw [herror]
    calc
      6 * (∫⁻ y in child,
          ENNReal.ofReal (‖hilbertifyVecField w.toH1Function.grad y‖ ^ (2 : ℕ)) ∂volume) ≤
          6 * (ENNReal.ofReal ((stoppingComparisonParentSide r depth) ^ d) *
            (ENNReal.ofReal (eps * level)) ^ (2 : ℝ)) := by
              gcongr
      _ = 6 * (ENNReal.ofReal ((10 * (3 : ℝ) ^ depth * r) ^ d) *
            (ENNReal.ofReal (eps * level)) ^ (2 : ℝ)) := by
              rw [stoppingComparison_parent_side_eq]
      _ = _ := by
              rw [ENNReal.rpow_two]
              simpa only [mul_assoc] using
                (oneBall_correction_tail_scale_factor x hr.le heps.le hlevel.le depth)
  have hharmonic_raw :
      (∫⁻ y in child, ENNReal.ofReal (‖v y‖ ^ q.exponent.toReal) ∂volume) ≤
        ENNReal.ofReal ((10 * r) ^ d) *
          ((2 * (G.constant * (d : ℝ≥0∞))) * ENNReal.ofReal level) ^
            q.exponent.toReal := by
    simpa only [child, z, L] using
      (stoppingComparison_harmonic_raw_bound x hr depth v hvBound')
  have hA : 2 * (G.constant * (d : ℝ≥0∞)) ≠ ∞ := by
    apply ENNReal.mul_ne_top
    · norm_num
    · exact axisCube_harmonicEuclideanGradientGain_coefficient_ne_top G
  have hharmonic_scale :
      2 * ENNReal.ofReal ((M * level / 2) ^ (2 - q.exponent.toReal)) *
          (∫⁻ y in child, ENNReal.ofReal (‖v y‖ ^ q.exponent.toReal) ∂volume) ≤
        2 * (5 : ℝ≥0∞) ^ d * (2 * (G.constant * (d : ℝ≥0∞))) ^ q.exponent.toReal *
          ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) *
          ENNReal.ofReal (level ^ (2 : ℝ)) * volume (Metric.closedBall x r) := by
    calc
      2 * ENNReal.ofReal ((M * level / 2) ^ (2 - q.exponent.toReal)) *
          (∫⁻ y in child, ENNReal.ofReal (‖v y‖ ^ q.exponent.toReal) ∂volume) ≤
          2 * ENNReal.ofReal ((M * level / 2) ^ (2 - q.exponent.toReal)) *
            (ENNReal.ofReal ((10 * r) ^ d) *
              ((2 * (G.constant * (d : ℝ≥0∞))) * ENNReal.ofReal level) ^
                q.exponent.toReal) := by
              gcongr
      _ = _ := oneBall_harmonic_tail_scale_factor x hr.le hM hlevel hA
  let Kh : ℝ≥0∞ :=
    2 * (5 : ℝ≥0∞) ^ d * (2 * (G.constant * (d : ℝ≥0∞))) ^ q.exponent.toReal
  let Kc : ℝ≥0∞ := 6 * (5 * (3 : ℝ≥0∞) ^ depth) ^ d
  let m : ℝ≥0∞ := ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal))
  let e : ℝ≥0∞ := ENNReal.ofReal (eps ^ (2 : ℕ))
  let Q : ℝ≥0∞ := ENNReal.ofReal (level ^ (2 : ℕ)) * volume (Metric.closedBall x r)
  have hharmonic_local :
      2 * ENNReal.ofReal ((M * level / 2) ^ (2 - q.exponent.toReal)) *
          (∫⁻ y in child, ENNReal.ofReal (‖v y‖ ^ q.exponent.toReal) ∂volume) ≤
        Kh * m * Q := by
    simpa only [Kh, m, Q, Real.rpow_two, mul_assoc] using hharmonic_scale
  have hcorrection_local :
      6 * (∫⁻ y in child,
        ENNReal.ofReal (‖f y - v y‖ ^ (2 : ℕ)) ∂volume) ≤ Kc * e * Q := by
    simpa only [Kc, e, Q, mul_assoc] using hcorrection_scale
  have hlocal :
      sqWeightedMeasure f volume ({y | M * level < ‖f y‖} ∩ Metric.closedBall x (5 * r)) ≤
        (Kh * m + Kc * e) * Q := by
    calc
      sqWeightedMeasure f volume
          ({y | M * level < ‖f y‖} ∩ Metric.closedBall x (5 * r)) ≤
          2 * ENNReal.ofReal ((M * level / 2) ^ (2 - q.exponent.toReal)) *
              (∫⁻ y in child, ENNReal.ofReal (‖v y‖ ^ q.exponent.toReal) ∂volume) +
            6 * (∫⁻ y in child,
              ENNReal.ofReal (‖f y - v y‖ ^ (2 : ℕ)) ∂volume) := htail
      _ ≤ Kh * m * Q + Kc * e * Q :=
        add_le_add hharmonic_local hcorrection_local
      _ = (Kh * m + Kc * e) * Q := by ring
  let g : Vec d → HilbertVec d := sigma0⁻¹ • hilbertifyVecField H
  have hg : MemLp g 2 volume := by
    simpa only [g] using hH.const_smul sigma0⁻¹
  have htransfer : Q ≤
      2 * sqWeightedMeasure f volume
          ({y | level / 2 < ‖f y‖} ∩ Metric.closedBall x r) +
        2 * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) * sqWeightedMeasure g volume
          ({y | eps * level / 2 < ‖g y‖} ∩ Metric.closedBall x r) := by
    dsimp only [Q]
    exact goodLambdaCombinedEnergy_eq_tail_transfer f g heps hr
      hf.aestronglyMeasurable hg.aestronglyMeasurable
      (hf.integrable_norm_pow (by norm_num))
      (hg.integrable_norm_pow (by norm_num)) x (by simpa only [g] using hstop)
  have hpropagated :
      sqWeightedMeasure f volume ({y | M * level < ‖f y‖} ∩ Metric.closedBall x (5 * r)) ≤
        (Kh * m + Kc * e) *
          (2 * sqWeightedMeasure f volume
              ({y | level / 2 < ‖f y‖} ∩ Metric.closedBall x r) +
            2 * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) * sqWeightedMeasure g volume
              ({y | eps * level / 2 < ‖g y‖} ∩ Metric.closedBall x r)) :=
    hlocal.trans (by
      calc
        (Kh * m + Kc * e) * Q = Q * (Kh * m + Kc * e) := by ring
        _ ≤ (2 * sqWeightedMeasure f volume
              ({y | level / 2 < ‖f y‖} ∩ Metric.closedBall x r) +
            2 * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) * sqWeightedMeasure g volume
              ({y | eps * level / 2 < ‖g y‖} ∩ Metric.closedBall x r)) *
              (Kh * m + Kc * e) := by
                simpa only [mul_comm] using
                  (mul_le_mul_right htransfer (Kh * m + Kc * e))
        _ = _ := by ring)
  let Tf : ℝ≥0∞ := sqWeightedMeasure f volume
    ({y | level / 2 < ‖f y‖} ∩ Metric.closedBall x r)
  let Tg : ℝ≥0∞ := ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) * sqWeightedMeasure g volume
    ({y | eps * level / 2 < ‖g y‖} ∩ Metric.closedBall x r)
  have hfactor :
      (Kh * m + Kc * e) * (2 * Tf + 2 * Tg) ≤
        (2 * Kh + 2 * Kc) * (m + e) * (Tf + Tg) :=
    oneBall_tail_coefficient_factor Kh Kc m e Tf Tg
  have hKc : 2 * Kc = 12 * ENNReal.ofReal ((5 * (3 : ℝ) ^ depth) ^ d) := by
    dsimp only [Kc]
    have hP : (5 * (3 : ℝ≥0∞) ^ depth) ^ d =
        ENNReal.ofReal ((5 * (3 : ℝ) ^ depth) ^ d) := by
      calc
        (5 * (3 : ℝ≥0∞) ^ depth) ^ d =
            (ENNReal.ofReal (5 * (3 : ℝ) ^ depth)) ^ d := by
              congr 2
              rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 5),
                ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
              norm_num
        _ = ENNReal.ofReal ((5 * (3 : ℝ) ^ depth) ^ d) := by
              exact (ENNReal.ofReal_pow
                (by positivity : 0 ≤ 5 * (3 : ℝ) ^ depth) d).symm
    rw [hP]
    ring
  calc
    sqWeightedMeasure f volume ({y | M * level < ‖f y‖} ∩ Metric.closedBall x (5 * r)) ≤
        (Kh * m + Kc * e) *
          (2 * sqWeightedMeasure f volume
              ({y | level / 2 < ‖f y‖} ∩ Metric.closedBall x r) +
            2 * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) * sqWeightedMeasure g volume
              ({y | eps * level / 2 < ‖g y‖} ∩ Metric.closedBall x r)) := hpropagated
    _ = (Kh * m + Kc * e) * (2 * Tf + 2 * Tg) := by
          dsimp only [Tf, Tg]
          ring
    _ ≤ (2 * Kh + 2 * Kc) * (m + e) * (Tf + Tg) := hfactor
    _ = oneStoppingBallCoefficient depth G *
        (ENNReal.ofReal ((M / 2) ^ (2 - q.exponent.toReal)) +
          ENNReal.ofReal (eps ^ (2 : ℕ))) *
        (sqWeightedMeasure f volume ({y | level / 2 < ‖f y‖} ∩ Metric.closedBall x r) +
          ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ)) *
            sqWeightedMeasure (sigma0⁻¹ • hilbertifyVecField H) volume
              ({y | eps * level / 2 < ‖(sigma0⁻¹ • hilbertifyVecField H) y‖} ∩
                Metric.closedBall x r)) := by
          rw [hKc]
          dsimp only [Kh, m, e, Tf, Tg, g, oneStoppingBallCoefficient]
          ring

end CubeCalderonZygmund

end

end Homogenization
