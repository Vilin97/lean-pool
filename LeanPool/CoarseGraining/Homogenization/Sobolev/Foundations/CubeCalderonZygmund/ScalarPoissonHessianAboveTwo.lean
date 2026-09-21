/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaIntegration
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaParameters
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.ReflectedHessianRowOneLevelTail
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.WeakHessianFiniteP
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeDirichletH2.EuclideanNormalized

/-!
# Scalar Poisson Hessian estimates above the energy exponent

This file integrates the source-facing one-level Hessian-row estimate.  The
good-`lambda` parameters, weak Hessian, reflected problem, cutoff, and
low-level estimate are all chosen internally.
-/

namespace Homogenization

open scoped BigOperators ENNReal

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory Set

private noncomputable def exponentSucc (q : FiniteLpExponent) :
    FiniteLpExponent where
  exponent := q.exponent + 1
  one_lt := lt_of_lt_of_le q.one_lt (le_add_of_nonneg_right bot_le)
  lt_top := ENNReal.add_lt_top.mpr ⟨q.lt_top, by norm_num⟩

private theorem exponentSucc_toReal (q : FiniteLpExponent) :
    (exponentSucc q).exponent.toReal = q.exponent.toReal + 1 := by
  simp only [exponentSucc]
  rw [ENNReal.toReal_add q.lt_top.ne ENNReal.one_ne_top]
  norm_num

private theorem exponent_lt_succ (q : FiniteLpExponent) :
    q.exponent.toReal < (exponentSucc q).exponent.toReal := by
  rw [exponentSucc_toReal]
  linarith

private theorem sqWeightedMeasure_restrict_apply_eq_inter
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {B T : Set α} {f : α → E}
    (hB : MeasurableSet B) :
    sqWeightedMeasure f (μ.restrict B) T =
      sqWeightedMeasure f μ (T ∩ B) := by
  change ((μ.restrict B).withDensity fun x ↦
      ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) T =
    (μ.withDensity fun x ↦ ENNReal.ofReal (‖f x‖ ^ (2 : ℕ))) (T ∩ B)
  rw [← MeasureTheory.restrict_withDensity hB]
  exact Measure.restrict_apply' hB

private theorem sqWeightedMeasure_smul_measure
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {c : ℝ≥0∞} {T : Set α} {f : α → E} :
    sqWeightedMeasure f (c • μ) T = c * sqWeightedMeasure f μ T := by
  unfold sqWeightedMeasure
  rw [MeasureTheory.withDensity_smul_measure]
  rfl

private theorem sqWeightedMeasure_univ_ne_top_of_memLp_two
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {f : α → E} (hf : MemLp f 2 μ) :
    sqWeightedMeasure f μ Set.univ ≠ ∞ := by
  rw [sqWeightedMeasure_apply_univ_eq_eLpNorm_two_sq]
  exact ENNReal.pow_ne_top hf.eLpNorm_ne_top

private theorem lintegral_divided_moment_ne_top
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {q : FiniteLpExponent} {a : ℝ} {f : α → E}
    (ha : 0 < a) (hf : MemLp f q.exponent μ) :
    (∫⁻ x, ENNReal.ofReal
      (‖f x‖ ^ q.exponent.toReal / a ^ (q.exponent.toReal - 2)) ∂μ) ≠ ∞ := by
  let b : ℝ := a ^ (q.exponent.toReal - 2)
  have hb : 0 < b := Real.rpow_pos_of_pos ha _
  have hpoint (x : α) :
      ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal / b) =
        (ENNReal.ofReal b)⁻¹ *
          ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal) := by
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul
      (inv_nonneg.mpr hb.le), ENNReal.ofReal_inv_of_pos hb]
  have hmeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal)) μ :=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow
      aemeasurable_const).ennreal_ofReal
  simp_rw [show a ^ (q.exponent.toReal - 2) = b by rfl, hpoint]
  rw [MeasureTheory.lintegral_const_mul'' _ hmeas]
  exact ENNReal.mul_ne_top
    (ENNReal.inv_ne_top.2 (ENNReal.ofReal_ne_zero_iff.mpr hb))
    (by
      simpa only [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _)
          ENNReal.toReal_nonneg] using
        (MeasureTheory.lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
          (ne_of_gt (zero_lt_one.trans q.one_lt)) q.lt_top.ne
          hf.eLpNorm_lt_top).ne)

private theorem eLpNorm_rpow_eq_lintegral_ofReal_norm_rpow
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} (q : FiniteLpExponent) (f : α → E) :
    (eLpNorm f q.exponent μ) ^ q.exponent.toReal =
      ∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal) ∂μ := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (ne_of_gt (zero_lt_one.trans q.one_lt)) q.lt_top.ne,
    ← ENNReal.rpow_mul]
  have hq0 : q.exponent.toReal ≠ 0 :=
    (ENNReal.toReal_pos (ne_of_gt (zero_lt_one.trans q.one_lt))
      q.lt_top.ne).ne'
  rw [one_div, inv_mul_cancel₀ hq0, ENNReal.rpow_one]
  apply MeasureTheory.lintegral_congr
  intro x
  rw [← ofReal_norm,
    ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) ENNReal.toReal_nonneg]

private theorem divided_moment_eq
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {q : FiniteLpExponent} {a : ℝ} {f : α → E}
    (ha : 0 < a) (hf : MemLp f q.exponent μ) :
    ∫⁻ x, ENNReal.ofReal
        (‖f x‖ ^ q.exponent.toReal / a ^ (q.exponent.toReal - 2)) ∂μ =
      (ENNReal.ofReal (a ^ (q.exponent.toReal - 2)))⁻¹ *
        (eLpNorm f q.exponent μ) ^ q.exponent.toReal := by
  let b : ℝ := a ^ (q.exponent.toReal - 2)
  have hb : 0 < b := Real.rpow_pos_of_pos ha _
  have hpoint (x : α) :
      ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal / b) =
        (ENNReal.ofReal b)⁻¹ *
          ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal) := by
    rw [div_eq_mul_inv, mul_comm, ENNReal.ofReal_mul
      (inv_nonneg.mpr hb.le), ENNReal.ofReal_inv_of_pos hb]
  have hmeas : AEMeasurable
      (fun x ↦ ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal)) μ :=
    (hf.aestronglyMeasurable.norm.aemeasurable.pow
      aemeasurable_const).ennreal_ofReal
  simp_rw [show a ^ (q.exponent.toReal - 2) = b by rfl, hpoint]
  rw [MeasureTheory.lintegral_const_mul'' _ hmeas,
    ← eLpNorm_rpow_eq_lintegral_ofReal_norm_rpow q f]

private theorem lintegral_norm_rpow_eq_mul_divided_moment
    {α E : Type*} [MeasurableSpace α] [NormedAddCommGroup E]
    {μ : Measure α} {q : FiniteLpExponent} {a : ℝ} {f : α → E}
    (ha : 0 < a) :
    (∫⁻ x, ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal) ∂μ) =
      ENNReal.ofReal (a ^ (q.exponent.toReal - 2)) *
        ∫⁻ x, ENNReal.ofReal
          (‖f x‖ ^ q.exponent.toReal /
            a ^ (q.exponent.toReal - 2)) ∂μ := by
  let b : ℝ := a ^ (q.exponent.toReal - 2)
  have hb : 0 < b := Real.rpow_pos_of_pos ha _
  have hpoint (x : α) :
      ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal) =
        ENNReal.ofReal b *
          ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal / b) := by
    calc
      ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal) =
          ENNReal.ofReal
            ((‖f x‖ ^ q.exponent.toReal / b) * b) := by
        congr 1
        exact (div_mul_cancel₀ _ hb.ne').symm
      _ = ENNReal.ofReal (‖f x‖ ^ q.exponent.toReal / b) *
          ENNReal.ofReal b :=
        ENNReal.ofReal_mul
          (div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) hb.le)
      _ = _ := mul_comm _ _
  simp_rw [show a ^ (q.exponent.toReal - 2) = b by rfl, hpoint]
  rw [MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

private theorem tail_norm_package
    {p : ℝ} {cM D L B cdata X Y Jf Jg low : ℝ≥0∞}
    (hp : 0 < p)
    (hJf : X ^ p = cM * Jf)
    (hJg : Jg = cdata⁻¹ * Y ^ p)
    (htail : Jf ≤ (low + B * Jg) / D)
    (hlow : low ≤ L * Y ^ p) :
    X ≤ (cM * D⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ * Y := by
  have hpow : X ^ p ≤
      (cM * D⁻¹ * (L + B * cdata⁻¹)) * Y ^ p := by
    calc
      X ^ p = cM * Jf := hJf
      _ ≤ cM * ((low + B * Jg) / D) := mul_le_mul_right htail _
      _ ≤ cM * ((L * Y ^ p + B * (cdata⁻¹ * Y ^ p)) / D) := by
        apply mul_le_mul_right
        apply ENNReal.div_le_div_right
        apply add_le_add hlow
        exact mul_le_mul_right (le_of_eq hJg) _
      _ = (cM * D⁻¹ * (L + B * cdata⁻¹)) * Y ^ p := by
        rw [ENNReal.div_eq_inv_mul]
        ring
  have hp0 : p ≠ 0 := hp.ne'
  calc
    X = X ^ (p * p⁻¹) := by rw [mul_inv_cancel₀ hp0, ENNReal.rpow_one]
    _ = (X ^ p) ^ p⁻¹ := ENNReal.rpow_mul _ _ _
    _ ≤ ((cM * D⁻¹ * (L + B * cdata⁻¹)) * Y ^ p) ^ p⁻¹ :=
      ENNReal.rpow_le_rpow hpow (inv_nonneg.mpr hp.le)
    _ = (cM * D⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ * Y := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.mpr hp.le),
        ← ENNReal.rpow_mul, mul_inv_cancel₀ hp0, ENNReal.rpow_one]

private theorem exists_parameters
    {d : ℕ} [NeZero d] (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) :
    ∃ (depth : ℕ) (G : INTERNAL.HarmonicEuclideanGradientGain d
        (exponentSucc q) depth) (M eps : ℝ),
      1 < M ∧ 0 < eps ∧ eps ≤ 1 ∧
        (((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G *
          (ENNReal.ofReal ((M / 2) ^
            (2 - (exponentSucc q).exponent.toReal)) +
            ENNReal.ofReal (eps ^ (2 : ℕ)))) *
          ENNReal.ofReal ((2 * M) ^ (q.exponent.toReal - 2)) < 1 := by
  obtain ⟨⟨depth, G⟩⟩ :=
    INTERNAL.nonempty_harmonicEuclideanGradientGain_finiteTarget_of_pos d
      (Nat.pos_of_ne_zero (NeZero.ne d)) (exponentSucc q)
  let K : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) * oneStoppingBallCoefficient depth G
  have hK : K ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.pow_ne_top (by norm_num)) (oneStoppingBallCoefficient_ne_top G)
  obtain ⟨M, eps, hM, heps, heps_one, hsmall⟩ :=
    INTERNAL.exists_strict_goodLambda_parameters hK hq (exponent_lt_succ q)
  exact ⟨depth, G, M, eps, hM, heps, heps_one, hsmall⟩

private theorem normalized_l2_le_lq
    {d : ℕ} {Q : TriadicCube d} {q : FiniteLpExponent}
    {F : Vec d → ℝ} (hq : 2 < q.exponent.toReal)
    (hFq : MemLp F q.exponent (normalizedCubeMeasure Q)) :
    eLpNorm F 2 (normalizedCubeMeasure Q) ≤
      eLpNorm F q.exponent (normalizedCubeMeasure Q) := by
  let : IsProbabilityMeasure (normalizedCubeMeasure Q) :=
    ⟨normalizedCubeMeasure_apply_univ Q⟩
  apply eLpNorm_le_eLpNorm_of_exponent_le _ hFq.aestronglyMeasurable
  apply le_of_lt
  apply (ENNReal.toReal_lt_toReal (a := (2 : ℝ≥0∞))
    (b := q.exponent) (by norm_num) q.lt_top.ne).mp
  simpa using hq

private theorem sourceCutoff_le_normalizedLq
    {d : ℕ} [NeZero d] {q : FiniteLpExponent} {m : ℤ}
    (depth : ℕ) {eps : ℝ} (hq : 2 < q.exponent.toReal)
    {F : Vec d → ℝ}
    (hF2 : MemLp F 2 (normalizedCubeMeasure (originCube d m)))
    (hFq : MemLp F q.exponent (normalizedCubeMeasure (originCube d m)))
    {u : H1Function (openCubeSet (originCube d m))}
    (H : HasWeakHessianOn (openCubeSet (originCube d m)) u)
    (hH : H.hessianCoordL2NormSum ≤
      CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityConstantExact
          (originCube d m) * cubeLpNorm (originCube d m) 2 F) :
    reflectedHessianRowGoodLambdaCutoff depth eps H F ≤
      Real.sqrt (((3 : ℝ) * (10 * (3 : ℝ) ^ depth)) ^ d *
        (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
            d ^ (2 : ℕ) +
          (eps⁻¹) ^ (2 : ℕ))) *
        (eLpNorm F q.exponent
          (normalizedCubeMeasure (originCube d m))).toReal := by
  let Q : TriadicCube d := originCube d m
  let V : ℝ := cubeVolume Q
  let N₂ : ℝ := (eLpNorm F 2 (normalizedCubeMeasure Q)).toReal
  let Nq : ℝ := (eLpNorm F q.exponent (normalizedCubeMeasure Q)).toReal
  let C₂ : ℝ :=
    CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact d
  have hN : N₂ ≤ Nq := by
    apply ENNReal.toReal_mono hFq.eLpNorm_ne_top
    exact normalized_l2_le_lq hq hFq
  have hHscale : H.hessianCoordL2NormSum ≤ V ^ (1 / 2 : ℝ) * C₂ * N₂ := by
    simpa only [Q, V, C₂, N₂, cubeLpNorm,
      CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityConstantExact_eq_volume_rpow_half_mul_volumeL2ConstantExact]
      using hH
  have hFopen := memL2On_openCubeSet_of_memLp_normalizedCubeMeasure Q hF2
  have hFint : ∫ x in openCubeSet Q, F x * F x ∂volume = V * N₂ ^ (2 : ℕ) := by
    have hsq := toReal_eLpNorm_two_sq_eq_integral_sq hFopen
    have hnorm := norm_toScalarL2_openCubeSet_eq_volume_rpow_half_mul_cubeLpNorm_two Q hF2
    rw [Homogenization.toScalarL2, MeasureTheory.Lp.norm_toLp] at hnorm
    have hfun : (fun x => F x * F x) = fun x => F x ^ (2 : ℕ) := by
      funext x
      ring
    rw [hfun, ← hsq]
    rw [hnorm]
    have hV : 0 ≤ V := cubeVolume_nonneg Q
    rw [mul_pow]
    rw [show (V ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = V by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hV]
      norm_num]
    simp only [N₂, cubeLpNorm]
  have hVpos : 0 < V := cubeVolume_pos Q
  have hgeo :
      (((2 * (cubeRadius Q / (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹) *
          (3 : ℝ) ^ d * V =
        ((3 : ℝ) * (10 * (3 : ℝ) ^ depth)) ^ d := by
    rw [show 2 * (cubeRadius Q / (10 * (3 : ℝ) ^ depth)) =
        cubeScaleFactor Q / (10 * (3 : ℝ) ^ depth) by
      calc
        2 * (cubeRadius Q / (10 * (3 : ℝ) ^ depth)) =
            (2 * cubeRadius Q) / (10 * (3 : ℝ) ^ depth) := by ring
        _ = cubeScaleFactor Q / (10 * (3 : ℝ) ^ depth) := by
          rw [cubeScaleFactor_eq_two_mul_cubeRadius Q]]
    change ((cubeScaleFactor Q / (10 * (3 : ℝ) ^ depth)) ^ d)⁻¹ *
      (3 : ℝ) ^ d * cubeVolume Q = _
    rw [cubeVolume_eq_scaleFactor_pow]
    rw [← inv_pow, inv_div]
    calc
      (10 * 3 ^ depth / cubeScaleFactor Q) ^ d * 3 ^ d *
          cubeScaleFactor Q ^ d =
        ((10 * 3 ^ depth / cubeScaleFactor Q) * 3 *
          cubeScaleFactor Q) ^ d := by
        rw [mul_pow, mul_pow]
      _ = (3 * (10 * 3 ^ depth)) ^ d := by
        congr 1
        have hs : cubeScaleFactor Q ≠ 0 := by
          rw [cubeScaleFactor_eq_two_mul_cubeRadius]
          exact mul_ne_zero (by norm_num) (cubeRadius_pos Q).ne'
        field_simp [hs]
  have hinside :
      (((2 * (cubeRadius Q / (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹) *
          ((3 : ℝ) ^ d * H.hessianCoordL2NormSum ^ (2 : ℕ) +
            (eps⁻¹) ^ (2 : ℕ) * (3 : ℝ) ^ d *
              ∫ x in openCubeSet Q, F x * F x ∂volume) ≤
        (((3 : ℝ) * (10 * (3 : ℝ) ^ depth)) ^ d *
          (C₂ ^ (2 : ℕ) + (eps⁻¹) ^ (2 : ℕ))) * Nq ^ (2 : ℕ) := by
    have hfac : 0 ≤
        (((2 * (cubeRadius Q / (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹) := by
      apply inv_nonneg.mpr
      apply pow_nonneg
      exact mul_nonneg (by norm_num)
        (div_nonneg (cubeRadius_pos Q).le (by positivity))
    have hHsq : H.hessianCoordL2NormSum ^ (2 : ℕ) ≤
        V * C₂ ^ (2 : ℕ) * Nq ^ (2 : ℕ) := by
      have hC : 0 ≤ C₂ :=
        CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d
      calc
        H.hessianCoordL2NormSum ^ (2 : ℕ) ≤
            (V ^ (1 / 2 : ℝ) * C₂ * N₂) ^ (2 : ℕ) :=
          pow_le_pow_left₀ H.hessianCoordL2NormSum_nonneg hHscale 2
        _ = V * C₂ ^ (2 : ℕ) * N₂ ^ (2 : ℕ) := by
          rw [mul_pow, mul_pow]
          rw [show (V ^ (1 / 2 : ℝ)) ^ (2 : ℕ) = V by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hVpos.le]
            norm_num]
        _ ≤ V * C₂ ^ (2 : ℕ) * Nq ^ (2 : ℕ) := by
          gcongr
    rw [hFint]
    calc
      _ ≤ (((2 * (cubeRadius Q / (10 * (3 : ℝ) ^ depth))) ^ d)⁻¹) *
          ((3 : ℝ) ^ d * (V * C₂ ^ (2 : ℕ) * Nq ^ (2 : ℕ)) +
            (eps⁻¹) ^ (2 : ℕ) * (3 : ℝ) ^ d *
              (V * Nq ^ (2 : ℕ))) := by
        gcongr
      _ = _ := by
        rw [← hgeo]
        ring
  change Real.sqrt _ ≤ _
  apply (Real.sqrt_le_iff).2
  constructor
  · positivity
  · calc
      _ ≤ (((3 : ℝ) * (10 * (3 : ℝ) ^ depth)) ^ d *
          (C₂ ^ (2 : ℕ) + (eps⁻¹) ^ (2 : ℕ))) * Nq ^ (2 : ℕ) :=
        hinside
      _ = (Real.sqrt (((3 : ℝ) * (10 * (3 : ℝ) ^ depth)) ^ d *
          (C₂ ^ (2 : ℕ) + (eps⁻¹) ^ (2 : ℕ))) * Nq) ^ (2 : ℕ) := by
        symm
        calc
          (Real.sqrt (((3 : ℝ) * (10 * (3 : ℝ) ^ depth)) ^ d *
              (C₂ ^ (2 : ℕ) + (eps⁻¹) ^ (2 : ℕ))) * Nq) ^ (2 : ℕ) =
            (Real.sqrt (((3 : ℝ) * (10 * (3 : ℝ) ^ depth)) ^ d *
              (C₂ ^ (2 : ℕ) + (eps⁻¹) ^ (2 : ℕ)))) ^ (2 : ℕ) *
                Nq ^ (2 : ℕ) := by ring
          _ = _ := by
            rw [Real.sq_sqrt (by positivity)]

private theorem finite_coefficient_ne_top
    {p : ℝ} {cM rho L B cdata : ℝ≥0∞}
    (hp : 0 < p) (hcM : cM ≠ ∞) (hrho : rho < 1) (hL : L ≠ ∞)
    (hB : B ≠ ∞) (hcdata : cdata ≠ 0) :
    (cM * (1 - rho)⁻¹ * (L + B * cdata⁻¹)) ^ p⁻¹ ≠ ∞ := by
  apply ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hp.le)
  apply ENNReal.mul_ne_top
  · exact ENNReal.mul_ne_top hcM
      (ENNReal.inv_ne_top.mpr (ne_of_gt (tsub_pos_iff_lt.mpr hrho)))
  · exact ENNReal.add_ne_top.mpr
      ⟨hL, ENNReal.mul_ne_top hB (ENNReal.inv_ne_top.mpr hcdata)⟩

/-- Above the energy exponent, scalar Dirichlet Poisson data have a weak
Hessian whose full Hilbert-matrix normalized `L^q` norm is controlled by the
normalized scalar datum norm, uniformly over the centered-cube scale. -/
theorem exists_scalarPoisson_hessianHilbertMat_normalizedCubeMeasure_le_of_two_lt
    (d : ℕ) [NeZero d] (q : FiniteLpExponent)
    (hq : 2 < q.exponent.toReal) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ (m : ℤ) (F : Vec d → ℝ),
      MemLp F 2 (normalizedCubeMeasure (originCube d m)) →
      MemLp F q.exponent (normalizedCubeMeasure (originCube d m)) →
      ∀ u : H10Function (openCubeSet (originCube d m)),
        CubeDirichletWeakPoissonProblem (originCube d m) u F →
        ∃ H : HasWeakHessianOn
            (openCubeSet (originCube d m)) u.toH1Function,
          MemLp (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x))
              q.exponent (normalizedCubeMeasure (originCube d m)) ∧
            eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x))
                q.exponent (normalizedCubeMeasure (originCube d m)) ≤
              C * eLpNorm F q.exponent
                (normalizedCubeMeasure (originCube d m)) := by
  obtain ⟨depth, G, M, eps, hM, heps, heps_one, hsmall⟩ :=
    exists_parameters (d := d) q hq
  let theta : ℝ≥0∞ := ((3 : ℝ≥0∞) ^ d) *
    oneStoppingBallCoefficient depth G *
      (ENNReal.ofReal ((M / 2) ^
        (2 - (exponentSucc q).exponent.toReal)) +
        ENNReal.ofReal (eps ^ (2 : ℕ)))
  let B : ℝ≥0∞ := theta * ENNReal.ofReal ((eps⁻¹) ^ (2 : ℕ))
  let cM : ℝ≥0∞ := ENNReal.ofReal (M ^ (q.exponent.toReal - 2))
  let cdata : ℝ≥0∞ := ENNReal.ofReal
    ((eps / 2) ^ (q.exponent.toReal - 2))
  let rho : ℝ≥0∞ := theta * ENNReal.ofReal
    ((2 * M) ^ (q.exponent.toReal - 2))
  let Ccut : ℝ := Real.sqrt
    (((3 : ℝ) * (10 * (3 : ℝ) ^ depth)) ^ d *
      (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
          d ^ (2 : ℕ) +
        (eps⁻¹) ^ (2 : ℕ)))
  let L : ℝ≥0∞ := ENNReal.ofReal
      (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
        d ^ (2 : ℕ)) *
    (ENNReal.ofReal (2 * Ccut)) ^ (q.exponent.toReal - 2)
  let Crow : ℝ≥0∞ :=
    (cM * (1 - rho)⁻¹ * (L + B * cdata⁻¹)) ^
      (q.exponent.toReal)⁻¹
  let C : ℝ≥0∞ := d * Crow
  have hp : 0 < q.exponent.toReal := by linarith
  have htheta : theta ≠ ∞ := by
    dsimp only [theta]
    exact ENNReal.mul_ne_top
      (ENNReal.mul_ne_top (ENNReal.pow_ne_top (by norm_num))
        (oneStoppingBallCoefficient_ne_top G))
      (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩)
  have hBtop : B ≠ ∞ :=
    ENNReal.mul_ne_top htheta ENNReal.ofReal_ne_top
  have hCdata : cdata ≠ 0 := by
    dsimp only [cdata]
    exact (ENNReal.ofReal_pos.mpr
      (Real.rpow_pos_of_pos (by linarith) _)).ne'
  have hCrow : Crow ≠ ∞ := by
    apply finite_coefficient_ne_top hp ENNReal.ofReal_ne_top
    · simpa only [rho, theta] using hsmall
    · dsimp only [L]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top)
    · exact hBtop
    · exact hCdata
  refine ⟨C, lt_top_iff_ne_top.mpr
    (ENNReal.mul_ne_top (ENNReal.natCast_ne_top d) hCrow), ?_⟩
  intro m F hF2 hFq u hweak
  obtain ⟨H, hH, htail⟩ :=
    exists_hasWeakHessianOn_sqWeightedMeasure_oneLevel_tail_originCube
      G (hq.trans (exponent_lt_succ q)) heps heps_one hM.le F hF2 u hweak
  let Q : TriadicCube d := originCube d m
  let μ : Measure (Vec d) := normalizedCubeMeasure Q
  let row : Fin d → Vec d → HilbertVec d := fun i x ↦
    HilbertVec.ofVec (fun j ↦ H.hess i j x)
  let Y : ℝ≥0∞ := eLpNorm F q.exponent μ
  have hrows : ∀ i : Fin d, MemLp (row i) q.exponent μ ∧
      eLpNorm (row i) q.exponent μ ≤ Crow * Y := by
    intro i
    have hrow2 : MemLp (row i) 2 μ := by
      simpa only [row, Q, μ] using!
        H.hessianHilbertRow_memLp_two_normalizedCubeMeasure Q i
    have hrowMeas : AEStronglyMeasurable (row i) μ :=
      hrow2.aestronglyMeasurable
    have hFMeas : AEStronglyMeasurable F μ := by
      simpa only [μ, Q] using hFq.aestronglyMeasurable
    by_cases hYzero : Y = 0
    · have hFae : F =ᵐ[μ] 0 :=
        (eLpNorm_eq_zero_iff hFq.aestronglyMeasurable
          (ne_of_gt (zero_lt_one.trans q.one_lt))).mp (by
            simpa only [Y, μ] using hYzero)
      have hF2zero : eLpNorm F 2 μ = 0 :=
        eLpNorm_eq_zero_of_ae_zero hFae
      have hrow2norm : eLpNorm (row i) 2 μ = 0 := by
        apply le_zero_iff.mp
        calc
          eLpNorm (row i) 2 μ ≤ ENNReal.ofReal
              (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                H.hessianCoordL2NormSum) := by
            simpa only [row] using!
              H.eLpNorm_hessianHilbertRow_two_normalizedCubeMeasure_le Q i
          _ ≤ 0 := by
            have hN2 : cubeLpNorm Q 2 F = 0 := by
              simpa only [cubeLpNorm, μ] using!
                congrArg ENNReal.toReal hF2zero
            rw [hN2, mul_zero] at hH
            have hHzero := le_antisymm hH H.hessianCoordL2NormSum_nonneg
            rw [hHzero, mul_zero, ENNReal.ofReal_zero]
      have hrowAe : row i =ᵐ[μ] 0 :=
        (eLpNorm_eq_zero_iff hrow2.aestronglyMeasurable (by norm_num)).mp
          hrow2norm
      have hrowq : MemLp (row i) q.exponent μ :=
        MemLp.zero'.ae_eq hrowAe.symm
      refine ⟨hrowq, ?_⟩
      rw [eLpNorm_eq_zero_of_ae_zero hrowAe, hYzero, mul_zero]
    · have hYpos : 0 < Y.toReal :=
        ENNReal.toReal_pos hYzero (by simpa only [Y, μ] using hFq.eLpNorm_ne_top)
      have hcut := sourceCutoff_le_normalizedLq (eps := eps)
        depth hq hF2 hFq H hH
      have hCcut : 0 < Ccut := by
        dsimp only [Ccut]
        positivity
      let lambda0 : ℝ :=
        reflectedHessianRowGoodLambdaCutoff depth eps H F + Ccut * Y.toReal
      have hlambda : 0 < lambda0 := by
        dsimp only [lambda0]
        exact add_pos_of_nonneg_of_pos
          (reflectedHessianRowGoodLambdaCutoff_nonneg depth eps H F)
          (mul_pos hCcut hYpos)
      have hcutoff :
          reflectedHessianRowGoodLambdaCutoff depth eps H F < lambda0 := by
        dsimp only [lambda0]
        exact lt_add_of_pos_right _ (mul_pos hCcut hYpos)
      have hlambdaBound : lambda0 ≤ 2 * Ccut * Y.toReal := by
        dsimp only [lambda0]
        have hcut' : reflectedHessianRowGoodLambdaCutoff depth eps H F ≤
            Ccut * Y.toReal := by
          simpa only [Q, μ, Y, Ccut] using hcut
        nlinarith
      have htailNorm : ∀ t, lambda0 ≤ t →
          sqWeightedMeasure (row i) μ {x | M * t < ‖row i x‖} ≤
            theta * sqWeightedMeasure (row i) μ
              {x | t / 2 < ‖row i x‖} +
              B * sqWeightedMeasure F μ {x | eps * t / 2 < ‖F x‖} := by
        intro t ht
        have hraw := htail i t (hcutoff.trans_le ht)
        let c : ℝ≥0∞ := ENNReal.ofReal ((cubeVolume Q)⁻¹)
        have hc : c ≠ 0 := (ENNReal.ofReal_pos.mpr
          (inv_pos.mpr (cubeVolume_pos Q))).ne'
        have hscaled := mul_le_mul_right hraw c
        simpa only [Q, μ, row, normalizedCubeMeasure, cubeMeasure,
          volume_restrict_cubeSet_eq_volume_restrict_openCubeSet,
          sqWeightedMeasure_smul_measure,
          sqWeightedMeasure_restrict_apply_eq_inter
            (measurableSet_openCubeSet Q), theta, B, mul_add, mul_assoc,
          mul_left_comm, mul_comm] using! hscaled
      have hBfinite : B ≠ ∞ := hBtop
      have hintegrated := lp_le_of_oneLevel_weighted_tail
        hrowMeas hFMeas hq (by linarith) (by linarith) heps hlambda
        (sqWeightedMeasure_univ_ne_top_of_memLp_two hrow2) hBfinite
        (lintegral_divided_moment_ne_top (by linarith) hFq)
        (by simpa only [rho, theta] using hsmall) htailNorm
      let Jrow : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal
        (‖row i x‖ ^ q.exponent.toReal /
          M ^ (q.exponent.toReal - 2)) ∂μ
      let JF : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal
        (‖F x‖ ^ q.exponent.toReal /
          (eps / 2) ^ (q.exponent.toReal - 2)) ∂μ
      let low : ℝ≥0∞ := sqWeightedMeasure (row i) μ Set.univ *
        ENNReal.ofReal (lambda0 ^ (q.exponent.toReal - 2))
      have hlow : low ≤ L * Y ^ q.exponent.toReal := by
        have hS : sqWeightedMeasure (row i) μ Set.univ ≤
            ENNReal.ofReal
              (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
                d ^ (2 : ℕ)) *
                Y ^ (2 : ℕ) := by
          rw [sqWeightedMeasure_apply_univ_eq_eLpNorm_two_sq]
          have hrowL2 :=
            H.eLpNorm_hessianHilbertRow_two_normalizedCubeMeasure_le Q i
          have hHnorm : ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
              H.hessianCoordL2NormSum ≤
                CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
                    d *
                  (eLpNorm F 2 μ).toReal := by
            have hscale := hH
            rw [CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityConstantExact_eq_volume_rpow_half_mul_volumeL2ConstantExact]
              at hscale
            have hscale' : H.hessianCoordL2NormSum ≤
                cubeVolume Q ^ (1 / 2 : ℝ) *
                    CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact d *
                  cubeLpNorm Q 2 F := by
              simpa only [Q] using hscale
            have hcancel : ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                cubeVolume Q ^ (1 / 2 : ℝ) = 1 := by
              rw [Real.inv_rpow (cubeVolume_nonneg Q)]
              exact inv_mul_cancel₀
                (Real.rpow_pos_of_pos (cubeVolume_pos Q) _).ne'
            calc
              _ ≤ ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                  (cubeVolume Q ^ (1 / 2 : ℝ) *
                    CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
                      d *
                    cubeLpNorm Q 2 F) :=
                mul_le_mul_of_nonneg_left hscale'
                  (Real.rpow_nonneg (inv_nonneg.mpr (cubeVolume_nonneg Q)) _)
              _ = _ := by
                calc
                  ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                      (cubeVolume Q ^ (1 / 2 : ℝ) *
                        CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact d *
                        cubeLpNorm Q 2 F) =
                    (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                      cubeVolume Q ^ (1 / 2 : ℝ)) *
                        (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact d *
                          cubeLpNorm Q 2 F) := by ring
                  _ = _ := by rw [hcancel, one_mul, cubeLpNorm]
          have hN2q : (eLpNorm F 2 μ).toReal ≤ Y.toReal := by
            apply ENNReal.toReal_mono
              (by simpa only [Y, μ] using hFq.eLpNorm_ne_top)
            simpa only [Y, μ] using normalized_l2_le_lq hq hFq
          have hreal : ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
              H.hessianCoordL2NormSum ≤
                CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
                    d * Y.toReal :=
            hHnorm.trans (mul_le_mul_of_nonneg_left hN2q
              (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d))
          calc
            eLpNorm (row i) 2 μ ^ (2 : ℕ) ≤
                ENNReal.ofReal
                  (((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                    H.hessianCoordL2NormSum) ^ (2 : ℕ) := by
              exact pow_le_pow_left₀ bot_le hrowL2 2
            _ ≤ ENNReal.ofReal
                (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
                    d *
                  Y.toReal) ^ (2 : ℕ) := by
              have hleft : 0 ≤ ((cubeVolume Q)⁻¹) ^ (1 / 2 : ℝ) *
                  H.hessianCoordL2NormSum :=
                mul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr
                  (cubeVolume_nonneg Q)) _) H.hessianCoordL2NormSum_nonneg
              rw [← ENNReal.ofReal_pow hleft]
              rw [← ENNReal.ofReal_pow (mul_nonneg
                (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d)
                ENNReal.toReal_nonneg)]
              exact ENNReal.ofReal_le_ofReal
                (pow_le_pow_left₀ hleft hreal 2)
            _ = _ := by
              rw [ENNReal.ofReal_mul
                (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d),
                ENNReal.ofReal_toReal
                  (by simpa only [Y, μ] using hFq.eLpNorm_ne_top), mul_pow,
                ← ENNReal.ofReal_pow
                  (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact_nonneg d)]
        have hlamENN : ENNReal.ofReal lambda0 ≤
            ENNReal.ofReal (2 * Ccut) * Y := by
          calc
            ENNReal.ofReal lambda0 ≤ ENNReal.ofReal (2 * Ccut * Y.toReal) :=
              ENNReal.ofReal_le_ofReal hlambdaBound
            _ = ENNReal.ofReal (2 * Ccut) * Y := by
              rw [ENNReal.ofReal_mul (by positivity),
                ENNReal.ofReal_toReal
                  (by simpa only [Y, μ] using hFq.eLpNorm_ne_top)]
        have he : 0 ≤ q.exponent.toReal - 2 := by linarith
        dsimp only [low, L]
        rw [← ENNReal.ofReal_rpow_of_nonneg hlambda.le he]
        calc
          sqWeightedMeasure (row i) μ Set.univ *
              (ENNReal.ofReal lambda0) ^ (q.exponent.toReal - 2) ≤
            (ENNReal.ofReal
                (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
                  d ^ (2 : ℕ)) *
              Y ^ (2 : ℕ)) *
              (ENNReal.ofReal (2 * Ccut) * Y) ^
                (q.exponent.toReal - 2) :=
            mul_le_mul hS (ENNReal.rpow_le_rpow hlamENN he) bot_le bot_le
          _ = ENNReal.ofReal
                (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
                  d ^ (2 : ℕ)) *
              (ENNReal.ofReal (2 * Ccut)) ^ (q.exponent.toReal - 2) *
                Y ^ q.exponent.toReal := by
            rw [ENNReal.mul_rpow_of_nonneg _ _ he]
            calc
              _ = ENNReal.ofReal
                    (CubeDirichletWeakPoissonProblem.cubeDirichletH2RegularityVolumeL2ConstantExact
                      d ^ (2 : ℕ)) *
                  (ENNReal.ofReal (2 * Ccut)) ^ (q.exponent.toReal - 2) *
                    (Y ^ (2 : ℕ) * Y ^ (q.exponent.toReal - 2)) := by ring
              _ = _ := by
                rw [← ENNReal.rpow_natCast,
                  ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) he]
                congr 3
                ring
      have hJrow : (eLpNorm (row i) q.exponent μ) ^ q.exponent.toReal =
          cM * Jrow := by
        dsimp only [cM, Jrow]
        rw [eLpNorm_rpow_eq_lintegral_ofReal_norm_rpow]
        have hMpos : 0 < M := by linarith
        exact lintegral_norm_rpow_eq_mul_divided_moment hMpos
      have hJF : JF = cdata⁻¹ * Y ^ q.exponent.toReal := by
        simpa only [JF, cdata, Y] using divided_moment_eq (by linarith) hFq
      have hbound : eLpNorm (row i) q.exponent μ ≤ Crow * Y := by
        apply tail_norm_package hp hJrow hJF
        · simpa only [Jrow, JF, low, theta, B, rho] using hintegrated
        · exact hlow
      have hrowq : MemLp (row i) q.exponent μ :=
        ⟨hrowMeas, hbound.trans_lt (ENNReal.mul_lt_top
          (lt_top_iff_ne_top.mpr hCrow)
          (by simpa only [Y, μ] using hFq.eLpNorm_lt_top))⟩
      exact ⟨hrowq, hbound⟩
  have hrowsMem : ∀ i, MemLp (row i) q.exponent μ := fun i ↦ (hrows i).1
  refine ⟨H, H.hessianHilbertMat_memLp_normalizedCubeMeasure_of_rows
    Q q (by simpa only [row, μ] using hrowsMem), ?_⟩
  calc
    eLpNorm (fun x ↦ HilbertMat.ofMat (fun i j ↦ H.hess i j x))
        q.exponent μ ≤
      ∑ i : Fin d, eLpNorm (row i) q.exponent μ := by
        simpa only [row] using
          H.eLpNorm_hessianHilbertMat_normalizedCubeMeasure_le_sum_rows
            Q q (by simpa only [row, μ] using hrowsMem)
    _ ≤ ∑ _i : Fin d, Crow * Y := Finset.sum_le_sum fun i _ ↦ (hrows i).2
    _ = C * Y := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul, C]; ring
    _ = C * eLpNorm F q.exponent (normalizedCubeMeasure (originCube d m)) := rfl

end CubeCalderonZygmund

end

end Homogenization
