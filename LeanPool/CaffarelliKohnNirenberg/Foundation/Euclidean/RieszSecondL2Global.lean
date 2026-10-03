/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.RieszSecondL2GlobalBounds

/-!
# Riesz Second L2 Global

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Euclidean

noncomputable section

namespace CKN.Foundation.Euclidean

private lemma cutoffError_pointwise_bound_hq_1 :
    ∀ {F : Vec3 → ℝ} {ρ : ℝ} (hρ : 0 < ρ) {x : Vec3},
      let B : ℝ := 60 / 13 * Foundation.Euclidean.potentialTailSize F;
      0 ≤ Foundation.Euclidean.potentialTailSize F →
        1 ≤ ρ →
          |pressureNewtonianPotential F x| ≤ B / ρ →
            0 ≤ cutoffGradientConstant →
              0 ≤ cutoffSecondDerivativeConstant →
                |spatialGradDot (mollifiedBallCutoff 0 hρ) (pressureNewtonianPotential F) x| ≤
                    3 * cutoffGradientConstant * B / ρ ^ 2 →
                  |spatialLaplacian (mollifiedBallCutoff 0 hρ) x| ≤
                      3 * cutoffSecondDerivativeConstant / ρ ^ 2 →
                    |Foundation.Euclidean.cutoffError F hρ x| ≤
                      B * (6 * cutoffGradientConstant + 3 * cutoffSecondDerivativeConstant) /
                        ρ ^ 2
    := by
  intro F ρ hρ x B htail hρone hpot0 hgradConst hsecondConst hgradDot hlap
  rw [cutoffError]
  calc
    |2 * spatialGradDot (mollifiedBallCutoff 0 hρ)
        (pressureNewtonianPotential F) x +
        pressureNewtonianPotential F x *
          spatialLaplacian (mollifiedBallCutoff 0 hρ) x| ≤
        2 * |spatialGradDot (mollifiedBallCutoff 0 hρ)
          (pressureNewtonianPotential F) x| +
          |pressureNewtonianPotential F x| *
            |spatialLaplacian (mollifiedBallCutoff 0 hρ) x| := by
      calc
        |2 * spatialGradDot (mollifiedBallCutoff 0 hρ)
            (pressureNewtonianPotential F) x +
            pressureNewtonianPotential F x *
              spatialLaplacian (mollifiedBallCutoff 0 hρ) x| ≤
            |2 * spatialGradDot (mollifiedBallCutoff 0 hρ)
              (pressureNewtonianPotential F) x| +
              |pressureNewtonianPotential F x *
                spatialLaplacian (mollifiedBallCutoff 0 hρ) x| :=
          abs_add_le _ _
        _ = 2 * |spatialGradDot (mollifiedBallCutoff 0 hρ)
              (pressureNewtonianPotential F) x| +
              |pressureNewtonianPotential F x| *
                |spatialLaplacian (mollifiedBallCutoff 0 hρ) x| := by
          rw [abs_mul, abs_mul]
          norm_num
    _ ≤ 2 * (3 * cutoffGradientConstant * B / ρ ^ 2) +
        (B / ρ) * (3 * cutoffSecondDerivativeConstant / ρ ^ 2) := by
      gcongr
    _ ≤ B * (6 * cutoffGradientConstant + 3 * cutoffSecondDerivativeConstant) /
        ρ ^ 2 := by
      have hconst : 0 ≤ 6 * cutoffGradientConstant +
          3 * cutoffSecondDerivativeConstant := by
        positivity
      have hρpow : ρ ^ 2 ≤ ρ ^ 3 := by
        nlinarith only [hρone, sq_nonneg (ρ - 1)]
      have hterm :
          (B / ρ) * (3 * cutoffSecondDerivativeConstant / ρ ^ 2) ≤
            3 * B * cutoffSecondDerivativeConstant / ρ ^ 2 := by
        calc
          (B / ρ) * (3 * cutoffSecondDerivativeConstant / ρ ^ 2) =
              3 * B * cutoffSecondDerivativeConstant / ρ ^ 3 := by
            field_simp [ne_of_gt hρ]
          _ ≤ 3 * B * cutoffSecondDerivativeConstant / ρ ^ 2 := by
            gcongr
      calc
        2 * (3 * cutoffGradientConstant * B / ρ ^ 2) +
            (B / ρ) * (3 * cutoffSecondDerivativeConstant / ρ ^ 2) ≤
            2 * (3 * cutoffGradientConstant * B / ρ ^ 2) +
              3 * B * cutoffSecondDerivativeConstant / ρ ^ 2 :=
          (add_le_add_right hterm
            (2 * (3 * cutoffGradientConstant * B / ρ ^ 2))).trans_eq
            (by ring)
        _ = B * (6 * cutoffGradientConstant +
            3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
          ring

private lemma cutoffError_pointwise_bound {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hlarge : 10 * R ≤ ρ)
    (hRone : 1 ≤ R)
    (hSupp : tsupport F ⊆ Metric.closedBall (0 : Vec3) R)
    {x : Vec3}
    (hx : x ∈ euclideanBall 0 (3 * ρ / 4) \
      euclideanClosedBall 0 (13 * ρ / 20)) :
    |cutoffError F hρ x| ≤ cutoffErrorConstant F / ρ ^ 2 := by
  let B : ℝ := (60 / 13) * potentialTailSize F
  have htail : 0 ≤ potentialTailSize F := potentialTailSize_nonneg
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have hρone : 1 ≤ ρ := by
    nlinarith only [hlarge, hRone]
  have hxinner : 13 * ρ / 20 < vecEuclideanNorm (x - 0) := by
    have hnot : ¬ vecEuclideanNorm (x - 0) ≤ 13 * ρ / 20 := by
      intro hle
      exact hx.2 ((mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by positivity)).2 hle)
    exact lt_of_not_ge hnot
  have hthree : vecEuclideanNorm (x - 0) ≤ 3 * ‖x‖ := by
    have h := euclideanNorm_le_three_mul_space_norm (x - 0)
    simpa [vecEuclideanNorm, vecNormSq, vecDot, spaceEuclideanNorm, pow_two] using h
  have hnormlower : 13 * ρ / 60 < ‖x‖ := by
    nlinarith only [hxinner, hthree]
  have hnormpos : 0 < ‖x‖ := by
    exact lt_of_lt_of_le (by positivity) (le_of_lt hnormlower)
  have hinv : ‖x‖⁻¹ ≤ (60 / 13) / ρ := by
    have h := (inv_le_inv₀ (a := ‖x‖) (b := 13 * ρ / 60)
      hnormpos (by positivity)).2 hnormlower.le
    calc
      ‖x‖⁻¹ ≤ (13 * ρ / 60)⁻¹ := h
      _ = (60 / 13) / ρ := by
        field_simp [ne_of_gt hρ]
  have hfar : 2 * R ≤ ‖x‖ := by
    have hinner : 2 * R ≤ 13 * ρ / 60 := by
      nlinarith only [hlarge, hR]
    exact le_trans hinner (le_of_lt hnormlower)
  have hpot := pressure_potential_tail_bound hF hFc hR hSupp hfar
  have hpot0 : |pressureNewtonianPotential F x| ≤ B / ρ := by
    have hI : 0 ≤ ∫ y, |F y| := integral_nonneg (fun y => abs_nonneg _)
    have hIsum : (∫ y, |F y|) ≤
        (∫ y, |F y|) + ∑ i : Fin 3, ∫ y, |spatialDeriv F i y| := by
      have hsum : 0 ≤ ∑ i : Fin 3, ∫ y, |spatialDeriv F i y| := by
        exact Finset.sum_nonneg fun i hi =>
          integral_nonneg (fun y => abs_nonneg _)
      exact le_add_of_nonneg_right
        (a := ∫ y, |F y|)
        (b := ∑ i : Fin 3, ∫ y, |spatialDeriv F i y|) hsum
    calc
      |pressureNewtonianPotential F x| ≤
          (2 * (4 * Real.pi)⁻¹) * ‖x‖⁻¹ * ∫ y, |F y| := by
        simpa [div_eq_mul_inv, mul_assoc] using hpot
      _ ≤ (2 * (4 * Real.pi)⁻¹) * ((60 / 13) / ρ) * ∫ y, |F y| := by
        gcongr
      _ ≤ (2 * (4 * Real.pi)⁻¹) * ((60 / 13) / ρ) *
          ((∫ y, |F y|) + ∑ i : Fin 3, ∫ y, |spatialDeriv F i y|) := by
        gcongr
      _ = B / ρ := by
        dsimp [B, potentialTailSize]
        ring
  have hderiv : ∀ i : Fin 3,
      |spatialDeriv (pressureNewtonianPotential F) i x| ≤ B / ρ := by
    intro i
    have hi := pressure_potential_deriv_tail_bound hF hFc hR hSupp i hfar
    have hI : 0 ≤ ∫ y, |spatialDeriv F i y| :=
      integral_nonneg (fun y => abs_nonneg _)
    have hIsum : ∫ y, |spatialDeriv F i y| ≤
        ∑ k : Fin 3, ∫ y, |spatialDeriv F k y| := by
      exact Finset.single_le_sum (s := (Finset.univ : Finset (Fin 3)))
        (f := fun k : Fin 3 => ∫ y, |spatialDeriv F k y|)
        (fun k hk => integral_nonneg (fun y => abs_nonneg _)) (Finset.mem_univ i)
    have hIsum' : (∫ y, |spatialDeriv F i y|) ≤
        (∫ y, |F y|) + ∑ k : Fin 3, ∫ y, |spatialDeriv F k y| := by
      have hFnonneg : 0 ≤ ∫ y, |F y| :=
        integral_nonneg (fun y => abs_nonneg _)
      exact hIsum.trans (le_add_of_nonneg_left
        (a := ∑ k : Fin 3, ∫ y, |spatialDeriv F k y|)
        (b := ∫ y, |F y|) hFnonneg)
    calc
      |spatialDeriv (pressureNewtonianPotential F) i x| ≤
          (2 * (4 * Real.pi)⁻¹) * ‖x‖⁻¹ *
            ∫ y, |spatialDeriv F i y| := by
        simpa [div_eq_mul_inv, mul_assoc] using hi
      _ ≤ (2 * (4 * Real.pi)⁻¹) * ((60 / 13) / ρ) *
          ∫ y, |spatialDeriv F i y| := by
        gcongr
      _ ≤ (2 * (4 * Real.pi)⁻¹) * ((60 / 13) / ρ) *
          ((∫ y, |F y|) + ∑ k : Fin 3, ∫ y, |spatialDeriv F k y|) := by
        gcongr
      _ = B / ρ := by
        dsimp [B, potentialTailSize]
        ring
  have hgradConst : 0 ≤ cutoffGradientConstant := by
    let h₁ : (0 : ℝ) < 1 := by norm_num
    have hgrad' := mollifiedBallCutoff_gradient_bound (0 : Vec3)
      h₁ (0 : Vec3)
    have hn := vecEuclideanNorm_nonneg
      (classicalGradient (mollifiedBallCutoff (0 : Vec3) h₁) 0)
    simpa using le_trans hn hgrad'
  have hsecondConst : 0 ≤ cutoffSecondDerivativeConstant := by
    let h₁ : (0 : ℝ) < 1 := by norm_num
    have hsecond' := mollifiedBallCutoff_second_derivative_bound (0 : Vec3)
      h₁ (0 : Vec3)
    have hn := norm_nonneg
      (fderiv ℝ (classicalGradient (mollifiedBallCutoff (0 : Vec3) h₁)) 0)
    simpa using le_trans hn hsecond'
  have hgradDot :
      |spatialGradDot (mollifiedBallCutoff 0 hρ)
        (pressureNewtonianPotential F) x| ≤
        3 * cutoffGradientConstant * B / ρ ^ 2 := by
    unfold spatialGradDot
    calc
      |∑ i : Fin 3, spatialDeriv (mollifiedBallCutoff 0 hρ) i x *
          spatialDeriv (pressureNewtonianPotential F) i x| ≤
          ∑ i : Fin 3,
            |spatialDeriv (mollifiedBallCutoff 0 hρ) i x *
              spatialDeriv (pressureNewtonianPotential F) i x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, cutoffGradientConstant * B / ρ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        have hχ := pressure_cutoff_spatialDeriv_bound 0 hρ x i
        have hw := hderiv i
        calc
          |spatialDeriv (mollifiedBallCutoff 0 hρ) i x *
              spatialDeriv (pressureNewtonianPotential F) i x| =
              |spatialDeriv (mollifiedBallCutoff 0 hρ) i x| *
                |spatialDeriv (pressureNewtonianPotential F) i x| := abs_mul _ _
          _ ≤ (cutoffGradientConstant / ρ) * (B / ρ) := by
            have hgrad' : 0 ≤ cutoffGradientConstant / ρ :=
              div_nonneg hgradConst hρ.le
            gcongr
          _ = cutoffGradientConstant * B / ρ ^ 2 := by
            field_simp [ne_of_gt hρ]
      _ = 3 * cutoffGradientConstant * B / ρ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hlap :
      |spatialLaplacian (mollifiedBallCutoff 0 hρ) x| ≤
        3 * cutoffSecondDerivativeConstant / ρ ^ 2 := by
    unfold spatialLaplacian
    calc
      |∑ i : Fin 3, mixedSecond (mollifiedBallCutoff 0 hρ) i i x| ≤
          ∑ i : Fin 3, |mixedSecond (mollifiedBallCutoff 0 hρ) i i x| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi
        exact pressure_cutoff_mixedSecond_bound 0 hρ x i i
      _ = 3 * cutoffSecondDerivativeConstant / ρ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        ring
  have hq := @cutoffError_pointwise_bound_hq_1 F ρ hρ x htail hρone hpot0 hgradConst hsecondConst
    hgradDot hlap
  calc
    |cutoffError F hρ x| ≤
        B * (6 * cutoffGradientConstant + 3 * cutoffSecondDerivativeConstant) /
          ρ ^ 2 := hq
    _ = cutoffErrorConstant F / ρ ^ 2 := by
      dsimp [cutoffErrorConstant, B]

private lemma cutoffError_eq_zero_of_not_annulus {F : Vec3 → ℝ}
    {ρ : ℝ} (hρ : 0 < ρ) {x : Vec3}
    (hx : x ∉ euclideanBall 0 (3 * ρ / 4) \
      euclideanClosedBall 0 (13 * ρ / 20)) :
    cutoffError F hρ x = 0 := by
  obtain ⟨hgrad, hhess⟩ := pressure_cutoff_derivatives_vanish 0 hρ hx
  have hgrad' : spatialGradDot (mollifiedBallCutoff 0 hρ)
      (pressureNewtonianPotential F) x = 0 := by
    simp only [spatialGradDot]
    rw [Finset.sum_eq_zero]
    intro i hi
    simp [hgrad i]
  have hlap : spatialLaplacian (mollifiedBallCutoff 0 hρ) x = 0 := by
    simp only [spatialLaplacian]
    rw [Finset.sum_eq_zero]
    intro i hi
    exact hhess i i
  simp [cutoffError, hgrad', hlap]

private lemma cutoffError_abs_bound {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hlarge : 10 * R ≤ ρ)
    (hRone : 1 ≤ R)
    (hSupp : tsupport F ⊆ Metric.closedBall (0 : Vec3) R) {x : Vec3} :
    |cutoffError F hρ x| ≤ cutoffErrorConstant F / ρ ^ 2 := by
  by_cases hx : x ∈ euclideanBall 0 (3 * ρ / 4) \
      euclideanClosedBall 0 (13 * ρ / 20)
  · exact cutoffError_pointwise_bound hF hFc hR hρ hlarge hRone hSupp hx
  · rw [cutoffError_eq_zero_of_not_annulus hρ hx]
    exact (abs_zero).le.trans (div_nonneg
      (cutoffErrorConstant_nonneg (F := F)) (by positivity))

private lemma cutoffError_l2_bound {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hlarge : 10 * R ≤ ρ)
    (hRone : 1 ≤ R)
    (hSupp : tsupport F ⊆ Metric.closedBall (0 : Vec3) R) :
    ∫ x, (cutoffError F hρ x) ^ 2 ≤
      (cutoffErrorConstant F / ρ ^ 2) ^ 2 *
        (volume (euclideanClosedBall (0 : Vec3) (3 * ρ / 4))).toReal := by
  let K : Set Vec3 := euclideanClosedBall 0 (3 * ρ / 4)
  let M : ℝ := cutoffErrorConstant F / ρ ^ 2
  have hKcompact : IsCompact K := by
    dsimp [K]
    exact isCompact_euclideanClosedBall 0 (by positivity)
  have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
  have hqcont : Continuous (cutoffError F hρ) :=
    (cutoffError_smooth hF hFc hρ).continuous
  have hqcomp : HasCompactSupport (fun x => (cutoffError F hρ x) ^ 2) := by
    refine HasCompactSupport.intro hKcompact ?_
    intro x hx
    have hxann : x ∉ euclideanBall 0 (3 * ρ / 4) \
        euclideanClosedBall 0 (13 * ρ / 20) := by
      intro hxann
      apply hx
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
        ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hxann.1).le
    rw [cutoffError_eq_zero_of_not_annulus hρ hxann]
    simp
  have hqint : Integrable (fun x => (cutoffError F hρ x) ^ 2) volume :=
    (hqcont.pow 2).integrable_of_hasCompactSupport hqcomp
  have hM : 0 ≤ M := by
    dsimp [M]
    exact div_nonneg (cutoffErrorConstant_nonneg (F := F)) (by positivity)
  have hbound : ∀ x, |cutoffError F hρ x| ≤ M := by
    intro x
    exact cutoffError_abs_bound hF hFc hR hρ hlarge hRone hSupp
  have hconstOn : IntegrableOn (fun _ : Vec3 => M ^ 2) K volume :=
    integrableOn_const hKcompact.measure_ne_top (by finiteness)
  have hconst : Integrable (K.indicator (fun _ : Vec3 => M ^ 2)) volume :=
    hconstOn.integrable_indicator hKmeas
  have hmono : ∫ x, (cutoffError F hρ x) ^ 2 ≤
      ∫ x, K.indicator (fun _ : Vec3 => M ^ 2) x := by
    apply integral_mono hqint hconst
    intro x
    by_cases hx : x ∈ K
    · rw [Set.indicator_of_mem hx]
      have habs := hbound x
      have hsq : |cutoffError F hρ x| ^ 2 ≤ M ^ 2 :=
        (sq_le_sq₀ (abs_nonneg _) hM).2 habs
      simpa [sq_abs] using hsq
    · rw [Set.indicator_of_notMem hx]
      have hxann : x ∉ euclideanBall 0 (3 * ρ / 4) \
          euclideanClosedBall 0 (13 * ρ / 20) := by
        intro hxann
        apply hx
        exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
          ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hxann.1).le
      change (cutoffError F hρ x) ^ 2 ≤ 0
      rw [cutoffError_eq_zero_of_not_annulus hρ hxann]
      simp
  calc
    ∫ x, (cutoffError F hρ x) ^ 2 ≤
        ∫ x, K.indicator (fun _ : Vec3 => M ^ 2) x := hmono
    _ = ∫ x in K, M ^ 2 := integral_indicator hKmeas
    _ = (volume K).toReal * M ^ 2 := by
      rw [integral_const]
      simp [Measure.real, K, smul_eq_mul]
    _ = (cutoffErrorConstant F / ρ ^ 2) ^ 2 *
        (volume (euclideanClosedBall 0 (3 * ρ / 4))).toReal := by
      simp [K, M]
      ring

private lemma euclideanClosedBall_volume_toReal_le {r : ℝ} (hr : 0 < r) :
    (volume (euclideanClosedBall (0 : Vec3) r)).toReal ≤
      (2 * r) ^ 3 * (Real.pi * 4 / 3) := by
  have hsub : euclideanClosedBall (0 : Vec3) r ⊆ vec3Ball 0 (2 * r) := by
    intro x hx
    rw [mem_vec3Ball]
    have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).1 hx
    have hx'' : vec3EuclideanNorm (x - 0) ≤ r := by
      simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
        using hx'
    linarith only [hx'', hr]
  have htop : volume (vec3Ball (0 : Vec3) (2 * r)) ≠ ∞ := by
    rw [volume_vec3Ball_eq]
    exact ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
      ENNReal.ofReal_ne_top
  calc
    (volume (euclideanClosedBall (0 : Vec3) r)).toReal ≤
        (volume (vec3Ball (0 : Vec3) (2 * r))).toReal :=
      ENNReal.toReal_mono htop (measure_mono hsub)
    _ = (2 * r) ^ 3 * (Real.pi * 4 / 3) := by
      rw [volume_vec3Ball_eq, ENNReal.toReal_mul, ENNReal.toReal_pow]
      rw [ENNReal.toReal_ofReal (by positivity),
        ENNReal.toReal_ofReal (by positivity)]

private lemma cutoffError_l2_decay {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hlarge : 10 * R ≤ ρ)
    (hRone : 1 ≤ R)
    (hSupp : tsupport F ⊆ Metric.closedBall (0 : Vec3) R) :
    ∫ x, (cutoffError F hρ x) ^ 2 ≤
      (9 * Real.pi / 2) * cutoffErrorConstant F ^ 2 / ρ := by
  have hvol := euclideanClosedBall_volume_toReal_le (r := 3 * ρ / 4)
    (by positivity)
  have hq := cutoffError_l2_bound hF hFc hR hρ hlarge hRone hSupp
  have hC : 0 ≤ cutoffErrorConstant F := cutoffErrorConstant_nonneg
  have hρ4 : 0 < ρ ^ 4 := by positivity
  calc
    ∫ x, (cutoffError F hρ x) ^ 2 ≤
        (cutoffErrorConstant F / ρ ^ 2) ^ 2 *
          (volume (euclideanClosedBall (0 : Vec3) (3 * ρ / 4))).toReal := hq
    _ ≤ (cutoffErrorConstant F / ρ ^ 2) ^ 2 *
          ((2 * (3 * ρ / 4)) ^ 3 * (Real.pi * 4 / 3)) := by
      gcongr
    _ = (9 * Real.pi / 2) * cutoffErrorConstant F ^ 2 / ρ := by
      field_simp [ne_of_gt hρ]
      ring

private lemma cutoff_laplacian_energy_bound {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hlarge : 10 * R ≤ ρ)
    (hRone : 1 ≤ R)
    (hSupp : tsupport F ⊆ Metric.closedBall (0 : Vec3) R) :
    ∫ x, (spatialLaplacian (fun y =>
      mollifiedBallCutoff 0 hρ y * pressureNewtonianPotential F y) x) ^ 2 ≤
      (∫ x, F x ^ 2) + (9 * Real.pi / 2) * cutoffErrorConstant F ^ 2 / ρ := by
  let χ : Vec3 → ℝ := mollifiedBallCutoff 0 hρ
  let w : Vec3 → ℝ := pressureNewtonianPotential F
  let q : Vec3 → ℝ := cutoffError F hρ
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := mollifiedBallCutoff_smooth 0 hρ
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := pressureNewtonianPotential_smooth hF hFc
  have hu : ContDiff ℝ (⊤ : ℕ∞) (fun x => χ x * w x) := hχ.mul hw
  have huc : HasCompactSupport (fun x => χ x * w x) := by
    exact (mollifiedBallCutoff_hasCompactSupport 0 hρ).mul_right
  have hχF : ∀ x, χ x * F x = F x := by
    intro x
    by_cases hx : x ∈ tsupport F
    · have hxR := hSupp hx
      rw [Metric.mem_closedBall, dist_zero_right] at hxR
      have hthree : vecEuclideanNorm (x - 0) ≤ 3 * ‖x‖ := by
        have h := euclideanNorm_le_three_mul_space_norm (x - 0)
        simpa [vecEuclideanNorm, vecNormSq, vecDot, spaceEuclideanNorm, pow_two]
          using h
      have hxinner : vecEuclideanNorm (x - 0) < 13 * ρ / 20 := by
        nlinarith only [hthree, hxR, hlarge, hρ]
      have hχeq := mollifiedBallCutoff_eq_one_on_inner 0 hρ
        ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2 hxinner)
      simp [χ, hχeq]
    · have hFzero : F x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hFzero]
  have hFq : ∀ x, F x * q x = 0 := by
    intro x
    by_cases hx : x ∈ tsupport F
    · have hxR := hSupp hx
      rw [Metric.mem_closedBall, dist_zero_right] at hxR
      have hthree : vecEuclideanNorm (x - 0) ≤ 3 * ‖x‖ := by
        have h := euclideanNorm_le_three_mul_space_norm (x - 0)
        simpa [vecEuclideanNorm, vecNormSq, vecDot, spaceEuclideanNorm, pow_two]
          using h
      have hxinner : vecEuclideanNorm (x - 0) < 13 * ρ / 20 := by
        nlinarith only [hthree, hxR, hlarge, hρ]
      have hxinner' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by positivity)).2 hxinner.le
      have hxnot : x ∉ euclideanBall 0 (3 * ρ / 4) \
          euclideanClosedBall 0 (13 * ρ / 20) := by
        intro hxann
        exact hxann.2 hxinner'
      have hqzero : q x = 0 := by
        exact cutoffError_eq_zero_of_not_annulus hρ hxnot
      simp [q, hqzero]
    · have hFzero : F x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hFzero]
  have hdecomp : ∀ x, spatialLaplacian (fun y => χ y * w y) x =
      F x + q x := by
    intro x
    rw [show (fun y => χ y * w y) =
      (fun y => mollifiedBallCutoff 0 hρ y *
        pressureNewtonianPotential F y) by rfl]
    rw [spatialLaplacian_mul_smooth hχ hw]
    change χ x * spatialLaplacian (pressureNewtonianPotential F) x +
      2 * spatialGradDot χ w x + w x * spatialLaplacian χ x = F x + q x
    rw [pressureNewtonianPotential_laplacian_eq hF hFc x]
    rw [hχF x]
    simp [χ, w, q, cutoffError, add_assoc]
  have hF2comp : HasCompactSupport (fun x => F x ^ 2) := by
    refine hFc.mono ?_
    intro x hx hzero
    apply hx
    simp [hzero]
  have hF2int : Integrable (fun x => F x ^ 2) volume :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport hF2comp
  have hq2comp : HasCompactSupport (fun x => q x ^ 2) := by
    refine (cutoffError_hasCompactSupport (F := F) hρ).mono ?_
    intro x hx hzero
    apply hx
    have hqzero : q x = 0 := (sq_eq_zero_iff).1 (by simpa using hzero)
    simp [hqzero]
  have hq2int : Integrable (fun x => q x ^ 2) volume :=
    ((cutoffError_smooth hF hFc hρ).continuous.pow 2).integrable_of_hasCompactSupport
      hq2comp
  have hsq : ∀ x,
      (spatialLaplacian (fun y => χ y * w y) x) ^ 2 = F x ^ 2 + q x ^ 2 := by
    intro x
    rw [hdecomp x]
    calc
      (F x + q x) ^ 2 = F x ^ 2 + 2 * (F x * q x) + q x ^ 2 := by ring
      _ = F x ^ 2 + q x ^ 2 := by rw [hFq x]; ring
  have henergy :
      ∫ x, (spatialLaplacian (fun y => χ y * w y) x) ^ 2 =
        (∫ x, F x ^ 2) + ∫ x, q x ^ 2 := by
    calc
      ∫ x, (spatialLaplacian (fun y => χ y * w y) x) ^ 2 =
          ∫ x, (F x ^ 2 + q x ^ 2) := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact hsq x
      _ = (∫ x, F x ^ 2) + ∫ x, q x ^ 2 :=
        integral_add hF2int hq2int
  rw [henergy]
  have hqdecay : ∫ x, q x ^ 2 ≤
      (9 * Real.pi / 2) * cutoffErrorConstant F ^ 2 / ρ := by
    simpa [q] using cutoffError_l2_decay hF hFc hR hρ hlarge hRone hSupp
  exact add_le_add_right hqdecay _

private lemma cutoff_mixedSecond_local_bound {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    {R ρ : ℝ} (hR : 0 < R) (hρ : 0 < ρ) (hlarge : 10 * R ≤ ρ)
    (hRone : 1 ≤ R)
    (hSupp : tsupport F ⊆ Metric.closedBall (0 : Vec3) R)
    (n : ℕ) (hninner : 3 * (n : ℝ) < 13 * ρ / 20)
    (i j : Fin 3) :
    ∫ x in Metric.closedBall (0 : Vec3) (n : ℝ),
        (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2 ≤
      (∫ x, F x ^ 2) + (9 * Real.pi / 2) * cutoffErrorConstant F ^ 2 / ρ := by
  let χ : Vec3 → ℝ := mollifiedBallCutoff 0 hρ
  let w : Vec3 → ℝ := pressureNewtonianPotential F
  let u : Vec3 → ℝ := fun x => χ x * w x
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := mollifiedBallCutoff_smooth 0 hρ
  have hw : ContDiff ℝ (⊤ : ℕ∞) w := pressureNewtonianPotential_smooth hF hFc
  have hu : ContDiff ℝ (⊤ : ℕ∞) u := by
    exact hχ.mul hw
  have huc : HasCompactSupport u := by
    exact (mollifiedBallCutoff_hasCompactSupport 0 hρ).mul_right
  have hKcompact : IsCompact (Metric.closedBall (0 : Vec3) (n : ℝ)) :=
    isCompact_closedBall (0 : Vec3) (n : ℝ)
  have hKmeas : MeasurableSet (Metric.closedBall (0 : Vec3) (n : ℝ)) :=
    hKcompact.isClosed.measurableSet
  have hmixedc : HasCompactSupport (mixedSecond u i j) := by
    exact (huc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  have hmixedint : Integrable (fun x => (mixedSecond u i j x) ^ 2) volume :=
    (contDiff_mixedSecond_smooth hu i j).continuous.pow 2 |>.integrable_of_hasCompactSupport
      (hmixedc.mono (fun x hx => by
        intro hzero
        apply hx
        simp [hzero]))
  have hlocaleq : ∀ x ∈ Metric.closedBall (0 : Vec3) (n : ℝ),
      mixedSecond u i j x = mixedSecond w i j x := by
    intro x hx
    have hxnorm := (Metric.mem_closedBall.1 hx)
    rw [dist_zero_right] at hxnorm
    have hthree : vecEuclideanNorm (x - 0) ≤ 3 * ‖x‖ := by
      have h := euclideanNorm_le_three_mul_space_norm (x - 0)
      simpa [vecEuclideanNorm, vecNormSq, vecDot, spaceEuclideanNorm, pow_two]
        using h
    have hvec : vecEuclideanNorm (x - 0) < 13 * ρ / 20 := by
      exact lt_of_le_of_lt (hthree.trans (mul_le_mul_of_nonneg_left hxnorm (by positivity)))
        hninner
    have hχeq := mollifiedBallCutoff_eq_one_on_inner 0 hρ
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2 hvec)
    have hinner' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (by positivity)).2 hvec.le
    have hxnot : x ∉ euclideanBall 0 (3 * ρ / 4) \
        euclideanClosedBall 0 (13 * ρ / 20) := by
      intro hxann
      exact hxann.2 hinner'
    obtain ⟨hgrad, hhess⟩ := pressure_cutoff_derivatives_vanish 0 hρ hxnot
    rw [spatialSecondDeriv_mul_smooth hχ hw i j x]
    simp [w, χ, hχeq, hgrad i, hgrad j, hhess i j]
  have hsetle :
      ∫ x in Metric.closedBall (0 : Vec3) (n : ℝ),
          (mixedSecond u i j x) ^ 2 ≤
        ∫ x, (mixedSecond u i j x) ^ 2 := by
    rw [← integral_indicator hKmeas]
    apply integral_mono (hmixedint.integrableOn.integrable_indicator hKmeas) hmixedint
    intro x
    by_cases hx : x ∈ Metric.closedBall (0 : Vec3) (n : ℝ)
    · simp [Set.indicator_of_mem hx]
    · simp only [Set.indicator_of_notMem hx]
      positivity
  have hcomponent := riesz_second_l2_bound hu huc i j
  have henergy := cutoff_laplacian_energy_bound hF hFc hR hρ hlarge hRone hSupp
  calc
    ∫ x in Metric.closedBall (0 : Vec3) (n : ℝ),
        (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2 =
        ∫ x in Metric.closedBall (0 : Vec3) (n : ℝ),
          (mixedSecond u i j x) ^ 2 := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem hKmeas] with x hx
      rw [hlocaleq x hx]
    _ ≤ ∫ x, (mixedSecond u i j x) ^ 2 := hsetle
    _ ≤ ∫ x, (spatialLaplacian u x) ^ 2 := hcomponent
    _ ≤ (∫ x, F x ^ 2) + (9 * Real.pi / 2) * cutoffErrorConstant F ^ 2 / ρ := by
      simpa [χ, w] using henergy

private lemma exists_cutoff_radius {R : ℝ} (hR : 0 < R) {n : ℕ}
    {ε C : ℝ} (hε : 0 < ε) (hC : 0 ≤ C) :
    ∃ ρ : ℝ, 0 < ρ ∧ 10 * R ≤ ρ ∧
      3 * (n : ℝ) < 13 * ρ / 20 ∧ C / ρ ≤ ε := by
  let ρ : ℝ := 10 * R + 60 * (n : ℝ) / 13 + C / ε + 1
  have hdiv : 0 ≤ C / ε := div_nonneg hC hε.le
  have hn : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hρ : 0 < ρ := by
    dsimp [ρ]
    positivity
  have hlarge : 10 * R ≤ ρ := by
    dsimp [ρ]
    nlinarith only [hdiv, hn]
  have hinner : 3 * (n : ℝ) < 13 * ρ / 20 := by
    dsimp [ρ]
    nlinarith only [hR, hε, hdiv]
  have hρC : C / ε ≤ ρ := by
    dsimp [ρ]
    nlinarith only [hR, hdiv, hn]
  have herror : C / ρ ≤ ε := by
    apply (div_le_iff₀ hρ).2
    have hmul := (div_le_iff₀ hε).1 hρC
    nlinarith only [hmul]
  exact ⟨ρ, hρ, hlarge, hinner, herror⟩

private lemma riesz_second_l2_bound_global_ofReal {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (i j : Fin 3) :
    ∫⁻ x, ENNReal.ofReal
        ((mixedSecond (pressureNewtonianPotential F) i j x) ^ 2) ≤
      ∫⁻ x, ENNReal.ofReal (F x ^ 2) := by
  let g : Vec3 → ENNReal := fun x => ENNReal.ofReal
    ((mixedSecond (pressureNewtonianPotential F) i j x) ^ 2)
  let b : ENNReal := ∫⁻ x, ENNReal.ofReal (F x ^ 2)
  change (∫⁻ x, g x) ≤ b
  obtain ⟨R, hR, hRone, hSupp⟩ := pressure_potential_compact_radius hFc
  have hF2int : Integrable (fun x => F x ^ 2) volume := by
    have hF2comp : HasCompactSupport (fun x => F x ^ 2) := by
      refine hFc.mono ?_
      intro x hx hzero
      apply hx
      simp [hzero]
    exact (hF.continuous.pow 2).integrable_of_hasCompactSupport hF2comp
  have hFnn : 0 ≤ᵐ[volume] (fun x => F x ^ 2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg (F x))
  have hFof : ENNReal.ofReal (∫ x, F x ^ 2) = b := by
    simpa [b] using
      (ofReal_integral_eq_lintegral_ofReal hF2int hFnn)
  have hbtop : b < ∞ := by
    rw [← hFof]
    exact ENNReal.ofReal_lt_top
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε hb
  have hεr : 0 < (ε : ℝ) := by exact_mod_cast hε
  let C : ℝ := (9 * Real.pi / 2) * cutoffErrorConstant F ^ 2
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hCbound : ∀ n : ℕ, ∃ ρ : ℝ, 0 < ρ ∧ 10 * R ≤ ρ ∧
      3 * (n : ℝ) < 13 * ρ / 20 ∧ C / ρ ≤ (ε : ℝ) := by
    intro n
    exact exists_cutoff_radius hR hεr hC
  have hset : ∀ n : ℕ,
      ∫⁻ x in Metric.closedBall (0 : Vec3) (n : ℝ), g x ≤ b + ε := by
    intro n
    obtain ⟨ρ, hρ, hlarge, hninner, herror⟩ := hCbound n
    have hlocal := cutoff_mixedSecond_local_bound hF hFc hR hρ hlarge hRone
      hSupp n hninner i j
    let K : Set Vec3 := Metric.closedBall (0 : Vec3) (n : ℝ)
    have hKcompact : IsCompact K := by
      dsimp [K]
      exact isCompact_closedBall (0 : Vec3) (n : ℝ)
    have hKmeas : MeasurableSet K := hKcompact.isClosed.measurableSet
    have hwi : Integrable (fun x =>
        (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2)
        (volume.restrict K) := by
      exact ((contDiff_mixedSecond_smooth
        (pressureNewtonianPotential_smooth hF hFc) i j).continuous.pow
          2).continuousOn.integrableOn_compact
          hKcompact
    have hwi_nn : 0 ≤ᵐ[volume.restrict K] (fun x =>
        (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2) :=
      Filter.Eventually.of_forall (fun x => sq_nonneg _)
    have hconvert := ofReal_integral_eq_lintegral_ofReal hwi hwi_nn
    have hlocal' : ∫ x in K,
        (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2 ≤
        (∫ x, F x ^ 2) + (ε : ℝ) := by
      calc
        ∫ x in K, (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2 ≤
            (∫ x, F x ^ 2) + C / ρ := by
          simpa [K] using hlocal
        _ ≤ (∫ x, F x ^ 2) + (ε : ℝ) := by
          exact add_le_add_right herror _
    have hIF : 0 ≤ ∫ x, F x ^ 2 := integral_nonneg (fun x => sq_nonneg _)
    have hset' : ∫⁻ x in K, g x ≤ b + ε := by
      calc
        ∫⁻ x in K, g x = ENNReal.ofReal
            (∫ x in K, (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2) := by
          simpa [g, K] using hconvert.symm
        _ ≤ ENNReal.ofReal ((∫ x, F x ^ 2) + (ε : ℝ)) :=
          ENNReal.ofReal_le_ofReal hlocal'
        _ = ENNReal.ofReal (∫ x, F x ^ 2) + ENNReal.ofReal (ε : ℝ) :=
          ENNReal.ofReal_add hIF hεr.le
        _ = b + ε := by
          rw [hFof]
          simp [ENNReal.ofReal_coe_nnreal]
    simpa [K] using hset'
  have hd : Directed (fun s t : Set Vec3 => s ⊆ t)
      (fun n : ℕ => Metric.closedBall (0 : Vec3) (n : ℝ)) := by
    intro a b
    refine ⟨max a b, ?_, ?_⟩
    · apply Metric.closedBall_subset_closedBall
      exact_mod_cast Nat.le_max_left a b
    · apply Metric.closedBall_subset_closedBall
      exact_mod_cast Nat.le_max_right a b
  calc
    ∫⁻ x, g x = ∫⁻ x in Set.univ, g x := by simp
    _ = ∫⁻ x in ⋃ n : ℕ, Metric.closedBall (0 : Vec3) (n : ℝ), g x := by
      rw [Metric.iUnion_closedBall_nat]
    _ = ⨆ n : ℕ, ∫⁻ x in Metric.closedBall (0 : Vec3) (n : ℝ), g x :=
      setLIntegral_iUnion_of_directed g hd
    _ ≤ b + ε := iSup_le hset

/-- The global strong `(2,2)` estimate for one Hessian component of the
Newtonian potential, in the ENNReal interface used by interpolation. -/
theorem riesz_second_l2_bound_global {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (i j : Fin 3) :
    ∫⁻ x, absE (fun y => mixedSecond (pressureNewtonianPotential F) i j y) x ^
        (2 : ℕ) ≤
      ENNReal.ofReal ((1 : ℝ) ^ 2) * ∫⁻ x, absE F x ^ (2 : ℕ) := by
  have h := riesz_second_l2_bound_global_ofReal hF hFc i j
  have hleft : ∀ x, absE
      (fun y => mixedSecond (pressureNewtonianPotential F) i j y) x ^ (2 : ℕ) =
      ENNReal.ofReal ((mixedSecond (pressureNewtonianPotential F) i j x) ^ 2) := by
    intro x
    rw [absE, ← ENNReal.ofReal_pow (abs_nonneg _) 2]
    simp [sq_abs]
  have hright : ∀ x, absE F x ^ (2 : ℕ) = ENNReal.ofReal (F x ^ 2) := by
    intro x
    rw [absE, ← ENNReal.ofReal_pow (abs_nonneg _) 2]
    simp [sq_abs]
  simp only [hleft, hright, one_pow, ENNReal.ofReal_one, one_mul]
  exact h

/-- The same endpoint estimate as a finite real Lebesgue-integral inequality. -/
theorem riesz_second_l2_bound_global_real {F : Vec3 → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFc : HasCompactSupport F)
    (i j : Fin 3) :
    ∫ x, (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2 ≤
      ∫ x, F x ^ 2 := by
  have hF2comp : HasCompactSupport (fun x => F x ^ 2) := by
    refine hFc.mono ?_
    intro x hx hzero
    apply hx
    simp [hzero]
  have hF2int : Integrable (fun x => F x ^ 2) volume :=
    (hF.continuous.pow 2).integrable_of_hasCompactSupport hF2comp
  have hFnn : 0 ≤ᵐ[volume] (fun x => F x ^ 2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg (F x))
  have hFof := ofReal_integral_eq_lintegral_ofReal hF2int hFnn
  have hFtop : (∫⁻ x, ENNReal.ofReal (F x ^ 2)) ≠ ∞ := by
    rw [← hFof]
    exact ENNReal.ofReal_ne_top
  have hglobal := riesz_second_l2_bound_global_ofReal hF hFc i j
  have hdesttop : (∫⁻ x, ENNReal.ofReal
      ((mixedSecond (pressureNewtonianPotential F) i j x) ^ 2)) ≠ ∞ := by
    exact ne_of_lt (lt_of_le_of_lt hglobal (lt_top_iff_ne_top.mpr hFtop))
  have hdestint : Integrable (fun x =>
      (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2) volume := by
    apply (lintegral_ofReal_ne_top_iff_integrable
      ((contDiff_mixedSecond_smooth
        (pressureNewtonianPotential_smooth hF hFc) i j).continuous.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x => sq_nonneg _))).1
    exact hdesttop
  have hdestnn : 0 ≤ᵐ[volume] (fun x =>
      (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2) :=
    Filter.Eventually.of_forall (fun x => sq_nonneg _)
  have hdestof := ofReal_integral_eq_lintegral_ofReal hdestint hdestnn
  have hreal : ENNReal.ofReal
      (∫ x, (mixedSecond (pressureNewtonianPotential F) i j x) ^ 2) ≤
      ENNReal.ofReal (∫ x, F x ^ 2) := by
    simpa [hdestof, hFof] using hglobal
  have hFintnonneg : 0 ≤ ∫ x, F x ^ 2 :=
    integral_nonneg (fun x => sq_nonneg (F x))
  exact (ENNReal.ofReal_le_ofReal_iff hFintnonneg).1 hreal

end CKN.Foundation.Euclidean
