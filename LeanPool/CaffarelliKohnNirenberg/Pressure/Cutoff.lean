/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Mollify.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Equiv
public import Mathlib.Analysis.Normed.Lp.PiLp

/-!
# A smooth ball cut-off with two derivative bounds

The native carrier is `Fin 3 → ℝ`.  The cut-off below is obtained by
convolving the indicator of the `7ρ/10` ball with a normalized smooth bump.
The bump is chosen with a slightly smaller inherited-metric radius so that
its Euclidean support has a strict collar in the native carrier.  This keeps
the stated Euclidean radii literal while avoiding an implicit change of norm.
-/

@[expose] public section

open Set MeasureTheory Metric
open scoped Convolution


noncomputable section

namespace CKN

private lemma vecEuclideanNorm_eq_l2 (x : Vec 3) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [vecEuclideanNorm, vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private lemma vecEuclideanNorm_add_le (x y : Vec 3) :
    vecEuclideanNorm (x + y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  rw [vecEuclideanNorm_eq_l2, vecEuclideanNorm_eq_l2, vecEuclideanNorm_eq_l2]
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

private lemma vecEuclideanNorm_eq_spaceEuclideanNorm (x : Vec 3) :
    vecEuclideanNorm x = spaceEuclideanNorm x := by
  simp [vecEuclideanNorm, spaceEuclideanNorm, vecNormSq, vecDot, pow_two]

private lemma euclideanBall_measurable (x₀ : Vec 3) (R : ℝ) :
    MeasurableSet (euclideanBall x₀ R) := by
  change MeasurableSet ((fun x : Vec 3 => euclideanSqDist x x₀) ⁻¹' Iio (R ^ 2))
  exact measurableSet_Iio.preimage
    (contDiff_euclideanSqDist_left x₀).continuous.measurable

def ballIndicator (x₀ : Vec 3) (R : ℝ) : Vec 3 → ℝ :=
  (euclideanBall x₀ R).indicator (fun _ => 1)

private lemma ballIndicator_locallyIntegrable (x₀ : Vec 3) (R : ℝ) :
    LocallyIntegrable (ballIndicator x₀ R) volume := by
  exact (locallyIntegrable_const (1 : ℝ)).indicator
    (euclideanBall_measurable x₀ R)

def unitBallCutoff : Vec 3 → ℝ :=
  mollify (ballIndicator 0 (7 / 10)) (1 / 100) (by norm_num)

private lemma unitBallCutoff_smooth :
    ContDiff ℝ (⊤ : ℕ∞) unitBallCutoff := by
  simpa [unitBallCutoff] using
    (mollify_contDiff (d := 3) (u := ballIndicator 0 (7 / 10))
      (ε := (1 / 100 : ℝ)) (by norm_num)
      (ballIndicator_locallyIntegrable 0 (7 / 10)))

private lemma mollifier_mem_ball_of_ne_zero {ε : ℝ} (hε : 0 < ε)
    {y : Vec 3} (hy : mollifier ε hε y ≠ 0) :
    y ∈ Metric.ball 0 ε := by
  have hy' : y ∈ Function.support (mollifier ε hε) := hy
  have hy'' : y ∈ Metric.ball (0 : Vec 3) ε := by
    change y ∈ Function.support ((standardMollifier (d := 3) ε hε).normed volume) at hy'
    rw [(standardMollifier (d := 3) ε hε).support_normed_eq] at hy'
    simpa [standardMollifier] using hy'
  simpa [Metric.mem_ball, dist_eq_norm] using hy''

private lemma unitBallCutoff_eq_one_of_norm_lt {x : Vec 3}
    (hx : vecEuclideanNorm (x - 0) < (67 / 100 : ℝ)) :
    unitBallCutoff x = 1 := by
  have hconst : ∀ y ∈ Metric.ball x (1 / 100 : ℝ),
      ballIndicator 0 (7 / 10) y = ballIndicator 0 (7 / 10) x := by
    intro y hy
    have hyx : ‖y - x‖ < (1 / 100 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
    have hye : vecEuclideanNorm (y - x) < (3 / 100 : ℝ) := by
      calc
        vecEuclideanNorm (y - x) ≤ 3 * ‖y - x‖ :=
          by simpa [vecEuclideanNorm_eq_spaceEuclideanNorm] using
            (euclideanNorm_le_three_mul_space_norm (y - x))
        _ < 3 / 100 := by nlinarith only [hyx]
    have hxy : vecEuclideanNorm (x - 0) < (67 / 100 : ℝ) := hx
    have hyball : y ∈ euclideanBall 0 (7 / 10) := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
      have hsum := vecEuclideanNorm_add_le (y - x) (x - 0)
      have heq : y - 0 = (y - x) + (x - 0) := by abel
      rw [heq]
      linarith only [hsum, hye, hxy]
    have hxball : x ∈ euclideanBall 0 (7 / 10) := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
      linarith only [hxy]
    simp [ballIndicator, hyball, hxball]
  have hconv := ContDiffBump.normed_convolution_eq_right
      (μ := (volume : Measure (Vec 3)))
      (φ := standardMollifier (1 / 100 : ℝ) (by norm_num))
      (g := ballIndicator 0 (7 / 10)) hconst
  have hxball : x ∈ euclideanBall 0 (7 / 10) := by
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
    linarith only [hx]
  calc
    unitBallCutoff x = ballIndicator 0 (7 / 10) x := by
      simpa [unitBallCutoff, mollify, mollifier] using hconv
    _ = 1 := by simp [ballIndicator, hxball]

private lemma unitBallCutoff_eq_one_on_inner {x : Vec 3}
    (hx : x ∈ euclideanBall 0 (13 / 20)) : unitBallCutoff x = 1 := by
  apply unitBallCutoff_eq_one_of_norm_lt
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (x₀ := (0 : Vec 3)) (x := x) (by norm_num)).mp hx
  simpa [sub_zero] using lt_trans hx' (by norm_num : (13 / 20 : ℝ) < 67 / 100)

private lemma unitBallCutoff_eq_zero_of_not_mem_closedBall {x : Vec 3}
    (hx : x ∉ euclideanClosedBall 0 (73 / 100)) : unitBallCutoff x = 0 := by
  rw [unitBallCutoff, mollify, MeasureTheory.convolution_def]
  apply integral_eq_zero_of_ae
  filter_upwards [] with y
  by_cases hy : mollifier (1 / 100 : ℝ) (by norm_num) y = 0
  · rw [hy]
    simp
  · have hyball := mollifier_mem_ball_of_ne_zero (by norm_num : (0 : ℝ) < 1 / 100) hy
    have hynorm : ‖y‖ < (1 / 100 : ℝ) := by
      simpa [Metric.mem_ball, dist_eq_norm] using hyball
    by_cases hbase : ballIndicator 0 (7 / 10) (x - y) = 0
    · simp [hbase]
    · have hxy : x - y ∈ euclideanBall 0 (7 / 10) := by
        by_contra hnot
        apply hbase
        simp [ballIndicator, hnot]
      have hxy' : vecEuclideanNorm (x - y) < (7 / 10 : ℝ) := by
        simpa using (mem_euclideanBall_iff_vecEuclideanNorm_lt
          (x₀ := (0 : Vec 3)) (x := x - y) (by norm_num)).mp hxy
      have hye : vecEuclideanNorm y < (3 / 100 : ℝ) := by
        calc
          vecEuclideanNorm y ≤ 3 * ‖y‖ := by
            simpa [vecEuclideanNorm_eq_spaceEuclideanNorm] using
              (euclideanNorm_le_three_mul_space_norm y)
          _ < 3 / 100 := by nlinarith only [hynorm]
      have hsum := vecEuclideanNorm_add_le (x - y) y
      have heq : x - 0 = (x - y) + y := by abel
      have hlt : vecEuclideanNorm (x - 0) < (73 / 100 : ℝ) := by
        rw [heq]
        linarith only [hsum, hxy', hye]
      exact False.elim (hx ((mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by norm_num : (0 : ℝ) ≤ 73 / 100)).2 hlt.le))

private lemma unitBallCutoff_nonneg (x : Vec 3) : 0 ≤ unitBallCutoff x := by
  rw [unitBallCutoff, mollify, MeasureTheory.convolution_def]
  apply integral_nonneg
  intro y
  exact mul_nonneg (mollifier_nonneg (by norm_num) y)
    (show 0 ≤ ballIndicator 0 (7 / 10) (x - y) by
      exact indicator_nonneg (by intro z _hz; norm_num) _)

private lemma unitBallCutoff_le_one (x : Vec 3) : unitBallCutoff x ≤ 1 := by
  rw [unitBallCutoff, mollify, MeasureTheory.convolution_def]
  calc
    ∫ y, mollifier (1 / 100 : ℝ) (by norm_num) y *
        ballIndicator 0 (7 / 10) (x - y) ∂volume ≤
      ∫ y, mollifier (1 / 100 : ℝ) (by norm_num) y ∂volume := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall (fun y =>
            mul_nonneg (mollifier_nonneg (by norm_num) y)
              (show 0 ≤ ballIndicator 0 (7 / 10) (x - y) by
                exact indicator_nonneg (by intro z _hz; norm_num) _))
        · exact (standardMollifier (1 / 100 : ℝ) (by norm_num)).integrable_normed
        · exact Filter.Eventually.of_forall (fun y => by
            change mollifier (1 / 100 : ℝ) (by norm_num) y *
              ballIndicator 0 (7 / 10) (x - y) ≤
                mollifier (1 / 100 : ℝ) (by norm_num) y
            have hle : ballIndicator 0 (7 / 10) (x - y) ≤ 1 := by
              by_cases hmem : x - y ∈ euclideanBall 0 (7 / 10)
              · simp [ballIndicator, hmem]
              · simp [ballIndicator, hmem]
            simpa only [mul_one] using
              (mul_le_mul_of_nonneg_left hle
                (mollifier_nonneg (d := 3) (ε := (1 / 100 : ℝ)) (by norm_num) y)))
    _ = 1 := mollifier_integral_one (by norm_num)

private lemma unitBallCutoff_tsupport_subset :
    tsupport unitBallCutoff ⊆ euclideanClosedBall 0 (73 / 100) := by
  apply closure_minimal
  · intro x hx
    by_contra hnot
    exact hx (unitBallCutoff_eq_zero_of_not_mem_closedBall hnot)
  · exact isClosed_euclideanClosedBall 0 (73 / 100)

/-- The convolution cut-off at center `x₀` and radius `ρ`. -/
def mollifiedBallCutoff (x₀ : Vec 3) {ρ : ℝ} (_hρ : 0 < ρ) : Vec 3 → ℝ :=
  fun x => unitBallCutoff (ρ⁻¹ • (x - x₀))

theorem mollifiedBallCutoff_smooth (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ) :
    ContDiff ℝ (⊤ : ℕ∞) (mollifiedBallCutoff x₀ hρ) := by
  unfold mollifiedBallCutoff
  apply unitBallCutoff_smooth.comp
  fun_prop

theorem mollifiedBallCutoff_nonneg (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Vec 3) : 0 ≤ mollifiedBallCutoff x₀ hρ x := by
  exact unitBallCutoff_nonneg _

theorem mollifiedBallCutoff_le_one (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ)
    (x : Vec 3) : mollifiedBallCutoff x₀ hρ x ≤ 1 := by
  exact unitBallCutoff_le_one _

theorem mollifiedBallCutoff_eq_one_on_inner (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) {x : Vec 3}
    (hx : x ∈ euclideanBall x₀ (13 * ρ / 20)) :
    mollifiedBallCutoff x₀ hρ x = 1 := by
  apply unitBallCutoff_eq_one_on_inner
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (x₀ := x₀) (x := x) (by positivity)).mp hx
  have hρne : ρ ≠ 0 := hρ.ne'
  rw [sub_zero, vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hρ)]
  change ρ⁻¹ * vecEuclideanNorm (x - x₀) < 13 / 20
  rw [← div_eq_inv_mul]
  exact (div_lt_iff₀ hρ).2 (by nlinarith only [hx'])

private lemma mollifiedBallCutoff_eq_zero_of_not_mem_closedBall (x₀ : Vec 3)
    {ρ : ℝ} (hρ : 0 < ρ) {x : Vec 3}
    (hx : x ∉ euclideanClosedBall x₀ (73 * ρ / 100)) :
    mollifiedBallCutoff x₀ hρ x = 0 := by
  apply unitBallCutoff_eq_zero_of_not_mem_closedBall
  intro hy
  apply hx
  apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
  have hy' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
    (by norm_num : (0 : ℝ) ≤ 73 / 100)).mp hy
  rw [sub_zero, vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hρ)] at hy'
  have hρne : ρ ≠ 0 := hρ.ne'
  have hle : vecEuclideanNorm (x - x₀) ≤ 73 * ρ / 100 := by
    have hmul := mul_le_mul_of_nonneg_right hy' hρ.le
    calc
      vecEuclideanNorm (x - x₀) =
          (ρ⁻¹ * vecEuclideanNorm (x - x₀)) * ρ := by
            field_simp [hρne]
      _ ≤ (73 / 100) * ρ := hmul
      _ = 73 * ρ / 100 := by ring
  exact hle

theorem mollifiedBallCutoff_hasCompactSupport (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) : HasCompactSupport (mollifiedBallCutoff x₀ hρ) := by
  refine HasCompactSupport.intro
    (isCompact_euclideanClosedBall x₀ (R := 73 * ρ / 100) (by positivity)) ?_
  intro x hx
  exact mollifiedBallCutoff_eq_zero_of_not_mem_closedBall x₀ hρ hx

private lemma mollifiedBallCutoff_tsupport_subset_closedBall (x₀ : Vec 3)
    {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (mollifiedBallCutoff x₀ hρ) ⊆
      euclideanClosedBall x₀ (73 * ρ / 100) := by
  apply closure_minimal
  · intro x hx
    by_contra hnot
    exact hx (mollifiedBallCutoff_eq_zero_of_not_mem_closedBall x₀ hρ hnot)
  · exact isClosed_euclideanClosedBall x₀ _

theorem mollifiedBallCutoff_tsupport_subset_outer (x₀ : Vec 3)
    {ρ : ℝ} (hρ : 0 < ρ) :
    tsupport (mollifiedBallCutoff x₀ hρ) ⊆
      euclideanBall x₀ (3 * ρ / 4) := by
  exact (mollifiedBallCutoff_tsupport_subset_closedBall x₀ hρ).trans
    (euclideanClosedBall_subset_euclideanBall (x₀ := x₀)
      (r := 73 * ρ / 100) (R := 3 * ρ / 4) (by positivity) (by
        nlinarith only [hρ]))

private lemma unitGradient_eq_zero_of_not_mem_closedBall {x : Vec 3}
    (hx : x ∉ euclideanClosedBall 0 (73 / 100)) :
    classicalGradient unitBallCutoff x = 0 := by
  have hx' : x ∉ tsupport unitBallCutoff := by
    intro h
    exact hx (unitBallCutoff_tsupport_subset h)
  have hfd : fderiv ℝ unitBallCutoff x = 0 :=
    fderiv_of_notMem_tsupport ℝ hx'
  funext i
  rw [classicalGradient_apply, hfd]
  simp

private lemma unitGradient_eq_zero_of_norm_lt {x : Vec 3}
    (hx : vecEuclideanNorm (x - 0) < (67 / 100 : ℝ)) :
    classicalGradient unitBallCutoff x = 0 := by
  let δ : ℝ := (67 / 100 - vecEuclideanNorm (x - 0)) / 6
  have hδ : 0 < δ := by
    dsimp [δ]
    linarith only [hx]
  have hlocal : unitBallCutoff =ᶠ[nhds x] (fun _ : Vec 3 => (1 : ℝ)) := by
    filter_upwards [Metric.ball_mem_nhds x hδ] with y hy
    have hyx : ‖y - x‖ < δ := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
    have hye : vecEuclideanNorm (y - x) < 3 * δ := by
      calc
        vecEuclideanNorm (y - x) ≤ 3 * ‖y - x‖ := by
          simpa [vecEuclideanNorm_eq_spaceEuclideanNorm] using
            (euclideanNorm_le_three_mul_space_norm (y - x))
        _ < 3 * δ := by nlinarith only [hyx, hδ]
    have hsum := vecEuclideanNorm_add_le (y - x) (x - 0)
    have heq : y - 0 = (y - x) + (x - 0) := by abel
    have hy' : vecEuclideanNorm (y - 0) < (67 / 100 : ℝ) := by
      rw [heq]
      dsimp [δ] at hye ⊢
      linarith only [hsum, hye, hx]
    simpa using unitBallCutoff_eq_one_of_norm_lt hy'
  have hfd : fderiv ℝ unitBallCutoff x =
      fderiv ℝ (fun _ : Vec 3 => (1 : ℝ)) x := hlocal.fderiv_eq
  funext i
  rw [classicalGradient_apply, hfd]
  simp

private lemma unitGradient_hasCompactSupport :
    HasCompactSupport (classicalGradient unitBallCutoff) := by
  refine HasCompactSupport.intro
    (isCompact_euclideanClosedBall (d := 3) 0 (R := (73 / 100 : ℝ))
      (by norm_num)) ?_
  intro x hx
  exact unitGradient_eq_zero_of_not_mem_closedBall hx

private lemma unitGradient_tsupport_subset_closedBall :
    tsupport (classicalGradient unitBallCutoff) ⊆
      euclideanClosedBall 0 (73 / 100) := by
  apply closure_minimal
  · intro x hx
    by_contra hnot
    exact hx (unitGradient_eq_zero_of_not_mem_closedBall hnot)
  · exact isClosed_euclideanClosedBall 0 (73 / 100)

private lemma unitHessian_eq_zero_of_not_mem_closedBall {x : Vec 3}
    (hx : x ∉ euclideanClosedBall 0 (73 / 100)) :
    fderiv ℝ (classicalGradient unitBallCutoff) x = 0 := by
  apply fderiv_of_notMem_tsupport ℝ
  intro hx'
  exact hx (unitGradient_tsupport_subset_closedBall hx')

private lemma unitGradient_smooth :
    ContDiff ℝ (⊤ : ℕ∞) (classicalGradient unitBallCutoff) := by
  rw [contDiff_pi]
  intro i
  change ContDiff ℝ (⊤ : ℕ∞)
    (fun x => (fderiv ℝ unitBallCutoff x) (basisVec i))
  have hfd := unitBallCutoff_smooth.contDiff_fderiv_apply
    (m := (⊤ : ℕ∞)) (by simp)
  let hmap : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Vec 3 => (x, basisVec i)) :=
    contDiff_id.prodMk (contDiff_const :
      ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 3 => basisVec i))
  have hcomp := hfd.comp hmap
  simpa [Function.comp_def] using hcomp

private lemma unitGradient_norm_continuous :
    Continuous (fun x => vecEuclideanNorm (classicalGradient unitBallCutoff x)) := by
  have hgrad : Continuous (classicalGradient unitBallCutoff) :=
    unitGradient_smooth.continuous
  unfold vecEuclideanNorm vecNormSq vecDot
  apply Real.continuous_sqrt.comp
  apply continuous_finsetSum
  intro i _hi
  exact ((continuous_apply i).comp hgrad).mul ((continuous_apply i).comp hgrad)

private lemma unitHessian_norm_continuous :
    Continuous (fun x => ‖fderiv ℝ (classicalGradient unitBallCutoff) x‖) := by
  exact (unitGradient_smooth.continuous_fderiv (by simp)).norm

private lemma unitHessian_hasCompactSupport :
    HasCompactSupport (fderiv ℝ (classicalGradient unitBallCutoff)) := by
  exact unitGradient_hasCompactSupport.fderiv ℝ

/-- The absolute unit-scale gradient constant of the convolution cut-off. -/
noncomputable def cutoffGradientConstant : ℝ :=
  sSup (Set.range (fun x : Vec 3 =>
    vecEuclideanNorm (classicalGradient unitBallCutoff x)))

/-- The absolute unit-scale second-derivative constant of the convolution
cut-off. -/
noncomputable def cutoffSecondDerivativeConstant : ℝ :=
  sSup (Set.range (fun x : Vec 3 =>
    ‖fderiv ℝ (classicalGradient unitBallCutoff) x‖))

private lemma cutoffGradientConstant_bddAbove :
    BddAbove (Set.range (fun x : Vec 3 =>
      vecEuclideanNorm (classicalGradient unitBallCutoff x))) := by
  exact unitGradient_norm_continuous.bddAbove_range_of_hasCompactSupport
    (HasCompactSupport.intro
      (isCompact_euclideanClosedBall (d := 3) 0 (R := (73 / 100 : ℝ))
        (by norm_num)) (by
        intro x hx
        rw [unitGradient_eq_zero_of_not_mem_closedBall hx]
        simp [vecEuclideanNorm, vecNormSq, vecDot]))

private lemma cutoffSecondDerivativeConstant_bddAbove :
    BddAbove (Set.range (fun x : Vec 3 =>
      ‖fderiv ℝ (classicalGradient unitBallCutoff) x‖)) := by
  exact unitHessian_norm_continuous.bddAbove_range_of_hasCompactSupport
    unitHessian_hasCompactSupport.norm

private lemma unitGradient_norm_le_constant (x : Vec 3) :
    vecEuclideanNorm (classicalGradient unitBallCutoff x) ≤
      cutoffGradientConstant := by
  exact le_csSup cutoffGradientConstant_bddAbove (Set.mem_range_self x)

private lemma unitHessian_norm_le_constant (x : Vec 3) :
    ‖fderiv ℝ (classicalGradient unitBallCutoff) x‖ ≤
      cutoffSecondDerivativeConstant := by
  exact le_csSup cutoffSecondDerivativeConstant_bddAbove (Set.mem_range_self x)

private lemma mollifiedBallCutoff_gradient_formula (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Vec 3) :
    classicalGradient (mollifiedBallCutoff x₀ hρ) x =
      ρ⁻¹ • classicalGradient unitBallCutoff (ρ⁻¹ • (x - x₀)) := by
  have hA : HasFDerivAt (fun y : Vec 3 => ρ⁻¹ • (y - x₀))
      (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3)) x := by
    have hid := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀
    simpa using hid.const_smul (ρ⁻¹ : ℝ)
  have hunit : DifferentiableAt ℝ unitBallCutoff
      (ρ⁻¹ • (x - x₀)) :=
    unitBallCutoff_smooth.differentiable (by simp) _
  have hcomp := hunit.hasFDerivAt.comp x hA
  funext i
  change (fderiv ℝ
      (fun y : Vec 3 => unitBallCutoff (ρ⁻¹ • (y - x₀))) x) (basisVec i) = _
  rw [show (fun y : Vec 3 => unitBallCutoff (ρ⁻¹ • (y - x₀))) =
      unitBallCutoff ∘ (fun y : Vec 3 => ρ⁻¹ • (y - x₀)) by rfl]
  rw [hcomp.fderiv]
  simp [classicalGradient, smul_eq_mul]

private lemma mollifiedBallCutoff_hessian_formula (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Vec 3) :
    fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x =
      ρ⁻¹ • ((fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))).comp
        (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3))) := by
  have hA : HasFDerivAt (fun y : Vec 3 => ρ⁻¹ • (y - x₀))
      (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3)) x := by
    have hid := (hasFDerivAt_id (𝕜 := ℝ) x).sub_const x₀
    simpa using hid.const_smul (ρ⁻¹ : ℝ)
  have hgrad : DifferentiableAt ℝ (classicalGradient unitBallCutoff)
      (ρ⁻¹ • (x - x₀)) :=
    unitGradient_smooth.differentiable (by simp) _
  have hcomp := hgrad.hasFDerivAt.comp x hA
  have hscaled := hcomp.const_smul (ρ⁻¹ : ℝ)
  have hfun : classicalGradient (mollifiedBallCutoff x₀ hρ) =
      (fun y : Vec 3 => ρ⁻¹ • classicalGradient unitBallCutoff
        (ρ⁻¹ • (y - x₀))) := by
    funext y
    exact mollifiedBallCutoff_gradient_formula x₀ hρ y
  rw [hfun]
  have hpointwise :
      (ρ⁻¹ • (classicalGradient unitBallCutoff ∘
        (fun y : Vec 3 => ρ⁻¹ • (y - x₀)))) =
      (fun y : Vec 3 => ρ⁻¹ • classicalGradient unitBallCutoff
        (ρ⁻¹ • (y - x₀))) := by
    funext y
    rfl
  rw [← hpointwise]
  simpa [Function.comp_def] using hscaled.fderiv

private lemma mollifiedBallCutoff_gradient_eq_zero_on_closed_inner
    (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ) {x : Vec 3}
    (hx : x ∈ euclideanClosedBall x₀ (13 * ρ / 20)) :
    classicalGradient (mollifiedBallCutoff x₀ hρ) x = 0 := by
  rw [mollifiedBallCutoff_gradient_formula]
  apply smul_eq_zero.mpr
  right
  apply unitGradient_eq_zero_of_norm_lt
  have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
    (x₀ := x₀) (x := x) (by positivity)).mp hx
  rw [sub_zero, vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hρ)]
  calc
    ρ⁻¹ * vecEuclideanNorm (x - x₀) ≤
        ρ⁻¹ * (13 * ρ / 20) :=
      mul_le_mul_of_nonneg_left hx' (by positivity)
    _ = 13 / 20 := by
      field_simp [hρ.ne']
    _ < 67 / 100 := by norm_num

private lemma mollifiedBallCutoff_hessian_eq_zero_on_closed_inner
    (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ) {x : Vec 3}
    (hx : x ∈ euclideanClosedBall x₀ (13 * ρ / 20)) :
    fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x = 0 := by
  have hlocal : classicalGradient (mollifiedBallCutoff x₀ hρ) =ᶠ[nhds x]
      (fun _ : Vec 3 => (0 : Vec 3)) := by
    filter_upwards [Metric.ball_mem_nhds x (by positivity : (0 : ℝ) < ρ / 1000)]
      with y hy
    have hyx : ‖y - x‖ < ρ / 1000 := by
      simpa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] using hy
    have hye : vecEuclideanNorm (y - x) < 3 * ρ / 1000 := by
      calc
        vecEuclideanNorm (y - x) ≤ 3 * ‖y - x‖ := by
          simpa [vecEuclideanNorm_eq_spaceEuclideanNorm] using
            (euclideanNorm_le_three_mul_space_norm (y - x))
        _ < 3 * ρ / 1000 := by nlinarith only [hyx]
    have hx' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (x₀ := x₀) (x := x) (by positivity)).mp hx
    have hsum := vecEuclideanNorm_add_le (y - x) (x - x₀)
    have heq : y - x₀ = (y - x) + (x - x₀) := by abel
    have htotal : vecEuclideanNorm (y - x₀) <
        13 * ρ / 20 + 3 * ρ / 1000 := by
      rw [heq]
      linarith only [hsum, hye, hx']
    have hy' : vecEuclideanNorm (ρ⁻¹ • (y - x₀) - 0) <
        (67 / 100 : ℝ) := by
      rw [sub_zero, vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hρ)]
      calc
        ρ⁻¹ * vecEuclideanNorm (y - x₀) <
            ρ⁻¹ * (13 * ρ / 20 + 3 * ρ / 1000) :=
          mul_lt_mul_of_pos_left htotal (by positivity)
        _ = 13 / 20 + 3 / 1000 := by
          field_simp [hρ.ne']
        _ < 67 / 100 := by norm_num
    rw [mollifiedBallCutoff_gradient_formula]
    simp [unitGradient_eq_zero_of_norm_lt hy']
  simpa using hlocal.fderiv_eq

private lemma mollifiedBallCutoff_gradient_eq_zero_of_not_mem_outer
    (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ) {x : Vec 3}
    (hx : x ∉ euclideanBall x₀ (3 * ρ / 4)) :
    classicalGradient (mollifiedBallCutoff x₀ hρ) x = 0 := by
  have hscaled : ρ⁻¹ • (x - x₀) ∉ euclideanClosedBall 0 (73 / 100) := by
    intro hz
    have hz' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (x₀ := (0 : Vec 3)) (x := ρ⁻¹ • (x - x₀)) (by norm_num)).mp hz
    rw [sub_zero, vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hρ)] at hz'
    have hmul := mul_le_mul_of_nonneg_right hz' hρ.le
    have hle : vecEuclideanNorm (x - x₀) ≤ 73 * ρ / 100 := by
      calc
        vecEuclideanNorm (x - x₀) =
            (ρ⁻¹ * vecEuclideanNorm (x - x₀)) * ρ := by
              field_simp [hρ.ne']
        _ ≤ (73 / 100) * ρ := hmul
        _ = 73 * ρ / 100 := by ring
    apply hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    exact lt_of_le_of_lt hle (by nlinarith only [hρ])
  rw [mollifiedBallCutoff_gradient_formula]
  simp [unitGradient_eq_zero_of_not_mem_closedBall hscaled]

private lemma mollifiedBallCutoff_hessian_eq_zero_of_not_mem_outer
    (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ) {x : Vec 3}
    (hx : x ∉ euclideanBall x₀ (3 * ρ / 4)) :
    fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x = 0 := by
  have hscaled : ρ⁻¹ • (x - x₀) ∉ euclideanClosedBall 0 (73 / 100) := by
    intro hz
    have hz' := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (x₀ := (0 : Vec 3)) (x := ρ⁻¹ • (x - x₀)) (by norm_num)).mp hz
    rw [sub_zero, vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hρ)] at hz'
    have hmul := mul_le_mul_of_nonneg_right hz' hρ.le
    have hle : vecEuclideanNorm (x - x₀) ≤ 73 * ρ / 100 := by
      calc
        vecEuclideanNorm (x - x₀) =
            (ρ⁻¹ * vecEuclideanNorm (x - x₀)) * ρ := by
              field_simp [hρ.ne']
        _ ≤ (73 / 100) * ρ := hmul
        _ = 73 * ρ / 100 := by ring
    apply hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).2
    exact lt_of_le_of_lt hle (by nlinarith only [hρ])
  rw [mollifiedBallCutoff_hessian_formula]
  simp [unitHessian_eq_zero_of_not_mem_closedBall hscaled]

theorem mollifiedBallCutoff_derivatives_vanish_outside_annulus
    (x₀ : Vec 3) {ρ : ℝ} (hρ : 0 < ρ) {x : Vec 3}
    (hx : x ∉ euclideanBall x₀ (3 * ρ / 4) \
      euclideanClosedBall x₀ (13 * ρ / 20)) :
    classicalGradient (mollifiedBallCutoff x₀ hρ) x = 0 ∧
      fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x = 0 := by
  by_cases houter : x ∈ euclideanBall x₀ (3 * ρ / 4)
  · have hinner : x ∈ euclideanClosedBall x₀ (13 * ρ / 20) := by
      by_contra hinner
      exact hx ⟨houter, hinner⟩
    exact ⟨mollifiedBallCutoff_gradient_eq_zero_on_closed_inner x₀ hρ hinner,
      mollifiedBallCutoff_hessian_eq_zero_on_closed_inner x₀ hρ hinner⟩
  · exact ⟨mollifiedBallCutoff_gradient_eq_zero_of_not_mem_outer x₀ hρ houter,
      mollifiedBallCutoff_hessian_eq_zero_of_not_mem_outer x₀ hρ houter⟩

theorem cutoff_annulus_distance (x₀ : Vec 3) {ρ r : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hrr : r ≤ ρ / 2) {x y : Vec 3}
    (hx : x ∈ euclideanBall x₀ r)
    (hy : y ∈ euclideanBall x₀ (3 * ρ / 4) \
      euclideanClosedBall x₀ (13 * ρ / 20)) :
    3 * ρ / 20 ≤ vecEuclideanNorm (x - y) := by
  have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt
    (x₀ := x₀) (x := x) (by positivity)).mp hx
  have hy' : 13 * ρ / 20 < vecEuclideanNorm (y - x₀) := by
    by_contra hnot
    apply hy.2
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (x₀ := x₀) (x := y) (by positivity)).2
    exact le_of_not_gt hnot
  have hsum := vecEuclideanNorm_add_le (y - x) (x - x₀)
  have heq : y - x₀ = (y - x) + (x - x₀) := by abel
  have hsum' : vecEuclideanNorm (y - x₀) ≤
      vecEuclideanNorm (y - x) + vecEuclideanNorm (x - x₀) := by
    rw [heq]
    exact hsum
  have hdist : 3 * ρ / 20 ≤ vecEuclideanNorm (y - x) := by
    linarith only [hy', hsum', hx', hrr]
  have hneg : y - x = -(x - y) := by abel
  rw [hneg] at hdist
  have hnorm : vecEuclideanNorm (-(x - y)) = vecEuclideanNorm (x - y) := by
    rw [vecEuclideanNorm_eq_spaceEuclideanNorm,
      vecEuclideanNorm_eq_spaceEuclideanNorm]
    change Real.sqrt (∑ i, (-(x - y)) i ^ 2) =
      Real.sqrt (∑ i, (x - y) i ^ 2)
    congr 1
    apply Finset.sum_congr rfl
    intro i _hi
    simp
    ring
  rw [hnorm] at hdist
  exact hdist

theorem mollifiedBallCutoff_gradient_bound (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Vec 3) :
    vecEuclideanNorm (classicalGradient (mollifiedBallCutoff x₀ hρ) x) ≤
      cutoffGradientConstant / ρ := by
  rw [mollifiedBallCutoff_gradient_formula]
  rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hρ)]
  calc
    ρ⁻¹ * vecEuclideanNorm
        (classicalGradient unitBallCutoff (ρ⁻¹ • (x - x₀))) ≤
        ρ⁻¹ * cutoffGradientConstant :=
      mul_le_mul_of_nonneg_left (unitGradient_norm_le_constant _) (by positivity)
    _ = cutoffGradientConstant / ρ := by
      field_simp [hρ.ne']

theorem mollifiedBallCutoff_second_derivative_bound (x₀ : Vec 3) {ρ : ℝ}
    (hρ : 0 < ρ) (x : Vec 3) :
    ‖fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x‖ ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  rw [mollifiedBallCutoff_hessian_formula]
  calc
    ‖ρ⁻¹ • ((fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))).comp
        (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3)))‖ =
        ‖ρ⁻¹‖ * ‖(fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))).comp
        (ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3))‖ := norm_smul _ _
    _ ≤ ρ⁻¹ * (‖fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))‖ *
        ‖ρ⁻¹ • ContinuousLinearMap.id ℝ (Vec 3)‖) := by
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ)]
      gcongr
      exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = (ρ⁻¹) ^ 2 * ‖fderiv ℝ (classicalGradient unitBallCutoff)
        (ρ⁻¹ • (x - x₀))‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hρ),
        ContinuousLinearMap.norm_id]
      ring
    _ ≤ (ρ⁻¹) ^ 2 * cutoffSecondDerivativeConstant := by
      exact mul_le_mul_of_nonneg_left (unitHessian_norm_le_constant _)
        (by positivity)
    _ = cutoffSecondDerivativeConstant / ρ ^ 2 := by
      field_simp [hρ.ne']

end CKN
