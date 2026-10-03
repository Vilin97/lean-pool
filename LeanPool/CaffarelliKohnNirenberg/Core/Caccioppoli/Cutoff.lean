/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.Admissibility
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.SpaceTime
public import LeanPool.CaffarelliKohnNirenberg.Setting.Energy.Calculus
public import LeanPool.CaffarelliKohnNirenberg.Core.Caccioppoli.CutoffBase

/-!
# Cutoff

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic


noncomputable section

namespace CKN

theorem caccioppoli_spatial_cutoff_gradient_bound (x₀ : Vec3) (ρ : ℝ)
    (hρ : 0 < ρ) (x : Vec3) :
    vecEuclideanNorm (classicalGradient (mollifiedBallCutoff x₀ hρ) x) ≤
      cutoffGradientConstant / ρ :=
  mollifiedBallCutoff_gradient_bound x₀ hρ x

theorem caccioppoli_spatial_cutoff_second_derivative_bound (x₀ : Vec3) (ρ : ℝ)
    (hρ : 0 < ρ) (x : Vec3) (i j : Fin 3) :
    |(fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x
        (basisVec j)) i| ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := by
  have hmap := mollifiedBallCutoff_second_derivative_bound x₀ hρ x
  have hcoord :
      |(fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x
          (basisVec j)) i| ≤
        ‖fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x
          (basisVec j)‖ := by
    simpa only [Real.norm_eq_abs] using
      (norm_le_pi_norm
        (fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x
          (basisVec j)) i)
  have hbasis : ‖basisVec j‖ = (1 : ℝ) := by
    apply le_antisymm
    · rw [Pi.norm_def]
      change (↑(Finset.univ.sup (fun b => ‖basisVec j b‖₊) : NNReal) : ℝ) ≤
        ↑(1 : NNReal)
      exact_mod_cast (Finset.sup_le fun k hk => by
        by_cases h : k = j
        · subst h
          simp only [basisVec_apply]
          simp
        · simp only [basisVec_apply]
          simp [h])
    · have hj : ‖basisVec j j‖ ≤ ‖basisVec j‖ := norm_le_pi_norm _ _
      simpa [basisVec] using hj
  calc
    |(fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x
        (basisVec j)) i| ≤
        ‖fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x
          (basisVec j)‖ := hcoord
    _ ≤ ‖fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x‖ *
          ‖basisVec j‖ := ContinuousLinearMap.le_opNorm _ _
    _ = ‖fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) x‖ := by
      rw [hbasis, mul_one]
    _ ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := hmap

theorem caccioppoli_cutoff_spatial_partial_bound (x₀ : Vec3) (t₀ ρ R : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) (z : Vec3 × ℝ) (i : Fin 3) :
    |spatialPartial (caccioppoliCutoff x₀ t₀ ρ R hρ hR) i z| ≤
      cutoffGradientConstant / ρ := by
  have hη := caccioppoli_cutoff_smooth x₀ t₀ ρ R hρ hR
  have hsp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1) := by
    exact (mollifiedBallCutoff_smooth x₀ hρ).comp contDiff_fst
  unfold caccioppoliCutoff
  change |spatialPartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 * timeCutoff t₀ (ρ / 2) R z.2) i z| ≤
    cutoffGradientConstant / ρ
  have hformula₀ := spatialPartial_mul_time
    (ψ := fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1)
    (χ := timeCutoff t₀ (ρ / 2) R) hsp i z
  have hformula : spatialPartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 * timeCutoff t₀ (ρ / 2) R z.2) i z =
      spatialPartial (fun z : ParabolicPoint => mollifiedBallCutoff x₀ hρ z.1) i z *
        timeCutoff t₀ (ρ / 2) R z.2 := by
    simpa [ParabolicPoint] using hformula₀
  rw [hformula]
  rw [abs_mul]
  have hχ : |timeCutoff t₀ (ρ / 2) R z.2| ≤ 1 := by
    rw [abs_of_nonneg (timeCutoff_nonneg t₀ (ρ / 2) R z.2)]
    exact timeCutoff_le_one t₀ (ρ / 2) R z.2
  have hcoord :
      |(fderiv ℝ (mollifiedBallCutoff x₀ hρ) z.1) (basisVec i)| ≤
        vecEuclideanNorm (classicalGradient (mollifiedBallCutoff x₀ hρ) z.1) := by
    calc
      |(fderiv ℝ (mollifiedBallCutoff x₀ hρ) z.1) (basisVec i)| =
          |classicalGradient (mollifiedBallCutoff x₀ hρ) z.1 i| := by rfl
      _ ≤ vecEuclideanNorm (classicalGradient (mollifiedBallCutoff x₀ hρ) z.1) :=
        abs_apply_le_vecEuclideanNorm _ i
  have hgrad := caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ z.1
  have hcoord' :
      |(fderiv ℝ (mollifiedBallCutoff x₀ hρ) z.1) (basisVec i)| ≤
        cutoffGradientConstant / ρ := hcoord.trans hgrad
  have hχ' : 0 ≤ |timeCutoff t₀ (ρ / 2) R z.2| := abs_nonneg _
  calc
    |(fderiv ℝ (mollifiedBallCutoff x₀ hρ) z.1) (basisVec i)| *
        |timeCutoff t₀ (ρ / 2) R z.2| ≤
        (cutoffGradientConstant / ρ) *
          |timeCutoff t₀ (ρ / 2) R z.2| :=
      mul_le_mul_of_nonneg_right hcoord' hχ'
    _ ≤ (cutoffGradientConstant / ρ) * 1 :=
      mul_le_mul_of_nonneg_left hχ
        ((vecEuclideanNorm_nonneg _).trans hgrad)
    _ = cutoffGradientConstant / ρ := by ring

theorem caccioppoli_cutoff_time_partial_bound (x₀ : Vec3) (t₀ ρ R : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) (z : Vec3 × ℝ) :
    |timePartial (caccioppoliCutoff x₀ t₀ ρ R hρ hR) z| ≤
      32 / (R ^ 2 - (ρ / 2) ^ 2) := by
  have hsp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1) := by
    exact (mollifiedBallCutoff_smooth x₀ hρ).comp contDiff_fst
  have hχ : ContDiff ℝ (⊤ : ℕ∞) (timeCutoff t₀ (ρ / 2) R) :=
    timeCutoff_smooth (caccioppoli_cutoff_time_parameters hρ hR).1 hR
  unfold caccioppoliCutoff
  change |timePartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 * timeCutoff t₀ (ρ / 2) R z.2) z| ≤
      32 / (R ^ 2 - (ρ / 2) ^ 2)
  have hformula₀ := timePartial_mul_time
    (ψ := fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1)
    (χ := timeCutoff t₀ (ρ / 2) R) hsp hχ z
  have hformula : timePartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 * timeCutoff t₀ (ρ / 2) R z.2) z =
      timePartial (fun z : ParabolicPoint => mollifiedBallCutoff x₀ hρ z.1) z *
        timeCutoff t₀ (ρ / 2) R z.2 +
      mollifiedBallCutoff x₀ hρ z.1 * deriv (timeCutoff t₀ (ρ / 2) R) z.2 := by
    simpa [ParabolicPoint] using hformula₀
  rw [hformula]
  have hzero : timePartial (fun w : ParabolicPoint => mollifiedBallCutoff x₀ hρ w.1) z = 0 := by
    unfold timePartial
    change (fderiv ℝ (fun _ : ℝ => mollifiedBallCutoff x₀ hρ z.1) z.2) 1 = 0
    have hconst : (fun _ : ℝ => mollifiedBallCutoff x₀ hρ z.1) =
        Function.const ℝ (mollifiedBallCutoff x₀ hρ z.1) := by
      rfl
    rw [hconst, fderiv_const]
    simp
  rw [hzero, zero_mul, zero_add]
  rw [abs_mul]
  rw [abs_of_nonneg (mollifiedBallCutoff_nonneg x₀ hρ z.1)]
  calc
    mollifiedBallCutoff x₀ hρ z.1 *
        |deriv (timeCutoff t₀ (ρ / 2) R) z.2| ≤
        1 * |deriv (timeCutoff t₀ (ρ / 2) R) z.2| := by
      gcongr
      exact mollifiedBallCutoff_le_one x₀ hρ z.1
    _ = |deriv (timeCutoff t₀ (ρ / 2) R) z.2| := by ring
    _ ≤ 32 / (R ^ 2 - (ρ / 2) ^ 2) :=
      timeCutoff_abs_deriv_le (t := z.2)
        (caccioppoli_cutoff_time_parameters hρ hR).1 hR

private lemma spatialSecondPartial_spatial (g : Vec3 → ℝ) (z : ParabolicPoint)
    (i j : Fin 3) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    spatialSecondPartial (fun z : ParabolicPoint => g z.1) i j z =
      (fderiv ℝ (classicalGradient g) z.1 (basisVec j)) i := by
  unfold spatialSecondPartial
  change (fderiv ℝ (fun x : Vec3 =>
      spatialPartial (fun w : ParabolicPoint => g w.1) i (x, z.2)) z.1)
        (basisVec j) = _
  have hinner : (fun x : Vec3 =>
      spatialPartial (fun w : ParabolicPoint => g w.1) i (x, z.2)) =
      (fun x : Vec3 => classicalGradient g x i) := by
    funext x
    unfold spatialPartial
    change (fderiv ℝ (fun y : Vec3 => g y) x) (basisVec i) = _
    rfl
  rw [hinner]
  have hgrad : ContDiff ℝ (⊤ : ℕ∞) (classicalGradient g) := by
    unfold classicalGradient
    refine contDiff_pi.2 ?_
    intro i
    have hfg := hg.contDiff_fderiv_apply
      (m := (⊤ : ℕ∞)) (n := (⊤ : ℕ∞)) (by simp)
    have hcomp := hfg.comp (contDiff_id.prodMk (contDiff_const (c := basisVec i)))
    convert hcomp using 1
    funext x
    rfl
  have happly := fderiv_apply
    (hgrad.contDiffAt.differentiableAt (by simp) :
      DifferentiableAt ℝ (classicalGradient g) z.1) i
  rw [happly]
  rfl

theorem caccioppoli_cutoff_second_spatial_partial_bound
    (x₀ : Vec3) (t₀ ρ R : ℝ) (hρ : 0 < ρ) (hR : ρ / 2 < R)
    (z : Vec3 × ℝ) (i j : Fin 3) :
    |spatialSecondPartial (caccioppoliCutoff x₀ t₀ ρ R hρ hR) i j z| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  have hsp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1) := by
    exact (mollifiedBallCutoff_smooth x₀ hρ).comp contDiff_fst
  unfold caccioppoliCutoff
  change |spatialSecondPartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 * timeCutoff t₀ (ρ / 2) R z.2) i j z| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2
  have hformula₀ := spatialSecondPartial_mul_time
    (ψ := fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1)
    (χ := timeCutoff t₀ (ρ / 2) R) hsp i j z
  have hformula : spatialSecondPartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 * timeCutoff t₀ (ρ / 2) R z.2) i j z =
      spatialSecondPartial (fun z : ParabolicPoint => mollifiedBallCutoff x₀ hρ z.1) i j z *
        timeCutoff t₀ (ρ / 2) R z.2 := by
    simpa [ParabolicPoint] using hformula₀
  rw [hformula]
  rw [abs_mul]
  have hχ : |timeCutoff t₀ (ρ / 2) R z.2| ≤ 1 := by
    rw [abs_of_nonneg (timeCutoff_nonneg t₀ (ρ / 2) R z.2)]
    exact timeCutoff_le_one t₀ (ρ / 2) R z.2
  have hcoord := caccioppoli_spatial_cutoff_second_derivative_bound x₀ ρ hρ z.1 i j
  have hspcoord := spatialSecondPartial_spatial
    (mollifiedBallCutoff x₀ hρ) z i j (mollifiedBallCutoff_smooth x₀ hρ)
  rw [hspcoord]
  calc
    |(fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) z.1
        (basisVec j)) i| * |timeCutoff t₀ (ρ / 2) R z.2| ≤
        (cutoffSecondDerivativeConstant / ρ ^ 2) *
          |timeCutoff t₀ (ρ / 2) R z.2| :=
      mul_le_mul_of_nonneg_right hcoord (abs_nonneg _)
    _ ≤ (cutoffSecondDerivativeConstant / ρ ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hχ
        ((abs_nonneg _).trans hcoord)
    _ = cutoffSecondDerivativeConstant / ρ ^ 2 := by ring

theorem caccioppoli_cutoff_laplacian_bound (x₀ : Vec3) (t₀ ρ R : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) (z : Vec3 × ℝ) :
    |∑ i, spatialSecondPartial (caccioppoliCutoff x₀ t₀ ρ R hρ hR) i i z| ≤
      3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
  calc
    |∑ i, spatialSecondPartial (caccioppoliCutoff x₀ t₀ ρ R hρ hR) i i z| ≤
        ∑ i, |spatialSecondPartial
          (caccioppoliCutoff x₀ t₀ ρ R hρ hR) i i z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact caccioppoli_cutoff_second_spatial_partial_bound x₀ t₀ ρ R hρ hR z i i
    _ = 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num

theorem caccioppoli_cutoff_time_plus_laplacian_bound (x₀ : Vec3) (t₀ ρ R : ℝ)
    (hρ : 0 < ρ) (hR : ρ / 2 < R) (z : Vec3 × ℝ) :
    |timePartial (caccioppoliCutoff x₀ t₀ ρ R hρ hR) z +
        ∑ i, spatialSecondPartial (caccioppoliCutoff x₀ t₀ ρ R hρ hR) i i z| ≤
      32 / (R ^ 2 - (ρ / 2) ^ 2) +
        3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
  calc
    |timePartial (caccioppoliCutoff x₀ t₀ ρ R hρ hR) z +
        ∑ i, spatialSecondPartial
          (caccioppoliCutoff x₀ t₀ ρ R hρ hR) i i z| ≤
        |timePartial (caccioppoliCutoff x₀ t₀ ρ R hρ hR) z| +
          |∑ i, spatialSecondPartial
            (caccioppoliCutoff x₀ t₀ ρ R hρ hR) i i z| := abs_add_le _ _
    _ ≤ 32 / (R ^ 2 - (ρ / 2) ^ 2) +
        3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := add_le_add
      (caccioppoli_cutoff_time_partial_bound x₀ t₀ ρ R hρ hR z)
      (caccioppoli_cutoff_laplacian_bound x₀ t₀ ρ R hρ hR z)

/-- Temporal cutoff with separate backward-cylinder and forward regularization transition
intervals. -/
def caccioppoliAsymmetricTimeCutoff (t₀ ρ ε t : ℝ) : ℝ :=
  smoothTransitionProfile
      ((t - (t₀ - ρ ^ 2 / 2)) / (ρ ^ 2 / 4)) *
    smoothTransitionProfile
      ((t₀ + ε - t) / (ε / 2))

theorem caccioppoli_asymmetricTimeCutoff_smooth {t₀ ρ ε : ℝ}
    (_ : 0 < ρ) (_ : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) := by
  unfold caccioppoliAsymmetricTimeCutoff
  apply (smoothTransitionProfile.smooth.comp ?_).mul
    (smoothTransitionProfile.smooth.comp ?_)
  · fun_prop
  · fun_prop

theorem caccioppoli_asymmetricTimeCutoff_nonneg (t₀ ρ ε t : ℝ) :
    0 ≤ caccioppoliAsymmetricTimeCutoff t₀ ρ ε t := by
  unfold caccioppoliAsymmetricTimeCutoff
  exact mul_nonneg (smoothTransitionProfile.nonneg _)
    (smoothTransitionProfile.nonneg _)

theorem caccioppoli_asymmetricTimeCutoff_le_one (t₀ ρ ε t : ℝ) :
    caccioppoliAsymmetricTimeCutoff t₀ ρ ε t ≤ 1 := by
  unfold caccioppoliAsymmetricTimeCutoff
  calc
    _ ≤ 1 * smoothTransitionProfile ((t₀ + ε - t) / (ε / 2)) :=
      mul_le_mul_of_nonneg_right (smoothTransitionProfile.le_one _)
        (smoothTransitionProfile.nonneg _)
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left
      (smoothTransitionProfile.le_one _) (by norm_num)
    _ = 1 := by norm_num

theorem caccioppoli_asymmetricTimeCutoff_support_subset {t₀ ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    Function.support (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) ⊆
      Ioo (t₀ - ρ ^ 2) (t₀ + ε) := by
  intro t ht
  constructor
  · by_contra hleft
    have harg : (t - (t₀ - ρ ^ 2 / 2)) / (ρ ^ 2 / 4) ≤ 0 := by
      apply (div_nonpos_iff).2
      right
      constructor
      · linarith only [le_of_not_gt hleft, sq_nonneg ρ]
      · positivity
    have hzero := smoothTransitionProfile.zero_of_nonpos harg
    apply ht
    simp only [caccioppoliAsymmetricTimeCutoff, hzero, zero_mul]
  · by_contra hright
    have harg : (t₀ + ε - t) / (ε / 2) ≤ 0 := by
      apply (div_nonpos_iff).2
      right
      constructor
      · linarith only [le_of_not_gt hright]
      · positivity
    have hzero := smoothTransitionProfile.zero_of_nonpos harg
    apply ht
    simp only [caccioppoliAsymmetricTimeCutoff, hzero, mul_zero]

theorem caccioppoli_asymmetricTimeCutoff_tsupport_subset {t₀ ρ ε r : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) (hεr : ε < r ^ 2) :
    tsupport (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) ⊆
      {t : ℝ | t < t₀ + r ^ 2} := by
  intro t ht
  have hclosed : t ∈ Iic (t₀ + ε) := by
    apply closure_minimal
    · intro s hs
      exact (caccioppoli_asymmetricTimeCutoff_support_subset hρ hε hs).2.le
    · exact isClosed_Iic
    · exact ht
  have hupper : t ≤ t₀ + ε := hclosed
  change t < t₀ + r ^ 2
  linarith only [hupper, hεr]

theorem caccioppoli_asymmetricTimeCutoff_hasCompactSupport {t₀ ρ ε : ℝ}
    (hρ : 0 < ρ) (hε : 0 < ε) :
    HasCompactSupport (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) := by
  refine HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Icc (t₀ - ρ ^ 2) (t₀ + ε))) ?_
  intro t ht
  by_contra hne
  have hmem := caccioppoli_asymmetricTimeCutoff_support_subset hρ hε
    (Function.mem_support.mpr hne)
  exact ht ⟨hmem.1.le, hmem.2.le⟩

private theorem caccioppoli_asymmetricTimeCutoff_right_eq_one_near
    {t₀ ε t : ℝ} (hε : 0 < ε) (ht : t ≤ t₀) :
    ∀ᶠ s in 𝓝 t,
      smoothTransitionProfile ((t₀ + ε - s) / (ε / 2)) = 1 := by
  have hlt : t < t₀ + ε / 2 := by
    linarith only [ht, hε]
  filter_upwards [Iio_mem_nhds hlt] with s hs
  change s < t₀ + ε / 2 at hs
  apply smoothTransitionProfile.one_of_one_le
  apply (le_div_iff₀ (by positivity)).2
  linarith only [hs, hε]

theorem caccioppoli_asymmetricTimeCutoff_abs_deriv_le_on_left
    {t₀ ρ ε t : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (ht : t ≤ t₀) :
    |deriv (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) t| ≤ 32 / ρ ^ 2 := by
  have hcongr : ∀ᶠ s in 𝓝 t,
      caccioppoliAsymmetricTimeCutoff t₀ ρ ε s =
        smoothTransitionProfile
          ((s - (t₀ - ρ ^ 2 / 2)) / (ρ ^ 2 / 4)) := by
    filter_upwards [caccioppoli_asymmetricTimeCutoff_right_eq_one_near hε ht]
      with s hs
    simp only [caccioppoliAsymmetricTimeCutoff, hs, mul_one]
  have harg := ((hasDerivAt_id t).sub_const
    (t₀ - ρ ^ 2 / 2)).div_const (ρ ^ 2 / 4)
  have hbase := (smoothTransitionProfile.smooth.differentiable (by simp)
    ((t - (t₀ - ρ ^ 2 / 2)) / (ρ ^ 2 / 4))).hasDerivAt.comp t harg
  have htest := hbase.congr_of_eventuallyEq hcongr
  calc
    |deriv (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) t| =
        |deriv smoothTransitionProfile
          ((t - (t₀ - ρ ^ 2 / 2)) / (ρ ^ 2 / 4))| /
          (ρ ^ 2 / 4) := by
      have hden : 0 < ρ ^ 2 / 4 := by positivity
      rw [htest.deriv, abs_mul]
      rw [abs_of_pos (one_div_pos.mpr hden)]
      ring
    _ ≤ 8 / (ρ ^ 2 / 4) :=
      div_le_div_of_nonneg_right
        (smoothTransitionProfile.abs_deriv_le_eight _) (by positivity)
    _ = 32 / ρ ^ 2 := by field_simp [hρ.ne']; ring

/-- Product cutoff used to test the local energy inequality with a regularized backward heat
kernel. -/
@[expose]
def caccioppoliHeatCutoff (x₀ : Vec3) (t₀ ρ ε : ℝ)
    (hρ : 0 < ρ) (_hε : 0 < ε) (z : Vec3 × ℝ) : ℝ :=
  mollifiedBallCutoff x₀ hρ z.1 *
    caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2

theorem caccioppoli_heat_cutoff_smooth (x₀ : Vec3) (t₀ ρ ε : ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    ContDiff ℝ (⊤ : ℕ∞) (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) := by
  unfold caccioppoliHeatCutoff
  exact (mollifiedBallCutoff_smooth x₀ hρ).comp contDiff_fst |>.mul
    ((caccioppoli_asymmetricTimeCutoff_smooth hρ hε).comp contDiff_snd)

theorem caccioppoli_heat_cutoff_nonneg (x₀ : Vec3) (t₀ ρ ε : ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) (z : Vec3 × ℝ) :
    0 ≤ caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε z := by
  unfold caccioppoliHeatCutoff
  exact mul_nonneg (mollifiedBallCutoff_nonneg x₀ hρ _)
    (caccioppoli_asymmetricTimeCutoff_nonneg t₀ ρ ε z.2)

theorem caccioppoli_heat_cutoff_le_one (x₀ : Vec3) (t₀ ρ ε : ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) (z : Vec3 × ℝ) :
    caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε z ≤ 1 := by
  unfold caccioppoliHeatCutoff
  calc
    _ ≤ 1 * caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2 :=
      mul_le_mul_of_nonneg_right (mollifiedBallCutoff_le_one x₀ hρ _)
        (caccioppoli_asymmetricTimeCutoff_nonneg t₀ ρ ε z.2)
    _ ≤ 1 * 1 := mul_le_mul_of_nonneg_left
      (caccioppoli_asymmetricTimeCutoff_le_one t₀ ρ ε z.2) (by norm_num)
    _ = 1 := by norm_num

theorem caccioppoli_heat_cutoff_support_subset (x₀ : Vec3) (t₀ ρ ε : ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    Function.support (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) ⊆
      euclideanBall x₀ (3 * ρ / 4) ×ˢ Ioo (t₀ - ρ ^ 2) (t₀ + ε) := by
  intro z hz
  constructor
  · apply mollifiedBallCutoff_tsupport_subset_outer x₀ hρ
    apply subset_tsupport
    intro hzero
    apply hz
    simp [caccioppoliHeatCutoff, hzero]
  · apply caccioppoli_asymmetricTimeCutoff_support_subset hρ hε
    intro hzero
    apply hz
    simp [caccioppoliHeatCutoff, hzero]

theorem caccioppoli_heat_cutoff_hasCompactSupport (x₀ : Vec3) (t₀ ρ ε : ℝ)
    (hρ : 0 < ρ) (hε : 0 < ε) :
    HasCompactSupport (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) := by
  refine HasCompactSupport.intro
    ((isCompact_euclideanClosedBall x₀ (R := 3 * ρ / 4) (by positivity)).prod
      (isCompact_Icc : IsCompact (Icc (t₀ - ρ ^ 2) (t₀ + ε)))) ?_
  intro z hz
  by_contra hne
  have hmem := caccioppoli_heat_cutoff_support_subset x₀ t₀ ρ ε hρ hε
    (show z ∈ Function.support (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) from
      Function.mem_support.mpr hne)
  by_cases hx : z.1 ∈ euclideanClosedBall x₀ (3 * ρ / 4)
  · have ht : z.2 ∉ Icc (t₀ - ρ ^ 2) (t₀ + ε) := by
      intro ht
      exact hz ⟨hx, ht⟩
    exact ht (⟨hmem.2.1.le, hmem.2.2.le⟩)
  · apply hx
    apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
    exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hmem.1).le

theorem caccioppoli_heat_cutoff_time_support_bound
    (x₀ : Vec3) (t₀ ρ ε r : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (_ : 0 < r) (hεr : ε < r ^ 2) :
    tsupport (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) ⊆
      {z : Vec3 × ℝ | z.2 < t₀ + r ^ 2} := by
  intro z hz
  have hupper_mem : z ∈ {y : Vec3 × ℝ | y.2 ≤ t₀ + ε} := by
    apply closure_minimal
    · intro y hy
      exact (caccioppoli_heat_cutoff_support_subset x₀ t₀ ρ ε hρ hε hy).2.2.le
    · exact isClosed_Iic.preimage continuous_snd
    · exact hz
  have hupper : z.2 ≤ t₀ + ε := hupper_mem
  have hstrict : t₀ + ε < t₀ + r ^ 2 := by linarith only [hεr]
  exact lt_of_le_of_lt hupper hstrict

theorem caccioppoli_heat_cutoff_spatial_partial_bound
    (x₀ : Vec3) (t₀ ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (z : Vec3 × ℝ) (i : Fin 3) :
    |spatialPartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i z| ≤
      cutoffGradientConstant / ρ := by
  have hsp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1) := by
    exact (mollifiedBallCutoff_smooth x₀ hρ).comp contDiff_fst
  unfold caccioppoliHeatCutoff
  change |spatialPartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 *
        caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2) i z| ≤
    cutoffGradientConstant / ρ
  have hformula₀ := spatialPartial_mul_time
    (ψ := fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1)
    (χ := caccioppoliAsymmetricTimeCutoff t₀ ρ ε) hsp i z
  have hformula : spatialPartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 *
        caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2) i z =
      spatialPartial (fun z : ParabolicPoint => mollifiedBallCutoff x₀ hρ z.1) i z *
        caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2 := by
    simpa [ParabolicPoint] using hformula₀
  rw [hformula, abs_mul]
  have hχ : |caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2| ≤ 1 := by
    rw [abs_of_nonneg (caccioppoli_asymmetricTimeCutoff_nonneg t₀ ρ ε z.2)]
    exact caccioppoli_asymmetricTimeCutoff_le_one t₀ ρ ε z.2
  have hcoord :
      |(fderiv ℝ (mollifiedBallCutoff x₀ hρ) z.1 (basisVec i))| ≤
        vecEuclideanNorm (classicalGradient (mollifiedBallCutoff x₀ hρ) z.1) := by
    calc
      |(fderiv ℝ (mollifiedBallCutoff x₀ hρ) z.1 (basisVec i))| =
          |classicalGradient (mollifiedBallCutoff x₀ hρ) z.1 i| := by rfl
      _ ≤ vecEuclideanNorm (classicalGradient (mollifiedBallCutoff x₀ hρ) z.1) :=
        abs_apply_le_vecEuclideanNorm _ i
  have hcoord' := hcoord.trans
    (caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ z.1)
  calc
    |(fderiv ℝ (mollifiedBallCutoff x₀ hρ) z.1 (basisVec i))| *
        |caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2| ≤
        (cutoffGradientConstant / ρ) *
          |caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2| :=
      mul_le_mul_of_nonneg_right hcoord' (abs_nonneg _)
    _ ≤ (cutoffGradientConstant / ρ) * 1 :=
      mul_le_mul_of_nonneg_left hχ
        ((vecEuclideanNorm_nonneg _).trans
          (caccioppoli_spatial_cutoff_gradient_bound x₀ ρ hρ z.1))
    _ = cutoffGradientConstant / ρ := by ring

theorem caccioppoli_heat_cutoff_time_partial_bound_on_left
    (x₀ : Vec3) (t₀ ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    {z : Vec3 × ℝ} (ht : z.2 ≤ t₀) :
    |timePartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) z| ≤
      32 / ρ ^ 2 := by
  have hsp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1) := by
    exact (mollifiedBallCutoff_smooth x₀ hρ).comp contDiff_fst
  have hχ : ContDiff ℝ (⊤ : ℕ∞)
      (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) :=
    caccioppoli_asymmetricTimeCutoff_smooth hρ hε
  unfold caccioppoliHeatCutoff
  change |timePartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 *
        caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2) z| ≤ 32 / ρ ^ 2
  have hformula₀ := timePartial_mul_time
    (ψ := fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1)
    (χ := caccioppoliAsymmetricTimeCutoff t₀ ρ ε) hsp hχ z
  have hformula : timePartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 *
        caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2) z =
      timePartial (fun z : ParabolicPoint => mollifiedBallCutoff x₀ hρ z.1) z *
        caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2 +
      mollifiedBallCutoff x₀ hρ z.1 *
        deriv (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) z.2 := by
    simpa [ParabolicPoint] using hformula₀
  rw [hformula]
  have hzero : timePartial (fun w : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ w.1) z = 0 := by
    unfold timePartial
    change (fderiv ℝ (fun _ : ℝ => mollifiedBallCutoff x₀ hρ z.1) z.2) 1 = 0
    rw [show (fun _ : ℝ => mollifiedBallCutoff x₀ hρ z.1) =
      Function.const ℝ (mollifiedBallCutoff x₀ hρ z.1) by rfl]
    rw [fderiv_const]
    simp
  rw [hzero, zero_mul, zero_add, abs_mul]
  have hη : 0 ≤ mollifiedBallCutoff x₀ hρ z.1 :=
    mollifiedBallCutoff_nonneg x₀ hρ _
  rw [abs_of_nonneg hη]
  calc
    mollifiedBallCutoff x₀ hρ z.1 *
        |deriv (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) z.2| ≤
        1 * |deriv (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) z.2| := by
      gcongr
      exact mollifiedBallCutoff_le_one x₀ hρ _
    _ = |deriv (caccioppoliAsymmetricTimeCutoff t₀ ρ ε) z.2| := by ring
    _ ≤ 32 / ρ ^ 2 :=
      caccioppoli_asymmetricTimeCutoff_abs_deriv_le_on_left hρ hε ht

private lemma caccioppoli_heat_cutoff_spatialSecondPartial_spatial
    (x₀ : Vec3) (ρ : ℝ) (hρ : 0 < ρ) (z : ParabolicPoint)
    (i j : Fin 3) :
    spatialSecondPartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1) i j z =
      (fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) z.1
        (basisVec j)) i := by
  exact spatialSecondPartial_spatial (mollifiedBallCutoff x₀ hρ) z i j
    (mollifiedBallCutoff_smooth x₀ hρ)

theorem caccioppoli_heat_cutoff_second_spatial_partial_bound
    (x₀ : Vec3) (t₀ ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (z : Vec3 × ℝ) (i j : Fin 3) :
    |spatialSecondPartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i j z| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  have hsp : ContDiff ℝ (⊤ : ℕ∞)
      (fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1) := by
    exact (mollifiedBallCutoff_smooth x₀ hρ).comp contDiff_fst
  unfold caccioppoliHeatCutoff
  change |spatialSecondPartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 *
        caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2) i j z| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2
  have hformula₀ := spatialSecondPartial_mul_time
    (ψ := fun z : Vec3 × ℝ => mollifiedBallCutoff x₀ hρ z.1)
    (χ := caccioppoliAsymmetricTimeCutoff t₀ ρ ε) hsp i j z
  have hformula : spatialSecondPartial (fun z : ParabolicPoint =>
      mollifiedBallCutoff x₀ hρ z.1 *
        caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2) i j z =
      spatialSecondPartial (fun z : ParabolicPoint => mollifiedBallCutoff x₀ hρ z.1) i j z *
        caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2 := by
    simpa [ParabolicPoint] using hformula₀
  rw [hformula, abs_mul]
  have hχ : |caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2| ≤ 1 := by
    rw [abs_of_nonneg (caccioppoli_asymmetricTimeCutoff_nonneg t₀ ρ ε z.2)]
    exact caccioppoli_asymmetricTimeCutoff_le_one t₀ ρ ε z.2
  have hcoord := caccioppoli_spatial_cutoff_second_derivative_bound
    x₀ ρ hρ z.1 i j
  have hspcoord := caccioppoli_heat_cutoff_spatialSecondPartial_spatial
    x₀ ρ hρ z i j
  rw [hspcoord]
  calc
    |(fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) z.1
        (basisVec j)) i| *
        |caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2| ≤
        (cutoffSecondDerivativeConstant / ρ ^ 2) *
          |caccioppoliAsymmetricTimeCutoff t₀ ρ ε z.2| :=
      mul_le_mul_of_nonneg_right hcoord (abs_nonneg _)
    _ ≤ (cutoffSecondDerivativeConstant / ρ ^ 2) * 1 :=
      mul_le_mul_of_nonneg_left hχ
        ((abs_nonneg _).trans hcoord)
    _ = cutoffSecondDerivativeConstant / ρ ^ 2 := by ring

theorem caccioppoli_heat_cutoff_laplacian_bound
    (x₀ : Vec3) (t₀ ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    (z : Vec3 × ℝ) :
    |∑ i, spatialSecondPartial
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i i z| ≤
      3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
  calc
    |∑ i, spatialSecondPartial
        (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i i z| ≤
        ∑ i, |spatialSecondPartial
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i i z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact caccioppoli_heat_cutoff_second_spatial_partial_bound
        x₀ t₀ ρ ε hρ hε z i i
    _ = 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      norm_num

theorem caccioppoli_heat_cutoff_time_plus_laplacian_bound_on_left
    (x₀ : Vec3) (t₀ ρ ε : ℝ) (hρ : 0 < ρ) (hε : 0 < ε)
    {z : Vec3 × ℝ} (ht : z.2 ≤ t₀) :
    |timePartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) z +
        ∑ i, spatialSecondPartial
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i i z| ≤
      32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := by
  calc
    _ ≤ |timePartial (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) z| +
        |∑ i, spatialSecondPartial
          (caccioppoliHeatCutoff x₀ t₀ ρ ε hρ hε) i i z| := abs_add_le _ _
    _ ≤ 32 / ρ ^ 2 + 3 * (cutoffSecondDerivativeConstant / ρ ^ 2) := add_le_add
      (caccioppoli_heat_cutoff_time_partial_bound_on_left x₀ t₀ ρ ε hρ hε ht)
      (caccioppoli_heat_cutoff_laplacian_bound x₀ t₀ ρ ε hρ hε z)

theorem caccioppoli_asymmetricTimeCutoff_eq_one_on
    {t₀ ρ ε r t : ℝ} (hρ : 0 < ρ) (hε : 0 < ε)
    (hr : 0 < r) (hscale : r ≤ ρ / 2)
    (ht : t ∈ Icc (t₀ - r ^ 2) (t₀ + ε / 2)) :
    caccioppoliAsymmetricTimeCutoff t₀ ρ ε t = 1 := by
  unfold caccioppoliAsymmetricTimeCutoff
  have hleft : 1 ≤ (t - (t₀ - ρ ^ 2 / 2)) / (ρ ^ 2 / 4) := by
    apply (le_div_iff₀ (by positivity)).2
    have hsq : r ^ 2 ≤ (ρ / 2) ^ 2 :=
      (sq_le_sq₀ hr.le (by positivity)).2 hscale
    nlinarith only [ht.1, hsq]
  have hright : 1 ≤ (t₀ + ε - t) / (ε / 2) := by
    apply (le_div_iff₀ (by positivity)).2
    linarith only [ht.2, hε]
  rw [smoothTransitionProfile.one_of_one_le hleft,
    smoothTransitionProfile.one_of_one_le hright]
  norm_num

end CKN
