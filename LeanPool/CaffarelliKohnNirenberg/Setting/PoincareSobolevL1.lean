/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Ambient.Euclidean
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyL1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.Smooth
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.LpOne
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Poincare.Scaling
public import Mathlib.Analysis.Convex.Measure
public import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
public import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.NormLeVecEuclidean

/-!
# The same-ball `W^{1,1}` to `L^{3/2}` estimate

The endpoint estimate is obtained by subtracting the ball average, applying the
two-reflection extension and a compact cutoff, and then using the global
Gagliardo--Nirenberg inequality at `p = 1`.  The affine bookkeeping is kept
explicit so that the final constant is independent of the ball.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

def unitEuclideanBall : Set (Vec 3) :=
  euclideanBall (0 : Vec 3) 1

private theorem vecEuclideanNorm_eq_l2 (x : Vec 3) :
    vecEuclideanNorm x = ‖WithLp.toLp 2 x‖ := by
  rw [PiLp.norm_eq_of_L2]
  simp [vecEuclideanNorm, vecNormSq, vecDot, Real.norm_eq_abs, sq_abs]
  congr 1
  apply Finset.sum_congr rfl
  intro i _hi
  ring

private theorem vecEuclideanNorm_add_le (x y : Vec 3) :
    vecEuclideanNorm (x + y) ≤ vecEuclideanNorm x + vecEuclideanNorm y := by
  rw [vecEuclideanNorm_eq_l2, vecEuclideanNorm_eq_l2, vecEuclideanNorm_eq_l2]
  rw [WithLp.toLp_add]
  exact norm_add_le _ _

private theorem unitEuclideanBall_measurable :
    MeasurableSet unitEuclideanBall := by
  change MeasurableSet (euclideanBall (0 : Vec 3) 1)
  change MeasurableSet ((fun x : Vec 3 => euclideanSqDist x 0) ⁻¹' Iio ((1 : ℝ) ^ 2))
  exact measurableSet_Iio.preimage
    (contDiff_euclideanSqDist_left (0 : Vec 3)).continuous.measurable

private theorem unitEuclideanBall_open : IsOpen unitEuclideanBall := by
  change IsOpen (euclideanBall (0 : Vec 3) 1)
  change IsOpen {x : Vec 3 | euclideanSqDist x 0 < (1 : ℝ) ^ 2}
  exact isOpen_lt (contDiff_euclideanSqDist_left (0 : Vec 3)).continuous
    continuous_const

theorem unitEuclideanBall_bounded :
    IsBoundedDomain unitEuclideanBall := by
  refine ⟨1, by norm_num, ?_⟩
  intro x hx i
  have hx' : vecEuclideanNorm x < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  exact (abs_apply_le_vecEuclideanNorm x i).trans hx'.le

private theorem unitEuclideanBall_convex :
    Convex ℝ unitEuclideanBall := by
  rw [convex_iff_segment_subset]
  intro x hx y hy z hz
  rcases hz with ⟨a, b, ha, hb, hab, habz⟩
  have hx' : vecEuclideanNorm x < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx
  have hy' : vecEuclideanNorm y < 1 := by
    simpa only [sub_zero] using
      (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hy
  apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
  simp only [sub_zero]
  rw [← habz]
  calc
    vecEuclideanNorm (a • x + b • y) ≤
        vecEuclideanNorm (a • x) + vecEuclideanNorm (b • y) :=
      vecEuclideanNorm_add_le _ _
    _ = a * vecEuclideanNorm x + b * vecEuclideanNorm y := by
      rw [vecEuclideanNorm_smul, vecEuclideanNorm_smul,
        abs_of_nonneg ha, abs_of_nonneg hb]
    _ < a * 1 + b * 1 := by
      by_cases hapos : 0 < a
      · exact add_lt_add_of_lt_of_le
          (mul_lt_mul_of_pos_left hx' hapos)
          (mul_le_mul_of_nonneg_left hy'.le hb)
      · have ha0 : a = 0 := le_antisymm (not_lt.mp hapos) ha
        have hbpos : 0 < b := by linarith only [hab, ha0]
        exact add_lt_add_of_le_of_lt
          (mul_le_mul_of_nonneg_left hx'.le ha)
          (mul_lt_mul_of_pos_left hy' hbpos)
    _ = 1 := by simp [hab]

private theorem unitEuclideanBall_domain :
    IsOpenBoundedConvexDomain unitEuclideanBall :=
  ⟨unitEuclideanBall_open, unitEuclideanBall_bounded,
    unitEuclideanBall_convex⟩

private theorem unitSphere_subset_frontier {x : Vec 3}
    (hx : vecEuclideanNorm x = 1) :
    x ∈ frontier unitEuclideanBall := by
  have hnorm : ‖x‖ ≤ 1 := by
    have h := space_norm_le_euclideanNorm x
    calc
      ‖x‖ ≤ vecEuclideanNorm x := by
        simpa [vecEuclideanNorm, spaceEuclideanNorm, vecNormSq, vecDot, pow_two] using h
      _ = 1 := hx
  have hcl : x ∈ closure unitEuclideanBall := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    let δ : ℝ := min (1 / 2) (ε / 2)
    have hδ : 0 < δ := lt_min (by norm_num) (by linarith only [hε])
    have hδle : δ ≤ 1 / 2 := min_le_left _ _
    have hδeps : δ < ε := lt_of_le_of_lt (min_le_right _ _) (by linarith only [hε])
    refine ⟨(1 - δ) • x, ?_, ?_⟩
    · apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
      simp only [sub_zero]
      rw [vecEuclideanNorm_smul, hx, abs_of_nonneg]
      · linarith only [hδ]
      · linarith only [hδle]
    · rw [dist_eq_norm]
      have heq : x - (1 - δ) • x = δ • x := by
        calc
          x - (1 - δ) • x = (1 : ℝ) • x - (1 - δ) • x := by simp
          _ = (1 - (1 - δ)) • x := by
            rw [← one_smul ℝ x]
            rw [← sub_smul]
          _ = δ • x := by ring_nf
      rw [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
      have hδeps' : δ * 1 < ε := by simpa using hδeps
      exact (mul_le_mul_of_nonneg_left hnorm hδ.le).trans_lt hδeps'
  have hint : x ∉ interior unitEuclideanBall := by
    rw [unitEuclideanBall_open.interior_eq]
    intro h
    have h' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp h
    have h'' : vecEuclideanNorm x < 1 := by simpa only [sub_zero] using h'
    exact (ne_of_lt h'') hx
  exact ⟨hcl, hint⟩

private theorem unitSphere_null :
    volume {x : Vec 3 | vecEuclideanNorm x = 1} = 0 := by
  apply measure_mono_null
    (fun x hx => unitSphere_subset_frontier hx)
  exact unitEuclideanBall_convex.addHaar_frontier volume

private theorem unitClosedBall_ae_eq :
    euclideanClosedBall (0 : Vec 3) 1 =ᵐ[volume] unitEuclideanBall := by
  rw [ae_eq_set]
  constructor
  · apply measure_mono_null (fun x hx => by
      have hle := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by norm_num)).mp hx.1
      have hnotlt : ¬vecEuclideanNorm x < 1 := by
        intro hlt
        exact hx.2 ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
          (by simpa only [sub_zero] using hlt))
      exact le_antisymm (by simpa only [sub_zero] using hle)
        (le_of_not_gt hnotlt)) unitSphere_null
  · have hsub : unitEuclideanBall \ euclideanClosedBall (0 : Vec 3) 1 ⊆ (∅ : Set (Vec 3)) := by
      intro x hx
      exact (hx.2 ((mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by norm_num)).2 (by
          exact ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx.1).le))).elim
    exact measure_mono_null hsub measure_empty

private theorem unitEuclideanBall_volume_pos :
    0 < (volume unitEuclideanBall).toReal := by
  have hball : Metric.ball (0 : Vec 3) (1 / 3) ⊆ unitEuclideanBall := by
    intro x hx
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
    simp only [sub_zero]
    have hnorm : ‖x‖ < 1 / 3 := by
      simpa [Metric.mem_ball, dist_eq_norm] using hx
    have hcomp : vecEuclideanNorm x ≤ 3 * ‖x‖ := by
      simpa [vecEuclideanNorm, spaceEuclideanNorm, vecNormSq, vecDot, pow_two] using
        (euclideanNorm_le_three_mul_space_norm x)
    nlinarith only [hcomp, hnorm]
  have hpos : 0 < volume (Metric.ball (0 : Vec 3) (1 / 3)) := by
    exact Metric.isOpen_ball.measure_pos volume
      (Metric.nonempty_ball.mpr (by norm_num))
  have htop : volume unitEuclideanBall < ∞ :=
    unitEuclideanBall_bounded.volume_lt_top
  exact ENNReal.toReal_pos (lt_of_lt_of_le hpos (measure_mono hball)).ne' htop.ne

noncomputable def unitL1PoincareConstant : ℝ :=
  (volume unitEuclideanBall).toReal⁻¹ *
      (((2 * Classical.choose unitEuclideanBall_bounded) ^ 3) / (3 : ℝ)) *
    ((3 : ℝ) * (volume (Metric.ball (0 : Vec 3) 1)).toReal *
      (4 * Classical.choose unitEuclideanBall_bounded))

private theorem unitL1PoincareConstant_nonneg :
    0 ≤ unitL1PoincareConstant := by
  dsimp [unitL1PoincareConstant]
  have hchoose : 0 < Classical.choose unitEuclideanBall_bounded :=
    (Classical.choose_spec unitEuclideanBall_bounded).1
  positivity

private theorem unit_value_poincare (g : Vec 3 → ℝ)
    (hg : ContDiff ℝ 1 g) :
    ∫ x in unitEuclideanBall,
        |g x - integralAverage unitEuclideanBall g| ∂volume ≤
      unitL1PoincareConstant *
        ∫ x in unitEuclideanBall, ‖fderiv ℝ g x‖ ∂volume := by
  let _ : IsFiniteMeasure (volumeMeasureOn unitEuclideanBall) :=
    unitEuclideanBall_domain.isFiniteMeasure_restrict_volume
  have hcompact : IsCompact (closure unitEuclideanBall) := by
    exact unitEuclideanBall_bounded.isBounded.isCompact_closure
  have hgint : IntegrableOn g unitEuclideanBall := by
    exact (hg.continuous.continuousOn.integrableOn_compact hcompact).mono_set
      subset_closure
  have h := integral_norm_sub_integralAverage_le_bound_of_isOpenBoundedConvexDomain
    unitEuclideanBall_domain hgint hg (unitEuclideanBall_volume_pos)
  simpa [unitL1PoincareConstant, abs_of_nonneg] using h

private theorem seeleyExtension_eq_exterior_on_closedAnnulus
    (v : Vec 3 → ℝ) {x : Vec 3} (hx : x ∈ seeleyClosedAnnulus) :
    seeleyExtension v x = seeleyExterior v x := by
  by_cases hnorm : vecEuclideanNorm x = 1
  · have hxC : x ∈ euclideanClosedBall (0 : Vec 3) 1 :=
      (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2
        (by simpa only [sub_zero] using hnorm.le)
    rw [seeleyExtension, ite_eq_left hxC]
    exact (seeleyExterior_eq_on_sphere v hnorm).symm
  · have hnorm' : 1 < vecEuclideanNorm x := lt_of_le_of_ne hx.1 (Ne.symm hnorm)
    have hxC : x ∉ euclideanClosedBall (0 : Vec 3) 1 := by
      intro hxC
      have hxle := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by norm_num)).mp hxC
      have hxle' : vecEuclideanNorm x ≤ 1 := by simpa only [sub_zero] using hxle
      linarith only [hnorm', hxle']
    rw [seeleyExtension, ite_eq_right hxC]

private theorem fderiv_norm_le_three_classicalGradient_l1
    {f : Vec 3 → ℝ} (x : Vec 3) :
    ‖fderiv ℝ f x‖ ≤ 3 * ‖classicalGradient f x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro z
  calc
    ‖(fderiv ℝ f x) z‖ =
        ‖∑ i : Fin 3, z i • (fderiv ℝ f x) (basisVec i)‖ := by
      have hz : z = ∑ i : Fin 3, z i • basisVec i :=
        (sum_smul_basisVec z).symm
      rw [hz, map_sum]
      simp [Pi.smul_apply, smul_eq_mul]
    _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ f x) (basisVec i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖z‖ * ‖classicalGradient f x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      have hz : |z i| ≤ ‖z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
      have hg : |(fderiv ℝ f x) (basisVec i)| ≤
          ‖classicalGradient f x‖ := by
        simpa only [classicalGradient_apply, Real.norm_eq_abs] using
          norm_le_pi_norm (classicalGradient f x) i
      exact mul_le_mul hz hg (abs_nonneg _) (norm_nonneg _)
    _ = 3 * ‖classicalGradient f x‖ * ‖z‖ := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

private theorem seeley_extension_value_pointwise_annulus
    (g : Vec 3 → ℝ) (c : ℝ) {x : Vec 3}
    (hx : 1 < vecEuclideanNorm x ∧ vecEuclideanNorm x ≤ 2) :
    |seeleyExtension (fun y => g y - c) x| ≤
      3 * |g (seeleyReflectionOne x) - c| +
        2 * |g (seeleyReflectionTwo x) - c| := by
  have hAnn : x ∈ seeleyClosedAnnulus := ⟨le_of_lt hx.1, hx.2⟩
  have hext := seeleyExtension_eq_exterior_on_closedAnnulus (fun y => g y - c) hAnn
  rw [hext]
  calc
    |3 * (g (seeleyReflectionOne x) - c) -
        2 * (g (seeleyReflectionTwo x) - c)| ≤
      |3 * (g (seeleyReflectionOne x) - c)| +
        |2 * (g (seeleyReflectionTwo x) - c)| := abs_sub _ _
    _ = _ := by rw [abs_mul, abs_mul]; norm_num

private theorem seeley_cutoff_gradient_pointwise_inner
    (g : Vec 3 → ℝ) (c : ℝ) (hg : ContDiff ℝ 1 g) {x : Vec 3}
    (hx : x ∈ unitEuclideanBall) :
    ‖fderiv ℝ (seeleyCutoffExtension (fun y => g y - c)) x‖ ≤
      ‖fderiv ℝ g x‖ := by
  let η : Vec 3 → ℝ := canonicalBallCutoff (0 : Vec 3) 1 2
  let v : Vec 3 → ℝ := fun y => g y - c
  have hη : ContDiff ℝ 1 η :=
    (canonicalBallCutoff_smooth (0 : Vec 3) (by norm_num) (by norm_num)).of_le
      (by simp)
  have hv : ContDiff ℝ 1 v := hg.sub contDiff_const
  have hη0 : fderiv ℝ η x = 0 := by
    have hmax : IsMaxOn η univ x := by
      intro y hy
      change canonicalBallCutoff (0 : Vec 3) 1 2 y ≤
        canonicalBallCutoff (0 : Vec 3) 1 2 x
      rw [canonicalBallCutoff_eq_one_on_inner (by norm_num) (by norm_num) hx]
      exact canonicalBallCutoff_le_one _ _ _ _
    exact IsLocalMax.fderiv_eq_zero (hmax.isLocalMax (by simp))
  have hη1 : η x = 1 :=
    canonicalBallCutoff_eq_one_on_inner (by norm_num) (by norm_num) hx
  have hveq : fderiv ℝ (seeleyExtension v) x = fderiv ℝ v x := by
    apply Filter.EventuallyEq.fderiv_eq
    filter_upwards [unitEuclideanBall_open.mem_nhds hx] with y hy
    rw [seeleyExtension, ite_eq_left (by
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2
        (by simpa only [sub_zero] using
          ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hy).le))]
  have hprod := fderiv_mul (hη.differentiable (by norm_num) x)
    ((seeleyExtension_contDiff v hv).differentiable (by norm_num) x)
  change ‖fderiv ℝ (η * seeleyExtension v) x‖ ≤ ‖fderiv ℝ g x‖
  rw [hprod, hη0, hη1, hveq]
  simpa [v] using (show ‖fderiv ℝ (fun y => g y - c) x‖ ≤ ‖fderiv ℝ g x‖ by
    rw [fderiv_sub_const])

private theorem seeleyExtension_fderiv_combo_of_one_lt
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : 1 < vecEuclideanNorm x ∧ vecEuclideanNorm x < 3) :
    fderiv ℝ (seeleyExtension v) x =
      (3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
        (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x := by
  have hAnn : x ∈ seeleyAnnulus := ⟨by linarith only [hx.1], hx.2⟩
  have hopen : IsOpen seeleyAnnulus := by
    rw [seeleyAnnulus]
    have hnorm : Continuous (vecEuclideanNorm (d := 3)) := by
      change Continuous (fun y : Vec 3 => Real.sqrt (vecNormSq y))
      exact (contDiff_vecNormSq (d := 3)).continuous.sqrt
    exact (isOpen_lt continuous_const hnorm).inter
      (isOpen_lt hnorm continuous_const)
  have hρ1 := seeleyReflectionOne_contDiffOn.contDiffAt (hopen.mem_nhds hAnn)
  have hρ2 := seeleyReflectionTwo_contDiffOn.contDiffAt (hopen.mem_nhds hAnn)
  have h1 := (hv.differentiable_one (seeleyReflectionOne x)).hasFDerivAt.comp x
    (hρ1.differentiableAt (by simp)).hasFDerivAt
  have h2 := (hv.differentiable_one (seeleyReflectionTwo x)).hasFDerivAt.comp x
    (hρ2.differentiableAt (by simp)).hasFDerivAt
  have h := (h1.const_mul 3).sub (h2.const_mul 2)
  have hseeley : seeleyExterior v =
      (fun y => 3 * (v ∘ seeleyReflectionOne) y) -
        (fun y => 2 * (v ∘ seeleyReflectionTwo) y) := by
    funext y
    rfl
  have houtside : x ∉ euclideanClosedBall (0 : Vec 3) 1 := by
    intro hxC
    have hxle := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (by norm_num)).mp hxC
    have hxle' : vecEuclideanNorm x ≤ 1 := by simpa only [sub_zero] using hxle
    linarith only [hx.1, hxle']
  have hformula : HasFDerivAt (seeleyExterior v)
      ((3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
        (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x) x := by
    rw [hseeley]
    simpa only [h1.fderiv, h2.fderiv] using h
  have hext := seeley_glue_hasFDerivAt_of_not_mem
    (C := euclideanClosedBall (0 : Vec 3) 1) (g := v) (h := seeleyExterior v)
    (isClosed_euclideanClosedBall (0 : Vec 3) 1) houtside hformula
  exact hext.fderiv

private theorem seeley_cutoff_gradient_pointwise_annulus
    (g : Vec 3 → ℝ) (c : ℝ) (hg : ContDiff ℝ 1 g) {x : Vec 3}
    (hx : 1 < vecEuclideanNorm x ∧ vecEuclideanNorm x ≤ 2) :
    ‖fderiv ℝ (seeleyCutoffExtension (fun y => g y - c)) x‖ ≤
      3 * (25 * ‖fderiv ℝ g (seeleyReflectionOne x)‖) +
        2 * (169 * ‖fderiv ℝ g (seeleyReflectionTwo x)‖) +
        96 * (3 * |g (seeleyReflectionOne x) - c| +
          2 * |g (seeleyReflectionTwo x) - c|) := by
  let η : Vec 3 → ℝ := canonicalBallCutoff (0 : Vec 3) 1 2
  let v : Vec 3 → ℝ := fun y => g y - c
  have hη : ContDiff ℝ 1 η :=
    (canonicalBallCutoff_smooth (0 : Vec 3) (by norm_num) (by norm_num)).of_le
      (by simp)
  have hv : ContDiff ℝ 1 v := hg.sub contDiff_const
  have hη0 : 0 ≤ η x := canonicalBallCutoff_nonneg _ _ _ _
  have hη1 : η x ≤ 1 := canonicalBallCutoff_le_one _ _ _ _
  have hprod := fderiv_mul (hη.differentiable (by norm_num) x)
    ((seeleyExtension_contDiff v hv).differentiable (by norm_num) x)
  have hcombo := seeleyExtension_fderiv_combo_of_one_lt v hv
    ⟨hx.1, lt_of_le_of_lt hx.2 (by norm_num)⟩
  have hηgrad : ‖fderiv ℝ η x‖ ≤ 96 := by
    calc
      ‖fderiv ℝ η x‖ ≤ 3 * ‖classicalGradient η x‖ :=
        fderiv_norm_le_three_classicalGradient_l1 x
      _ ≤ 3 * vecEuclideanNorm (classicalGradient η x) := by
        gcongr
        exact pi_norm_le_vecEuclideanNorm _
      _ ≤ 96 := by
        have h := canonicalBallCutoff_gradient_bound (d := 3)
          (x₀ := (0 : Vec 3)) (r := 1) (R := 2) (by norm_num) (by norm_num) x
        dsimp [η]
        nlinarith only [h]
  have hext := seeley_extension_value_pointwise_annulus g c hx
  change ‖fderiv ℝ (η * seeleyExtension v) x‖ ≤ _
  rw [hprod, hcombo]
  calc
    ‖η x • ((3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
        (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x) +
        seeleyExtension v x • fderiv ℝ η x‖ ≤
      η x * (3 * ‖fderiv ℝ (v ∘ seeleyReflectionOne) x‖ +
        2 * ‖fderiv ℝ (v ∘ seeleyReflectionTwo) x‖) +
        |seeleyExtension v x| * ‖fderiv ℝ η x‖ := by
          calc
            _ ≤ ‖η x • ((3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
                (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x)‖ +
                ‖seeleyExtension v x • fderiv ℝ η x‖ := norm_add_le _ _
            _ = η x * ‖(3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
                (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ +
                |seeleyExtension v x| * ‖fderiv ℝ η x‖ := by
                  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hη0,
                    norm_smul, Real.norm_eq_abs]
            _ ≤ _ := by
                  have hnorm :
                      ‖(3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
                        (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ ≤
                        3 * ‖fderiv ℝ (v ∘ seeleyReflectionOne) x‖ +
                          2 * ‖fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ := by
                    calc
                      _ ≤ ‖(3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x‖ +
                          ‖(2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ :=
                        norm_sub_le _ _
                      _ = _ := by
                        rw [norm_smul, norm_smul]
                        norm_num
                  exact add_le_add
                    (mul_le_mul_of_nonneg_left hnorm hη0) le_rfl
    _ ≤ 3 * ‖fderiv ℝ (v ∘ seeleyReflectionOne) x‖ +
        2 * ‖fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ +
        96 * |seeleyExtension v x| := by
          have hA := mul_le_of_le_one_left
            (by positivity : 0 ≤ 3 * ‖fderiv ℝ (v ∘ seeleyReflectionOne) x‖ +
              2 * ‖fderiv ℝ (v ∘ seeleyReflectionTwo) x‖) hη1
          have hB := mul_le_mul_of_nonneg_left hηgrad
            (abs_nonneg (seeleyExtension v x))
          exact add_le_add hA (by simpa [mul_comm] using hB)
    _ ≤ 3 * (25 * ‖fderiv ℝ g (seeleyReflectionOne x)‖) +
        2 * (169 * ‖fderiv ℝ g (seeleyReflectionTwo x)‖) +
        96 * (3 * |g (seeleyReflectionOne x) - c| +
          2 * |g (seeleyReflectionTwo x) - c|) := by
          have h1 := seeleyReflectionOne_comp_fderiv_norm_le_l1 v hv
            ⟨le_of_lt hx.1, hx.2⟩
          have h2 := seeleyReflectionTwo_comp_fderiv_norm_le_l1 v hv
            ⟨le_of_lt hx.1, hx.2⟩
          dsimp [v] at h1 h2
          rw [fderiv_sub_const] at h1 h2
          gcongr

private theorem cutoff_gradient_lintegral_le (g : Vec 3 → ℝ) (hg : ContDiff ℝ 1 g)
    (hc : ℝ) :
    ∫⁻ x in euclideanClosedBall (0 : Vec 3) 2,
        ENNReal.ofReal ‖fderiv ℝ (seeleyCutoffExtension (fun y => g y - hc)) x‖ ∂volume ≤
      (1 + 3 * 25 * 64 + 2 * 169 * 648 : ℝ≥0∞) *
          ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
            ENNReal.ofReal ‖fderiv ℝ g y‖ ∂volume +
        96 * (3 * 64 + 2 * 648 : ℝ≥0∞) *
          ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
            ENNReal.ofReal |g y - hc| ∂volume := by
  let U := euclideanClosedBall (0 : Vec 3) 1
  let O := euclideanClosedBall (0 : Vec 3) 2
  let A := seeleyClosedAnnulus
  let F : Vec 3 → ℝ≥0∞ := fun x => ENNReal.ofReal
    ‖fderiv ℝ (seeleyCutoffExtension (fun y => g y - hc)) x‖
  have hcover : O ⊆ U ∪ A := by
    intro x hx
    by_cases hU : x ∈ U
    · exact Or.inl hU
    · right
      have h2 := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
        (by norm_num)).mp hx
      have h2' : vecEuclideanNorm x ≤ 2 := by simpa [O, sub_zero] using h2
      have h1' : 1 ≤ vecEuclideanNorm x := by
        by_contra h
        apply hU
        have hlt : vecEuclideanNorm x < 1 := lt_of_not_ge h
        exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2
          (by simpa [sub_zero] using hlt.le)
      exact ⟨h1', h2'⟩
  have hsplit : ∫⁻ x in O, F x ∂volume ≤
      (∫⁻ x in U, F x ∂volume) + ∫⁻ x in A, F x ∂volume := by
    calc
      _ ≤ ∫⁻ x in U ∪ A, F x ∂volume :=
        lintegral_mono' (Measure.restrict_mono hcover le_rfl) le_rfl
      _ ≤ _ := by
        rw [← lintegral_add_measure]
        exact lintegral_mono' (Measure.restrict_union_le _ _) le_rfl
  have hsphere : ∀ᵐ x ∂volume, x ∉ {y : Vec 3 | vecEuclideanNorm y = 1} := by
    rw [ae_iff]
    simpa only [not_not, Set.mem_ofPred_eq] using unitSphere_null
  have hinner : ∫⁻ x in U, F x ∂volume ≤
      ∫⁻ x in U, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂volume := by
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem (isClosed_euclideanClosedBall
      (0 : Vec 3) 1 |>.measurableSet), ae_restrict_of_ae hsphere] with x hx hxs
    have hle := (mem_euclideanClosedBall_iff_vecEuclideanNorm_le
      (by norm_num)).mp hx
    have hlt : vecEuclideanNorm x < 1 := by
      apply lt_of_le_of_ne (by simpa only [sub_zero] using hle)
      exact hxs
    have hx' : x ∈ unitEuclideanBall := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
      simpa only [sub_zero] using hlt
    exact ENNReal.ofReal_le_ofReal
      (seeley_cutoff_gradient_pointwise_inner g hc hg hx')
  have hgradgReal : Measurable (fun x : Vec 3 => ‖fderiv ℝ g x‖) :=
    (hg.continuous_fderiv (by norm_num)).norm.measurable
  have hgradg : Measurable (fun x : Vec 3 => ENNReal.ofReal
      ‖fderiv ℝ g x‖) := hgradgReal.ennreal_ofReal
  have hA : ∫⁻ x in A, F x ∂volume ≤
      3 * 25 * (64 * ∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ g y‖ ∂volume) +
      2 * 169 * (648 * ∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ g y‖ ∂volume) +
      96 * (3 * (64 * ∫⁻ y in U, ENNReal.ofReal |g y - hc| ∂volume) +
        2 * (648 * ∫⁻ y in U, ENNReal.ofReal |g y - hc| ∂volume)) := by
    let G₁ : Vec 3 → ℝ≥0∞ := fun x => ENNReal.ofReal
      ‖fderiv ℝ g (seeleyReflectionOne x)‖
    let G₂ : Vec 3 → ℝ≥0∞ := fun x => ENNReal.ofReal
      ‖fderiv ℝ g (seeleyReflectionTwo x)‖
    let V₁ : Vec 3 → ℝ≥0∞ := fun x => ENNReal.ofReal
      |g (seeleyReflectionOne x) - hc|
    let V₂ : Vec 3 → ℝ≥0∞ := fun x => ENNReal.ofReal
      |g (seeleyReflectionTwo x) - hc|
    have hρ1 : Measurable seeleyReflectionOne := by
      unfold seeleyReflectionOne
      exact ((contDiff_vecNormSq (d := 3)).continuous.measurable.inv).smul measurable_id
    have hρ2 : Measurable seeleyReflectionTwo := by
      unfold seeleyReflectionTwo
      have hn : Measurable (vecEuclideanNorm (d := 3)) := by
        change Measurable (fun x : Vec 3 => Real.sqrt (vecNormSq x))
        exact ((contDiff_vecNormSq (d := 3)).continuous.sqrt).measurable
      exact (((measurable_const.mul hn).sub measurable_const).mul hn).inv.smul
        measurable_id
    have hG₁ : Measurable G₁ := by
      apply Measurable.ennreal_ofReal
      exact hgradgReal.comp hρ1
    have hG₂ : Measurable G₂ := by
      apply Measurable.ennreal_ofReal
      exact hgradgReal.comp hρ2
    have hV₁ : Measurable V₁ := by
      apply Measurable.ennreal_ofReal
      simpa [V₁, Real.norm_eq_abs] using
        (((hg.continuous.measurable.comp hρ1).sub measurable_const).norm)
    have hV₂ : Measurable V₂ := by
      apply Measurable.ennreal_ofReal
      simpa [V₂, Real.norm_eq_abs] using
        (((hg.continuous.measurable.comp hρ2).sub measurable_const).norm)
    calc
      _ ≤ ∫⁻ x in A, 3 * 25 * G₁ x + 2 * 169 * G₂ x +
          96 * (3 * V₁ x + 2 * V₂ x) ∂volume := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem seeleyClosedAnnulus_measurableSet,
          ae_restrict_of_ae hsphere] with x hx hxs
        have hx' : 1 < vecEuclideanNorm x := lt_of_le_of_ne hx.1 (Ne.symm hxs)
        calc
          F x ≤ ENNReal.ofReal
              (3 * (25 * ‖fderiv ℝ g (seeleyReflectionOne x)‖) +
                2 * (169 * ‖fderiv ℝ g (seeleyReflectionTwo x)‖) +
                96 * (3 * |g (seeleyReflectionOne x) - hc| +
                  2 * |g (seeleyReflectionTwo x) - hc|)) := by
            exact ENNReal.ofReal_le_ofReal
              (seeley_cutoff_gradient_pointwise_annulus g hc hg ⟨hx', hx.2⟩)
          _ = 3 * 25 * G₁ x + 2 * 169 * G₂ x +
              96 * (3 * V₁ x + 2 * V₂ x) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 25),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 169),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 96),
              ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3),
              ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
            norm_num [G₁, G₂, V₁, V₂]
            ring
      _ = 3 * 25 * (∫⁻ x in A, G₁ x ∂volume) +
          2 * 169 * (∫⁻ x in A, G₂ x ∂volume) +
          96 * (3 * (∫⁻ x in A, V₁ x ∂volume) +
            2 * (∫⁻ x in A, V₂ x ∂volume) ) := by
        calc
          _ = (∫⁻ x in A, 3 * 25 * G₁ x + 2 * 169 * G₂ x ∂volume) +
            ∫⁻ x in A, 96 * (3 * V₁ x + 2 * V₂ x) ∂volume := by
            have hlin := lintegral_add_left
              ((hG₁.const_mul (3 * 25)).add (hG₂.const_mul (2 * 169)))
              (fun x => 96 * (3 * V₁ x + 2 * V₂ x))
              (μ := volume.restrict A)
            simpa only [Pi.add_apply] using hlin
          _ = (∫⁻ x in A, 3 * 25 * G₁ x + 2 * 169 * G₂ x ∂volume) +
            ∫⁻ x in A, 96 * 3 * V₁ x + 96 * 2 * V₂ x ∂volume := by
            congr 1
            apply lintegral_congr
            intro x
            ring
          _ = _ := by
            rw [lintegral_add_left (hG₁.const_mul (3 * 25)),
              lintegral_const_mul' (3 * 25) _ (by norm_num),
              lintegral_const_mul' (2 * 169) _ (by norm_num),
              lintegral_add_left (hV₁.const_mul (96 * 3)),
              lintegral_const_mul' (96 * 3) _ (by norm_num),
              lintegral_const_mul' (96 * 2) _ (by norm_num)]
            ring
      _ ≤ _ := by
        have h1 := seeleyReflectionOne_lintegral_comp_le_l1
          (fun y => ENNReal.ofReal ‖fderiv ℝ g y‖)
        have h2 := seeleyReflectionTwo_lintegral_comp_le_l1
          (fun y => ENNReal.ofReal ‖fderiv ℝ g y‖)
        have v1 := seeleyReflectionOne_value_lintegral_le g hc
        have v2 := seeleyReflectionTwo_value_lintegral_le g hc
        dsimp [G₁, G₂, V₁, V₂] at h1 h2 v1 v2 ⊢
        gcongr
  calc
    _ ≤ (∫⁻ x in U, F x ∂volume) + ∫⁻ x in A, F x ∂volume := hsplit
    _ ≤ (∫⁻ x in U, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂volume) + _ :=
      add_le_add hinner hA
    _ = _ := by ring

/-- The absolute unit-ball constant in the smooth `W^{1,1}` endpoint estimate. -/
noncomputable def poincareSobolevL1Constant : ℝ≥0∞ :=
  (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec 3)) (1 : ℝ) : ℝ≥0∞) *
    ((1 + 3 * 25 * 64 + 2 * 169 * 648 : ℝ≥0∞) +
      96 * (3 * 64 + 2 * 648 : ℝ≥0∞) * ENNReal.ofReal unitL1PoincareConstant)

/-- Unit-ball `W^{1,1}` to `L^{3/2}` Poincare--Sobolev estimate for `C¹` functions.

The left side is the extended `L^{3/2}` seminorm of the function after
subtracting its ball average; the right side is the `L¹` seminorm of its
Fréchet derivative. -/
theorem poincareSobolevL1_unit (g : Vec 3 → ℝ) (hg : ContDiff ℝ 1 g) :
    eLpNorm (fun x => g x - integralAverage (euclideanBall (0 : Vec 3) 1) g)
        (3 / 2 : NNReal) (volume.restrict (euclideanBall (0 : Vec 3) 1)) ≤
      poincareSobolevL1Constant *
        eLpNorm (fderiv ℝ g) 1 (volume.restrict (euclideanBall (0 : Vec 3) 1)) := by
  let U : Set (Vec 3) := unitEuclideanBall
  let O : Set (Vec 3) := euclideanClosedBall (0 : Vec 3) 2
  let c : ℝ := integralAverage U g
  let v : Vec 3 → ℝ := fun y => g y - c
  let w : Vec 3 → ℝ := seeleyCutoffExtension v
  have hv : ContDiff ℝ 1 v := hg.sub contDiff_const
  have hw : ContDiff ℝ 1 w := by
    exact (canonicalBallCutoff_smooth (0 : Vec 3) (by norm_num) (by norm_num)
      |>.of_le (by simp)).mul (seeleyExtension_contDiff v hv)
  have hwC : HasCompactSupport w := by
    exact (canonicalBallCutoff_hasCompactSupport (by norm_num) (by norm_num)).mul_right
      (f' := seeleyExtension v)
  have hU : MeasurableSet U := by simpa [U] using unitEuclideanBall_measurable
  have hO : MeasurableSet O := by
    change MeasurableSet {x : Vec 3 | euclideanSqDist x 0 ≤ (2 : ℝ) ^ 2}
    exact (isClosed_le
      (contDiff_euclideanSqDist_left (0 : Vec 3)).continuous continuous_const).measurableSet
  have htw : tsupport w ⊆ O := by
    change tsupport (canonicalBallCutoff (0 : Vec 3) 1 2 * seeleyExtension v) ⊆ O
    have houter : euclideanBall (0 : Vec 3) 2 ⊆ O := by
      intro x hx
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2
        ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx).le
    exact (tsupport_mul_subset_left (f := canonicalBallCutoff (0 : Vec 3) 1 2)
      (g := seeleyExtension v)).trans
      ((canonicalBallCutoff_tsupport_subset_outer (d := 3) (by norm_num) (by norm_num)).trans
        houter)
  have hderiv_support : (fderiv ℝ w).support ⊆ O := by
    intro x hx
    by_contra hxo
    have hxt : x ∉ tsupport w := fun h => hxo (htw h)
    exact hx (by rw [fderiv_of_notMem_tsupport ℝ hxt])
  have hfw : AEStronglyMeasurable (fderiv ℝ w) volume :=
    (hw.continuous_fderiv (by norm_num)).aestronglyMeasurable
  have hfg : AEStronglyMeasurable (fderiv ℝ g) (volume.restrict U) :=
    (hg.continuous_fderiv (by norm_num)).aestronglyMeasurable.restrict
  have hderiv_norm :
      eLpNorm (fderiv ℝ w) 1 volume =
        ∫⁻ x in O, ENNReal.ofReal ‖fderiv ℝ w x‖ ∂volume := by
    rw [← eLpNorm_restrict_eq_of_support_subset hfw hderiv_support,
      eLpNorm_one_eq_lintegral_enorm hfw.restrict]
    apply lintegral_congr_ae
    filter_upwards [] with x
    rw [← ofReal_norm]
  have hgrad_norm :
      eLpNorm (fderiv ℝ g) 1 (volume.restrict U) =
        ∫⁻ x in U, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂volume := by
    rw [eLpNorm_one_eq_lintegral_enorm hfg]
    apply lintegral_congr_ae
    filter_upwards [] with x
    rw [← ofReal_norm]
  have hvalue :
      ∫⁻ x in U, ENNReal.ofReal |g x - c| ∂volume ≤
        ENNReal.ofReal unitL1PoincareConstant *
          ∫⁻ x in U, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂volume := by
    have hcompact : IsCompact (closure U) := by
      exact unitEuclideanBall_bounded.isBounded.isCompact_closure
    have hgv : IntegrableOn (fun x => |g x - c|) U := by
      exact ((hg.continuous.sub continuous_const).norm.continuousOn.integrableOn_compact hcompact).mono_set
        subset_closure
    have hgg : IntegrableOn (fun x => ‖fderiv ℝ g x‖) U := by
      exact ((hg.continuous_fderiv (by norm_num)).norm.continuousOn.integrableOn_compact hcompact).mono_set
        subset_closure
    have hreal := unit_value_poincare g hg
    calc
      _ = ENNReal.ofReal (∫ x in U, |g x - c| ∂volume) := by
        rw [ofReal_integral_eq_lintegral_ofReal hgv (ae_restrict_of_ae
          (Filter.Eventually.of_forall (fun x => abs_nonneg (g x - c))))]
      _ ≤ ENNReal.ofReal (unitL1PoincareConstant *
          ∫ x in U, ‖fderiv ℝ g x‖ ∂volume) :=
        ENNReal.ofReal_le_ofReal hreal
      _ = _ := by
        rw [ENNReal.ofReal_mul (unitL1PoincareConstant_nonneg)]
        rw [ofReal_integral_eq_lintegral_ofReal hgg (ae_restrict_of_ae
          (Filter.Eventually.of_forall (fun x => norm_nonneg (fderiv ℝ g x))))]
  have hgrad :
      ∫⁻ x in O, ENNReal.ofReal ‖fderiv ℝ w x‖ ∂volume ≤
        ((1 + 3 * 25 * 64 + 2 * 169 * 648 : ℝ≥0∞) +
          96 * (3 * 64 + 2 * 648 : ℝ≥0∞) * ENNReal.ofReal unitL1PoincareConstant) *
          ∫⁻ x in U, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂volume := by
    have hcut := cutoff_gradient_lintegral_le g hg c
    dsimp [U, O, v, w, c] at hcut ⊢
    calc
      _ ≤ (1 + 3 * 25 * 64 + 2 * 169 * 648 : ℝ≥0∞) *
            ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
              ENNReal.ofReal ‖fderiv ℝ g y‖ ∂volume +
          96 * (3 * 64 + 2 * 648 : ℝ≥0∞) *
            ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
              ENNReal.ofReal |g y - c| ∂volume := hcut
      _ ≤ _ := by
        have hvalue_closed :
            (∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
              ENNReal.ofReal |g y - c| ∂volume) ≤
            ENNReal.ofReal unitL1PoincareConstant *
              ∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ g y‖ ∂volume := by
          calc
            _ = ∫⁻ y in U, ENNReal.ofReal |g y - c| ∂volume := by
              rw [Measure.restrict_congr_set unitClosedBall_ae_eq]
            _ ≤ _ := hvalue
        calc
          _ ≤ (1 + 3 * 25 * 64 + 2 * 169 * 648 : ℝ≥0∞) *
                ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
                  ENNReal.ofReal ‖fderiv ℝ g y‖ ∂volume +
              96 * (3 * 64 + 2 * 648 : ℝ≥0∞) *
                (ENNReal.ofReal unitL1PoincareConstant *
                  ∫⁻ y in U, ENNReal.ofReal ‖fderiv ℝ g y‖ ∂volume) := by
            gcongr
          _ = _ := by
            rw [Measure.restrict_congr_set unitClosedBall_ae_eq]
            ring
  have hlocal :
      eLpNorm v (3 / 2 : NNReal) (volume.restrict U) ≤
        eLpNorm w (3 / 2 : NNReal) volume := by
    calc
      eLpNorm v (3 / 2 : NNReal) (volume.restrict U) =
          eLpNorm w (3 / 2 : NNReal) (volume.restrict U) := by
        apply eLpNorm_congr_ae
        filter_upwards [ae_restrict_mem hU] with x hx
        have hxC : x ∈ euclideanClosedBall (0 : Vec 3) 1 := by
          exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2
            ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).mp hx).le
        change v x = canonicalBallCutoff (0 : Vec 3) 1 2 x * seeleyExtension v x
        rw [canonicalBallCutoff_eq_one_on_inner (by norm_num) (by norm_num) hx,
          seeleyExtension, ite_eq_left hxC]
        simp
      _ ≤ eLpNorm w (3 / 2 : NNReal) volume :=
        eLpNorm_mono_measure w Measure.restrict_le_self
  have hgns := eLpNorm_le_eLpNorm_fderiv_of_eq
    (μ := (volume : Measure (Vec 3))) (F := ℝ) hw hwC
      (p := (1 : NNReal)) (p' := (3 / 2 : NNReal)) (by norm_num) (by norm_num)
      (by norm_num)
  calc
    eLpNorm (fun x => g x - integralAverage unitEuclideanBall g)
        (3 / 2 : NNReal) (volume.restrict unitEuclideanBall) =
      eLpNorm v (3 / 2 : NNReal) (volume.restrict U) := by rfl
    _ ≤ eLpNorm w (3 / 2 : NNReal) volume := hlocal
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec 3)) (1 : ℝ) : ℝ≥0∞) *
        eLpNorm (fderiv ℝ w) 1 volume := hgns
    _ ≤ (SNormLESNormFDerivOfEqConst ℝ (volume : Measure (Vec 3)) (1 : ℝ) : ℝ≥0∞) *
        (((1 + 3 * 25 * 64 + 2 * 169 * 648 : ℝ≥0∞) +
          96 * (3 * 64 + 2 * 648 : ℝ≥0∞) * ENNReal.ofReal unitL1PoincareConstant) *
          eLpNorm (fderiv ℝ g) 1 (volume.restrict U)) := by
      rw [hderiv_norm, hgrad_norm]
      gcongr
    _ = poincareSobolevL1Constant *
        eLpNorm (fderiv ℝ g) 1 (volume.restrict unitEuclideanBall) := by
      simp [poincareSobolevL1Constant, U]
      ring

end
end CKN
