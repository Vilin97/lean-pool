/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Setting.PoincareSobolevL1

/-!
# Poincare Sobolev L1 Ball

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal Pointwise

namespace CKN

noncomputable section

/-- Translation and dilation map transporting unit-ball inequalities to arbitrary balls. -/
def euclideanAffineMap (x₀ : Vec 3) (r : ℝ) (x : Vec 3) : Vec 3 :=
  x₀ + r • x

private theorem euclideanBallAffine_image_unitBall (x₀ : Vec 3) {r : ℝ} (hr : 0 < r) :
    euclideanAffineMap x₀ r '' euclideanBall (0 : Vec 3) 1 =
      euclideanBall x₀ r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    apply (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).2
    dsimp [euclideanAffineMap]
    rw [add_sub_cancel_left, vecEuclideanNorm_smul, abs_of_pos hr]
    have hx' := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx
    simpa using mul_lt_mul_of_pos_left hx' hr
  · intro hy
    have hy' := (mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hy
    let x : Vec 3 := r⁻¹ • (y - x₀)
    have hx : x ∈ euclideanBall (0 : Vec 3) 1 := by
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
      dsimp [x]
      simp only [sub_zero]
      rw [vecEuclideanNorm_smul, abs_of_pos (inv_pos.mpr hr)]
      have hdiv : vecEuclideanNorm (y - x₀) / r < 1 :=
        (div_lt_iff₀ hr).2 (by simpa using hy')
      simpa [div_eq_mul_inv, mul_comm] using hdiv
    refine ⟨x, hx, ?_⟩
    dsimp [euclideanAffineMap, x]
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
    abel

private theorem translate_smul_euclideanBall (x₀ : Vec 3) {r : ℝ} (hr : 0 < r) :
    translateSet x₀ (r • euclideanBall (0 : Vec 3) 1) = euclideanBall x₀ r := by
  calc
    translateSet x₀ (r • euclideanBall (0 : Vec 3) 1) =
        (fun z : Vec 3 => z + x₀) '' (r • euclideanBall (0 : Vec 3) 1) :=
      (image_addRight_eq_translateSet x₀ (r • euclideanBall (0 : Vec 3) 1)).symm
    _ = (fun x : Vec 3 => x₀ + r • x) '' euclideanBall (0 : Vec 3) 1 := by
      ext y
      constructor
      · rintro ⟨z, ⟨x, hx, rfl⟩, rfl⟩
        exact ⟨x, hx, by simp [add_comm]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨r • x, ⟨x, hx, rfl⟩, by simp [add_comm]⟩
    _ = euclideanBall x₀ r := euclideanBallAffine_image_unitBall x₀ hr

private theorem setIntegral_comp_euclideanAffine (x₀ : Vec 3) {r : ℝ} (hr : 0 < r)
    {f : Vec 3 → ℝ} :
    ∫ x in euclideanBall (0 : Vec 3) 1, f (euclideanAffineMap x₀ r x) ∂volume =
      (r ^ (3 : ℕ))⁻¹ * ∫ y in euclideanBall x₀ r, f y ∂volume := by
  let U : Set (Vec 3) := euclideanBall (0 : Vec 3) 1
  let g : Vec 3 → ℝ := fun z => f (x₀ + z)
  have hscale :
      ∫ x in U, g (r • x) ∂volume =
        (r ^ (3 : ℕ))⁻¹ • ∫ z in r • U, g z ∂volume := by
    simpa only [g, U, smul_eq_mul, Module.finrank_pi, Fintype.card_fin] using
      (Measure.setIntegral_comp_smul_of_pos volume g U hr)
  have htrans :
      ∫ z in r • U, f (x₀ + z) ∂volume =
        ∫ y in translateSet x₀ (r • U), f y ∂volume := by
    simpa [add_comm] using
      (setIntegral_comp_addRight_translateSet (d := 3) (E := ℝ) x₀ (r • U) f)
  calc
    ∫ x in euclideanBall (0 : Vec 3) 1, f (euclideanAffineMap x₀ r x) ∂volume =
        ∫ x in U, g (r • x) ∂volume := by rfl
    _ = (r ^ (3 : ℕ))⁻¹ * ∫ z in r • U, g z ∂volume := by
      rw [hscale, smul_eq_mul]
    _ = (r ^ (3 : ℕ))⁻¹ *
        ∫ z in r • U, f (x₀ + z) ∂volume := by rfl
    _ = (r ^ (3 : ℕ))⁻¹ *
        ∫ y in translateSet x₀ (r • U), f y ∂volume := by rw [htrans]
    _ = (r ^ (3 : ℕ))⁻¹ * ∫ y in euclideanBall x₀ r, f y ∂volume := by
      rw [translate_smul_euclideanBall x₀ hr]

private theorem euclideanBall_volume_pos (x₀ : Vec 3) {r : ℝ} (hr : 0 < r) :
    0 < (volume (euclideanBall x₀ r)).toReal := by
  have hunit : 0 < (volume (euclideanBall (0 : Vec 3) 1)).toReal := by
    have hball : Metric.ball (0 : Vec 3) (1 / 3) ⊆
        euclideanBall (0 : Vec 3) 1 := by
      intro x hx
      apply (mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).2
      have hnorm : ‖x‖ < 1 / 3 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hx
      have hcomp : vecEuclideanNorm x ≤ 3 * ‖x‖ := by
        simpa [vecEuclideanNorm, spaceEuclideanNorm, vecNormSq, vecDot, pow_two] using
          (euclideanNorm_le_three_mul_space_norm x)
      have hcomp' : vecEuclideanNorm (x - (0 : Vec 3)) ≤ 3 * ‖x‖ := by
        simpa only [sub_zero] using hcomp
      nlinarith only [hcomp', hnorm]
    have hpos : 0 < volume (Metric.ball (0 : Vec 3) (1 / 3)) := by
      exact Metric.isOpen_ball.measure_pos volume
        (Metric.nonempty_ball.mpr (by norm_num))
    have htop : volume (euclideanBall (0 : Vec 3) 1) < ∞ := by
      apply lt_of_le_of_lt (measure_mono (by
        intro x hx
        exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2
          ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx).le))
      exact (isCompact_euclideanClosedBall (0 : Vec 3)
        (by norm_num : (0 : ℝ) ≤ 1)).measure_lt_top
    exact ENNReal.toReal_pos (lt_of_lt_of_le hpos (measure_mono hball)).ne' htop.ne
  have hvol := setIntegral_comp_euclideanAffine x₀ hr
    (f := fun _ : Vec 3 => (1 : ℝ))
  have hleft :
      ∫ x in euclideanBall (0 : Vec 3) 1, (1 : ℝ) ∂volume =
        (volume (euclideanBall (0 : Vec 3) 1)).toReal := by
    rw [integral_const]
    simp [Measure.real]
  have hright :
      ∫ x in euclideanBall x₀ r, (1 : ℝ) ∂volume =
        (volume (euclideanBall x₀ r)).toReal := by
    rw [integral_const]
    simp [Measure.real]
  rw [hleft, hright] at hvol
  have hpow : 0 < r ^ (3 : ℕ) := by positivity
  have htop : volume (euclideanBall x₀ r) ≠ ∞ := by
    apply ne_of_lt
    exact (measure_mono (by
      intro x hx
      exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le hr.le).2
        ((mem_euclideanBall_iff_vecEuclideanNorm_lt hr).1 hx).le)).trans_lt
      (isCompact_euclideanClosedBall x₀ hr.le).measure_lt_top
  have hzero : (volume (euclideanBall x₀ r)).toReal ≠ 0 := by
    intro hz
    have : (volume (euclideanBall (0 : Vec 3) 1)).toReal = 0 := by
      rw [hvol, hz, mul_zero]
    exact (ne_of_gt hunit) this
  have hvolne : volume (euclideanBall x₀ r) ≠ 0 := by
    intro hz
    apply hzero
    simp [hz]
  exact ENNReal.toReal_pos hvolne htop

private theorem average_euclideanAffine (x₀ : Vec 3) {r : ℝ} (hr : 0 < r)
    {u : Vec 3 → ℝ} :
    integralAverage (euclideanBall (0 : Vec 3) 1)
        (fun x => u (euclideanAffineMap x₀ r x)) =
      integralAverage (euclideanBall x₀ r) u := by
  let U : Set (Vec 3) := euclideanBall (0 : Vec 3) 1
  have hIu := setIntegral_comp_euclideanAffine x₀ hr (f := u)
  have hIone := setIntegral_comp_euclideanAffine x₀ hr
    (f := fun _ : Vec 3 => (1 : ℝ))
  change (⨍ x in U, u (euclideanAffineMap x₀ r x) ∂volume) =
    ⨍ x in euclideanBall x₀ r, u x ∂volume
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq]
  simp only [smul_eq_mul]
  rw [hIu]
  have hIone' :
      ∫ x in U, (1 : ℝ) ∂volume =
        (r ^ (3 : ℕ))⁻¹ * ∫ y in euclideanBall x₀ r, (1 : ℝ) ∂volume := by
    simpa [U] using hIone
  have hvolU :
      ∫ x in U, (1 : ℝ) ∂volume =
        (volume.real U) := by
    rw [integral_const]
    simp [Measure.real]
  have hvolBall :
      ∫ x in euclideanBall x₀ r, (1 : ℝ) ∂volume =
        (volume.real (euclideanBall x₀ r)) := by
    rw [integral_const]
    simp [Measure.real]
  have hposU : 0 < (volume U).toReal := by
    dsimp [U]
    exact euclideanBall_volume_pos (0 : Vec 3) (by norm_num)
  have hposBall : 0 < (volume (euclideanBall x₀ r)).toReal :=
    euclideanBall_volume_pos x₀ hr
  rw [← hvolU, ← hvolBall, hIone']
  field_simp [hposU.ne', hposBall.ne', pow_ne_zero (3 : ℕ) hr.ne']

private theorem fderiv_euclideanAffine (x₀ : Vec 3) (r : ℝ)
    {g : Vec 3 → ℝ} (x : Vec 3) :
    fderiv ℝ (fun x => g (euclideanAffineMap x₀ r x)) x =
      r • fderiv ℝ g (euclideanAffineMap x₀ r x) := by
  have hcomp :
      (fun x : Vec 3 => g (x₀ + r • x)) =
        (fun x : Vec 3 => (fun y : Vec 3 => g (x₀ + y)) (r • x)) := by
    funext y
    rfl
  rw [show (fun x : Vec 3 => g (euclideanAffineMap x₀ r x)) =
      fun x => g (x₀ + r • x) by rfl, hcomp]
  have hfd :
      fderiv ℝ (fun x : Vec 3 => (fun y : Vec 3 => g (x₀ + y)) (r • x)) x =
        r • fderiv ℝ (fun y : Vec 3 => g (x₀ + y)) (r • x) := by
    simpa using
      (fderiv_comp_smul (𝕜 := ℝ) (f := fun y : Vec 3 => g (x₀ + y)) (x := x) r)
  rw [hfd, fderiv_comp_add_left]
  simp [euclideanAffineMap]

private theorem norm_fderiv_euclideanAffine (x₀ : Vec 3) {r : ℝ} (hr : 0 < r)
    {g : Vec 3 → ℝ} (x : Vec 3) :
    ‖fderiv ℝ (fun x => g (euclideanAffineMap x₀ r x)) x‖ =
      r * ‖fderiv ℝ g (euclideanAffineMap x₀ r x)‖ := by
  rw [fderiv_euclideanAffine]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]

private theorem integral_rpow_unit_to_real
    (g : Vec 3 → ℝ) (hg : ContDiff ℝ 1 g) :
    (∫ x in euclideanBall (0 : Vec 3) 1,
      |g x - integralAverage (euclideanBall (0 : Vec 3) 1) g| ^ (3 / 2 : ℝ)
      ∂volume) ^ (2 / 3 : ℝ) ≤
      poincareSobolevL1Constant.toReal *
        ∫ x in euclideanBall (0 : Vec 3) 1, ‖fderiv ℝ g x‖ ∂volume := by
  let U : Set (Vec 3) := euclideanBall (0 : Vec 3) 1
  let c : ℝ := integralAverage U g
  let v : Vec 3 → ℝ := fun x => g x - c
  have hgcont : Continuous g := (hg.differentiable (by simp)).continuous
  have hcompact : IsCompact (euclideanClosedBall (0 : Vec 3) 1) :=
    isCompact_euclideanClosedBall (0 : Vec 3) (by norm_num)
  have hUsub : U ⊆ euclideanClosedBall (0 : Vec 3) 1 := by
    intro x hx
    exact (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by norm_num)).2
      ((mem_euclideanBall_iff_vecEuclideanNorm_lt (by norm_num)).1 hx).le
  have hvpow : IntegrableOn (fun x => |v x| ^ (3 / 2 : ℝ)) U volume := by
    have hcont : ContinuousOn (fun x => |v x| ^ (3 / 2 : ℝ))
        (euclideanClosedBall (0 : Vec 3) 1) := by
      apply ((hgcont.sub continuous_const).abs.continuousOn.rpow_const)
      intro x hx
      exact Or.inr (by norm_num)
    exact (hcont.integrableOn_compact hcompact).mono_set hUsub
  have hgrad : IntegrableOn (fun x => ‖fderiv ℝ g x‖) U volume := by
    have hcont : ContinuousOn (fun x => ‖fderiv ℝ g x‖)
        (euclideanClosedBall (0 : Vec 3) 1) := by
      exact (hg.continuous_fderiv (by norm_num)).norm.continuousOn
    exact (hcont.integrableOn_compact hcompact).mono_set hUsub
  have hvmeas : AEStronglyMeasurable v (volume.restrict U) := by
    exact (hgcont.sub continuous_const).aestronglyMeasurable.restrict
  have hgradmeas : AEStronglyMeasurable (fderiv ℝ g) (volume.restrict U) := by
    exact (hg.continuous_fderiv (by norm_num)).aestronglyMeasurable.restrict
  have hA :
      ENNReal.ofReal (∫ x in U, |v x| ^ (3 / 2 : ℝ) ∂volume) =
        ∫⁻ x in U, ‖v x‖ₑ ^ (3 / 2 : ℝ) ∂volume := by
    rw [ofReal_integral_eq_lintegral_ofReal hvpow
      (ae_restrict_of_ae (Filter.Eventually.of_forall
        (fun (x : Vec 3) => Real.rpow_nonneg (abs_nonneg (v x))
          (3 / 2 : ℝ))))]
    apply lintegral_congr_ae
    filter_upwards [] with x
    rw [← ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (v x)) (by norm_num)]
    rw [← ofReal_norm]
    rw [Real.norm_eq_abs]
  have hB :
      ENNReal.ofReal (∫ x in U, ‖fderiv ℝ g x‖ ∂volume) =
        eLpNorm (fderiv ℝ g) 1 (volume.restrict U) := by
    calc
      ENNReal.ofReal (∫ x in U, ‖fderiv ℝ g x‖ ∂volume) =
          ∫⁻ x in U, ENNReal.ofReal ‖fderiv ℝ g x‖ ∂volume :=
        ofReal_integral_eq_lintegral_ofReal hgrad
          (ae_restrict_of_ae (Filter.Eventually.of_forall
            (fun (x : Vec 3) => norm_nonneg (fderiv ℝ g x))))
      _ = ∫⁻ x in U, ‖fderiv ℝ g x‖ₑ ∂volume := by
        apply lintegral_congr_ae
        filter_upwards [] with x
        rw [← ofReal_norm]
      _ = eLpNorm (fderiv ℝ g) 1 (volume.restrict U) := by
        rw [eLpNorm_one_eq_lintegral_enorm hgradmeas]
  have hunit := poincareSobolevL1_unit g hg
  have hunit' :
      (∫⁻ x in U, ‖v x‖ₑ ^ (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≤
        poincareSobolevL1Constant *
          eLpNorm (fderiv ℝ g) 1 (volume.restrict U) := by
    rw [eLpNorm_nnreal_eq_lintegral (p := (3 / 2 : NNReal))
      (by norm_num) hvmeas] at hunit
    norm_num at hunit ⊢
    simpa [U, v, c] using hunit
  rw [← hA] at hunit'
  rw [← hB] at hunit'
  have hCtop : poincareSobolevL1Constant ≠ ∞ := by
    rw [poincareSobolevL1Constant]
    exact ENNReal.mul_ne_top ENNReal.coe_ne_top
      ((ENNReal.add_ne_top.mpr ⟨by norm_num, by
        exact ENNReal.mul_ne_top (by norm_num) ENNReal.ofReal_ne_top⟩))
  have hAtop :
      ENNReal.ofReal (∫ x in U, |v x| ^ (3 / 2 : ℝ) ∂volume) ^ (2 / 3 : ℝ) ≠ ∞ := by
    exact ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top
  have hBtop : ENNReal.ofReal (∫ x in U, ‖fderiv ℝ g x‖ ∂volume) ≠ ∞ :=
    ENNReal.ofReal_ne_top
  have hrighttop :
      poincareSobolevL1Constant *
          ENNReal.ofReal (∫ x in U, ‖fderiv ℝ g x‖ ∂volume) ≠ ∞ :=
    ENNReal.mul_ne_top hCtop hBtop
  have hreal := (ENNReal.toReal_le_toReal hAtop hrighttop).mpr hunit'
  have hI : 0 ≤ ∫ x in U, |v x| ^ (3 / 2 : ℝ) ∂volume := by
    exact integral_nonneg_of_ae (ae_restrict_of_ae
      (Filter.Eventually.of_forall (fun (x : Vec 3) =>
        Real.rpow_nonneg (abs_nonneg (v x)) (3 / 2 : ℝ))))
  have hJ : 0 ≤ ∫ x in U, ‖fderiv ℝ g x‖ ∂volume := by
    exact integral_nonneg_of_ae (ae_restrict_of_ae
      (Filter.Eventually.of_forall (fun (x : Vec 3) =>
        norm_nonneg (fderiv ℝ g x))))
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_ofReal hI,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal hJ] at hreal
  simpa [U, v, c] using hreal

private theorem rpow_three_inverse_two_thirds (r : ℝ) (hr : 0 < r) :
    ((r ^ (3 : ℕ))⁻¹) ^ (2 / 3 : ℝ) = r ^ (-2 : ℝ) := by
  calc
    ((r ^ (3 : ℕ))⁻¹) ^ (2 / 3 : ℝ) =
        ((r ^ (3 : ℝ))⁻¹) ^ (2 / 3 : ℝ) := by
          congr 2
          exact (Real.rpow_natCast r 3).symm
    _ = ((r ^ (3 : ℝ)) ^ (2 / 3 : ℝ))⁻¹ := by
          exact Real.inv_rpow (x := r ^ (3 : ℝ)) (by positivity) (2 / 3 : ℝ)
    _ = (r ^ ((3 : ℝ) * (2 / 3 : ℝ)))⁻¹ := by
          rw [← Real.rpow_mul hr.le]
    _ = r ^ (-2 : ℝ) := by
          norm_num

private theorem r_mul_three_inverse (r : ℝ) (hr : 0 < r) :
    r * (r ^ (3 : ℕ))⁻¹ = (r ^ (2 : ℕ))⁻¹ := by
  field_simp [hr.ne']

theorem poincareSobolevL1_ball (x₀ : Vec 3) {r : ℝ} (hr : 0 < r)
    (g : Vec 3 → ℝ) (hg : ContDiff ℝ 1 g) :
    (∫ x in euclideanBall x₀ r,
        |g x - integralAverage (euclideanBall x₀ r) g| ^ (3 / 2 : ℝ)
        ∂volume) ^ (2 / 3 : ℝ) ≤
      poincareSobolevL1Constant.toReal *
        ∫ x in euclideanBall x₀ r, ‖fderiv ℝ g x‖ ∂volume := by
  let v : Vec 3 → ℝ := ballPullback x₀ r g
  have hv : ContDiff ℝ 1 v := ballPullback_contDiff x₀ r hg
  have havg :
      integralAverage (euclideanBall (0 : Vec 3) 1) v =
        integralAverage (euclideanBall x₀ r) g := by
    change integralAverage (euclideanBall (0 : Vec 3) 1)
        (fun x => g (x₀ + r • x)) = integralAverage (euclideanBall x₀ r) g
    exact average_euclideanAffine x₀ hr (u := g)
  have hunit := integral_rpow_unit_to_real v hv
  rw [havg] at hunit
  have hleft :
      ∫ x in euclideanBall (0 : Vec 3) 1,
          |v x - integralAverage (euclideanBall x₀ r) g| ^ (3 / 2 : ℝ) ∂volume =
        (r ^ (3 : ℕ))⁻¹ *
          ∫ y in euclideanBall x₀ r,
            |g y - integralAverage (euclideanBall x₀ r) g| ^ (3 / 2 : ℝ) ∂volume := by
    change ∫ x in euclideanBall (0 : Vec 3) 1,
        |g (x₀ + r • x) - integralAverage (euclideanBall x₀ r) g| ^
          (3 / 2 : ℝ) ∂volume = _
    exact setIntegral_comp_euclideanAffine x₀ hr
      (f := fun y : Vec 3 =>
        |g y - integralAverage (euclideanBall x₀ r) g| ^ (3 / 2 : ℝ))
  have hgrad :
      ∫ x in euclideanBall (0 : Vec 3) 1, ‖fderiv ℝ v x‖ ∂volume =
        r * (r ^ (3 : ℕ))⁻¹ *
          ∫ y in euclideanBall x₀ r, ‖fderiv ℝ g y‖ ∂volume := by
    calc
      ∫ x in euclideanBall (0 : Vec 3) 1, ‖fderiv ℝ v x‖ ∂volume =
          ∫ x in euclideanBall (0 : Vec 3) 1,
            r * ‖fderiv ℝ g (euclideanAffineMap x₀ r x)‖ ∂volume := by
        apply integral_congr_ae
        filter_upwards [] with x
        exact norm_fderiv_euclideanAffine x₀ hr x
      _ = r * ∫ x in euclideanBall (0 : Vec 3) 1,
            ‖fderiv ℝ g (euclideanAffineMap x₀ r x)‖ ∂volume := by
        rw [integral_const_mul]
      _ = r * ((r ^ (3 : ℕ))⁻¹ *
            ∫ y in euclideanBall x₀ r, ‖fderiv ℝ g y‖ ∂volume) := by
        have hscale := setIntegral_comp_euclideanAffine x₀ hr
          (f := fun y : Vec 3 => ‖fderiv ℝ g y‖)
        rw [hscale]
      _ = _ := by ring
  rw [hleft, hgrad] at hunit
  have hleftscale :
      ((r ^ (3 : ℕ))⁻¹ *
          ∫ y in euclideanBall x₀ r,
            |g y - integralAverage (euclideanBall x₀ r) g| ^ (3 / 2 : ℝ) ∂volume) ^
          (2 / 3 : ℝ) =
        (r ^ (2 : ℕ))⁻¹ *
          (∫ y in euclideanBall x₀ r,
            |g y - integralAverage (euclideanBall x₀ r) g| ^ (3 / 2 : ℝ) ∂volume) ^
            (2 / 3 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by
      exact integral_nonneg_of_ae (ae_restrict_of_ae
        (Filter.Eventually.of_forall (fun (x : Vec 3) =>
          Real.rpow_nonneg (abs_nonneg _) (3 / 2 : ℝ)))))]
    rw [rpow_three_inverse_two_thirds r hr]
    rw [show r ^ (-2 : ℝ) = (r ^ (2 : ℕ))⁻¹ by
      calc
        r ^ (-2 : ℝ) = (r ^ (2 : ℝ))⁻¹ := Real.rpow_neg hr.le (2 : ℝ)
        _ = (r ^ (2 : ℕ))⁻¹ := by
          exact congrArg (fun x : ℝ => x⁻¹) (Real.rpow_natCast r 2)]
  have hgradscale :
      r * (r ^ (3 : ℕ))⁻¹ = (r ^ (2 : ℕ))⁻¹ := r_mul_three_inverse r hr
  rw [hleftscale, hgradscale] at hunit
  have hmul := mul_le_mul_of_nonneg_left hunit
    (by positivity : 0 ≤ (r ^ (2 : ℕ)))
  calc
    (∫ y in euclideanBall x₀ r,
        |g y - integralAverage (euclideanBall x₀ r) g| ^ (3 / 2 : ℝ) ∂volume) ^
        (2 / 3 : ℝ) =
      (r ^ (2 : ℕ)) *
        ((r ^ (2 : ℕ))⁻¹ *
          (∫ y in euclideanBall x₀ r,
            |g y - integralAverage (euclideanBall x₀ r) g| ^ (3 / 2 : ℝ) ∂volume) ^
            (2 / 3 : ℝ)) := by
          field_simp [hr.ne']
    _ ≤ (r ^ (2 : ℕ)) *
        (poincareSobolevL1Constant.toReal *
          ((r ^ (2 : ℕ))⁻¹ *
            ∫ y in euclideanBall x₀ r, ‖fderiv ℝ g y‖ ∂volume)) := hmul
    _ = poincareSobolevL1Constant.toReal *
        ∫ y in euclideanBall x₀ r, ‖fderiv ℝ g y‖ ∂volume := by
      field_simp [hr.ne']

end
end CKN
