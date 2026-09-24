/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyEnergy
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleyC1
public import LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Inequalities.SeeleySplit
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Gradient energy bounds for the two-reflection extension

The chain rule and the operator-norm estimates from `SeeleyBounds` are
combined with the pullback estimates from `SeeleyEnergy`.
-/

@[expose] public section

open Set MeasureTheory
open scoped ENNReal

namespace CKN

noncomputable section

attribute [local instance] Classical.propDecidable

private theorem seeley_norm_le_vecEuclideanNorm (x : Vec 3) :
    ‖x‖ ≤ vecEuclideanNorm x := by
  rw [Pi.norm_def]
  have hnn : Finset.univ.sup (fun i => ‖x i‖₊) ≤
      ⟨vecEuclideanNorm x, vecEuclideanNorm_nonneg x⟩ := by
    apply Finset.sup_le
    intro i hi
    exact_mod_cast abs_apply_le_vecEuclideanNorm x i
  exact_mod_cast hnn

theorem seeley_fderiv_norm_le_three_classicalGradient
    (f : Vec 3 → ℝ) (x : Vec 3) :
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
    _ ≤ ∑ i : Fin 3, ‖z i • (fderiv ℝ f x) (basisVec i)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖z‖ * ‖classicalGradient f x‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      have hz : |z i| ≤ ‖z‖ := by
        simpa only [Real.norm_eq_abs] using norm_le_pi_norm z i
      have hg : |(fderiv ℝ f x) (basisVec i)| ≤ ‖classicalGradient f x‖ := by
        simpa only [classicalGradient_apply, Real.norm_eq_abs] using
          norm_le_pi_norm (classicalGradient f x) i
      exact mul_le_mul hz hg (abs_nonneg _) (norm_nonneg _)
    _ = 3 * ‖classicalGradient f x‖ * ‖z‖ := by
      simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
      ring

private theorem seeley_classicalGradient_norm_le_three_fderiv
    (f : Vec 3 → ℝ) (x : Vec 3) :
    ‖classicalGradient f x‖ ≤ 3 * ‖fderiv ℝ f x‖ := by
  have hcoord : ∀ i : Fin 3,
      |classicalGradient f x i| ≤ ‖fderiv ℝ f x‖ := by
    intro i
    rw [classicalGradient_apply]
    have hi := ContinuousLinearMap.le_opNorm (fderiv ℝ f x) (basisVec i)
    have hbi : ‖basisVec i‖ = (1 : ℝ) := by
      apply le_antisymm
      · rw [Pi.norm_def]
        change (↑(Finset.univ.sup (fun b => ‖basisVec i b‖₊) : NNReal) : ℝ) ≤
          ↑(1 : NNReal)
        exact_mod_cast (Finset.sup_le fun j hj => by
          by_cases h : j = i
          · subst h
            simp only [basisVec_apply]
            simp
          · simp only [basisVec_apply]
            simp [h])
      · have hi' : ‖basisVec i i‖ ≤ ‖basisVec i‖ := norm_le_pi_norm _ _
        simpa [basisVec] using hi'
    simpa only [Real.norm_eq_abs, hbi, mul_one] using hi
  have hvec : vecEuclideanNorm (classicalGradient f x) ≤
      3 * ‖fderiv ℝ f x‖ := by
    rw [vecEuclideanNorm, vecNormSq_eq_sum_sq]
    apply (Real.sqrt_le_iff).2
    constructor
    · positivity
    calc
      ∑ i : Fin 3, classicalGradient f x i ^ 2 ≤
          ∑ i : Fin 3, ‖fderiv ℝ f x‖ ^ 2 := by
        exact Finset.sum_le_sum fun i hi => by
          have hsq := (sq_le_sq₀ (abs_nonneg (classicalGradient f x i))
            (by positivity)).2 (hcoord i)
          simpa only [sq_abs] using hsq
      _ = 3 * ‖fderiv ℝ f x‖ ^ 2 := by simp
      _ ≤ (3 * ‖fderiv ℝ f x‖) ^ 2 := by
        nlinarith only [sq_nonneg (‖fderiv ℝ f x‖)]
  exact (seeley_norm_le_vecEuclideanNorm _).trans hvec

private theorem seeleyGradient_annulus_open : IsOpen seeleyAnnulus := by
  have hnorm : Continuous (vecEuclideanNorm (d := 3)) := by
    change Continuous (fun x : Vec 3 => Real.sqrt (vecNormSq x))
    exact (contDiff_vecNormSq (d := 3)).continuous.sqrt
  rw [seeleyAnnulus]
  exact (isOpen_lt continuous_const hnorm).inter (isOpen_lt hnorm continuous_const)

private theorem seeleyGradient_annulus_mem_of_closed {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) : x ∈ seeleyAnnulus := by
  exact ⟨by linarith only [hx.1], by linarith only [hx.2]⟩

private theorem seeleyReflectionOne_comp_fderiv_norm_le
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    ‖fderiv ℝ (v ∘ seeleyReflectionOne) x‖ ≤
      25 * ‖fderiv ℝ v (seeleyReflectionOne x)‖ := by
  have hA := seeleyGradient_annulus_mem_of_closed hx
  have hρ := seeleyReflectionOne_contDiffOn.contDiffAt
    (seeleyGradient_annulus_open.mem_nhds hA)
  have hρd := hρ.differentiableAt (by simp)
  have hvd := hv.differentiable_one (seeleyReflectionOne x)
  rw [fderiv_comp x hvd hρd]
  calc
    ‖fderiv ℝ v (seeleyReflectionOne x) ∘SL fderiv ℝ seeleyReflectionOne x‖ ≤
        ‖fderiv ℝ v (seeleyReflectionOne x)‖ *
          ‖fderiv ℝ seeleyReflectionOne x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ v (seeleyReflectionOne x)‖ * 25 := by
      exact mul_le_mul_of_nonneg_left
        (seeleyReflectionOne_fderiv_norm_le hx) (norm_nonneg _)
    _ = 25 * ‖fderiv ℝ v (seeleyReflectionOne x)‖ := by ring

private theorem seeleyReflectionTwo_comp_fderiv_norm_le
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) {x : Vec 3}
    (hx : x ∈ seeleyClosedAnnulus) :
    ‖fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ ≤
      169 * ‖fderiv ℝ v (seeleyReflectionTwo x)‖ := by
  have hA := seeleyGradient_annulus_mem_of_closed hx
  have hρ := seeleyReflectionTwo_contDiffOn.contDiffAt
    (seeleyGradient_annulus_open.mem_nhds hA)
  have hρd := hρ.differentiableAt (by simp)
  have hvd := hv.differentiable_one (seeleyReflectionTwo x)
  rw [fderiv_comp x hvd hρd]
  calc
    ‖fderiv ℝ v (seeleyReflectionTwo x) ∘SL fderiv ℝ seeleyReflectionTwo x‖ ≤
        ‖fderiv ℝ v (seeleyReflectionTwo x)‖ *
          ‖fderiv ℝ seeleyReflectionTwo x‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖fderiv ℝ v (seeleyReflectionTwo x)‖ * 169 := by
      exact mul_le_mul_of_nonneg_left
        (seeleyReflectionTwo_fderiv_norm_le hx) (norm_nonneg _)
    _ = 169 * ‖fderiv ℝ v (seeleyReflectionTwo x)‖ := by ring

private theorem seeleyExtension_gradient_energy_pointwise
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) (g : Vec 3 → ℝ≥0∞)
    (hρ : ∀ y : Vec 3,
      ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) = g y)
    {x : Vec 3} (hx : x ∈ seeleyOuterAnnulus) :
    ENNReal.ofReal (‖classicalGradient (seeleyExtension v) x‖ ^ 2) ≤
      (2 * 675 ^ 2 : ℝ≥0∞) * g (seeleyReflectionOne x) +
        (2 * 3042 ^ 2 : ℝ≥0∞) * g (seeleyReflectionTwo x) := by
  have hxC : x ∈ seeleyClosedAnnulus :=
    seeleyOuterAnnulus_subset_closedAnnulus hx
  have hcomp1 := seeleyReflectionOne_comp_fderiv_norm_le v hv hxC
  have hcomp2 := seeleyReflectionTwo_comp_fderiv_norm_le v hv hxC
  have hv1 := seeley_fderiv_norm_le_three_classicalGradient v
    (seeleyReflectionOne x)
  have hv2 := seeley_fderiv_norm_le_three_classicalGradient v
    (seeleyReflectionTwo x)
  have hcomp1' :
      ‖fderiv ℝ (v ∘ seeleyReflectionOne) x‖ ≤
        75 * ‖classicalGradient v (seeleyReflectionOne x)‖ := by
    calc
      _ ≤ 25 * ‖fderiv ℝ v (seeleyReflectionOne x)‖ := hcomp1
      _ ≤ 25 * (3 * ‖classicalGradient v (seeleyReflectionOne x)‖) := by
        gcongr
      _ = _ := by ring
  have hcomp2' :
      ‖fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ ≤
        507 * ‖classicalGradient v (seeleyReflectionTwo x)‖ := by
    calc
      _ ≤ 169 * ‖fderiv ℝ v (seeleyReflectionTwo x)‖ := hcomp2
      _ ≤ 169 * (3 * ‖classicalGradient v (seeleyReflectionTwo x)‖) := by
        gcongr
      _ = _ := by ring
  have hfdext := seeleyExtension_fderiv_eq_reflection_combo_of_mem_annulus
    v hv hx
  have hfdnorm :
      ‖fderiv ℝ (seeleyExtension v) x‖ ≤
        3 * ‖fderiv ℝ (v ∘ seeleyReflectionOne) x‖ +
          2 * ‖fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ := by
    rw [hfdext]
    calc
      ‖(3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x -
            (2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ ≤
          ‖(3 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionOne) x‖ +
            ‖(2 : ℝ) • fderiv ℝ (v ∘ seeleyReflectionTwo) x‖ :=
        norm_sub_le _ _
      _ = _ := by simp only [norm_smul, Real.norm_eq_abs]; norm_num
  have hgrad :
      ‖classicalGradient (seeleyExtension v) x‖ ≤
        675 * ‖classicalGradient v (seeleyReflectionOne x)‖ +
          3042 * ‖classicalGradient v (seeleyReflectionTwo x)‖ := by
    calc
      _ ≤ 3 * ‖fderiv ℝ (seeleyExtension v) x‖ :=
        seeley_classicalGradient_norm_le_three_fderiv _ _
      _ ≤ 3 * (3 * ‖fderiv ℝ (v ∘ seeleyReflectionOne) x‖ +
          2 * ‖fderiv ℝ (v ∘ seeleyReflectionTwo) x‖) := by
        gcongr
      _ ≤ 3 * (3 * (75 *
            ‖classicalGradient v (seeleyReflectionOne x)‖) +
          2 * (507 *
            ‖classicalGradient v (seeleyReflectionTwo x)‖)) := by
        gcongr
      _ = _ := by ring
  have hsq :
      ‖classicalGradient (seeleyExtension v) x‖ ^ 2 ≤
        2 * (675 * ‖classicalGradient v (seeleyReflectionOne x)‖) ^ 2 +
          2 * (3042 * ‖classicalGradient v (seeleyReflectionTwo x)‖) ^ 2 := by
    have hsq' := (sq_le_sq₀
      (norm_nonneg (classicalGradient (seeleyExtension v) x))
      (by positivity)).2 hgrad
    nlinarith only [hsq', sq_nonneg
      (675 * ‖classicalGradient v (seeleyReflectionOne x)‖ -
        3042 * ‖classicalGradient v (seeleyReflectionTwo x)‖)]
  calc
    _ ≤ ENNReal.ofReal
        (2 * (675 * ‖classicalGradient v (seeleyReflectionOne x)‖) ^ 2 +
          2 * (3042 * ‖classicalGradient v (seeleyReflectionTwo x)‖) ^ 2) :=
      ENNReal.ofReal_le_ofReal hsq
    _ = (2 * 675 ^ 2 : ℝ≥0∞) *
          ENNReal.ofReal (‖classicalGradient v (seeleyReflectionOne x)‖ ^ 2) +
        (2 * 3042 ^ 2 : ℝ≥0∞) *
          ENNReal.ofReal (‖classicalGradient v (seeleyReflectionTwo x)‖ ^ 2) := by
      rw [ENNReal.ofReal_add (by positivity) (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      norm_num
      ring
    _ = (2 * 675 ^ 2 : ℝ≥0∞) * g (seeleyReflectionOne x) +
          (2 * 3042 ^ 2 : ℝ≥0∞) * g (seeleyReflectionTwo x) := by
      rw [hρ, hρ]

private theorem seeleyExtension_gradient_density_measurable
    (v : Vec 3 → ℝ) (g : Vec 3 → ℝ≥0∞) (hv : ContDiff ℝ 1 v)
    (hρ : ∀ y : Vec 3,
      ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) = g y) :
    Measurable g := by
  rw [← funext hρ]
  have hgrad : Continuous (classicalGradient v) := by
    apply continuous_pi
    intro i
    simpa only [classicalGradient_apply] using
      (hv.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hbase : Measurable (fun x =>
      ENNReal.ofReal ‖classicalGradient v x‖) :=
    ENNReal.measurable_ofReal.comp (continuous_norm.comp hgrad).measurable
  have hpow : Measurable (fun x =>
      (ENNReal.ofReal ‖classicalGradient v x‖) ^ (2 : ℕ)) :=
    hbase.pow measurable_const
  convert hpow using 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _)]

theorem seeleyExtension_gradient_energy_le
    (v : Vec 3 → ℝ) (hv : ContDiff ℝ 1 v) :
    ∫⁻ x in seeleyOuterAnnulus,
        ENNReal.ofReal (‖classicalGradient (seeleyExtension v) x‖ ^ 2) ∂volume ≤
      (2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648 : ℝ≥0∞) *
        ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1,
          ENNReal.ofReal (‖classicalGradient v y‖ ^ 2) ∂volume := by
  generalize hρ : (fun y => ENNReal.ofReal (‖classicalGradient v y‖ ^ 2)) = g
  have hg := seeleyExtension_gradient_density_measurable v g hv
    (fun y => congrFun hρ y)
  have hsplit := lintegral_reflection_split_coeff seeleyClosedAnnulus_measurableSet
    (2 * 675 ^ 2 : ℝ≥0∞) (2 * 3042 ^ 2 : ℝ≥0∞) g hg
  have hpoint : ∀ x ∈ seeleyOuterAnnulus,
      ENNReal.ofReal (‖classicalGradient (seeleyExtension v) x‖ ^ 2) ≤
        (2 * 675 ^ 2 : ℝ≥0∞) * g (seeleyReflectionOne x) +
          (2 * 3042 ^ 2 : ℝ≥0∞) * g (seeleyReflectionTwo x) := by
    intro x hx
    exact seeleyExtension_gradient_energy_pointwise v hv g
      (fun y => congrFun hρ y) hx
  calc
    _ ≤ ∫⁻ x in seeleyOuterAnnulus,
        (2 * 675 ^ 2 : ℝ≥0∞) * g (seeleyReflectionOne x) +
          (2 * 3042 ^ 2 : ℝ≥0∞) * g (seeleyReflectionTwo x) ∂volume := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem seeleyOuterAnnulus_measurableSet] with x hx
      exact hpoint x hx
    _ ≤ ∫⁻ x in seeleyClosedAnnulus,
        (2 * 675 ^ 2 : ℝ≥0∞) * g (seeleyReflectionOne x) +
          (2 * 3042 ^ 2 : ℝ≥0∞) * g (seeleyReflectionTwo x) ∂volume := by
      exact lintegral_mono_set seeleyOuterAnnulus_subset_closedAnnulus
    _ = (2 * 675 ^ 2 : ℝ≥0∞) *
          ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionOne x) ∂volume +
        (2 * 3042 ^ 2 : ℝ≥0∞) *
          ∫⁻ x in seeleyClosedAnnulus, g (seeleyReflectionTwo x) ∂volume := hsplit
    _ ≤ (2 * 675 ^ 2 : ℝ≥0∞) *
          (64 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume) +
        (2 * 3042 ^ 2 : ℝ≥0∞) *
          (648 * ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (seeleyReflectionOne_lintegral_comp_le g) (by positivity))
        (mul_le_mul_of_nonneg_left
          (seeleyReflectionTwo_lintegral_comp_le g) (by positivity))
    _ = (2 * 675 ^ 2 * 64 + 2 * 3042 ^ 2 * 648 : ℝ≥0∞) *
        ∫⁻ y in euclideanClosedBall (0 : Vec 3) 1, g y ∂volume := by
      ring

end
end CKN
