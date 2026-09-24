/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP234
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP56
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsP8
public import LeanPool.CaffarelliKohnNirenberg.Pressure.Cutoff
public import LeanPool.CaffarelliKohnNirenberg.Pressure.DecompositionSWS
public import LeanPool.CaffarelliKohnNirenberg.Pressure.UTensorNormFactor
public import LeanPool.CaffarelliKohnNirenberg.Setting.UTensor
public import LeanPool.CaffarelliKohnNirenberg.Setting.TimeHolder
public import LeanPool.CaffarelliKohnNirenberg.Setting.SliceNormBounds

/-!
# Pk Bounds Cylinder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

private lemma pressure_basisVec_norm (i : Fin 3) : ‖basisVec i‖ = (1 : ℝ) := by
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

theorem pressure_cutoff_spatialDeriv_bound
    (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (y : Vec3) (i : Fin 3) :
    |spatialDeriv (mollifiedBallCutoff x₀ hρ) i y| ≤
      cutoffGradientConstant / ρ := by
  have hg := mollifiedBallCutoff_gradient_bound x₀ hρ y
  have hi := abs_apply_le_vecEuclideanNorm
    (classicalGradient (mollifiedBallCutoff x₀ hρ) y) i
  have hle := hi.trans hg
  simpa [spatialDeriv, classicalGradient, classicalGradient_apply, basisVec_apply] using hle

theorem pressure_cutoff_mixedSecond_bound
    (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) (y : Vec3) (i j : Fin 3) :
    |mixedSecond (mollifiedBallCutoff x₀ hρ) i j y| ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
  have hgrad_diff : DifferentiableAt ℝ
      (classicalGradient (mollifiedBallCutoff x₀ hρ)) y := by
    apply differentiableAt_pi.mpr
    intro k
    change DifferentiableAt ℝ
      (spatialDeriv (mollifiedBallCutoff x₀ hρ) k) y
    exact (contDiff_spatialDeriv_smooth
      (mollifiedBallCutoff_smooth x₀ hρ) k).differentiable (by norm_num) y
  have hh := mollifiedBallCutoff_second_derivative_bound x₀ hρ y
  have hi' (k : Fin 3) : ‖(fderiv ℝ (classicalGradient
      (mollifiedBallCutoff x₀ hρ)) y) (basisVec k)‖ ≤
      cutoffSecondDerivativeConstant / ρ ^ 2 := by
    have hi := ContinuousLinearMap.le_opNorm
      (fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) y)
      (basisVec k)
    calc
      _ ≤ ‖fderiv ℝ (classicalGradient
          (mollifiedBallCutoff x₀ hρ)) y‖ * ‖basisVec k‖ := hi
      _ = ‖fderiv ℝ (classicalGradient
          (mollifiedBallCutoff x₀ hρ)) y‖ := by
        rw [pressure_basisVec_norm, mul_one]
      _ ≤ cutoffSecondDerivativeConstant / ρ ^ 2 := hh
  have hcoord : (fun z : Vec3 =>
      classicalGradient (mollifiedBallCutoff x₀ hρ) z j) =
      spatialDeriv (mollifiedBallCutoff x₀ hρ) j := by
    rfl
  have hcoordfd := congrArg (fun g : Vec3 → ℝ => fderiv ℝ g y) hcoord
  have hcoordapply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcoordfd
  have hfdapply := fderiv_apply hgrad_diff j
  have hcoord_le :
      |(fderiv ℝ (fun z : Vec3 =>
          classicalGradient (mollifiedBallCutoff x₀ hρ) z j) y)
          (basisVec i)| ≤
        ‖(fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) y)
          (basisVec i)‖ := by
    rw [hfdapply]
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
      Real.norm_eq_abs] using
      (norm_le_pi_norm
        ((fderiv ℝ (classicalGradient (mollifiedBallCutoff x₀ hρ)) y)
          (basisVec i)) j)
  change |(fderiv ℝ (spatialDeriv
    (mollifiedBallCutoff x₀ hρ) j) y) (basisVec i)| ≤ _
  rw [← hcoordapply]
  exact hcoord_le.trans (hi' i)

theorem pressure_cutoff_derivatives_vanish
    (x₀ : Vec3) {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : y ∉ euclideanBall x₀ (3 * ρ / 4) \
      euclideanClosedBall x₀ (13 * ρ / 20)) :
    (∀ i, spatialDeriv (mollifiedBallCutoff x₀ hρ) i y = 0) ∧
      (∀ i j, mixedSecond (mollifiedBallCutoff x₀ hρ) i j y = 0) := by
  obtain ⟨hgrad, hhess⟩ :=
    mollifiedBallCutoff_derivatives_vanish_outside_annulus x₀ hρ hy
  constructor
  · intro i
    simpa [spatialDeriv, classicalGradient, classicalGradient_apply, basisVec_apply] using
      congrArg (fun v : Vec3 => v i) hgrad
  · intro i j
    have hgrad_diff : DifferentiableAt ℝ
        (classicalGradient (mollifiedBallCutoff x₀ hρ)) y := by
      apply differentiableAt_pi.mpr
      intro k
      change DifferentiableAt ℝ
        (spatialDeriv (mollifiedBallCutoff x₀ hρ) k) y
      exact (contDiff_spatialDeriv_smooth
        (mollifiedBallCutoff_smooth x₀ hρ) k).differentiable (by norm_num) y
    have hcoord : (fun z : Vec3 =>
        classicalGradient (mollifiedBallCutoff x₀ hρ) z j) =
        spatialDeriv (mollifiedBallCutoff x₀ hρ) j := by
      rfl
    have hcoordfd := congrArg (fun g : Vec3 → ℝ => fderiv ℝ g y) hcoord
    have hcoordapply := congrArg (fun L : Vec3 →L[ℝ] ℝ => L (basisVec i)) hcoordfd
    have hfdapply := fderiv_apply hgrad_diff j
    change (fderiv ℝ (spatialDeriv
      (mollifiedBallCutoff x₀ hρ) j) y) (basisVec i) = 0
    rw [← hcoordapply, hfdapply]
    rw [hhess]
    simp

theorem pressure_cutoff_support_subset_ball (x₀ : Vec3) {ρ : ℝ}
    (hρ : 0 < ρ) :
    tsupport (mollifiedBallCutoff x₀ hρ) ⊆ vec3Ball x₀ ρ := by
  intro y hy
  have houter := mollifiedBallCutoff_tsupport_subset_outer x₀ hρ hy
  apply (mem_vec3Ball).2
  have hlt := (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 houter
  have hlt' : vecEuclideanNorm (y - x₀) < ρ :=
    lt_of_lt_of_le hlt (by nlinarith only [hρ])
  simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using hlt'

theorem pressure_kernel_meas_shift (x : Vec3) :
    Measurable (fun y : Vec3 => -CKN.Foundation.Heat.newtonianKernel (x - y)) := by
  have hnorm : Measurable (fun z : Vec3 => vec3EuclideanNorm z) := by
    unfold vec3EuclideanNorm
    fun_prop
  unfold CKN.Foundation.Heat.newtonianKernel
  have hden : Measurable (fun y : Vec3 =>
      (4 * Real.pi) * vec3EuclideanNorm (x - y)) :=
    measurable_const.mul (hnorm.comp (measurable_const.sub measurable_id))
  exact (measurable_const.div hden).neg

theorem pressure_kernel_deriv_meas_shift (x : Vec3) (i : Fin 3) :
    Measurable (fun y : Vec3 =>
      CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)) := by
  unfold CKN.spatialDeriv
  exact (measurable_fderiv_apply_const ℝ CKN.Foundation.Heat.newtonianKernel
    (basisVec i)).comp (measurable_const.sub measurable_id)

theorem pressure_potential_source_integrable
    {g : Vec3 → ℝ} {x₀ x : Vec3} {ρ ρ' : ℝ}
    (hg : Integrable g volume)
    (hA : ∀ y, g y ≠ 0 → y ∈ pressureAnnulus x₀ ρ')
    (hρ : 0 < ρ') (hr : 0 < ρ) (hhalf : ρ ≤ ρ' / 2)
    (hx : x ∈ vec3Ball x₀ ρ) :
    Integrable (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) * g y) volume := by
  have hmeas : AEStronglyMeasurable
      (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) * g y) volume :=
    (pressure_kernel_meas_shift x).aestronglyMeasurable.mul hg.aestronglyMeasurable
  apply (hg.norm.const_mul (2 / ρ')).mono hmeas
  filter_upwards [] with y
  by_cases hzero : g y = 0
  · simp [hzero]
  · have hy := hA y hzero
    have hk := pressure_kernel_bound_on_annulus hρ hr hhalf hx hy
    have hcoef : 0 ≤ 2 / ρ' := by positivity
    simpa only [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hcoef, abs_abs] using
      (show |CKN.Foundation.Heat.newtonianKernel (x - y)| * |g y| ≤
          (2 / ρ') * |g y| from
        mul_le_mul_of_nonneg_right hk (abs_nonneg (g y)))

theorem pressure_derivative_source_integrable
    {g : Vec3 → ℝ} {x₀ x : Vec3} {ρ ρ' : ℝ} (i : Fin 3)
    (hg : Integrable g volume)
    (hA : ∀ y, g y ≠ 0 → y ∈ pressureAnnulus x₀ ρ')
    (hρ : 0 < ρ') (hr : 0 < ρ) (hhalf : ρ ≤ ρ' / 2)
    (hx : x ∈ vec3Ball x₀ ρ) :
    Integrable (fun y =>
      CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y) * g y) volume := by
  have hmeas : AEStronglyMeasurable (fun y =>
      CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y) * g y) volume :=
    (pressure_kernel_deriv_meas_shift x i).aestronglyMeasurable.mul hg.aestronglyMeasurable
  apply (hg.norm.const_mul (40 / ρ' ^ 2)).mono hmeas
  filter_upwards [] with y
  by_cases hzero : g y = 0
  · simp [hzero]
  · have hy := hA y hzero
    have hk := pressure_kernel_deriv_bound_on_annulus hρ hr hhalf hx hy i
    have hcoef : 0 ≤ 40 / ρ' ^ 2 := by positivity
    simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hcoef, abs_abs] using
      (show |CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel i (x - y)| *
          |g y| ≤ (40 / ρ' ^ 2) * |g y| from
        mul_le_mul_of_nonneg_right hk (abs_nonneg (g y)))

private lemma pressure_vec3EuclideanNorm_le_sqrt_three (v : Vec3) :
    vec3EuclideanNorm v ≤ Real.sqrt 3 * ‖v‖ := by
  have hsq : vec3EuclideanNorm v ^ 2 ≤ (Real.sqrt 3 * ‖v‖) ^ 2 := by
    have hv : vec3EuclideanNorm v ^ 2 = ∑ i : Fin 3, v i ^ 2 := by
      unfold vec3EuclideanNorm
      exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (v i)))
    rw [hv, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    calc
      ∑ i : Fin 3, v i ^ 2 ≤ ∑ _i : Fin 3, ‖v‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _hi
        rw [← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (norm_le_pi_norm v i) 2
      _ = 3 * ‖v‖ ^ 2 := by simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  have h2 : |vec3EuclideanNorm v| ≤ |Real.sqrt 3 * ‖v‖| := sq_le_sq.mp hsq
  rwa [abs_of_nonneg (vec3EuclideanNorm_nonneg v),
    abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg 3) (norm_nonneg v))] at h2

private lemma pressure_continuous_vec3EuclideanNorm :
    Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
  unfold vec3EuclideanNorm
  fun_prop

theorem pressure_utensor_integrable_on_ball
    {u : ParabolicPoint → Vec3} {c : ℝ → Vec3} {x₀ : Vec3} {ρ s : ℝ}
    (_ : 0 < ρ)
    (humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2
      (volume.restrict (vec3Ball x₀ ρ))) :
    Integrable (pressureUTensorNorm u c s)
      (volume.restrict (vec3Ball x₀ ρ)) := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ ρ)
  have hμtop : μ Set.univ < ∞ := by
    simp only [μ, Measure.restrict_apply MeasurableSet.univ, univ_inter]
    rw [volume_vec3Ball_eq]
    exact ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top
  have : IsFiniteMeasure μ := ⟨hμtop⟩
  have humeas' : AEStronglyMeasurable (fun y : Vec3 => u (y, s)) μ :=
    humeas.aestronglyMeasurable
  have hnormmeas : AEStronglyMeasurable
      (fun y : Vec3 => vec3EuclideanNorm (u (y, s))) μ := by
    exact (pressure_continuous_vec3EuclideanNorm.measurable.comp_aemeasurable
      humeas).aestronglyMeasurable
  have huE : MemLp (fun y : Vec3 => vec3EuclideanNorm (u (y, s))) 2 μ := by
    apply hu.of_le_mul hnormmeas
    on_goal 1 => filter_upwards [] with y
    simpa only [Real.norm_eq_abs, abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using
      pressure_vec3EuclideanNorm_le_sqrt_three (u (y, s))
  let cvec : Vec3 := c s
  have hsub : MemLp (fun y : Vec3 => u (y, s) - cvec) 2 μ :=
    hu.sub (memLp_const cvec)
  have hsubE : MemLp (fun y : Vec3 => vec3EuclideanNorm (u (y, s) - cvec)) 2 μ := by
    apply hsub.of_le_mul
      ((pressure_continuous_vec3EuclideanNorm.measurable.comp_aemeasurable
        (hsub.aestronglyMeasurable.aemeasurable)).aestronglyMeasurable)
    on_goal 1 => filter_upwards [] with y
    simpa only [Function.comp_apply, Real.norm_eq_abs,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _)] using
      pressure_vec3EuclideanNorm_le_sqrt_three (u (y, s) - cvec)
  have hmul : Integrable (fun y : Vec3 =>
      vec3EuclideanNorm (u (y, s)) * vec3EuclideanNorm (u (y, s) - cvec)) μ :=
    huE.integrable_mul hsubE
  have hmeas : AEStronglyMeasurable (pressureUTensorNorm u c s) μ := by
    let F : Vec3 → ℝ := fun v => Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      (-v i * (v j - c s j)) ^ (2 : ℕ))
    have hF : Continuous F := by
      dsimp [F]
      fun_prop
    have h := hF.measurable.comp_aemeasurable humeas
    change AEStronglyMeasurable (fun y => Real.sqrt (∑ i : Fin 3, ∑ j : Fin 3,
      (-u (y, s) i * (u (y, s) j - c s j)) ^ (2 : ℕ))) μ
    exact h.aestronglyMeasurable
  apply hmul.mono hmeas
  filter_upwards [] with y
  rw [CKN.pressureUTensorNorm_eq_mul]

theorem pressure_spatialGradientSq_le
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (w : ParabolicPoint) :
    spatialGradientSq u Du w ≤ 9 * ‖Du w‖ ^ (2 : ℕ) := by
  unfold spatialGradientSq
  calc
    ∑ i : Fin 3, ∑ j : Fin 3, (Du w i j) ^ (2 : ℕ) ≤
        ∑ _i : Fin 3, ∑ _j : Fin 3, ‖Du w‖ ^ (2 : ℕ) := by
      apply Finset.sum_le_sum
      intro i _hi
      apply Finset.sum_le_sum
      intro j _hj
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _)
        ((norm_le_pi_norm (Du w i) j).trans (norm_le_pi_norm (Du w) i)) 2
    _ = 9 * ‖Du w‖ ^ (2 : ℕ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      ring

theorem pressureP234_fixed_bound
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {x₀ : Vec3} {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r)
    (hhalf : r ≤ ρ / 2) (hC₁ : 0 ≤ cutoffGradientConstant)
    (hC₂ : 0 ≤ cutoffSecondDerivativeConstant)
    (hηeq : η = mollifiedBallCutoff x₀ hρ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ vec3Ball x₀ ρ)
    (_ : vec3Ball x₀ ρ ⊆ vec3Ball x₀ ρ)
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2
      (volume.restrict (vec3Ball x₀ ρ)))
    (_ : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hU : Integrable (pressureUTensorNorm u c s)
      (volume.restrict (vec3Ball x₀ ρ))) :
    ∀ x ∈ vec3Ball x₀ r,
      |pressureP2 η u c s x| + |pressureP3 η u c s x| +
          |pressureP4 η u c s x| ≤
        (18 * cutoffSecondDerivativeConstant + 720 * cutoffGradientConstant) /
            ρ ^ 3 * ∫ y in vec3Ball x₀ ρ, pressureUTensorNorm u c s y := by
  let μ : Measure Vec3 := volume.restrict (vec3Ball x₀ ρ)
  have : IsFiniteMeasure μ := by
    apply isFiniteMeasure_restrict.mpr
    rw [volume_vec3Ball_eq]
    exact (ENNReal.mul_lt_top (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
      ENNReal.ofReal_lt_top).ne
  have huComp (i : Fin 3) : MemLp (fun y : Vec3 => u (y, s) i) 2 μ := by
    exact hu.continuousLinearMap_comp
      (ContinuousLinearMap.proj i : Vec3 →L[ℝ] ℝ)
  have huInt (i : Fin 3) : Integrable (fun y : Vec3 => u (y, s) i) μ :=
    huComp i |>.integrable (by norm_num)
  have hUScalar {i j : Fin 3} {g : Vec3 → ℝ} (hg : Continuous g)
      (hgc : HasCompactSupport g) (hgΩ : tsupport g ⊆ vec3Ball x₀ ρ) :
      IntegrableOn (fun y => pressureUTensor u c (y, s) i j * g y)
        (vec3Ball x₀ ρ) volume := by
    obtain ⟨C, hC⟩ := hgc.exists_bound_of_continuous hg
    have hi := (huInt i).mul_bdd hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using hC y)
    have hj := (huInt j).mul_bdd hg.measurable.aestronglyMeasurable
      (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs] using hC y)
    have hprod : Integrable (fun y => u (y, s) i * u (y, s) j * g y) μ := by
      exact ((huComp i).integrable_mul (huComp j)).mul_bdd
        hg.measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          simpa only [Real.norm_eq_abs] using hC y)
    have hprod' : IntegrableOn
        (fun y => u (y, s) i * u (y, s) j * g y)
        (vec3Ball x₀ ρ) volume := hprod
    have hlin : IntegrableOn
        (fun y => u (y, s) i * g y) (vec3Ball x₀ ρ) volume := hi
    have hsum : IntegrableOn
        (fun y => -(u (y, s) i * u (y, s) j * g y) +
          c s j * (u (y, s) i * g y)) (vec3Ball x₀ ρ) volume :=
      hprod'.neg.add (hlin.const_mul (c s j))
    exact hsum.congr (Filter.Eventually.of_forall fun y => by
      simp only [pressureUTensor]
      ring)
  have hηd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) :=
    contDiff_spatialDeriv_smooth hη i
  have hηm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) :=
    contDiff_mixedSecond_smooth hη i j
  have hηdc (i : Fin 3) : HasCompactSupport (spatialDeriv η i) :=
    hηc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hηmc (i j : Fin 3) : HasCompactSupport (mixedSecond η i j) := by
    exact (hηc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  have hηdΩ (i : Fin 3) : tsupport (spatialDeriv η i) ⊆ vec3Ball x₀ ρ :=
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ
  have hηmΩ (i j : Fin 3) : tsupport (mixedSecond η i j) ⊆ vec3Ball x₀ ρ :=
    ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      (tsupport_fderiv_apply_subset ℝ (basisVec j))).trans hηΩ
  have hsource {g : Vec3 → ℝ} (hg : IntegrableOn g (vec3Ball x₀ ρ) volume)
      (hgs : tsupport g ⊆ vec3Ball x₀ ρ) : Integrable g volume :=
    decomposition_full_of_on_sws hg hgs
  have hI₂ (i j : Fin 3) : Integrable
      (fun y => mixedSecond η i j y * pressureUTensor u c (y, s) i j) volume := by
    apply hsource _
      ((tsupport_mul_subset_left (f := mixedSecond η i j)
        (g := fun y => pressureUTensor u c (y, s) i j)).trans (hηmΩ i j))
    exact (hUScalar (i := i) (j := j) (hηm i j).continuous
      (hηmc i j) (hηmΩ i j)).congr
      (Filter.Eventually.of_forall fun y => by ring)
  have hI₃ (i j : Fin 3) : Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η i y) volume := by
    apply hsource _
      ((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
        (g := spatialDeriv η i)).trans (hηdΩ i))
    exact (hUScalar (i := i) (j := j) (hηd i).continuous
      (hηdc i) (hηdΩ i)).congr
      (Filter.Eventually.of_forall fun y => by ring)
  have hI₄ (i j : Fin 3) : Integrable
      (fun y => pressureUTensor u c (y, s) i j * spatialDeriv η j y) volume := by
    apply hsource _
      ((tsupport_mul_subset_right (f := fun y => pressureUTensor u c (y, s) i j)
        (g := spatialDeriv η j)).trans (hηdΩ j))
    exact (hUScalar (i := i) (j := j) (hηd j).continuous
      (hηdc j) (hηdΩ j)).congr
      (Filter.Eventually.of_forall fun y => by ring)
  have hA₂ (i j : Fin 3) (y : Vec3)
      (hy : mixedSecond η i j y * pressureUTensor u c (y, s) i j ≠ 0) :
      y ∈ pressureAnnulus x₀ ρ := by
    rw [hηeq] at hy
    by_contra hnot
    have hy' : y ∉ euclideanBall x₀ (3 * ρ / 4) \
        euclideanClosedBall x₀ (13 * ρ / 20) := by
      intro hmem
      by_cases ho : y ∈ vec3Ball x₀ (3 * ρ / 4)
      · have hi : y ∉ vec3Ball x₀ (13 * ρ / 20) := by
          intro hi
          apply hmem.2
          apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
          simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
            using (mem_vec3Ball.mp hi).le
        exact hnot ⟨ho, hi⟩
      · exact ho ((mem_vec3Ball).2 (by
          simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
            using (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hmem.1))
    have hz := pressure_cutoff_derivatives_vanish x₀ hρ hy'
    exact hy (by rw [hz.2 i j, zero_mul])
  have hA₃ (i j : Fin 3) (y : Vec3)
      (hy : pressureUTensor u c (y, s) i j * spatialDeriv η i y ≠ 0) :
      y ∈ pressureAnnulus x₀ ρ := by
    rw [hηeq] at hy
    by_contra hnot
    have hy' : y ∉ euclideanBall x₀ (3 * ρ / 4) \
        euclideanClosedBall x₀ (13 * ρ / 20) := by
      intro hmem
      by_cases ho : y ∈ vec3Ball x₀ (3 * ρ / 4)
      · have hi : y ∉ vec3Ball x₀ (13 * ρ / 20) := by
          intro hi
          apply hmem.2
          apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
          simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
            using (mem_vec3Ball.mp hi).le
        exact hnot ⟨ho, hi⟩
      · exact ho ((mem_vec3Ball).2 (by
          simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
            using (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hmem.1))
    have hz := pressure_cutoff_derivatives_vanish x₀ hρ hy'
    exact hy (by rw [hz.1 i, mul_zero])
  have hA₄ (i j : Fin 3) (y : Vec3)
      (hy : pressureUTensor u c (y, s) i j * spatialDeriv η j y ≠ 0) :
      y ∈ pressureAnnulus x₀ ρ := by
    rw [hηeq] at hy
    by_contra hnot
    have hy' : y ∉ euclideanBall x₀ (3 * ρ / 4) \
        euclideanClosedBall x₀ (13 * ρ / 20) := by
      intro hmem
      by_cases ho : y ∈ vec3Ball x₀ (3 * ρ / 4)
      · have hi : y ∉ vec3Ball x₀ (13 * ρ / 20) := by
          intro hi
          apply hmem.2
          apply (mem_euclideanClosedBall_iff_vecEuclideanNorm_le (by positivity)).2
          simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
            using (mem_vec3Ball.mp hi).le
        exact hnot ⟨ho, hi⟩
      · exact ho ((mem_vec3Ball).2 (by
          simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two]
            using (mem_euclideanBall_iff_vecEuclideanNorm_lt (by positivity)).1 hmem.1))
    have hz := pressure_cutoff_derivatives_vanish x₀ hρ hy'
    exact hy (by rw [hz.1 j, mul_zero])
  have hI₂' : ∀ i j, Integrable
      (fun y => mixedSecond (mollifiedBallCutoff x₀ hρ) i j y *
        pressureUTensor u c (y, s) i j) volume := by
    intro i j
    simpa [hηeq] using hI₂ i j
  have hI₃' : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j *
        spatialDeriv (mollifiedBallCutoff x₀ hρ) i y) volume := by
    intro i j
    simpa [hηeq] using hI₃ i j
  have hI₄' : ∀ i j, Integrable
      (fun y => pressureUTensor u c (y, s) i j *
        spatialDeriv (mollifiedBallCutoff x₀ hρ) j y) volume := by
    intro i j
    simpa [hηeq] using hI₄ i j
  have hA₂' : ∀ i j y, mixedSecond (mollifiedBallCutoff x₀ hρ) i j y *
      pressureUTensor u c (y, s) i j ≠ 0 → y ∈ pressureAnnulus x₀ ρ := by
    intro i j y hy
    have hy' : mixedSecond η i j y * pressureUTensor u c (y, s) i j ≠ 0 := by
      simpa [hηeq] using hy
    exact hA₂ i j y hy'
  have hA₃' : ∀ i j y, pressureUTensor u c (y, s) i j *
      spatialDeriv (mollifiedBallCutoff x₀ hρ) i y ≠ 0 →
        y ∈ pressureAnnulus x₀ ρ := by
    intro i j y hy
    have hy' : pressureUTensor u c (y, s) i j * spatialDeriv η i y ≠ 0 := by
      simpa [hηeq] using hy
    exact hA₃ i j y hy'
  have hA₄' : ∀ i j y, pressureUTensor u c (y, s) i j *
      spatialDeriv (mollifiedBallCutoff x₀ hρ) j y ≠ 0 →
        y ∈ pressureAnnulus x₀ ρ := by
    intro i j y hy
    have hy' : pressureUTensor u c (y, s) i j * spatialDeriv η j y ≠ 0 := by
      simpa [hηeq] using hy
    exact hA₄ i j y hy'
  intro x hx
  have hP₂ := pressureP234_pointwise_annular_bound hρ hC₁ hC₂ hU
    (fun i j y => pressure_cutoff_mixedSecond_bound x₀ hρ y i j)
    (fun i y => pressure_cutoff_spatialDeriv_bound x₀ hρ y i)
    hI₂' (fun i j => fun {x} hx => pressure_potential_source_integrable
      (hI₂' i j) (hA₂' i j) hρ hr hhalf hx)
    hA₂' hI₃' (fun i j => fun {x} hx => pressure_derivative_source_integrable j
      (hI₃' i j) (hA₃' i j) hρ hr hhalf hx)
    hA₃' hI₄' (fun i j => fun {x} hx => pressure_derivative_source_integrable i
      (hI₄' i j) (hA₄' i j) hρ hr hhalf hx) hA₄' hr hhalf hx
  simpa [hηeq] using hP₂

/-! Cylinder assembly for the pressure terms whose fixed-time estimates use the
annular part of the cutoff. -/

theorem pressureP234_cylinder_bound
    {η : Vec3 → ℝ} {u : ParabolicPoint → Vec3} {c : ℝ → Vec3}
    {x₀ : Vec3} {t₀ r ρ K C₁₂ α β : ℝ}
    (_ : 0 < ρ) (hr : 0 < r) (_ : r ≤ ρ / 2)
    (hK : 0 ≤ K)
    {G : ℝ → ℝ}
    (hGmeas : AEStronglyMeasurable G
      (volume.restrict (Ioc (t₀ - r ^ 2) t₀)))
    (hP₂ : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t₀ r)),
      ‖pressureP2 η u c z.2 z.1‖ₑ ≤ ENNReal.ofReal K * ‖G z.2‖ₑ)
    (hP₃ : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t₀ r)),
      ‖pressureP3 η u c z.2 z.1‖ₑ ≤ ENNReal.ofReal K * ‖G z.2‖ₑ)
    (hP₄ : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t₀ r)),
      ‖pressureP4 η u c z.2 z.1‖ₑ ≤ ENNReal.ofReal K * ‖G z.2‖ₑ)
    (hscale :
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          (3 * ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume (vec3Ball x₀ r) *
            (∫⁻ s in Ioc (t₀ - r ^ 2) t₀, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^
              (2 / 3 : ℝ)) ≤
        ENNReal.ofReal (C₁₂ * (r / ρ) * α * β)) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (eLpNorm' (fun z : ParabolicPoint => pressureP2 η u c z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r)) +
          eLpNorm' (fun z : ParabolicPoint => pressureP3 η u c z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r)) +
          eLpNorm' (fun z : ParabolicPoint => pressureP4 η u c z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r))) ≤
      ENNReal.ofReal (C₁₂ * (r / ρ) * α * β) := by
  let R : ℝ≥0∞ := ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume (vec3Ball x₀ r) *
    (∫⁻ s in Ioc (t₀ - r ^ 2) t₀, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ)
  have h₂ := pressure_cylinder_eLpNorm_le (q := (3 / 2 : ℝ)) hr (by norm_num) hK hGmeas hP₂
  have h₃ := pressure_cylinder_eLpNorm_le (q := (3 / 2 : ℝ)) hr (by norm_num) hK hGmeas hP₃
  have h₄ := pressure_cylinder_eLpNorm_le (q := (3 / 2 : ℝ)) hr (by norm_num) hK hGmeas hP₄
  have hpow : (1 / (3 / 2 : ℝ)) = (2 / 3 : ℝ) := by norm_num
  rw [hpow] at h₂ h₃ h₄
  change eLpNorm' (fun z : ParabolicPoint => pressureP2 η u c z.2 z.1)
      (3 / 2 : ℝ) (volume.restrict (parabolicCylinder x₀ t₀ r)) ≤ R at h₂
  change eLpNorm' (fun z : ParabolicPoint => pressureP3 η u c z.2 z.1)
      (3 / 2 : ℝ) (volume.restrict (parabolicCylinder x₀ t₀ r)) ≤ R at h₃
  change eLpNorm' (fun z : ParabolicPoint => pressureP4 η u c z.2 z.1)
      (3 / 2 : ℝ) (volume.restrict (parabolicCylinder x₀ t₀ r)) ≤ R at h₄
  have hsum :
      eLpNorm' (fun z : ParabolicPoint => pressureP2 η u c z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r)) +
        eLpNorm' (fun z : ParabolicPoint => pressureP3 η u c z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r)) +
        eLpNorm' (fun z : ParabolicPoint => pressureP4 η u c z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r)) ≤ 3 * R := by
    calc
      _ ≤ R + R + R := by
        exact add_le_add (add_le_add h₂ h₃) h₄
      _ = 3 * R := by ring
  calc
    _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) * (3 * R) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ENNReal.ofReal (C₁₂ * (r / ρ) * α * β) := by simpa [R] using hscale

theorem pressureP56_cylinder_bound
    {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ}
    {x₀ : Vec3} {t₀ r ρ K C₁₂ δ : ℝ}
    (_ : 0 < ρ) (hr : 0 < r) (_ : r ≤ ρ / 2)
    (hK : 0 ≤ K)
    {G : ℝ → ℝ}
    (hGmeas : AEStronglyMeasurable G
      (volume.restrict (Ioc (t₀ - r ^ 2) t₀)))
    (hP₅ : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t₀ r)),
      ‖pressureP5 η p z.2 z.1‖ₑ ≤ ENNReal.ofReal K * ‖G z.2‖ₑ)
    (hP₆ : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t₀ r)),
      ‖pressureP6 η p z.2 z.1‖ₑ ≤ ENNReal.ofReal K * ‖G z.2‖ₑ)
    (hscale :
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          (2 * ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume (vec3Ball x₀ r) *
            (∫⁻ s in Ioc (t₀ - r ^ 2) t₀, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^
              (2 / 3 : ℝ)) ≤
        ENNReal.ofReal (C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) * δ ^ 2)) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (eLpNorm' (fun z : ParabolicPoint => pressureP5 η p z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r)) +
          eLpNorm' (fun z : ParabolicPoint => pressureP6 η p z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r))) ≤
      ENNReal.ofReal (C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) * δ ^ 2) := by
  let R : ℝ≥0∞ := ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume (vec3Ball x₀ r) *
    (∫⁻ s in Ioc (t₀ - r ^ 2) t₀, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^ (2 / 3 : ℝ)
  have h₅ := pressure_cylinder_eLpNorm_le (q := (3 / 2 : ℝ)) hr (by norm_num) hK hGmeas hP₅
  have h₆ := pressure_cylinder_eLpNorm_le (q := (3 / 2 : ℝ)) hr (by norm_num) hK hGmeas hP₆
  have hpow : (1 / (3 / 2 : ℝ)) = (2 / 3 : ℝ) := by norm_num
  rw [hpow] at h₅ h₆
  change eLpNorm' (fun z : ParabolicPoint => pressureP5 η p z.2 z.1)
      (3 / 2 : ℝ) (volume.restrict (parabolicCylinder x₀ t₀ r)) ≤ R at h₅
  change eLpNorm' (fun z : ParabolicPoint => pressureP6 η p z.2 z.1)
      (3 / 2 : ℝ) (volume.restrict (parabolicCylinder x₀ t₀ r)) ≤ R at h₆
  have hsum :
      eLpNorm' (fun z : ParabolicPoint => pressureP5 η p z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r)) +
        eLpNorm' (fun z : ParabolicPoint => pressureP6 η p z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r)) ≤ 2 * R := by
    calc
      _ ≤ R + R := add_le_add h₅ h₆
      _ = 2 * R := by ring
  calc
    _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) * (2 * R) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ ENNReal.ofReal (C₁₂ * (r / ρ) ^ (2 / 3 : ℝ) * δ ^ 2) := by
      simpa [R] using hscale

theorem pressureP8_cylinder_bound
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3}
    {x₀ : Vec3} {t₀ r ρ K C₁₃ lam : ℝ}
    (_ : 0 < ρ) (hr : 0 < r) (_ : r ≤ ρ / 2)
    (hK : 0 ≤ K)
    {G : ℝ → ℝ}
    (hGmeas : AEStronglyMeasurable G
      (volume.restrict (Ioc (t₀ - r ^ 2) t₀)))
    (hP₈ : ∀ᵐ z ∂(volume.restrict (parabolicCylinder x₀ t₀ r)),
      ‖pressureP8 η f z.2 z.1‖ₑ ≤ ENNReal.ofReal K * ‖G z.2‖ₑ)
    (hscale :
      ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
          ((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume (vec3Ball x₀ r) *
            (∫⁻ s in Ioc (t₀ - r ^ 2) t₀, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^
              (2 / 3 : ℝ) ≤
        ENNReal.ofReal (C₁₃ * (r / ρ) * lam)) :
    ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        eLpNorm' (fun z : ParabolicPoint => pressureP8 η f z.2 z.1) (3 / 2 : ℝ)
          (volume.restrict (parabolicCylinder x₀ t₀ r)) ≤
      ENNReal.ofReal (C₁₃ * (r / ρ) * lam) := by
  have h₈ := pressure_cylinder_eLpNorm_le (q := (3 / 2 : ℝ)) hr (by norm_num) hK hGmeas hP₈
  have hpow : (1 / (3 / 2 : ℝ)) = (2 / 3 : ℝ) := by norm_num
  rw [hpow] at h₈
  calc
    _ ≤ ENNReal.ofReal (r ^ (-4 / 3 : ℝ)) *
        (((ENNReal.ofReal K) ^ (3 / 2 : ℝ) * volume (vec3Ball x₀ r) *
          (∫⁻ s in Ioc (t₀ - r ^ 2) t₀, ‖G s‖ₑ ^ (3 / 2 : ℝ))) ^
            (2 / 3 : ℝ)) :=
      mul_le_mul_of_nonneg_left h₈ (by positivity)
    _ ≤ ENNReal.ofReal (C₁₃ * (r / ρ) * lam) := hscale

end CKN
