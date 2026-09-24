/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsCylinder
public import LeanPool.CaffarelliKohnNirenberg.Pressure.PkBoundsUnconditionalScale

/-!
# Pk Bounds Unconditional Core

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Parabolic.Integration

noncomputable section

namespace CKN

lemma pressure_slice_integral_aemeasurable
    {Ω' B : Set Vec3} {J : Set ℝ} {g : Vec3 × ℝ → ℝ}
    (_ : MeasurableSet B) (_ : MeasurableSet J)
    (hsub : B ⊆ Ω')
    (hg : AEStronglyMeasurable g
      (volume.restrict (spaceTimeSet Ω' J))) :
    AEMeasurable (fun s : ℝ => ∫ x in B, g (x, s))
      (volume.restrict J) := by
  have hg' : AEStronglyMeasurable g
      ((volume.restrict Ω').prod (volume.restrict J)) := by
    rw [Measure.prod_restrict Ω' J]
    exact hg
  have hgB : AEStronglyMeasurable g
      ((volume.restrict B).prod (volume.restrict J)) :=
    hg'.mono_measure (Measure.prod_mono
      (Measure.restrict_mono_set volume hsub) le_rfl)
  have hswap := hgB.prod_swap.integral_prod_right'
  simpa only [Prod.swap_prod_mk] using hswap.aemeasurable

lemma pressure_box_geometry
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∃ Ω' J, localBox Ω I Ω' J ∧ vec3Ball z.1 ρ ⊆ Ω' ∧
      Ioc (z.2 - ρ ^ 2) z.2 ⊆ J := by
  obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
    hsol.1 hsol.2.1 hρ hsub
  refine ⟨Ω', J, hbox, ?_, ?_⟩
  · intro y hy
    have hy' : (y, z.2) ∈ parabolicCylinder z.1 z.2 ρ := by
      rw [parabolicCylinder]
      exact ⟨hy, ⟨by linarith only [sq_pos_of_pos hρ], le_rfl⟩⟩
    exact (hcyl hy').1
  · intro s hs
    have hx : z.1 ∈ vec3Ball z.1 ρ := by
      rw [mem_vec3Ball]
      simpa [vec3EuclideanNorm_zero] using hρ
    have hs' : (z.1, s) ∈ parabolicCylinder z.1 z.2 ρ := by
      rw [parabolicCylinder]
      exact ⟨hx, hs⟩
    exact (hcyl hs').2

lemma pressure_prod_lintegral_swap
    {B : Set Vec3} {T : Set ℝ} {F : Vec3 × ℝ → ℝ}
    (hF : AEMeasurable F ((volume.restrict B).prod (volume.restrict T))) :
    (∫⁻ z in B ×ˢ T, ENNReal.ofReal (F z)) =
      ∫⁻ s in T, ∫⁻ x in B, ENNReal.ofReal (F (x, s)) := by
  rw [show (volume : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) from
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict]
  calc
    _ = ∫⁻ x : Vec3, ∫⁻ s : ℝ, ENNReal.ofReal (F (x, s))
        ∂(volume.restrict T) ∂(volume.restrict B) :=
      MeasureTheory.lintegral_prod _ (hF.ennreal_ofReal)
    _ = _ := MeasureTheory.lintegral_lintegral_swap (hF.ennreal_ofReal)

lemma pressure_time_norm_bound
    {B : Set Vec3} {T : Set ℝ} {F : Vec3 × ℝ → ℝ}
    {G : ℝ → ℝ} {D : ℝ≥0∞} {p₀ : ℝ}
    (hp : 0 < p₀)
    (hF : Integrable F ((volume.restrict B).prod (volume.restrict T)))
    (_ : AEStronglyMeasurable G (volume.restrict T))
    (hGdef : ∀ s, G s = (∫ x in B, F (x, s)) ^ (1 / p₀ : ℝ))
    (hFnonneg : ∀ z, 0 ≤ F z)
    (hbound : (∫⁻ z in B ×ˢ T, ENNReal.ofReal (F z)) ≤ D) :
    eLpNorm' G p₀ (volume.restrict T) ≤ D ^ (1 / p₀ : ℝ) := by
  have hFs : ∀ᵐ s ∂volume.restrict T,
      Integrable (fun x => F (x, s)) (volume.restrict B) := hF.prod_left_ae
  have hGpow : ∀ᵐ s ∂volume.restrict T,
      ‖G s‖ₑ ^ p₀ = ∫⁻ x in B, ENNReal.ofReal (F (x, s)) := by
    filter_upwards [hFs] with s hFs
    have hI : 0 ≤ ∫ x in B, F (x, s) :=
      integral_nonneg_of_ae (Eventually.of_forall (fun x => hFnonneg (x, s)))
    have hconv := ofReal_integral_eq_lintegral_ofReal hFs
      (Eventually.of_forall (fun x => hFnonneg (x, s)))
    rw [hGdef s, Real.enorm_eq_ofReal (Real.rpow_nonneg hI _)]
    rw [← ENNReal.ofReal_rpow_of_nonneg hI (by positivity)]
    rw [← ENNReal.rpow_mul]
    have hpn : p₀ ≠ 0 := ne_of_gt hp
    have hpow : (1 / p₀ : ℝ) * p₀ = 1 := by field_simp
    rw [hpow, ENNReal.rpow_one]
    exact hconv
  have hswap := pressure_prod_lintegral_swap (B := B) (T := T)
    hF.aemeasurable
  calc
    eLpNorm' G p₀ (volume.restrict T) =
        (∫⁻ s in T, ‖G s‖ₑ ^ p₀) ^ (1 / p₀ : ℝ) := by
      rw [eLpNorm'_eq_lintegral_enorm]
    _ = (∫⁻ s in T, ∫⁻ x in B, ENNReal.ofReal (F (x, s))) ^
        (1 / p₀ : ℝ) := by
      congr 1
      apply lintegral_congr_ae
      exact hGpow
    _ = (∫⁻ z in B ×ˢ T, ENNReal.ofReal (F z)) ^ (1 / p₀ : ℝ) := by
      rw [hswap]
    _ ≤ D ^ (1 / p₀ : ℝ) := ENNReal.rpow_le_rpow hbound (by positivity)

lemma pressure_lift_time_ae {B : Set Vec3} {T : Set ℝ} {P : ℝ → Prop}
    (h : ∀ᵐ s ∂volume.restrict T, P s) :
    ∀ᵐ z ∂volume.restrict (B ×ˢ T), P z.2 := by
  rw [show (volume : Measure (Vec3 × ℝ)) =
      (volume : Measure Vec3).prod (volume : Measure ℝ) from
        MeasureTheory.Measure.volume_eq_prod Vec3 ℝ, ← Measure.prod_restrict]
  exact (Measure.quasiMeasurePreserving_snd).ae h

lemma pressure_gradient_integrable
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    Integrable (fun w => spatialGradientSq u Du w)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
  have hmeasBox : AEStronglyMeasurable
      (fun w => spatialGradientSq u Du w)
      (volume.restrict (parabolicCylinder z.1 z.2 ρ)) := by
    obtain ⟨Ω', J, hbox, hcyl⟩ := exists_localBox_of_closure_subset
      hsol.1 hsol.2.1 hρ hsub
    have hdata := hsol.2.2.2.2.2.1 Ω' J hbox
    have hcont : Continuous (fun v : Fin 3 → Vec3 =>
        ∑ i, ∑ j, (v i j) ^ (2 : ℕ)) := by fun_prop
    have hmeas := hcont.comp_aestronglyMeasurable hdata.2.1
    have hmeas' : AEStronglyMeasurable
        (fun w => spatialGradientSq u Du w)
        (volume.restrict (spaceTimeSet Ω' J)) := by
      simpa [spatialGradientSq, Function.comp_def] using hmeas
    exact hmeas'.mono_measure (Measure.restrict_mono hcyl le_rfl)
  have hnonneg : 0 ≤ᵐ[volume.restrict (parabolicCylinder z.1 z.2 ρ)]
      fun w => spatialGradientSq u Du w :=
    Eventually.of_forall (fun w => by unfold spatialGradientSq; positivity)
  have hfin : (∫⁻ w in parabolicCylinder z.1 z.2 ρ,
      ENNReal.ofReal (spatialGradientSq u Du w)) < ⊤ :=
    sws_gradient_integral_lt_top hsol hρ hsub
  exact (lintegral_ofReal_ne_top_iff_integrable hmeasBox hnonneg).mp
    (ne_of_lt hfin)

lemma pressure_energy_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ} {u : ParabolicPoint → Vec3}
    {Du : ParabolicPoint → Fin 3 → Vec3} {p : ParabolicPoint → ℝ}
    {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∫ y in vec3Ball z.1 ρ,
        vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
        Real.sqrt ρ * alpha u z ρ := by
  obtain ⟨Ω', J, hbox, hball, htime⟩ := pressure_box_geometry hsol hρ hsub
  have hslices := slice_memLp_ae_of_sws hsol hbox
  have hslices' := ae_restrict_of_ae_restrict_of_subset htime hslices
  have hess := sws_timeSliceEnergyEssSup_eq_ofReal_alpha_sq hsol z hρ hsub
  have hEae := ENNReal.ae_le_essSup
    (μ := volume.restrict (Ioc (z.2 - ρ ^ 2) z.2))
    (fun s => timeSliceBallEnergy z.1 ρ s
      (fun w => vec3EuclideanNorm (u w)))
  filter_upwards [hslices', hEae] with s hs hEss
  have huB : MemLp (fun x : Vec3 => u (x, s)) 2
      (volume.restrict (vec3Ball z.1 ρ)) :=
    hs.1.mono_measure (Measure.restrict_mono_set volume hball)
  have humeas : AEStronglyMeasurable (fun x : Vec3 => u (x, s))
      (volume.restrict (vec3Ball z.1 ρ)) := huB.aestronglyMeasurable
  have hnormmeas : AEStronglyMeasurable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, s)))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have hcont : Continuous (fun v : Vec3 => vec3EuclideanNorm v) := by
      unfold vec3EuclideanNorm
      fun_prop
    exact hcont.comp_aestronglyMeasurable humeas
  have hu2 : Integrable
      (fun x : Vec3 => vec3EuclideanNorm (u (x, s)) ^ (2 : ℕ))
      (volume.restrict (vec3Ball z.1 ρ)) := by
    have huNorm := huB.integrable_norm_rpow (by norm_num) (by norm_num)
    apply (huNorm.const_mul (3 : ℝ)).mono' (hnormmeas.pow 2)
    filter_upwards [] with x
    change |(vec3EuclideanNorm (u (x, s))) ^ (2 : ℕ)| ≤
      3 * ‖u (x, s)‖ ^ ENNReal.toReal 2
    rw [abs_of_nonneg (pow_nonneg (vec3EuclideanNorm_nonneg _) _)]
    have hle : vec3EuclideanNorm (u (x, s)) ≤
        Real.sqrt 3 * ‖u (x, s)‖ := by
      have hsq : vec3EuclideanNorm (u (x, s)) ^ 2 ≤
          (Real.sqrt 3 * ‖u (x, s)‖) ^ 2 := by
        unfold vec3EuclideanNorm
        rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg _)),
          mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        calc
          _ ≤ ∑ _i : Fin 3, ‖u (x, s)‖ ^ 2 := by
            apply Finset.sum_le_sum
            intro i _hi
            rw [← sq_abs]
            exact pow_le_pow_left₀ (norm_nonneg (u (x, s) i))
              (norm_le_pi_norm (u (x, s)) i) 2
          _ = 3 * ‖u (x, s)‖ ^ 2 := by
            simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      exact (sq_le_sq₀ (vec3EuclideanNorm_nonneg _) (by positivity)).mp hsq
    have hsqrt : (Real.sqrt 3) ^ 2 = (3 : ℝ) := by
      rw [Real.sq_sqrt]
      norm_num
    calc
      _ ≤ (Real.sqrt 3 * ‖u (x, s)‖) ^ 2 :=
        (sq_le_sq₀ (vec3EuclideanNorm_nonneg _) (by positivity)).mpr hle
      _ = 3 * ‖u (x, s)‖ ^ 2 := by rw [mul_pow, hsqrt]
      _ = 3 * ‖u (x, s)‖ ^ ENNReal.toReal 2 := by norm_num
  have hEconv := ofReal_integral_eq_lintegral_ofReal hu2
    (Eventually.of_forall (fun x => pow_nonneg (vec3EuclideanNorm_nonneg _) _))
  have hEss' := hEss.trans_eq hess
  have hEbound : ENNReal.ofReal
      (∫ y in vec3Ball z.1 ρ,
        vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ≤
      ENNReal.ofReal (ρ * alpha u z ρ ^ 2) := by
    calc
      _ = ∫⁻ y in vec3Ball z.1 ρ,
          ENNReal.ofReal (vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) := hEconv
      _ = ∫⁻ y in vec3Ball z.1 ρ,
          ‖vec3EuclideanNorm (u (y, s))‖ₑ ^ (2 : ℝ) := by
        apply lintegral_congr
        intro y
        rw [Real.enorm_eq_ofReal (vec3EuclideanNorm_nonneg _)]
        rw [ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg (u (y, s))) 2]
        norm_num [Real.rpow_natCast]
      _ ≤ _ := by simpa [timeSliceBallEnergy] using hEss'
  have hEreal : 0 ≤ ∫ y in vec3Ball z.1 ρ,
      vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ) :=
    integral_nonneg_of_ae (Eventually.of_forall
      (fun y => pow_nonneg (vec3EuclideanNorm_nonneg _) _))
  have hα : 0 ≤ alpha u z ρ := by unfold alpha; positivity
  have hroot := ENNReal.rpow_le_rpow hEbound
    (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hleft : ENNReal.ofReal
      (∫ y in vec3Ball z.1 ρ,
        vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) =
      ENNReal.ofReal ((∫ y in vec3Ball z.1 ρ,
        vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg hEreal (by norm_num)]
  rw [hleft] at hroot
  have hrealroot :
      (∫ y in vec3Ball z.1 ρ,
        vec3EuclideanNorm (u (y, s)) ^ (2 : ℕ)) ^ (1 / 2 : ℝ) ≤
        (ρ * alpha u z ρ ^ 2) ^ (1 / 2 : ℝ) := by
    have hright : ENNReal.ofReal (ρ * alpha u z ρ ^ 2) ^ (1 / 2 : ℝ) =
        ENNReal.ofReal ((ρ * alpha u z ρ ^ 2) ^ (1 / 2 : ℝ)) :=
      ENNReal.ofReal_rpow_of_nonneg (x := ρ * alpha u z ρ ^ 2)
        (p := (1 / 2 : ℝ)) (mul_nonneg hρ.le (sq_nonneg _)) (by norm_num)
    rw [hright] at hroot
    exact (ENNReal.ofReal_le_ofReal_iff
      (Real.rpow_nonneg (mul_nonneg hρ.le (sq_nonneg _)) _)).mp hroot
  calc
    _ ≤ (ρ * alpha u z ρ ^ 2) ^ (1 / 2 : ℝ) := hrealroot
    _ = Real.sqrt ρ * alpha u z ρ := by
      have hsq : alpha u z ρ ^ 2 = alpha u z ρ ^ (2 : ℝ) := by
        norm_num [Real.rpow_natCast]
      rw [hsq, Real.mul_rpow hρ.le (Real.rpow_nonneg hα 2),
        Real.sqrt_eq_rpow]
      rw [← Real.rpow_mul hα]
      norm_num


private lemma pressure_spatial_laplacian_bound
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) (y : Vec3) :
    |spatialLaplacian (mollifiedBallCutoff x₀ hρ) y| ≤
      (3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
  rw [spatialLaplacian]
  calc
    |∑ i : Fin 3, mixedSecond (mollifiedBallCutoff x₀ hρ) i i y| ≤
        ∑ i : Fin 3, |mixedSecond (mollifiedBallCutoff x₀ hρ) i i y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin 3, cutoffSecondDerivativeConstant / ρ ^ 2 := by
      gcongr with i hi
      exact pressure_cutoff_mixedSecond_bound x₀ hρ y i i
    _ = (3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring

private lemma pressure_spatial_laplacian_vanish
    {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) {y : Vec3}
    (hy : y ∉ euclideanBall x₀ (3 * ρ / 4) \
      euclideanClosedBall x₀ (13 * ρ / 20)) :
    spatialLaplacian (mollifiedBallCutoff x₀ hρ) y = 0 := by
  rw [spatialLaplacian]
  simp only [Fin.sum_univ_three]
  have hz := pressure_cutoff_derivatives_vanish x₀ hρ hy
  have h0 : spatialDeriv (spatialDeriv (mollifiedBallCutoff x₀ hρ) 0) 0 y = 0 := by
    simpa only [mixedSecond] using hz.2 0 0
  have h1 : spatialDeriv (spatialDeriv (mollifiedBallCutoff x₀ hρ) 1) 1 y = 0 := by
    simpa only [mixedSecond] using hz.2 1 1
  have h2 : spatialDeriv (spatialDeriv (mollifiedBallCutoff x₀ hρ) 2) 2 y = 0 := by
    simpa only [mixedSecond] using hz.2 2 2
  simp [h0, h1, h2]

theorem pressureP56_fixed_bound
    {η : Vec3 → ℝ} {p : ParabolicPoint → ℝ} {x₀ : Vec3}
    {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hp : Integrable (fun y => |p (y, s)|)
      (volume.restrict (vec3Ball x₀ ρ)))
    (hpm : AEStronglyMeasurable (fun y : Vec3 => p (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hηeq : η = mollifiedBallCutoff x₀ hρ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ vec3Ball x₀ ρ) :
    ∀ x ∈ vec3Ball x₀ r,
      |pressureP5 η p s x| + |pressureP6 η p s x| ≤
        (18 * cutoffSecondDerivativeConstant + 240 * cutoffGradientConstant) /
          ρ ^ 3 * ∫ y in vec3Ball x₀ ρ, |p (y, s)| := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  have hηd (i : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η i) :=
    contDiff_spatialDeriv_smooth hη i
  have hηm (i j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (mixedSecond η i j) :=
    contDiff_mixedSecond_smooth hη i j
  have hηdc (i : Fin 3) : HasCompactSupport (spatialDeriv η i) :=
    hηc.fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hηmc (i j : Fin 3) : HasCompactSupport (mixedSecond η i j) :=
    (hηc.fderiv_apply (𝕜 := ℝ) (basisVec j)).fderiv_apply
      (𝕜 := ℝ) (basisVec i)
  have hηdB (i : Fin 3) : tsupport (spatialDeriv η i) ⊆ B :=
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ
  have hηmB (i j : Fin 3) : tsupport (mixedSecond η i j) ⊆ B :=
    ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      (tsupport_fderiv_apply_subset ℝ (basisVec j))).trans hηΩ
  have hηLapB : tsupport (spatialLaplacian η) ⊆ B := by
    change tsupport (fun y => ∑ i : Fin 3,
      spatialDeriv (spatialDeriv η i) i y) ⊆ B
    apply decomposition_ts_support_sum₃_sws
    intro i
    exact (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hηΩ)
  have hp0 : Integrable (fun y => p (y, s)) (volume.restrict B) := by
    apply (integrable_norm_iff hpm).mp
    simpa only [Real.norm_eq_abs] using hp
  have hsource {g : Vec3 → ℝ} (hg : IntegrableOn g B)
      (hgs : tsupport g ⊆ B) : Integrable g volume :=
    decomposition_full_of_on_sws hg hgs
  have hI₅ : Integrable (fun y => p (y, s) * spatialLaplacian η y) volume := by
    apply hsource
      (hp0.mul_bdd
        (contDiff_spatialLaplacian_smooth hη).continuous.measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, hηeq]
          exact pressure_spatial_laplacian_bound hρ y))
      ((tsupport_mul_subset_right (f := fun y => p (y, s))
        (g := spatialLaplacian η)).trans (by simpa [B] using hηLapB))
  have hI₆ (j : Fin 3) : Integrable
      (fun y => spatialDeriv η j y * p (y, s)) volume := by
    apply hsource
      ((hp0.mul_bdd (hηd j).continuous.measurable.aestronglyMeasurable
          (Filter.Eventually.of_forall fun y => by
            rw [Real.norm_eq_abs, hηeq]
            exact pressure_cutoff_spatialDeriv_bound x₀ hρ y j)).congr
        (Filter.Eventually.of_forall fun y => by ring))
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y => p (y, s))).trans (by simpa [B] using hηdB j))
  have hAnn₅ (y : Vec3)
      (hy : p (y, s) * spatialLaplacian η y ≠ 0) :
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
    have hzlap := pressure_spatial_laplacian_vanish hρ hy'
    exact hy (by rw [hzlap]; simp)
  have hAnn₆ (j : Fin 3) (y : Vec3)
      (hy : spatialDeriv η j y * p (y, s) ≠ 0) :
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
    exact hy (by rw [hz.1 j, zero_mul])
  have hP₅ {x : Vec3} (hx : x ∈ vec3Ball x₀ r) :
      Integrable (fun y => (-CKN.Foundation.Heat.newtonianKernel (x - y)) *
        (p (y, s) * spatialLaplacian η y)) volume := by
    exact pressure_potential_source_integrable hI₅
      (fun w hw => hAnn₅ w hw) hρ hr hhalf hx
  have hP₆ (j : Fin 3) {x : Vec3} (hx : x ∈ vec3Ball x₀ r) :
      Integrable (fun y => CKN.spatialDeriv CKN.Foundation.Heat.newtonianKernel j
        (x - y) * (spatialDeriv η j y * p (y, s))) volume :=
    pressure_derivative_source_integrable j (hI₆ j)
      (fun w hw => hAnn₆ j w hw) hρ hr hhalf hx
  have hLap : ∀ y, |spatialLaplacian η y| ≤
      (3 * cutoffSecondDerivativeConstant) / ρ ^ 2 := by
    intro y
    simpa [hηeq] using pressure_spatial_laplacian_bound hρ y
  have hD₁ : ∀ j y, |spatialDeriv η j y| ≤
      cutoffGradientConstant / ρ := by
    intro j y
    simpa [hηeq] using pressure_cutoff_spatialDeriv_bound x₀ hρ y j
  intro x hx
  have hC₁ : 0 ≤ cutoffGradientConstant := by
    have h := pressure_cutoff_spatialDeriv_bound x₀ hρ x₀ (0 : Fin 3)
    have h' : 0 ≤ cutoffGradientConstant / ρ :=
      (abs_nonneg _).trans h
    rcases (div_nonneg_iff.mp h') with hpos | hneg
    · exact hpos.1
    · exfalso
      linarith only [hρ, hneg.2]
  have hC₂ : 0 ≤ cutoffSecondDerivativeConstant := by
    have h := pressure_cutoff_mixedSecond_bound x₀ hρ x₀ (0 : Fin 3) 0
    have h' : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 :=
      (abs_nonneg _).trans h
    have hρsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
    rcases (div_nonneg_iff.mp h') with hpos | hneg
    · exact hpos.1
    · exfalso
      linarith only [hρsq, hneg.2]
  simpa only [show 6 * (3 * cutoffSecondDerivativeConstant) +
      240 * cutoffGradientConstant =
      18 * cutoffSecondDerivativeConstant + 240 * cutoffGradientConstant by ring] using
    (pressureP56_pointwise_annular_bound hρ
    hC₁ (by positivity : 0 ≤ 3 * cutoffSecondDerivativeConstant)
    hp hLap hD₁ hI₅
    (fun {x} hx' => pressure_potential_source_integrable hI₅
        (fun w hw => hAnn₅ w hw) hρ hr hhalf hx')
    (fun w hw => hAnn₅ w hw) hI₆
    (fun j {x} hx' =>
      pressure_derivative_source_integrable j (hI₆ j)
        (fun w hw => hAnn₆ j w hw) hρ hr hhalf hx')
    hAnn₆ hr hhalf hx)

theorem pressureP234_fixed_slice_bound
    {u : ParabolicPoint → Vec3}
    {x₀ : Vec3} {ρ r s : ℝ}
    (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hu : MemLp (fun y : Vec3 => u (y, s)) 2
      (volume.restrict (vec3Ball x₀ ρ)))
    (humeas : AEMeasurable (fun y : Vec3 => u (y, s))
      (volume.restrict (vec3Ball x₀ ρ))) :
    ∀ x ∈ vec3Ball x₀ r,
      |pressureP2 (mollifiedBallCutoff x₀ hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball x₀ ρ))
            (fun y => u (y, t) j)) s x| +
        |pressureP3 (mollifiedBallCutoff x₀ hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball x₀ ρ))
            (fun y => u (y, t) j)) s x| +
        |pressureP4 (mollifiedBallCutoff x₀ hρ) u
          (fun t j => MeasureTheory.average
            (volume.restrict (vec3Ball x₀ ρ))
            (fun y => u (y, t) j)) s x| ≤
        (18 * cutoffSecondDerivativeConstant + 720 * cutoffGradientConstant) /
          ρ ^ 3 *
          ∫ y in vec3Ball x₀ ρ,
            pressureUTensorNorm u
              (fun t j => MeasureTheory.average
                (volume.restrict (vec3Ball x₀ ρ))
                (fun y => u (y, t) j)) s y := by
  let c : ℝ → Vec3 := fun t j => MeasureTheory.average
    (volume.restrict (vec3Ball x₀ ρ)) (fun y => u (y, t) j)
  have hU : Integrable (pressureUTensorNorm u c s)
      (volume.restrict (vec3Ball x₀ ρ)) :=
    pressure_utensor_integrable_on_ball hρ humeas hu
  have hC₁ : 0 ≤ cutoffGradientConstant := by
    have h := pressure_cutoff_spatialDeriv_bound x₀ hρ x₀ (0 : Fin 3)
    have h' : 0 ≤ cutoffGradientConstant / ρ :=
      (abs_nonneg _).trans h
    rcases (div_nonneg_iff.mp h') with hpos | hneg
    · exact hpos.1
    · exfalso
      linarith only [hρ, hneg.2]
  have hC₂ : 0 ≤ cutoffSecondDerivativeConstant := by
    have h := pressure_cutoff_mixedSecond_bound x₀ hρ x₀
      (0 : Fin 3) 0
    have h' : 0 ≤ cutoffSecondDerivativeConstant / ρ ^ 2 :=
      (abs_nonneg _).trans h
    have hρsq : 0 < ρ ^ 2 := sq_pos_of_pos hρ
    rcases (div_nonneg_iff.mp h') with hpos | hneg
    · exact hpos.1
    · exfalso
      linarith only [hρsq, hneg.2]
  have hfixed := pressureP234_fixed_bound hρ hr hhalf hC₁ hC₂
    (η := mollifiedBallCutoff x₀ hρ) (u := u) (c := c)
    (hηeq := rfl) (mollifiedBallCutoff_smooth x₀ hρ)
    (mollifiedBallCutoff_hasCompactSupport x₀ hρ)
    (pressure_cutoff_support_subset_ball x₀ hρ)
    (by intro y hy; exact hy) hu
    humeas hU
  simpa [c, pressureUTensorNorm, utensorNorm, pressureUTensor, utensor,
    meanFreeVec, meanFreeComponent] using hfixed

theorem pressureP8_fixed_bound
    {η : Vec3 → ℝ} {f : ParabolicPoint → Vec3} {x₀ : Vec3}
    {ρ r s : ℝ} (hρ : 0 < ρ) (hr : 0 < r) (hhalf : r ≤ ρ / 2)
    (hf : Integrable (fun y => vec3EuclideanNorm (f (y, s)))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hfm : AEStronglyMeasurable (fun y : Vec3 => f (y, s))
      (volume.restrict (vec3Ball x₀ ρ)))
    (hηeq : η = mollifiedBallCutoff x₀ hρ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηΩ : tsupport η ⊆ vec3Ball x₀ ρ) :
    ∀ x ∈ vec3Ball x₀ r,
      |pressureP8 η f s x| ≤
        (6 * cutoffGradientConstant) / ρ ^ 2 *
          ∫ y in vec3Ball x₀ ρ, vec3EuclideanNorm (f (y, s)) := by
  let B : Set Vec3 := vec3Ball x₀ ρ
  have hηd (j : Fin 3) : ContDiff ℝ (⊤ : ℕ∞) (spatialDeriv η j) :=
    contDiff_spatialDeriv_smooth hη j
  have hηdc (j : Fin 3) : HasCompactSupport (spatialDeriv η j) :=
    hηc.fderiv_apply (𝕜 := ℝ) (basisVec j)
  have hηdB (j : Fin 3) : tsupport (spatialDeriv η j) ⊆ B :=
    (tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hηΩ
  have hsource {g : Vec3 → ℝ} (hg : IntegrableOn g B)
      (hgs : tsupport g ⊆ B) : Integrable g volume :=
    decomposition_full_of_on_sws hg hgs
  have hfcomp (j : Fin 3) :
      Integrable (fun y : Vec3 => f (y, s) j) (volume.restrict B) := by
    apply hf.mono'
      ((ContinuousLinearMap.proj j : Vec3 →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hfm)
    filter_upwards [] with y
    change ‖f (y, s) j‖ ≤ vec3EuclideanNorm (f (y, s))
    simpa [vec3EuclideanNorm, vecEuclideanNorm, vecNormSq, vecDot, pow_two] using
      abs_apply_le_vecEuclideanNorm (f (y, s)) j
  have hI (j : Fin 3) : Integrable
      (fun y => spatialDeriv η j y * f (y, s) j) volume := by
    have hprod : Integrable
        (fun y => f (y, s) j * spatialDeriv η j y)
        (volume.restrict B) :=
      (hfcomp j).mul_bdd (hηd j).continuous.measurable.aestronglyMeasurable
        (Filter.Eventually.of_forall fun y => by
          rw [Real.norm_eq_abs, hηeq]
          exact pressure_cutoff_spatialDeriv_bound x₀ hρ y j)
    have hprod' : Integrable
        (fun y => spatialDeriv η j y * f (y, s) j)
        (volume.restrict B) :=
      hprod.congr (Filter.Eventually.of_forall fun y => by ring)
    exact hsource hprod'
      ((tsupport_mul_subset_left (f := spatialDeriv η j)
        (g := fun y => f (y, s) j)).trans (by simpa [B] using hηdB j))
  have hAnn (j : Fin 3) (y : Vec3)
      (hy : spatialDeriv η j y * f (y, s) j ≠ 0) :
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
    exact hy (by rw [hz.1 j, zero_mul])
  have hC₁ : 0 ≤ cutoffGradientConstant := by
    have h := pressure_cutoff_spatialDeriv_bound x₀ hρ x₀ (0 : Fin 3)
    have h' : 0 ≤ cutoffGradientConstant / ρ := (abs_nonneg _).trans h
    rcases (div_nonneg_iff.mp h') with hpos | hneg
    · exact hpos.1
    · exfalso
      linarith only [hρ, hneg.2]
  intro x hx
  exact pressureP8_pointwise_annular_bound_on_ball hρ hC₁ hf
    (fun j y => by
      rw [hηeq]
      exact pressure_cutoff_spatialDeriv_bound x₀ hρ y j)
    (fun j => hI j)
    (fun j {x} hx' => pressure_potential_source_integrable (hI j)
      (fun w hw => hAnn j w hw) hρ hr hhalf hx')
    (fun j w hw => hAnn j w hw) hr hhalf hx

end CKN
