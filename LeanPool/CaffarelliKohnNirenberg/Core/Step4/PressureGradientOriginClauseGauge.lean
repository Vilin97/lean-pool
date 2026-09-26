/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginClauseDoubling

/-!
# Pressure gauge covariance on clipped origin cells

A spatial constant is removed from the harmonic remainder on each slice;
its gradient, the divergence source, and the force potentials are unchanged.
The pressure mean is taken on the fixed carrier ball `vec3Ball 0 R₁`, so all
cells use one pressure normalization in the clipped carrier integral.
The argument is slicewise and requires no temporal integrability of the gauge.
-/

public section

open MeasureTheory Set Filter
open scoped BigOperators ENNReal Topology
open CKN.Foundation.Parabolic CKN.Foundation.Euclidean CKN.Foundation.Heat

noncomputable section
namespace CKN.Core.Step4

private theorem gauge_ball_open (x : Vec3) (r : ℝ) : IsOpen (euclideanBall x r) :=
  isOpen_lt (contDiff_euclideanSqDist_left x).continuous continuous_const

private theorem gauge_half_subset_inner {x : Vec3} {ρ : ℝ} (hρ : 0 < ρ) :
    euclideanBall x (ρ / 2) ⊆ euclideanBall x (13 * ρ / 20) := by
  rw [euclideanBall_eq_vec3Ball_of_pos (by positivity : 0 < ρ / 2),
    euclideanBall_eq_vec3Ball_of_pos (by positivity : 0 < 13 * ρ / 20)]
  exact vec3Ball_mono (by linarith only [hρ])

private theorem gauge_weak_const {B : Set Vec3} (hB : IsOpen B)
    (c : ℝ) (k : Fin 3) :
    HasWeakPartialDerivOn B k (fun _ => c) (fun _ => 0) := by
  have h := hasWeakPartialDerivOn_classicalGradient hB k
    (contDiffOn_const (c := c) (s := B) :
      ContDiffOn ℝ (1 : ℕ∞) (fun _ : Vec3 => c) B)
  simpa only [classicalGradient_apply, fderiv_const_apply, zero_apply] using h

private theorem gauge_integrable_mul_test {B : Set Vec3} (hB : IsOpen B)
    {f ψ : Vec3 → ℝ} (hf : LocallyIntegrableOn f B volume)
    (hψ : Continuous ψ) (hc : HasCompactSupport ψ) (hs : tsupport ψ ⊆ B) :
    IntegrableOn (fun x => f x * ψ x) B volume := by
  have hm := hf.mul_continuousOn hψ.continuousOn hB.isLocallyClosed
  have hk := hm.integrableOn_compact_subset hs hc.isCompact
  exact (hk.integrable_of_forall_notMem_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])).integrableOn

/-- Subtracting a spatial constant preserves distributional harmonicity. -/
private theorem gauge_harmonic_sub_const {B : Set Vec3} (hB : IsOpen B)
    {h : Vec3 → ℝ} (hloc : LocallyIntegrableOn h B volume)
    (hh : WeaklyHarmonicOn B h) (c : ℝ) :
    WeaklyHarmonicOn B (fun x => h x - c) := by
  intro ψ hψ hψc hψB
  have hdcont (i : Fin 3) : Continuous (spatialDeriv (spatialDeriv ψ i) i) :=
    (contDiff_spatialDeriv_smooth (contDiff_spatialDeriv_smooth hψ i) i).continuous
  have hdc (i : Fin 3) : HasCompactSupport (spatialDeriv (spatialDeriv ψ i) i) :=
    (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i)).fderiv_apply (𝕜 := ℝ) (basisVec i)
  have hdB (i : Fin 3) : tsupport (spatialDeriv (spatialDeriv ψ i) i) ⊆ B :=
    (tsupport_fderiv_apply_subset ℝ (basisVec i)).trans
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hψB)
  have hcLoc : LocallyIntegrableOn (fun _ : Vec3 => c) B volume :=
    continuousOn_const.locallyIntegrableOn hB.measurableSet
  have hzero (i : Fin 3) :
      (∫ x in B, c * spatialDeriv (spatialDeriv ψ i) i x) = 0 := by
    have hi := gauge_weak_const hB c i (spatialDeriv ψ i)
      (contDiff_spatialDeriv_smooth hψ i) (hψc.fderiv_apply (𝕜 := ℝ) (basisVec i))
      ((tsupport_fderiv_apply_subset ℝ (basisVec i)).trans hψB)
    simpa only [spatialDeriv, zero_mul, integral_zero, neg_zero] using hi
  have hint : IntegrableOn (fun x => h x * spatialLaplacian ψ x) B volume := by
    simp only [spatialLaplacian, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => gauge_integrable_mul_test hB hloc
      (hdcont i) (hdc i) (hdB i)
  have hcint : IntegrableOn (fun x => c * spatialLaplacian ψ x) B volume := by
    simp only [spatialLaplacian, Finset.mul_sum]
    exact integrable_finsetSum _ fun i _ => gauge_integrable_mul_test hB hcLoc
      (hdcont i) (hdc i) (hdB i)
  have hczero : (∫ x in B, c * spatialLaplacian ψ x) = 0 := by
    simp only [spatialLaplacian, Finset.mul_sum]
    rw [integral_finsetSum _ (fun i _ => gauge_integrable_mul_test hB hcLoc
      (hdcont i) (hdc i) (hdB i))]
    simp only [hzero, Finset.sum_const_zero]
  simp_rw [sub_mul]
  rw [integral_sub hint hcint, hh ψ hψ hψc hψB, hczero, sub_zero]

private theorem gauge_harmonic_display
    (C : ℝ) (hC : 1000 * harmonicInteriorDisplayConstant ≤ C)
    {h p p₁ p₇₈ : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hp₁ : MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hp₇₈ : MemLp p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20))))
    (hdecomp : h =ᵐ[volume.restrict (euclideanBall x₀ (13 * ρ / 20))]
      ((fun x => p x) - p₁ - p₇₈))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ (13 * ρ / 20)) h)
    (hsmooth : ContDiffOn ℝ (1 : ℕ∞) h (euclideanBall x₀ (ρ / 2))) :
    ∀ x ∈ euclideanBall x₀ (ρ / 2),
      vec3EuclideanNorm (classicalGradient h x) ≤ C * (ρ ^ 3)⁻¹ *
        (lpNorm (fun y => p y - c) (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ ρ)) +
          lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume +
          lpNorm p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ (13 * ρ / 20)))) := by
  have houter : euclideanBall x₀ ρ = vec3Ball x₀ ρ :=
    euclideanBall_eq_vec3Ball_of_pos hρ
  have hfinite : IsFiniteMeasure (volume.restrict (euclideanBall x₀ ρ)) := by
    apply isFiniteMeasure_restrict.mpr
    rw [houter]
    exact Integration.volume_vec3Ball_lt_top.ne
  have hpcenter : MemLp (fun y => p y - c) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)) := hp.sub (memLp_const c)
  have hdec : (fun y => h y - c) =ᵐ[volume.restrict
      (euclideanBall x₀ (13 * ρ / 20))] ((fun y => p y - c) - p₁ - p₇₈) := by
    filter_upwards [hdecomp] with y hy
    simp only [Pi.sub_apply] at hy ⊢
    rw [hy]
    ring
  have hm := harmonic_remainder_memLp_of_inner_decomposition hρ hp hp₁ hp₇₈ hdecomp
  have hmc := harmonic_remainder_memLp_of_inner_decomposition hρ hpcenter hp₁ hp₇₈ hdec
  have hopen : IsOpen (euclideanBall x₀ (13 * ρ / 20)) := by
    rw [euclideanBall_eq_vec3Ball_of_pos (by positivity : 0 < 13 * ρ / 20)]
    exact isOpen_vec3Ball _ _
  have hloc := locallyIntegrableOn_of_memLp_three_halves
    (by positivity : 0 < 13 * ρ / 20) hm
  have hwc := gauge_harmonic_sub_const hopen hloc hweak c
  have hsc : ContDiffOn ℝ (1 : ℕ∞) (fun y => h y - c)
      (euclideanBall x₀ (ρ / 2)) := hsmooth.sub contDiffOn_const
  have hgrad := harmonic_remainder_gradient_display C hC hρ hmc hwc hsc
  have hnorm := harmonic_remainder_inner_lpNorm_le hρ hpcenter hp₁ hp₇₈ hdec
  have hCnonneg : 0 ≤ C :=
    (mul_nonneg (by norm_num) harmonicInteriorDisplayConstant_nonneg).trans hC
  intro x hx
  have heq : classicalGradient (fun y => h y - c) x = classicalGradient h x := by
    ext k
    simp only [classicalGradient_apply, fderiv_sub_const]
  have hb := hgrad x hx
  rw [heq] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left hnorm
    (mul_nonneg hCnonneg (by positivity)))

private theorem gauge_harmonic_component_bound
    (C : ℝ) (hC : 1000 * harmonicInteriorDisplayConstant ≤ C)
    {h p p₁ p₇₈ : Vec3 → ℝ} {x₀ : Vec3} {ρ : ℝ} (hρ : 0 < ρ) (c : ℝ) (i : Fin 3)
    (hp : MemLp p (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)))
    (hp₁ : MemLp p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume)
    (hp₇₈ : MemLp p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20))))
    (hdecomp : h =ᵐ[volume.restrict (euclideanBall x₀ (13 * ρ / 20))]
      ((fun x => p x) - p₁ - p₇₈))
    (hweak : WeaklyHarmonicOn (euclideanBall x₀ (13 * ρ / 20)) h)
    (hsmooth : ContDiffOn ℝ (1 : ℕ∞) h (euclideanBall x₀ (ρ / 2))) :
    eLpNorm (fun x => classicalGradient h x i) (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (euclideanBall x₀ (ρ / 2))) ≤
      ENNReal.ofReal (C *
        (lpNorm (fun y => p y - c)
            (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall x₀ ρ)) +
          lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume +
          lpNorm p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
            (volume.restrict (euclideanBall x₀ (13 * ρ / 20)))) * ρ ^ (-1 / 2 : ℝ)) := by
  let L := lpNorm (fun y => p y - c) (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ ρ)) +
    lpNorm p₁ (ENNReal.ofReal (3 / 2 : ℝ)) volume +
    lpNorm p₇₈ (ENNReal.ofReal (3 / 2 : ℝ))
      (volume.restrict (euclideanBall x₀ (13 * ρ / 20)))
  have hL : 0 ≤ L := add_nonneg (add_nonneg lpNorm_nonneg lpNorm_nonneg) lpNorm_nonneg
  have hCnonneg : 0 ≤ C :=
    (mul_nonneg (by norm_num) harmonicInteriorDisplayConstant_nonneg).trans hC
  have hopen : IsOpen (euclideanBall x₀ (ρ / 2)) := by
    rw [euclideanBall_eq_vec3Ball_of_pos (by positivity : 0 < ρ / 2)]
    exact isOpen_vec3Ball _ _
  have hmeas := (locallyIntegrableOn_classicalGradient hopen i hsmooth).aestronglyMeasurable
  have hsup := gauge_harmonic_display C hC hρ c
    hp hp₁ hp₇₈ hdecomp hweak hsmooth
  have hb := eLpNorm_classicalGradient_component_le_of_sup hρ
    (mul_nonneg (mul_nonneg hCnonneg (by positivity : 0 ≤ (ρ ^ 3)⁻¹)) hL) i hmeas hsup
  have heq : C * (ρ ^ 3)⁻¹ * L = (C * L) * (ρ ^ 3)⁻¹ := by ring
  change eLpNorm (fun x => classicalGradient h x i) (ENNReal.ofReal (6 / 5 : ℝ))
    (volume.restrict (euclideanBall x₀ (ρ / 2))) ≤
    ENNReal.ofReal (C * L * ρ ^ (-1 / 2 : ℝ))
  change _ ≤ ENNReal.ofReal (C * (ρ ^ 3)⁻¹ * L) *
    (volume (euclideanBall x₀ (ρ / 2))) ^ (5 / 6 : ℝ) at hb
  rw [heq] at hb
  exact hb.trans (halfBall_volume_rpow_five_sixths_mul_inv_cube_le x₀ hρ
    (mul_nonneg hCnonneg hL))


private theorem gauge_local_slice_bound
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (γ : ℝ → ℝ) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      ∃ D : Vec3 → Vec3,
        (∀ k : Fin 3, LocallyIntegrableOn (fun x => D x k)
          (euclideanBall z.1 (ρ / 2)) volume) ∧
        MemLp D (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ∧
        (∀ k : Fin 3, HasWeakPartialDerivOn (euclideanBall z.1 (ρ / 2)) k
          (fun x => p (x, s)) (fun x => D x k)) ∧
        (∀ k : Fin 3, eLpNorm (fun x => D x k) (ENNReal.ofReal (6 / 5 : ℝ))
          (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
            originSliceGradientMajorant u Du (fun w => p w - γ w.2) f z hρ s) := by
  let c : ℝ → Vec3 := fun s j => average (volume.restrict (vec3Ball z.1 ρ))
    (fun y : Vec3 => u (y, s) j)
  let V : ParabolicPoint → Vec3 := fun w =>
    pressureDivergenceCutoffSourceCentredTensor
      (mollifiedBallCutoff z.1 hρ) (spatialDeriv (mollifiedBallCutoff z.1 hρ))
      (fun y => u (y, w.2)) (fun y => Du (y, w.2)) (c w.2) w.1
  have hsource := origin_tensor_source_data_ae_of_sws hsol hρ hsub c
  have hV : ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2),
      (∀ i : Fin 3, MemLp (fun x => V (x, s) i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ∧
      (∀ i : Fin 3, HasCompactSupport (fun x => V (x, s) i)) := by
    filter_upwards [hsource] with s hs
    exact ⟨hs.1, hs.2.1⟩
  have hpair := hsource.mono (fun _ hs => hs.2.2)
  have hCZ := pressureP1_thetaDecay_hCZ_of_sws (max czP1OperatorConstant 0)
    (le_max_right _ _) (le_max_left _ _) hsol hρ hsub
    (pressureSecondExtension_residual_growth_ae_of_sws hsol hρ hsub)
  have hP78 := slice_selected_gradient_hP78_input_of_sws hsol hρ hsub
  have hP1 := exists_weak_pressure_gradient_unconditional
  have hC : 0 ≤ czGradientOperatorConstant := by
    simp only [czGradientOperatorConstant, czGradientComponentConstant]
    positivity
  obtain ⟨gw, hforce⟩ := exists_slice_force_weak_gradient_ae_of_sws
    czGradientOperatorConstant sliceForceGradientConstant hC le_rfl hsol hρ hsub hP1
  have hident := slice_selected_gradient_hident_ae_of_sws hsol hρ hsub
    (hCZ.mono (fun _ hs => hs.1)) hV hpair
  have hregular := slice_harmonic_part_contDiffOn_ae_of_sws hsol hρ hsub
  have hrep := pressure_slice_representation_of_sws hsol hρ hsub
  have hp := sws_pressure_memLp_slice_ae hsol hρ hsub
  filter_upwards [hV, hCZ, hP78, hforce, hident, hregular, hrep, hp] with
    s hVs hcz h78 hfs hid hreg hrepr hps
  rw [← euclideanBall_eq_vec3Ball_of_pos hρ] at hps
  let H := harmonicPressurePart (mollifiedBallCutoff z.1 hρ) u c p s
  let P₁ := pressureP1 (mollifiedBallCutoff z.1 hρ) u c p f s
  let W := pressureP7 (mollifiedBallCutoff z.1 hρ) f s +
    pressureP8 (mollifiedBallCutoff z.1 hρ) f s
  have hdecomp : H =ᵐ[volume.restrict (euclideanBall z.1 (13 * ρ / 20))]
      ((fun x => p (x, s)) - P₁ - W) := by
    filter_upwards [hrepr.1] with x hx
    change p (x, s) = P₁ x + H x + W x at hx
    change H x = p (x, s) - P₁ x - W x
    linarith only [hx]
  let L : ℝ := lpNorm (fun x : Vec3 => p (x, s) - γ s)
      (ENNReal.ofReal (3 / 2 : ℝ)) (volume.restrict (euclideanBall z.1 ρ)) +
    (9 * max czP1OperatorConstant 0) *
      (∫ y in vec3Ball z.1 ρ, (utensorNorm u z.1 ρ s y) ^ (3 / 2 : ℝ)) ^
        (2 / 3 : ℝ) + harmonicRemainderForceBound z hρ f s
  have hbd : ∀ k : Fin 3, eLpNorm (fun x => classicalGradient H x k)
      (ENNReal.ofReal (6 / 5 : ℝ))
      (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
      ENNReal.ofReal ((1000 * harmonicInteriorDisplayConstant) * L *
        ρ ^ (-1 / 2 : ℝ)) := by
    intro k
    have hb := gauge_harmonic_component_bound
      (1000 * harmonicInteriorDisplayConstant) le_rfl hρ (γ s) k
      hps hcz.1 h78.1 hdecomp hrepr.2 hreg
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hρ.le _)
    apply mul_le_mul_of_nonneg_left _
      (mul_nonneg (by norm_num) harmonicInteriorDisplayConstant_nonneg)
    exact add_le_add (add_le_add le_rfl hcz.2) h78.2
  have hrepresentation : (fun x : Vec3 => p (x, s)) =ᵐ[
      volume.restrict (euclideanBall z.1 (ρ / 2))]
      fun x => (∑ i, pressureNewtonianDerivativePotential i
        (fun y => V (y, s) i) x) + (H x + W x) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset
      (gauge_half_subset_inner hρ) hrepr.1, hid] with x hx hxid
    change p (x, s) = P₁ x + H x + W x at hx
    change P₁ x = _ at hxid
    rw [hx, hxid]
    ring
  have hwloc : LocallyIntegrableOn W (euclideanBall z.1 (ρ / 2)) volume :=
    locallyIntegrableOn_of_memLp_three_halves (by positivity)
      (h78.1.mono_measure (Measure.restrict_mono_set volume (gauge_half_subset_inner hρ)))
  have hselected := slice_selected_gradient_of_potential_representation
    czGradientOperatorConstant ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
    (gauge_ball_open z.1 (ρ / 2)) hP1 hVs.1 hVs.2 hrepresentation hreg hbd
    hwloc (fun k => (hfs k).1) (fun k => (hfs k).2.1) (fun k => (hfs k).2.2)
  simpa only [originSliceGradientMajorant, V, c, L] using hselected

/-- The same fixed weak pressure gradient obeys the slice bound with any
spatially constant gauge removed from the pressure in the majorant. No time
regularity of the gauge is needed for this almost-everywhere slice statement. -/
theorem origin_fixed_gradient_slice_bound_gauge_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    {z : ParabolicPoint} {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : closure (parabolicCylinder z.1 z.2 ρ) ⊆ spaceTimeSet Ω I)
    (γ : ℝ → ℝ)
    {B : Set Vec3} {Dp : ParabolicPoint → Vec3}
    (hball : euclideanBall z.1 (ρ / 2) ⊆ B)
    (hfield : ∀ᵐ s ∂volume.restrict I, ∀ k : Fin 3,
      LocallyIntegrableOn (fun x => Dp (x, s) k) B volume ∧
      HasWeakPartialDerivOn B k (fun x => p (x, s)) (fun x => Dp (x, s) k)) :
    ∀ᵐ s ∂volume.restrict (Ioc (z.2 - ρ ^ 2) z.2), ∀ k : Fin 3,
      eLpNorm (fun x => Dp (x, s) k) (ENNReal.ofReal (6 / 5 : ℝ))
        (volume.restrict (euclideanBall z.1 (ρ / 2))) ≤
          originSliceGradientMajorant u Du (fun w => p w - γ w.2) f z hρ s := by
  have htime : Ioc (z.2 - ρ ^ 2) z.2 ⊆ I := by
    intro s hs
    apply (hsub (subset_closure (show (z.1, s) ∈ parabolicCylinder z.1 z.2 ρ from ?_))).2
    exact ⟨by simpa only [vec3Ball, mem_ofPred_eq, sub_self, vec3EuclideanNorm_zero] using hρ, hs⟩
  have hopen : IsOpen (euclideanBall z.1 (ρ / 2)) := by
    rw [euclideanBall_eq_vec3Ball_of_pos (by positivity : 0 < ρ / 2)]
    exact isOpen_vec3Ball _ _
  exact ae_glued_gradient_bound_of_vector_slice_bound hopen hball htime hfield
    (gauge_local_slice_bound hsol hρ hsub γ)


/-- The explicit slice majorant with the pressure mean on the fixed origin
carrier removed. The source and force terms keep their original values. -/
def originClauseGaugeMajorant (R₁ : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3)
    (p : ParabolicPoint → ℝ) (f : ParabolicPoint → Vec3)
    (z : ParabolicPoint) {ρ : ℝ} (hρ : 0 < ρ) (s : ℝ) : ℝ≥0∞ :=
  originSliceGradientMajorant u Du
    (fun w => p w - average (volume.restrict (vec3Ball (0 : Vec3) R₁))
      (fun y => p (y, w.2))) f z hρ s


/-- The clipped carrier-cell integral bound with the pressure mean removed,
obtained by applying the doubled-radius integral consumer to the slice estimate. -/
theorem originClauseGaugeCarrierCellIntegral_le_of_double_radius
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hR₁ : 0 ≤ R₁) (hR₁one : R₁ ≤ 1) (hI : Icc (-1 : ℝ) 0 ⊆ I)
    {x : Vec3} {t r : ℝ} (hr : 0 < r)
    (hsub : closure (parabolicCylinder x t (2 * r)) ⊆ spaceTimeSet Ω I)
    {Dp : ParabolicPoint → Vec3} {i : Fin 3}
    (hDmeas : AEMeasurable (fun z => Dp z i)
      (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I)))
    (hfield : ∀ᵐ s ∂volume.restrict I,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R₁) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i)) :
    (∫⁻ w in parabolicCylinder x t r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
      ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
      ∫⁻ s in Ioc (t - r ^ 2) t ∩ Ioc (-(R₁ ^ 2)) 0,
        originClauseGaugeMajorant R₁ u Du p f (x, t)
          (show 0 < 2 * r by positivity) s ^ (6 / 5 : ℝ) := by
  apply originClauseCarrierCellIntegral_le_of_double_radius
    (N := fun s => originClauseGaugeMajorant R₁ u Du p f (x, t)
      (show 0 < 2 * r by positivity) s) hR₁ hR₁one hI hr hDmeas hfield
  have hs := gauge_local_slice_bound (z := (x, t)) (ρ := 2 * r)
    hsol (show 0 < 2 * r by positivity) hsub
    (fun s => average (volume.restrict (vec3Ball (0 : Vec3) R₁)) (fun y => p (y, s)))
  simpa only [originClauseGaugeMajorant] using
    (exists_scalar_slice_gradient_of_vector_slice i hs)

/-- The doubled source geometry is unchanged by pressure normalization. -/
theorem originClauseGauge_doubleRadius_subset_unit
    {R₁ r : ℝ} {z : ParabolicPoint}
    (hR₁ : 0 < R₁) (hR₁one : R₁ < 1) (hr : 0 < r)
    (hmargin : r ≤ (1 - R₁) / 2)
    (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
    closure (parabolicCylinder z.1 z.2 (2 * r)) ⊆
      closure (parabolicCylinder (0 : Vec3) 0 1) :=
  originClause_doubleRadius_subset_unit hR₁ hR₁one hr hmargin hz

/-- Suitability supplies the doubled-radius slice estimate for a clipped
origin cell with its fixed carrier pressure mean removed, while the fixed derivative is required
  only on the carrier ball. -/
theorem originClauseGaugeCarrierCellIntegral_le_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁one : R₁ < 1)
    {Dp : ParabolicPoint → Vec3} {i : Fin 3}
    (hDmeas : AEMeasurable (fun z => Dp z i)
      (volume.restrict (vec3Ball (0 : Vec3) R₁ ×ˢ I)))
    (hfield : ∀ᵐ s ∂volume.restrict I,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R₁) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i))
    {z : ParabolicPoint} {r : ℝ} (hr : 0 < r)
    (hmargin : r ≤ 2 * ((1 - R₁) / 4))
    (hz : z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁)) :
    (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
      ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
      ∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
        originClauseGaugeMajorant R₁ u Du p f z
          (show 0 < 2 * r by positivity) s ^ (6 / 5 : ℝ) := by
  have hsub := (originClause_doubleRadius_subset_unit hR₁ hR₁one hr
    (by linarith only [hmargin]) hz).trans hdom
  exact originClauseGaugeCarrierCellIntegral_le_of_double_radius hsol hR₁.le hR₁one.le
    (OriginInstance.originUnitBall_subset_of_dom hdom).2 hr hsub hDmeas hfield

/-- One measurable carrier gradient, obtained from suitability, satisfies all
mean-subtracted clipped cell estimates through twice the origin margin scale. -/
theorem originClauseGauge_exists_doubled_cell_bounds_of_sws
    {Ω : Set Vec3} {I : Set ℝ} {q R₁ : ℝ}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hdom : closure (parabolicCylinder (0 : Vec3) 0 1) ⊆ spaceTimeSet Ω I)
    (hR₁ : 0 < R₁) (hR₁one : R₁ < 1) :
    ∃ Dp : ParabolicPoint → Vec3, Measurable Dp ∧
      (∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
        LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
        HasWeakPartialDerivOn (vec3Ball 0 R₁) i
          (fun y => p (y, s)) (fun y => Dp (y, s) i)) ∧
      (∀ z ∈ closure (parabolicCylinder (0 : Vec3) 0 R₁),
        ∀ (r : ℝ) (hr : 0 < r), r ≤ 2 * ((1 - R₁) / 4) → ∀ i : Fin 3,
          (∫⁻ w in parabolicCylinder z.1 z.2 r ∩ parabolicCylinder (0 : Vec3) 0 R₁,
            ENNReal.ofReal |Dp w i| ^ (6 / 5 : ℝ)) ≤
            ∫⁻ s in Ioc (z.2 - r ^ 2) z.2 ∩ Ioc (-(R₁ ^ 2)) 0,
              originClauseGaugeMajorant R₁ u Du p f z
                (show 0 < 2 * r by positivity) s ^ (6 / 5 : ℝ)) := by
  obtain ⟨Dp, hmeas, hweak⟩ :=
    origin_measurable_weak_gradient_of_sws hsol hdom hR₁ hR₁one
  have hfield : ∀ᵐ s ∂volume.restrict I, ∀ i : Fin 3,
      LocallyIntegrableOn (fun y => Dp (y, s) i) (vec3Ball 0 R₁) volume ∧
      HasWeakPartialDerivOn (vec3Ball 0 R₁) i
        (fun y => p (y, s)) (fun y => Dp (y, s) i) :=
    hweak.mono (fun _ hs i => ⟨(hs i).1, (hs i).2.1⟩)
  refine ⟨Dp, hmeas, hfield, ?_⟩
  intro z hz r hr hmargin i
  exact originClauseGaugeCarrierCellIntegral_le_of_sws hsol hdom hR₁ hR₁one
    ((measurable_pi_apply i).comp hmeas).aemeasurable.restrict
    (hfield.mono (fun _ hs => hs i)) hr hmargin hz

end CKN.Core.Step4
