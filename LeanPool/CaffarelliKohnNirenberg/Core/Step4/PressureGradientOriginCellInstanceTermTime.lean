/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceCenteredSource
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceMeanNorm
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.SliceSelectedGradientCentredSWSData
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceSourceObligations
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceHarmonicForceTime

/-!
# Time integrability of the actual centered slice terms

The sum of source norms and the real tensor energy in
`eq:pressure-gradient-morrey` are integrable on arbitrary interior time boxes.
-/

@[expose] public section

section

/-!
# Centered source control on arbitrary interior time boxes

The source estimate in `eq:pressure-gradient-morrey` is valid on any local
box of `def:sws`, not only on a backward cylinder's time window.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The actual centered tensor source is bounded by the integrable source
majorant on every interior ball-times-window box. -/
theorem origin_centered_source_le_majorant_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q ρ : ℝ} {x : Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hρ : 0 < ρ)
    (hbox : localBox Ω I (vec3Ball x ρ) J) :
    ∀ᵐ s ∂volume.restrict J,
      (∑ i : Fin 3, eLpNorm (fun y => pressureDivergenceCutoffSourceCentredTensor
        (mollifiedBallCutoff x hρ) (spatialDeriv (mollifiedBallCutoff x hρ))
        (fun y => u (y, s)) (fun y => Du (y, s))
        (fun j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, s) j)) y i)
        (ENNReal.ofReal (6 / 5 : ℝ)) volume) ≤ originCenteredSourceMajorant x ρ u Du s := by
  have hu3 : Integrable (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact origin_velocity_cube_integrable_on_local_box hsol hbox
  have hglobal := origin_centered_source_memLp_ae_on_local_box hsol hbox hρ (Subset.refl _)
    (fun s j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, s) j))
  let : IsFiniteMeasure (volume.restrict (vec3Ball x ρ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact
      (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top⟩
  filter_upwards [hu3.prod_left_ae, slice_memLp_ae_of_sws hsol hbox, hglobal]
    with s hu3s hs hglob
  have hus := hs.1.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  let U := eLpNorm (fun y => vec3EuclideanNorm (u (y, s)))
    (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x ρ))
  let D := eLpNorm (fun y => ‖Du (y, s)‖)
    (ENNReal.ofReal (2 : ℝ)) (volume.restrict (vec3Ball x ρ))
  let c : Vec3 := fun j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, s) j)
  let V := pressureDivergenceCutoffSourceCentredTensor
    (mollifiedBallCutoff x hρ) (spatialDeriv (mollifiedBallCutoff x hρ))
    (fun y => u (y, s)) (fun y => Du (y, s)) c
  have hUi (i : Fin 3) : eLpNorm (fun y => u (y, s) i)
      (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x ρ)) ≤ U := by
    apply eLpNorm_mono_ae (hs.1.eval i).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, Real.norm_of_nonneg (vec3EuclideanNorm_nonneg _)]
      exact abs_apply_le_vec3EuclideanNorm _ i
  have hDi (i j : Fin 3) : eLpNorm (fun y => Du (y, s) i j)
      (ENNReal.ofReal (2 : ℝ)) (volume.restrict (vec3Ball x ρ)) ≤ D := by
    apply eLpNorm_mono_ae ((hs.2.eval i).eval j).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      rw [norm_norm]
      exact (norm_le_pi_norm (Du (y, s) i) j).trans (norm_le_pi_norm (Du (y, s)) i)
  have hWi (j : Fin 3) : eLpNorm (fun y => u (y, s) j - c j)
      (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x ρ)) ≤
      (8 : ℝ≥0∞) ^ (1 / 3 : ℝ) * U :=
    origin_slice_mean_free_component_norm_bound hρ hus hu3s j
  have hCd : 0 ≤ cutoffGradientConstant / ρ :=
    (vecEuclideanNorm_nonneg _).trans (mollifiedBallCutoff_gradient_bound x hρ x)
  have hlocal (i : Fin 3) := origin_centered_tensor_source_slice_bound
    (c := c) (i := i) (by
      rw [Measure.restrict_apply_univ]
      exact (measure_mono (μ := volume) subset_closure).trans_lt (measure_closure_vec3Ball_lt_top
        hρ))
    (by norm_num : (0 : ℝ) ≤ 1) hCd
    (mollifiedBallCutoff_smooth x hρ).continuous.aestronglyMeasurable
    (Eventually.of_forall fun y => by
      rw [abs_of_nonneg (mollifiedBallCutoff_nonneg x hρ y)]
      exact mollifiedBallCutoff_le_one x hρ y)
    (fun j => (contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth x hρ)
      j).continuous.aestronglyMeasurable)
    (fun j => Eventually.of_forall fun y =>
      (abs_apply_le_vecEuclideanNorm (classicalGradient (mollifiedBallCutoff x hρ) y) j).trans
        (mollifiedBallCutoff_gradient_bound x hρ y))
    (hUi i) (hDi i) hWi (fun j => (hs.1.eval j).aestronglyMeasurable)
    (fun j => ((hs.2.eval i).eval j).aestronglyMeasurable)
  have hbound (i : Fin 3) : eLpNorm (fun y => V y i) (ENNReal.ofReal (6 / 5 : ℝ)) volume ≤
      3 * (8 : ℝ≥0∞) ^ (1 / 3 : ℝ) *
        (D * U + ENNReal.ofReal (cutoffGradientConstant / ρ) *
          (U * U * volume (vec3Ball x ρ) ^ (1 / 6 : ℝ))) := by
    have hsupp : Function.support (fun y => V y i) ⊆ vec3Ball x ρ := by
      intro y hy
      by_contra hn
      have he : mollifiedBallCutoff x hρ y = 0 := image_eq_zero_of_notMem_tsupport
        (fun h => hn (pressure_cutoff_support_subset_ball x hρ h))
      have hd (j : Fin 3) : spatialDeriv (mollifiedBallCutoff x hρ) j y = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hn
          (pressure_cutoff_support_subset_ball x hρ ((tsupport_fderiv_apply_subset ℝ (basisVec j))
            h)))
      apply hy
      simp only [V, pressureDivergenceCutoffSourceCentredTensor, he, hd, zero_mul,
        add_zero, Finset.sum_const_zero]
    rw [← eLpNorm_restrict_eq_of_support_subset (hglob i).aestronglyMeasurable hsupp]
    refine (hlocal i).trans_eq ?_
    simp only [ENNReal.ofReal_one, one_mul]
    ring
  have hh := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hbound i)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, show (3 : ℝ≥0∞) * 3 = 9 by norm_num] at hh
  refine hh.trans_eq ?_
  unfold originCenteredSourceMajorant
  dsimp only [U, D]
  ring


end CKN.Core.Step4
end

end

section

/-!
# Measurability of the centered slice terms

Spatial averaging and cutoff multiplication preserve product measurability
of the tensor and divergence source in `eq:pressure-gradient-morrey`.
-/

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- Spatial component averages are measurable in time. -/
theorem origin_velocity_average_aestronglyMeasurable
    {u : ParabolicPoint → Vec3} {B : Set Vec3} {J : Set ℝ}
    (hu : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict B).prod (volume.restrict J))) (j : Fin 3) :
    AEStronglyMeasurable (fun s => average (volume.restrict B) (fun y => u (y, s) j))
      (volume.restrict J) := by
  have hc := (ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable hu
  simp_rw [average_eq]
  exact hc.prod_swap.integral_prod_right'.const_smul
    (((volume : Measure Vec3).restrict B).real Set.univ)⁻¹

/-- The centered cutoff divergence source is jointly measurable on the full
spatial space and the chosen time window. -/
theorem origin_centered_source_product_aestronglyMeasurable
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {x : Vec3} {ρ : ℝ} {J : Set ℝ} (hρ : 0 < ρ)
    (hu : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)))
    (hDu : AEStronglyMeasurable (fun w : Vec3 × ℝ => Du w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J))) (i : Fin 3) :
    AEStronglyMeasurable (fun w : Vec3 × ℝ => pressureDivergenceCutoffSourceCentredTensor
      (mollifiedBallCutoff x hρ) (spatialDeriv (mollifiedBallCutoff x hρ))
      (fun y => u (y, w.2)) (fun y => Du (y, w.2))
      (fun j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, w.2) j)) w.1 i)
      ((volume : Measure Vec3).prod (volume.restrict J)) := by
  have hum (j : Fin 3) := (ContinuousLinearMap.proj (R := ℝ)
    j).continuous.comp_aestronglyMeasurable hu
  have hdm (j : Fin 3) := (ContinuousLinearMap.proj (R := ℝ) j).continuous.comp_aestronglyMeasurable
    ((ContinuousLinearMap.proj (R := ℝ) i).continuous.comp_aestronglyMeasurable hDu)
  have hmean (j : Fin 3) := origin_velocity_average_aestronglyMeasurable hu j
  have hw (j : Fin 3) := (hum j).sub (hmean j).comp_snd
  have hs := pressure_cutoff_support_subset_ball x hρ
  have hfirst (j : Fin 3) := origin_cutoff_product_aestronglyMeasurable
    (vec3Ball_measurable x ρ) ((hdm j).mul (hw j))
    (mollifiedBallCutoff_smooth x hρ).continuous.aestronglyMeasurable ((subset_tsupport _).trans hs)
  have hsecond (j : Fin 3) := origin_cutoff_product_aestronglyMeasurable
    (vec3Ball_measurable x ρ) ((hum i).mul (hw j))
    (contDiff_spatialDeriv_smooth (mollifiedBallCutoff_smooth x hρ)
      j).continuous.aestronglyMeasurable
    ((subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (basisVec j)).trans hs))
  simpa only [pressureDivergenceCutoffSourceCentredTensor, Finset.sum_fn, Pi.add_apply,
    Pi.mul_apply, Pi.sub_apply, ContinuousLinearMap.proj_apply, Prod.mk.eta, mul_assoc] using
    Finset.aestronglyMeasurable_sum Finset.univ (fun j _ => (hfirst j).add (hsecond j))

/-- The real tensor energy appearing in the harmonic bound is measurable in time. -/
theorem origin_tensor_energy_time_aemeasurable
    {u : ParabolicPoint → Vec3} {x : Vec3} {ρ : ℝ} {J : Set ℝ}
    (hu : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J))) :
    AEMeasurable (fun s => (∫ y in vec3Ball x ρ,
      utensorNorm u x ρ s y ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) (volume.restrict J) := by
  have hum (j : Fin 3) := (ContinuousLinearMap.proj (R := ℝ)
    j).continuous.comp_aestronglyMeasurable hu
  have hmean (j : Fin 3) := origin_velocity_average_aestronglyMeasurable hu j
  have ht (i j : Fin 3) : AEMeasurable (fun w : Vec3 × ℝ => utensor u x ρ w.2 i j w.1)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) :=
    (hum i).neg.aemeasurable.mul ((hum j).sub (hmean j).comp_snd).aemeasurable
  have hnorm : AEMeasurable (fun w : Vec3 × ℝ => utensorNorm u x ρ w.2 w.1)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    unfold utensorNorm
    apply Real.continuous_sqrt.measurable.comp_aemeasurable
    simp only [Fin.sum_univ_succ]
    fun_prop
  have hpow := hnorm.pow_const (3 / 2 : ℝ)
  exact hpow.aestronglyMeasurable.prod_swap.integral_prod_right'.aemeasurable.pow_const (2 / 3 : ℝ)

end CKN.Core.Step4
end

end

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology BigOperators
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The sum of the three actual global centered-source norms. -/
def originCenteredSourceNorm (x : Vec3) {ρ : ℝ} (hρ : 0 < ρ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) (s : ℝ) : ℝ≥0∞ :=
  ∑ i : Fin 3, eLpNorm (fun y => pressureDivergenceCutoffSourceCentredTensor
    (mollifiedBallCutoff x hρ) (spatialDeriv (mollifiedBallCutoff x hρ))
    (fun y => u (y, s)) (fun y => Du (y, s))
    (fun j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, s) j)) y i)
    (ENNReal.ofReal (6 / 5 : ℝ)) volume

/-- Product measurability of velocity and gradient implies time measurability
of the sum of the actual centered-source norms. -/
theorem origin_centered_source_norm_aemeasurable
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {x : Vec3} {ρ : ℝ} {J : Set ℝ} (hρ : 0 < ρ)
    (hum : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)))
    (hdm : AEStronglyMeasurable (fun w : Vec3 × ℝ => Du w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J))) :
    AEMeasurable (originCenteredSourceNorm x hρ u Du) (volume.restrict J) := by
  have hn (i : Fin 3) := origin_centered_source_product_aestronglyMeasurable hρ hum hdm i
  have hnm (i : Fin 3) : AEMeasurable (fun s => eLpNorm (fun y =>
      pressureDivergenceCutoffSourceCentredTensor
        (mollifiedBallCutoff x hρ) (spatialDeriv (mollifiedBallCutoff x hρ))
        (fun y => u (y, s)) (fun y => Du (y, s))
        (fun j => average (volume.restrict (vec3Ball x ρ)) (fun y => u (y, s) j)) y i)
      (ENNReal.ofReal (6 / 5 : ℝ)) volume) (volume.restrict J) := by
    have hg := (hn i).aemeasurable
    have hprod : (volume : Measure (Vec3 × ℝ)).restrict (univ ×ˢ J) =
        (volume : Measure Vec3).prod (volume.restrict J) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]
    rw [← hprod] at hg
    simpa only [Measure.restrict_univ] using
      origin_time_slice_norm_aemeasurable (by norm_num : (0 : ℝ) < 6 / 5) hg
  unfold originCenteredSourceNorm
  simpa only [Finset.sum_fn] using
    Finset.aemeasurable_sum Finset.univ (fun i _ => hnm i)

/-- The actual centered-source norm sum is measurable, finite a.e., and
integrable in real value on every local ball-times-window box. -/
theorem origin_centered_source_norm_time_obligations
    {Ω : Set Vec3} {I J : Set ℝ} {q ρ : ℝ} {x : Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hρ : 0 < ρ)
    (hbox : localBox Ω I (vec3Ball x ρ) J) :
    AEMeasurable (originCenteredSourceNorm x hρ u Du) (volume.restrict J) ∧
      (∀ᵐ s ∂volume.restrict J, originCenteredSourceNorm x hρ u Du s ≠ ⊤) ∧
      Integrable (fun s => (originCenteredSourceNorm x hρ u Du s).toReal) (volume.restrict J) := by
  have hd := hsol.2.2.2.2.2.1 (vec3Ball x ρ) J hbox
  have hum : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]; exact hd.1
  have hdm : AEStronglyMeasurable (fun w : Vec3 × ℝ => Du w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]; exact hd.2.1
  have hm := origin_centered_source_norm_aemeasurable hρ hum hdm
  have he := origin_centered_source_majorant_obligations_on_local_box hsol hbox
  have hb := origin_centered_source_le_majorant_on_local_box hsol hρ hbox
  have ht : ∀ᵐ s ∂volume.restrict J, originCenteredSourceNorm x hρ u Du s ≠ ⊤ := by
    filter_upwards [he.2.1, hb] with s hs hbound
    exact ne_of_lt (hbound.trans_lt (lt_top_iff_ne_top.mpr hs))
  refine ⟨hm, ht, he.2.2.mono' hm.ennreal_toReal.aestronglyMeasurable ?_⟩
  filter_upwards [he.2.1, hb, ht] with s hs hbound hfinite
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  exact (ENNReal.toReal_le_toReal hfinite hs).mpr hbound

private theorem integrable_real_of_power
    {J : Set ℝ} {F : ℝ → ℝ} (hJ : volume J < ⊤)
    (hF : AEMeasurable F (volume.restrict J)) (hFpos : ∀ s, 0 ≤ F s)
    (hpower : (∫⁻ s in J, ENNReal.ofReal (F s) ^ (6 / 5 : ℝ)) < ⊤) :
    Integrable F (volume.restrict J) := by
  have hb : (∫⁻ s in J, ENNReal.ofReal (F s)) ≤
      ∫⁻ s in J, 1 + ENNReal.ofReal (F s) ^ (6 / 5 : ℝ) := by
    apply lintegral_mono
    intro s
    by_cases hs : ENNReal.ofReal (F s) ≤ 1
    · exact hs.trans le_self_add
    · have hh := ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hs)
        (by norm_num : (1 : ℝ) ≤ 6 / 5)
      simpa only [ENNReal.rpow_one] using hh.trans le_add_self
  rw [lintegral_add_left measurable_const, lintegral_const, one_mul,
    Measure.restrict_apply_univ] at hb
  have hh := integrable_toReal_of_lintegral_ne_top hF.ennreal_ofReal
    (hb.trans_lt (ENNReal.add_lt_top.mpr ⟨hJ, hpower⟩)).ne
  simpa only [ENNReal.toReal_ofReal (hFpos _)] using hh

/-- The real two-thirds power of the tensor energy is integrable on every
interior ball-times-window box from suitability alone. -/
theorem origin_tensor_energy_integrable_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q ρ : ℝ} {x : Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f) (hρ : 0 < ρ)
    (hbox : localBox Ω I (vec3Ball x ρ) J) :
    Integrable (fun s => (∫ y in vec3Ball x ρ,
      utensorNorm u x ρ s y ^ (3 / 2 : ℝ)) ^ (2 / 3 : ℝ)) (volume.restrict J) := by
  have hd := hsol.2.2.2.2.2.1 (vec3Ball x ρ) J hbox
  have hum : AEStronglyMeasurable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]; exact hd.1
  have hu3 : Integrable (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w) ^ (3 : ℕ))
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact origin_velocity_cube_integrable_on_local_box hsol hbox
  let : IsFiniteMeasure ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    rw [Measure.prod_restrict]
    exact CKN.Core.Step3.local_box_isFiniteMeasure hbox.2.1 hbox.2.2.2.2.1
  have hu : Integrable (fun w : Vec3 × ℝ => u w)
      ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
    have hLp : MemLp (fun w : Vec3 × ℝ => u w) (2 : ℝ≥0∞)
        ((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J)) := by
      have henergy := hd.2.2.2.2.2.1
      have hfin : (∫⁻ w : Vec3 × ℝ, ‖u w‖ₑ ^ (2 : ℝ)
          ∂((volume.restrict (vec3Ball x ρ)).prod (volume.restrict J))) < ⊤ := by
        rw [Measure.prod_restrict]
        exact (lintegral_mono (fun _ => le_self_add)).trans_lt henergy
      apply memLp_iff.mpr
      rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num) hum]
      norm_num only [ENNReal.toReal_ofNat]
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hfin.ne
    exact hLp.integrable (by norm_num)
  have htime := origin_real_tensor_energy_time_bound hρ hu hu3
  have hmass : (∫⁻ w in vec3Ball x ρ ×ˢ J,
      ENNReal.ofReal (vec3EuclideanNorm (u w)) ^ (3 : ℝ)) < ⊤ := by
    have hh := hu3.hasFiniteIntegral
    rw [Measure.prod_restrict] at hh
    change (∫⁻ w : Vec3 × ℝ in vec3Ball x ρ ×ˢ J, ‖vec3EuclideanNorm (u w) ^ (3 : ℕ)‖ₑ) < ⊤ at hh
    simpa only [Real.enorm_eq_ofReal_abs, abs_pow, abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3, ENNReal.rpow_ofNat] using hh
  have hJ : volume J < ⊤ := (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  apply integrable_real_of_power hJ (origin_tensor_energy_time_aemeasurable hum)
    (fun _ => Real.rpow_nonneg (integral_nonneg (fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _)
      _)) _)
  exact htime.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hmass.ne))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJ.ne))

end CKN.Core.Step4
