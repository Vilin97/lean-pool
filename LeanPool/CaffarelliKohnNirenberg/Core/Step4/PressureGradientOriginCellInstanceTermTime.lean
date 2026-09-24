/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTermMeasurable
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceLocalSource

/-!
# Time integrability of the actual centered slice terms

The sum of source norms and the real tensor energy in
`eq:pressure-gradient-morrey` are integrable on arbitrary interior time boxes.
-/

@[expose] public section

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
    (fun _ => Real.rpow_nonneg (integral_nonneg (fun _ => Real.rpow_nonneg (Real.sqrt_nonneg _) _)) _)
  exact htime.trans_lt (ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by norm_num) (by norm_num))
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hmass.ne))
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) hJ.ne))

end CKN.Core.Step4
