/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceLocalMoments
public import LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeHolder

/-!
# Compact-time integrability of the centered source majorant

The centered tensor-source bound in `eq:pressure-gradient-morrey` is finite
and integrable on compact time windows of any local box. This is the source
contribution to the time obligations in `prop:bootstrap`; the pressure and
force-potential contributions are separate.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section
namespace CKN.Core.Step4

/-- The two-term bound for the sum of the centered tensor-source norms. -/
def originCenteredSourceMajorant (x : Vec3) (ρ : ℝ)
    (u : ParabolicPoint → Vec3) (Du : ParabolicPoint → Fin 3 → Vec3) (s : ℝ) : ℝ≥0∞ :=
  let U := eLpNorm (fun y => vec3EuclideanNorm (u (y, s)))
    (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x ρ))
  let D := eLpNorm (fun y => ‖Du (y, s)‖)
    (ENNReal.ofReal (2 : ℝ)) (volume.restrict (vec3Ball x ρ))
  9 * (8 : ℝ≥0∞) ^ (1 / 3 : ℝ) *
    (D * U + (ENNReal.ofReal (cutoffGradientConstant / ρ) *
      volume (vec3Ball x ρ) ^ (1 / 6 : ℝ)) * (U * U))

private theorem integrable_toReal_of_power
    {μ : Measure ℝ} {K : ℝ → ℝ≥0∞} {P : ℝ}
    (hP : 1 ≤ P) (hμ : μ univ < ⊤) (hm : AEMeasurable K μ)
    (hfin : (∫⁻ s, K s ^ P ∂μ) < ⊤) :
    (∀ᵐ s ∂μ, K s ≠ ⊤) ∧ Integrable (fun s => (K s).toReal) μ := by
  have hle : (∫⁻ s, K s ∂μ) ≤ ∫⁻ s, 1 + K s ^ P ∂μ := by
    apply lintegral_mono
    intro s
    by_cases hs : K s ≤ 1
    · exact hs.trans le_self_add
    · have hh := ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hs) hP
      simpa only [ENNReal.rpow_one] using hh.trans le_add_self
  rw [lintegral_add_left measurable_const, lintegral_const, one_mul] at hle
  have htop := hle.trans_lt (ENNReal.add_lt_top.mpr ⟨hμ, hfin⟩)
  exact ⟨(ae_lt_top' hm htop.ne).mono (fun _ h => h.ne),
    integrable_toReal_of_lintegral_ne_top hm htop.ne⟩

/-- On any local ball-times-window box, suitability gives measurable,
finite and integrable centered-source majorant without a decay hypothesis. -/
theorem origin_centered_source_majorant_obligations_on_local_box
    {Ω : Set Vec3} {I J : Set ℝ} {q ρ : ℝ} {x : Vec3}
    {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
    {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}
    (hsol : IsSuitableWeakSolutionIntegrable Ω I q u Du p f)
    (hbox : localBox Ω I (vec3Ball x ρ) J) :
    AEMeasurable (originCenteredSourceMajorant x ρ u Du) (volume.restrict J) ∧
      (∀ᵐ s ∂volume.restrict J, originCenteredSourceMajorant x ρ u Du s ≠ ⊤) ∧
      Integrable (fun s => (originCenteredSourceMajorant x ρ u Du s).toReal) (volume.restrict J) := by
  let U := fun s => eLpNorm (fun y => vec3EuclideanNorm (u (y, s)))
    (ENNReal.ofReal (3 : ℝ)) (volume.restrict (vec3Ball x ρ))
  let D := fun s => eLpNorm (fun y => ‖Du (y, s)‖)
    (ENNReal.ofReal (2 : ℝ)) (volume.restrict (vec3Ball x ρ))
  have hdata := hsol.2.2.2.2.2.1 (vec3Ball x ρ) J hbox
  have hcont : Continuous (vec3EuclideanNorm : Vec3 → ℝ) := by
    unfold vec3EuclideanNorm
    fun_prop
  have hum : AEMeasurable (fun w : Vec3 × ℝ => vec3EuclideanNorm (u w))
      (volume.restrict (vec3Ball x ρ ×ˢ J)) :=
    (hcont.comp_aestronglyMeasurable hdata.1).aemeasurable
  have hdm : AEMeasurable (fun w : Vec3 × ℝ => ‖Du w‖)
      (volume.restrict (vec3Ball x ρ ×ˢ J)) := hdata.2.1.norm.aemeasurable
  have hUm : AEMeasurable U (volume.restrict J) :=
    origin_time_slice_norm_aemeasurable (g := fun w => vec3EuclideanNorm (u w)) (by norm_num) hum
  have hDm : AEMeasurable D (volume.restrict J) :=
    origin_time_slice_norm_aemeasurable (g := fun w => ‖Du w‖) (by norm_num) hdm
  have hU : (∫⁻ s in J, U s ^ (3 : ℝ)) < ⊤ := by
    rw [origin_time_slice_norm_power_eq (by norm_num) hum]
    have hh := (origin_velocity_cube_integrable_on_local_box hsol hbox).hasFiniteIntegral
    change (∫⁻ w : Vec3 × ℝ in vec3Ball x ρ ×ˢ J,
      ‖vec3EuclideanNorm (u w) ^ (3 : ℕ)‖ₑ) < ⊤ at hh
    simp only [Real.enorm_eq_ofReal_abs, abs_pow,
      abs_of_nonneg (vec3EuclideanNorm_nonneg _),
      ENNReal.ofReal_pow (vec3EuclideanNorm_nonneg _) 3] at hh
    simpa only [abs_of_nonneg (vec3EuclideanNorm_nonneg _), ENNReal.rpow_ofNat] using hh
  have hD : (∫⁻ s in J, D s ^ (2 : ℝ)) < ⊤ := by
    rw [origin_time_slice_norm_power_eq (by norm_num) hdm]
    have hh := (lintegral_mono (fun w : ParabolicPoint =>
      show ‖Du w‖ₑ ^ (2 : ℝ) ≤ ‖u w‖ₑ ^ (2 : ℝ) + ‖Du w‖ₑ ^ (2 : ℝ) from le_add_self)).trans_lt
      hdata.2.2.2.2.2.1
    change (∫⁻ w : Vec3 × ℝ in vec3Ball x ρ ×ˢ J, ‖Du w‖ₑ ^ (2 : ℝ)) < ⊤ at hh
    simpa only [abs_of_nonneg (norm_nonneg _), ofReal_norm] using hh
  have hJ : (volume.restrict J) univ < ⊤ := by
    rw [Measure.restrict_apply_univ]
    exact (measure_mono subset_closure).trans_lt hbox.2.2.2.2.1.measure_lt_top
  have hB : volume (vec3Ball x ρ) < ⊤ :=
    (measure_mono subset_closure).trans_lt hbox.2.1.measure_lt_top
  have hm : AEMeasurable (originCenteredSourceMajorant x ρ u Du) (volume.restrict J) :=
    aemeasurable_const.mul ((hDm.mul hUm).add (aemeasurable_const.mul (hUm.mul hUm)))
  have hbound := origin_time_two_product_majorant_bound
    (9 * (8 : ℝ≥0∞) ^ (1 / 3 : ℝ))
    (ENNReal.ofReal (cutoffGradientConstant / ρ) * volume (vec3Ball x ρ) ^ (1 / 6 : ℝ))
    hUm hDm (Eventually.of_forall (fun s => le_refl (originCenteredSourceMajorant x ρ u Du s)))
  have hfin : (∫⁻ s in J, originCenteredSourceMajorant x ρ u Du s ^ (6 / 5 : ℝ)) < ⊤ := by
    apply hbound.trans_lt
    have hp {a : ℝ≥0∞} {b : ℝ} (ha : a < ⊤) (hb : 0 ≤ b) : a ^ b < ⊤ :=
      ENNReal.rpow_lt_top_of_nonneg hb ha.ne
    apply ENNReal.mul_lt_top
    · exact ENNReal.mul_lt_top
        (hp (ENNReal.mul_lt_top (by norm_num) (hp (by norm_num) (by norm_num))) (by norm_num))
        (hp (by norm_num) (by norm_num))
    · apply ENNReal.add_lt_top.mpr
      constructor
      · exact ENNReal.mul_lt_top (hp hU (by norm_num)) (hp hD (by norm_num))
      · exact ENNReal.mul_lt_top
          (hp (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (hp hB (by norm_num))) (by norm_num))
          (ENNReal.mul_lt_top (hp hU (by norm_num)) (hp hJ (by norm_num)))
  exact ⟨hm, integrable_toReal_of_power (by norm_num) hJ hm hfin⟩

end CKN.Core.Step4
