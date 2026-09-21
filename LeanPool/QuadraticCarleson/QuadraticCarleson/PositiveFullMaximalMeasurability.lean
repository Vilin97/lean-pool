/-
Copyright (c) 2026 Anastasios Fragkos. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anastasios Fragkos
-/

import LeanPool.QuadraticCarleson.QuadraticCarleson.HilbertMaximalWeakResolved
import Mathlib.Topology.Instances.Rat

/-!
# Measurability of the full real-modulation principal-value supremum

Subtracting the ordinary Hilbert principal value removes the singularity.
The remaining integral depends continuously on the real modulation, which
allows the full supremum to be recovered from countably many modulations.
-/

open Filter Function MeasureTheory Set
open scoped ENNReal Topology

namespace QuadraticCarleson.PositiveFullMaximalMeasurability

open PositivePrincipalValueEndpoints HilbertFiniteTruncationWeakOneOne


noncomputable
section

/-- The regular difference between the modulated and ordinary Hilbert
kernels. At zero, field division gives the removable value zero. -/
def quadraticDifferenceKernel (lam t : ℝ) : ℂ :=
  (phase (lam * t ^ 2) - 1) / (t : ℂ)

theorem quadraticDifferenceKernel_norm_le_linear (lam t : ℝ) :
    ‖quadraticDifferenceKernel lam t‖ ≤ 2 * Real.pi * |lam| * |t| := by
  by_cases ht : t = 0
  · simp [quadraticDifferenceKernel, ht]
  · unfold quadraticDifferenceKernel
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    apply (div_le_iff₀ (abs_pos.mpr ht)).mpr
    have hp := norm_phase_sub_one_le (lam * t ^ 2)
    rw [abs_mul, abs_pow] at hp
    simpa only [pow_two, mul_assoc] using hp

theorem measurable_quadraticDifferenceKernel (lam : ℝ) :
    Measurable (quadraticDifferenceKernel lam) := by
  unfold quadraticDifferenceKernel phase
  fun_prop

theorem continuous_quadraticDifferenceKernel_modulation (t : ℝ) :
    Continuous (fun lam ↦ quadraticDifferenceKernel lam t) := by
  unfold quadraticDifferenceKernel phase
  fun_prop

/-- A bound uniform in the spatial variable, suitable for an integrable
input and a bounded neighborhood of any modulation. -/
theorem quadraticDifferenceKernel_norm_le (lam t : ℝ) :
    ‖quadraticDifferenceKernel lam t‖ ≤ 2 * Real.pi * |lam| + 2 := by
  have hC : 0 ≤ 2 * Real.pi * |lam| := by positivity
  by_cases ht : |t| ≤ 1
  · calc
      _ ≤ 2 * Real.pi * |lam| * |t| := quadraticDifferenceKernel_norm_le_linear lam t
      _ ≤ 2 * Real.pi * |lam| * 1 := mul_le_mul_of_nonneg_left ht hC
      _ ≤ 2 * Real.pi * |lam| + 2 := by linarith
  · have ht1 : 1 < |t| := lt_of_not_ge ht
    have hp : ‖phase (lam * t ^ 2) - 1‖ ≤ 2 := by
      simpa only [norm_phase, norm_one, one_add_one_eq_two] using
        norm_sub_le (phase (lam * t ^ 2)) 1
    unfold quadraticDifferenceKernel
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs]
    have hb : ‖phase (lam * t ^ 2) - 1‖ / |t| ≤ 2 :=
      (div_le_iff₀ (lt_trans zero_lt_one ht1)).mpr (by linarith)
    exact hb.trans (le_add_of_nonneg_left hC)

/-- Convolution of a test function with the quadratic difference kernel. -/
def quadraticDifferenceIntegral (lam : ℝ) (f : L0Infinity) (x : ℝ) : ℂ :=
  ∫ t, f (x - t) * quadraticDifferenceKernel lam t

theorem integrable_quadraticDifference_row (lam : ℝ) (f : L0Infinity) (x : ℝ) :
    Integrable (fun t ↦ f (x - t) * quadraticDifferenceKernel lam t) := by
  have hi := (f.integrable.comp_sub_left x).bdd_mul
    (measurable_quadraticDifferenceKernel lam).aestronglyMeasurable
    (ae_of_all _ fun t ↦ quadraticDifferenceKernel_norm_le lam t)
  simpa only [mul_comm] using hi

/-- After removing the singular ordinary Hilbert kernel, the integral is
continuous in every real modulation, including zero. -/
theorem continuous_quadraticDifferenceIntegral_modulation (f : L0Infinity) (x : ℝ) :
    Continuous (fun lam ↦ quadraticDifferenceIntegral lam f x) := by
  apply continuous_iff_continuousAt.mpr
  intro lam₀
  unfold quadraticDifferenceIntegral
  apply continuousAt_of_dominated
    (bound := fun t ↦ (2 * Real.pi * (|lam₀| + 1) + 2) * ‖f (x - t)‖)
  · filter_upwards with lam
    exact ((f.measurable_toFun.comp (measurable_const.sub measurable_id)).mul
      (measurable_quadraticDifferenceKernel lam)).aestronglyMeasurable
  · have hnear : ∀ᶠ lam in 𝓝 lam₀, |lam| < |lam₀| + 1 :=
      (continuous_abs.tendsto lam₀).eventually
        (eventually_lt_nhds (show |lam₀| < |lam₀| + 1 by linarith))
    filter_upwards [hnear] with lam hlam
    filter_upwards with t
    rw [norm_mul, mul_comm ‖f (x - t)‖]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
    exact (quadraticDifferenceKernel_norm_le lam t).trans
      (add_le_add (mul_le_mul_of_nonneg_left hlam.le
        (by positivity : (0 : ℝ) ≤ 2 * Real.pi)) le_rfl)
  · exact (f.integrable.comp_sub_left x).norm.const_mul _
  · filter_upwards with t
    exact (continuous_const.mul (continuous_quadraticDifferenceKernel_modulation t)).continuousAt

/-- Exact subtraction removes the singularity before any principal-value
limit is taken. -/
theorem quadraticHilbertTrunc_eq_zero_add_difference
    (lam : ℝ) {ε : ℝ} (hε : 0 < ε) (f : L0Infinity) (x : ℝ) :
    quadraticHilbertTrunc lam ε f x = quadraticHilbertTrunc 0 ε f x +
      ∫ t in {t : ℝ | ε < |t|}, f (x - t) * quadraticDifferenceKernel lam t := by
  have hzero := integrableOn_zeroHilbertTail hε f.integrable x
  have hdiff := (integrable_quadraticDifference_row lam f x).integrableOn
    (s := {t : ℝ | ε < |t|})
  unfold quadraticHilbertTrunc
  simp only [zero_mul, phase_zero, mul_one]
  rw [← integral_add hzero hdiff]
  apply setIntegral_congr_fun (measurableSet_lt measurable_const measurable_norm)
  intro t ht
  unfold quadraticDifferenceKernel
  ring

/-- Truncating an integrable difference kernel at the origin tends to its
ordinary integral along the complete positive-radius filter. -/
theorem tendsto_quadraticDifference_truncations (lam : ℝ) (f : L0Infinity) (x : ℝ) :
    Tendsto (fun ε : ℝ ↦
      ∫ t in {t : ℝ | ε < |t|}, f (x - t) * quadraticDifferenceKernel lam t)
      (𝓝[>] 0) (𝓝 (quadraticDifferenceIntegral lam f x)) := by
  have hi := integrable_quadraticDifference_row lam f x
  have hc : Continuous (fun ε : ℝ ↦ volume (Icc (-ε) ε)) := by
    simp only [Real.volume_Icc]
    exact ENNReal.continuous_ofReal.comp (continuous_id.sub continuous_id.neg)
  have hmass : Tendsto (fun ε : ℝ ↦ volume (Icc (-ε) ε)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [neg_zero, Icc_self, measure_singleton] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have hsmall := hi.tendsto_setIntegral_nhds_zero
    (s := fun ε : ℝ ↦ Icc (-ε) ε) hmass
  have hsplit (ε : ℝ) :
      (∫ t in {t : ℝ | ε < |t|}, f (x - t) * quadraticDifferenceKernel lam t) =
        quadraticDifferenceIntegral lam f x -
          ∫ t in Icc (-ε) ε, f (x - t) * quadraticDifferenceKernel lam t := by
    have hset : {t : ℝ | ε < |t|} = (Icc (-ε) ε)ᶜ := by
      ext t
      simp only [mem_ofPred_eq, mem_compl_iff, mem_Icc, ← abs_le, not_le]
    rw [hset]
    exact setIntegral_compl measurableSet_Icc hi
  have hlim : Tendsto (fun ε : ℝ ↦ quadraticDifferenceIntegral lam f x -
      ∫ t in Icc (-ε) ε, f (x - t) * quadraticDifferenceKernel lam t)
      (𝓝[>] 0) (𝓝 (quadraticDifferenceIntegral lam f x)) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hsmall
  exact hlim.congr' (Eventually.of_forall fun ε ↦ (hsplit ε).symm)

/-- Every ordinary Hilbert principal value acquires exactly the integrable
regular difference when the real quadratic modulation is inserted. -/
theorem hasQuadraticPrincipalValue_zero_add_difference
    (lam : ℝ) {f : L0Infinity} {x : ℝ} {z : ℂ}
    (hz : HasQuadraticPrincipalValue 0 f x z) :
    HasQuadraticPrincipalValue lam f x (z + quadraticDifferenceIntegral lam f x) := by
  have hlim := hz.add (tendsto_quadraticDifference_truncations lam f x)
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (quadraticHilbertTrunc_eq_zero_add_difference lam hε f x).symm

/-- At a point possessing the ordinary Hilbert PV, the actual quadratic PV
representative depends continuously on all real modulations. -/
theorem continuous_principalValueRepresentative_modulation_of_zeroPV
    {f : L0Infinity} {x : ℝ} {z : ℂ}
    (hz : HasQuadraticPrincipalValue 0 f x z) :
    Continuous (fun lam : ℝ ↦ principalValueRepresentative lam f x) := by
  have heq : (fun lam : ℝ ↦ principalValueRepresentative lam f x) =
      (fun lam : ℝ ↦ z + quadraticDifferenceIntegral lam f x) := by
    funext lam
    exact principalValueRepresentative_eq
      (hasQuadraticPrincipalValue_zero_add_difference lam hz)
  rw [heq]
  exact continuous_const.add (continuous_quadraticDifferenceIntegral_modulation f x)

/-- One common conull set supports continuous dependence on the complete
real modulation parameter, rather than merely separate a.e. assertions. -/
theorem ae_continuous_principalValueRepresentative_modulation (f : L0Infinity) :
    ∀ᵐ x, Continuous (fun lam : ℝ ↦ principalValueRepresentative lam f x) := by
  filter_upwards [HilbertMaximalWeakResolved.ae_forall_real_exists_quadraticPrincipalValue f]
    with x hx
  obtain ⟨z, hz⟩ := hx 0
  exact continuous_principalValueRepresentative_modulation_of_zeroPV hz

/-- The actual full real supremum agrees almost everywhere with its rational
subsupremum. Density is used only after continuity holds on a common set. -/
theorem fullPrincipalValueMaximal_ae_eq_rationalSup (f : L0Infinity) :
    fullPrincipalValueMaximal f =ᵐ[volume]
      (fun x ↦ ⨆ q : ℚ, ENNReal.ofReal ‖principalValueRepresentative (q : ℝ) f x‖) := by
  filter_upwards [ae_continuous_principalValueRepresentative_modulation f] with x hx
  have hcont : Continuous (fun lam : ℝ ↦
      ENNReal.ofReal ‖principalValueRepresentative lam f x‖) :=
    ENNReal.continuous_ofReal.comp hx.norm
  have hsup := (Rat.denseRange_cast : DenseRange ((↑) : ℚ → ℝ)).ciSup' hcont
  simpa only [fullPrincipalValueMaximal, iSup_subtype, iSup_range] using hsup.symm

/-- The genuine PV norm has the measurable fixed-modulation truncation
limsup as an almost-everywhere equal representative. -/
theorem aemeasurable_principalValueRepresentative_norm (lam : ℝ) (f : L0Infinity) :
    AEMeasurable (fun x ↦ ENNReal.ofReal ‖principalValueRepresentative lam f x‖) volume := by
  apply (measurable_quadraticHilbertL0Limsup lam f).aemeasurable.congr
  filter_upwards [ae_forall_hasPrincipalValue_representative
    HilbertMaximalWeakResolved.hasUniformHilbertMaximalWeakBound f] with x hx
  exact quadraticHilbertL0Limsup_eq_of_principalValue lam f x _ (hx lam)

/-- The complete real-modulation PV supremum is measurable modulo a null
set. Its definition and its real modulation set are unchanged. -/
theorem aemeasurable_fullPrincipalValueMaximal (f : L0Infinity) :
    AEMeasurable (fullPrincipalValueMaximal f) volume := by
  have hrat : AEMeasurable
      (fun x ↦ ⨆ q : ℚ, ENNReal.ofReal ‖principalValueRepresentative (q : ℝ) f x‖) volume :=
    AEMeasurable.iSup (fun q : ℚ ↦ aemeasurable_principalValueRepresentative_norm q f)
  exact hrat.congr (fullPrincipalValueMaximal_ae_eq_rationalSup f).symm

/-- The full real supremum of the original truncation limsups has the same
measurability conclusion through its established common-set PV identity. -/
theorem aemeasurable_quadraticCarlesonL0 (f : L0Infinity) :
    AEMeasurable (quadraticCarlesonL0 f) volume :=
  (aemeasurable_fullPrincipalValueMaximal f).congr
    (fullPrincipalValueMaximal_ae_eq
      HilbertMaximalWeakResolved.hasUniformHilbertMaximalWeakBound f)

theorem aemeasurable_lacunaryPrincipalValueMaximal (f : L0Infinity) :
    AEMeasurable (lacunaryPrincipalValueMaximal f) volume :=
  (measurable_lacunaryQuadraticCarlesonL0 f).aemeasurable.congr
    (lacunaryPrincipalValueMaximal_ae_eq
      HilbertMaximalWeakResolved.hasUniformHilbertMaximalWeakBound f).symm


end
end QuadraticCarleson.PositiveFullMaximalMeasurability
