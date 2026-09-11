/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.NavierStokesAndEuler.Euler.Foundations.TransportDerivatives
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Cylinder Graph Trace
-/

section

/-!
# Terminal Energy
-/

@[expose] public section

noncomputable section

open Set MeasureTheory

namespace EulerTerminalEnergy

open InnerProductSpace

theorem integral_sq_le_length_mul (g : ℝ → ℝ) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    (∫ t in a..b, g t) ^ 2 ≤ (b - a) * ∫ t in a..b, (g t) ^ 2 := by
  rcases hab.eq_or_lt with rfl | hab
  · simp
  let c := (∫ t in a..b, g t) / (b - a)
  have hgi := hg.intervalIntegrable_of_Icc (μ := volume) hab.le
  have hgs := (hg.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  change IntervalIntegrable (fun t => (g t) ^ 2) volume a b at hgs
  have hn := intervalIntegral.integral_nonneg (μ := volume) hab.le
    (fun t _ => sq_nonneg (g t - c))
  have hex : (fun t => (g t - c) ^ 2) =
      (fun t => (g t) ^ 2 - 2 * c * g t + c ^ 2) := by
    funext t
    ring
  rw [hex, intervalIntegral.integral_add (hgs.sub (hgi.const_mul (2 * c)))
    intervalIntegrable_const, intervalIntegral.integral_sub hgs (hgi.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hn
  simp only [smul_eq_mul] at hn
  have hlen : 0 < b - a := sub_pos.mpr hab
  have hc : c * (b - a) = ∫ t in a..b, g t := div_mul_cancel₀ _ hlen.ne'
  have := mul_nonneg hlen.le hn
  nlinarith [sq_nonneg ((b - a) * c - ∫ t in a..b, g t)]

theorem norm_integral_sq_le_length_mul {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (g : ℝ → E) {a b : ℝ} (hab : a ≤ b)
    (hg : ContinuousOn g (Icc a b)) :
    ‖∫ t in a..b, g t‖ ^ 2 ≤ (b - a) * ∫ t in a..b, ‖g t‖ ^ 2 := by
  have hn := intervalIntegral.norm_integral_le_integral_norm (μ := volume) (f := g) hab
  have hq := integral_sq_le_length_mul (fun t => ‖g t‖) hab hg.norm
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hq

theorem terminal_trace {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (η v : ℝ → E) {S t : ℝ} (ht : t ≤ S)
    (hv : ContinuousOn v (Icc t S))
    (hη : ∀ s ∈ Icc t S, HasDerivAt η (v s) s) (hS : η S = 0) :
    ‖η t‖ ^ 2 ≤ (S - t) * ∫ s in t..S, ‖v s‖ ^ 2 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun s hs => hη s ((uIcc_of_le ht) ▸ hs))
    (hv.intervalIntegrable_of_Icc ht)
  have hn := norm_integral_sq_le_length_mul v ht hv
  simpa only [he, hS, zero_sub, norm_neg] using hn

theorem terminal_poincare {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (η v : ℝ → E) {S : ℝ} (hS0 : 0 ≤ S)
    (hv : ContinuousOn v (Icc 0 S))
    (hη : ∀ t ∈ Icc 0 S, HasDerivAt η (v t) t) (hS : η S = 0) :
    (∫ t in 0..S, ‖η t‖ ^ 2) ≤ S ^ 2 / 2 * ∫ t in 0..S, ‖v t‖ ^ 2 := by
  let energy := ∫ t in 0..S, ‖v t‖ ^ 2
  have hvi : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 S :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hS0
  have hηc : ContinuousOn η (Icc 0 S) :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  have hp : ∀ t ∈ Icc 0 S, ‖η t‖ ^ 2 ≤ (S - t) * energy := by
    intro t ht
    have hsub : Icc t S ⊆ Icc 0 S := Icc_subset_Icc_left ht.1
    have htrace := terminal_trace η v ht.2 (hv.mono hsub)
      (fun s hs => hη s (hsub hs)) hS
    have hi := intervalIntegral.integral_mono_interval (μ := volume)
      ht.1 ht.2 (le_refl S) (Filter.Eventually.of_forall (fun t => sq_nonneg ‖v t‖)) hvi
    exact htrace.trans (mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr ht.2))
  have hm := intervalIntegral.integral_mono_on (μ := volume) hS0
    ((hηc.norm.pow 2).intervalIntegrable_of_Icc hS0)
    (((continuous_const.sub continuous_id).mul continuous_const).intervalIntegrable
      (a := 0) (b := S)) hp
  have he : (∫ t in 0..S, (S - t) * energy) = S ^ 2 / 2 * energy := by
    have hic : IntervalIntegrable (fun _ : ℝ => S) volume 0 S := intervalIntegrable_const
    have hid : IntervalIntegrable (fun t : ℝ => t) volume 0 S :=
      continuous_id.intervalIntegrable 0 S
    rw [intervalIntegral.integral_mul_const,
      intervalIntegral.integral_sub hic hid,
      intervalIntegral.integral_const, integral_id]
    simp only [sub_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), smul_eq_mul]
    ring
  exact hm.trans_eq he

theorem localized_boundary_lower_bound {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (M A R : E →L[ℝ] E) (Be Bc C₁ C₂ r L : ℝ)
    (hBc : 0 ≤ Bc) (hC : 0 ≤ L - Bc * C₁)
    (hA : ∀ z, 0 ≤ ⟪A z, z⟫_ℝ)
    (hM : ∀ z, -Be * ‖z‖ ^ 2 - Bc * ‖R z‖ ^ 2 ≤ ⟪M z, z⟫_ℝ)
    (hR : ∀ z, ‖R z‖ ^ 2 ≤ C₁ * ⟪A z, z⟫_ℝ + C₂ * r ^ 3 * ‖z‖ ^ 2)
    (z : E) :
    -(Be + C₂ * Bc * r ^ 3) * ‖z‖ ^ 2 ≤
      ⟪M z, z⟫_ℝ + L * ⟪A z, z⟫_ℝ := by
  have h1 := mul_le_mul_of_nonneg_left (hR z) hBc
  have h2 := mul_nonneg hC (hA z)
  linarith [hM z]

theorem mean_form_coercive {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (η v : ℝ → E) (H : ℝ → E →L[ℝ] E) (M A : E →L[ℝ] E)
    (S K B L : ℝ) (hS0 : 0 ≤ S) (hK : 0 ≤ K) (hB : 0 ≤ B)
    (hsmall : K * S ^ 2 / 2 + B * S ≤ 1 / 2)
    (hv : ContinuousOn v (Icc 0 S)) (hH : ContinuousOn H (Icc 0 S))
    (hη : ∀ t ∈ Icc 0 S, HasDerivAt η (v t) t) (hS : η S = 0)
    (hpot : ∀ t ∈ Icc 0 S, ∀ z, ⟪H t z, z⟫_ℝ ≤ K * ‖z‖ ^ 2)
    (hboundary : ∀ z, -B * ‖z‖ ^ 2 ≤ ⟪M z, z⟫_ℝ + L * ⟪A z, z⟫_ℝ) :
    (∫ t in 0..S, ‖v t‖ ^ 2) / 2 ≤
      (∫ t in 0..S, ‖v t‖ ^ 2 - ⟪H t (η t), η t⟫_ℝ) +
        ⟪M (η 0), η 0⟫_ℝ + L * ⟪A (η 0), η 0⟫_ℝ := by
  have hηc : ContinuousOn η (Icc 0 S) :=
    fun t ht => (hη t ht).continuousAt.continuousWithinAt
  have hvi : IntervalIntegrable (fun t => ‖v t‖ ^ 2) volume 0 S :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hS0
  have hηi : IntervalIntegrable (fun t => ‖η t‖ ^ 2) volume 0 S :=
    (hηc.norm.pow 2).intervalIntegrable_of_Icc hS0
  have hHi : IntervalIntegrable (fun t => ⟪H t (η t), η t⟫_ℝ) volume 0 S :=
    ((hH.clm_apply hηc).inner hηc).intervalIntegrable_of_Icc hS0
  have hip := intervalIntegral.integral_mono_on hS0 hHi (hηi.const_mul K)
    (fun t ht => hpot t ht (η t))
  rw [intervalIntegral.integral_const_mul] at hip
  have htrace := terminal_trace η v hS0 hv hη hS
  simp only [sub_zero] at htrace
  have hpoin := terminal_poincare η v hS0 hv hη hS
  have h1 := mul_le_mul_of_nonneg_left hpoin hK
  have h2 := mul_le_mul_of_nonneg_left htrace hB
  have he : 0 ≤ ∫ t in 0..S, ‖v t‖ ^ 2 :=
    intervalIntegral.integral_nonneg hS0 (fun t _ => sq_nonneg ‖v t‖)
  have h3 := mul_le_mul_of_nonneg_right hsmall he
  rw [intervalIntegral.integral_sub hvi hHi]
  linarith [hboundary (η 0)]

end EulerTerminalEnergy

end
end

end

section

/-!
# Interval Trace
-/

@[expose] public section

noncomputable section

namespace EulerIntervalTrace

open Set MeasureTheory EulerTerminalEnergy

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_sub_sq_le_interval_energy (f v : ℝ → E) (a b : ℝ) (hab : a ≤ b)
    (hv : ContinuousOn v (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (v t) t)
    (s t : ℝ) (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) :
    ‖f t - f s‖ ^ 2 ≤ (b - a) * ∫ r in a..b, ‖v r‖ ^ 2 := by
  have hvi : IntervalIntegrable (fun r => ‖v r‖ ^ 2) volume a b :=
    (hv.norm.pow 2).intervalIntegrable_of_Icc hab
  have hpos : 0 ≤ ∫ r in a..b, ‖v r‖ ^ 2 :=
    intervalIntegral.integral_nonneg hab (fun r _ => sq_nonneg _)
  wlog hst : s ≤ t generalizing s t
  · have h := this t s ht hs (le_of_lt (lt_of_not_ge hst))
    simpa only [norm_sub_rev] using h
  have hsub : Icc s t ⊆ Icc a b := Icc_subset_Icc hs.1 ht.2
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r hr => hf r (hsub ((uIcc_of_le hst) ▸ hr)))
    ((hv.mono hsub).intervalIntegrable_of_Icc hst)
  have hq := norm_integral_sq_le_length_mul v hst (hv.mono hsub)
  rw [he] at hq
  have hi := intervalIntegral.integral_mono_interval hs.1 hst ht.2
    (Filter.Eventually.of_forall (fun r => sq_nonneg ‖v r‖)) hvi
  exact hq.trans ((mul_le_mul_of_nonneg_left hi (sub_nonneg.mpr hst)).trans
    (mul_le_mul_of_nonneg_right (by linarith [hs.1, ht.2] : t - s ≤ b - a) hpos))

/-- Point evaluation on an interval is bounded by the actual zeroth and first derivative energies.
-/
theorem pointwise_H1_trace (f v : ℝ → E) (a b : ℝ) (hab : a < b)
    (hv : ContinuousOn v (Icc a b)) (hf : ∀ t ∈ Icc a b, HasDerivAt f (v t) t)
    (t : ℝ) (ht : t ∈ Icc a b) :
    ‖f t‖ ^ 2 ≤ 2 / (b - a) * (∫ s in a..b, ‖f s‖ ^ 2) +
      2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2) := by
  have hc : ContinuousOn f (Icc a b) := fun s hs => (hf s hs).continuousAt.continuousWithinAt
  have hfi := (hc.norm.pow 2).intervalIntegrable_of_Icc (μ := volume) hab.le
  let V := ∫ s in a..b, ‖v s‖ ^ 2
  have hp (s : ℝ) (hs : s ∈ Icc a b) :
      ‖f t‖ ^ 2 ≤ 2 * ‖f s‖ ^ 2 + 2 * (b - a) * V := by
    have hd := norm_sub_sq_le_interval_energy f v a b hab.le hv hf s t hs ht
    have hn : ‖f t‖ ≤ ‖f t - f s‖ + ‖f s‖ := by
      calc
        _ = ‖(f t - f s) + f s‖ := by rw [sub_add_cancel]
        _ ≤ _ := norm_add_le _ _
    dsimp [V]
    nlinarith [norm_nonneg (f t), norm_nonneg (f s), norm_nonneg (f t - f s),
      sq_nonneg (‖f t - f s‖ - ‖f s‖)]
  have hi := intervalIntegral.integral_mono_on (μ := volume) hab.le
    (intervalIntegrable_const (c := ‖f t‖ ^ 2))
    ((hfi.const_mul 2).add intervalIntegrable_const) hp
  rw [intervalIntegral.integral_const, intervalIntegral.integral_add
    (hfi.const_mul 2) intervalIntegrable_const, intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const] at hi
  simp only [smul_eq_mul] at hi
  have hlen : 0 < b - a := sub_pos.mpr hab
  apply (mul_le_mul_iff_right₀ hlen).mp
  dsimp [V] at hi ⊢
  have he : (b - a) * (2 / (b - a) * (∫ s in a..b, ‖f s‖ ^ 2) +
      2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2)) =
      2 * (∫ s in a..b, ‖f s‖ ^ 2) + (b - a) *
        (2 * (b - a) * (∫ s in a..b, ‖v s‖ ^ 2)) := by
    field_simp [hlen.ne']
  rw [he]
  exact hi

end EulerIntervalTrace

end
end

end

@[expose] public section

noncomputable section

namespace EulerCylinderGraphTrace

open MeasureTheory EulerLiftedGradientSpace EulerMetricTransport EulerTransportDerivatives
open Set
open scoped ContDiff

variable (period : ℝ) [Fact (0 < period)]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

omit [Fact (0 < period)] [CompleteSpace F] in
theorem angular_hasDerivAt (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x)) (x : Vector3) (t : ℝ) :
    HasDerivAt (fun s : ℝ => f (x, (s : AddCircle period)))
      (fieldDerivative period (0, 1) f (x, (t : AddCircle period))) t := by
  have hd := ((hf 0).differentiable (by simp) (x, t)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))
  have he := fderiv_localFieldLift_cover period f (x, t)
  change fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0 =
    fderiv ℝ (localFieldLift period f 0) (x, t) at he
  change HasDerivAt _ ((fderiv ℝ (localFieldLift period f (x, (t : AddCircle period))) 0) (0, 1)) t
  rw [he]
  simpa [Function.comp_def, localFieldLift] using hd

/-- Point evaluation in the periodic coordinate costs one angular derivative,
with a bound independent of the chosen phase. -/
theorem cylinder_pointwise_trace (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (x : Vector3) (θ : AddCircle period) :
    ‖f (x, θ)‖ ^ 2 ≤
      (2 / period) * (∫ s : AddCircle period, ‖f (x, s)‖ ^ 2) +
      (2 * period) * (∫ s : AddCircle period,
        ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2) := by
  have hT : 0 < period := Fact.out
  let θ₀ := AddCircle.equivIco period 0 θ
  have hθ : (θ₀ : ℝ) ∈ Icc 0 period := by
    have hh := θ₀.property
    simp only [zero_add] at hh
    exact ⟨hh.1, hh.2.le⟩
  have hcont : Continuous (fun s : ℝ => fieldDerivative period (0, 1) f
      (x, (s : AddCircle period))) := by
    exact (smoothField_continuous period _
      (fieldDerivative_smooth period (0, 1) f hf)).comp
      (continuous_const.prodMk (AddCircle.continuous_mk' period))
  have h := EulerIntervalTrace.pointwise_H1_trace
    (fun s : ℝ => f (x, (s : AddCircle period)))
    (fun s : ℝ => fieldDerivative period (0, 1) f (x, (s : AddCircle period)))
    0 period hT hcont.continuousOn (fun s _ => angular_hasDerivAt period f hf x s)
    θ₀ hθ
  have hcoe : ((θ₀ : ℝ) : AddCircle period) = θ := AddCircle.coe_equivIco
  rw [hcoe] at h
  have hfi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖f (x, s)‖ ^ 2)
  have hdi := AddCircle.intervalIntegral_preimage period 0
    (fun s : AddCircle period => ‖fieldDerivative period (0, 1) f (x, s)‖ ^ 2)
  simp only [zero_add] at hfi hdi
  simpa only [sub_zero, hfi, hdi] using h

/-- Pullback to any continuous phase graph preserves square integrability.
The estimate has no dependence on the phase frequency. -/
theorem graph_memLp_and_energy_bound (f : LiftDomain period → F)
    (hf : ∀ x, ContDiff ℝ ∞ (localFieldLift period f x))
    (hfL2 : MemLp f 2 (liftMeasure period))
    (hdL2 : MemLp (fieldDerivative period (0, 1) f) 2 (liftMeasure period))
    (θ : Vector3 → AddCircle period) (hθ : Continuous θ) :
    MemLp (fun x => f (x, θ x)) 2 volume ∧
      (∫ x : Vector3, ‖f (x, θ x)‖ ^ 2) ≤
        (2 / period) * (∫ z, ‖f z‖ ^ 2 ∂liftMeasure period) +
        (2 * period) * (∫ z, ‖fieldDerivative period (0, 1) f z‖ ^ 2
          ∂liftMeasure period) := by
  have hfc : Continuous (fun x => f (x, θ x)) :=
    (smoothField_continuous period f hf).comp (continuous_id.prodMk hθ)
  have hfint := hfL2.norm.integrable_sq
  have hdint := hdL2.norm.integrable_sq
  have hi := (hfint.integral_prod_left.const_mul (2 / period)).add
    (hdint.integral_prod_left.const_mul (2 * period))
  have hgraph : Integrable (fun x => ‖f (x, θ x)‖ ^ 2) volume := by
    apply hi.mono' (hfc.norm.pow 2).aestronglyMeasurable
    filter_upwards [] with x
    change ‖‖f (x, θ x)‖ ^ 2‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg ‖f (x, θ x)‖)]
    exact cylinder_pointwise_trace period f hf x (θ x)
  refine ⟨(memLp_two_iff_integrable_sq_norm hfc.aestronglyMeasurable).mpr hgraph, ?_⟩
  have hbound := integral_mono hgraph hi (fun x => cylinder_pointwise_trace period f hf x (θ x))
  simp only [Pi.add_apply] at hbound
  rw [integral_add (hfint.integral_prod_left.const_mul (2 / period))
    (hdint.integral_prod_left.const_mul (2 * period)), integral_const_mul, integral_const_mul,
    integral_integral hfint, integral_integral hdint] at hbound
  exact hbound

end EulerCylinderGraphTrace
