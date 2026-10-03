/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Energy.ZeroMass
public import LeanPool.Zeta32.Analytic.Energy.CircleTools
public import LeanPool.Zeta32.Analytic.Energy.Regularity

/-! The configuration inequality (13′) of the proof notes, §5.3 for a density on `[-a, a]`.

Replace each point `x_i` by the circle of radius `ε` about it (angular measure, mass `2π`) and
the comparison
density by the measure `ν = ρ(t)dt` on `[-a, a] ⊂ ℂ`; apply the zero-mass energy inequality
(ZeroMass) to
`ν − (1/(2πh)) Σ circles`. Circle self energy `(2π)² log ε`, circle–circle `≥ (2π)² log|x_i − x_j|`
(CircleTools, from Li₂), circle–`ν`: `2π ∫ ρ(t) log max(ε, |x_i − t|) dt = 2π(L(x_i) + ∫ ρ K)`
with the truncation
error `K ≥ 0`, `K = 0` for `|x_i − t| ≥ ε`, and `∫ ρK ≤ √ε(N²/2 + 2)` by AM–GM and `∫ K² ≤ 4ε`
(this replaces the rearrangement step of the proof notes (13′); only `ρ ∈ L²` is used). -/

public section

open Real MeasureTheory Set Filter
open scoped Interval

namespace Zeta32.Analytic.EnergyI
noncomputable section

/-- A probability density on `[-a, a]` with square-integrable density. -/
structure GoodDensity (ρ : ℝ → ℝ) (a : ℝ) : Prop where
  pos : 0 < a
  meas : Measurable ρ
  nonneg : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ Set.Icc (-a) a → 0 ≤ ρ t
  int : IntervalIntegrable ρ volume (-a) a
  int2 : IntervalIntegrable (fun t => ρ t ^ 2) volume (-a) a
  mass : ∫ t in (-a)..a, ρ t = 1

/-! ### `∫ log²` -/

section logsq

/-- `t log²t − 2t log t + 2t`, written so that it is visibly continuous at `0`. -/
def gLog2 (t : ℝ) : ℝ := 4 * (√t * Real.log √t) ^ 2 - 2 * (t * Real.log t) + 2 * t

theorem continuous_gLog2 : Continuous gLog2 := by
  have h1 : Continuous fun t : ℝ => √t * Real.log √t :=
    Real.continuous_mul_log.comp Real.continuous_sqrt
  exact ((continuous_const.mul (h1.pow 2)).sub (continuous_const.mul Real.continuous_mul_log)).add
    (continuous_const.mul continuous_id)

theorem hasDerivAt_gLog2 {t : ℝ} (ht0 : 0 < t) : HasDerivAt gLog2 (Real.log t ^ 2) t := by
  have hloc : gLog2 =ᶠ[nhds t] fun s => s * Real.log s ^ 2 - 2 * (s * Real.log s) + 2 * s := by
    filter_upwards [lt_mem_nhds ht0] with s hs
    simp only [gLog2]
    rw [Real.log_sqrt hs.le, mul_pow, Real.sq_sqrt hs.le]
    ring
  have h := (((hasDerivAt_id t).mul ((Real.hasDerivAt_log ht0.ne').pow 2)).sub
    (((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0.ne')).const_mul 2)).add
    ((hasDerivAt_id t).const_mul 2)
  refine (h.congr_of_eventuallyEq hloc).congr_deriv ?_
  simp only [id, Pi.pow_apply]
  field_simp
  ring

theorem integral_log_sq_zero_one : ∫ v in (0:ℝ)..1, Real.log v ^ 2 = 2 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one continuous_gLog2.continuousOn
    (fun t ht => hasDerivAt_gLog2 ht.1) (intervalIntegrable_log_sq 0 1)]
  simp [gLog2]

theorem integral_log_abs_sq_neg_one_one : ∫ v in (-1:ℝ)..1, Real.log |v| ^ 2 = 4 := by
  have h0 : ∫ v in (0:ℝ)..1, Real.log |v| ^ 2 = 2 := by
    simpa only [Real.log_abs] using integral_log_sq_zero_one
  have hneg : ∫ v in (-1:ℝ)..0, Real.log |v| ^ 2 = 2 := by
    have := intervalIntegral.integral_comp_neg (a := 0) (b := 1) (fun v => Real.log |v| ^ 2)
    simp only [abs_neg, neg_zero] at this
    rw [← this, h0]
  have hi : IntervalIntegrable (fun v => Real.log |v| ^ 2) volume (-1) 0 := by
    simpa only [Real.log_abs] using intervalIntegrable_log_sq (-1) 0
  have hi' : IntervalIntegrable (fun v => Real.log |v| ^ 2) volume 0 1 := by
    simpa only [Real.log_abs] using intervalIntegrable_log_sq 0 1
  rw [← intervalIntegral.integral_add_adjacent_intervals hi hi', hneg, h0]
  norm_num

theorem integral_log_div_sq {ε : ℝ} (hε : 0 < ε) (c : ℝ) :
    ∫ t in (c - ε)..(c + ε), Real.log (|c - t| / ε) ^ 2 = 4 * ε := by
  have h := intervalIntegral.integral_comp_div_sub (f := fun v => Real.log |v| ^ 2)
    (a := c - ε) (b := c + ε) hε.ne' (c / ε)
  have e1 : (c - ε) / ε - c / ε = -1 := by field_simp; ring
  have e2 : (c + ε) / ε - c / ε = 1 := by field_simp; ring
  rw [e1, e2, integral_log_abs_sq_neg_one_one, smul_eq_mul] at h
  calc ∫ t in (c - ε)..(c + ε), Real.log (|c - t| / ε) ^ 2
      = ∫ t in (c - ε)..(c + ε), Real.log |t / ε - c / ε| ^ 2 := by
        apply intervalIntegral.integral_congr
        intro t _
        simp only
        rw [show t / ε - c / ε = (t - c) / ε by ring, abs_div, abs_of_pos hε, abs_sub_comm]
    _ = ε * 4 := h
    _ = 4 * ε := by ring

theorem intervalIntegrable_log_div_sq {ε : ℝ} (hε : 0 < ε) (c α β : ℝ) :
    IntervalIntegrable (fun t => Real.log (|c - t| / ε) ^ 2) volume α β := by
  have hl : IntervalIntegrable (fun t => Real.log |c - t|) volume α β := by
    have h := (intervalIntegral.intervalIntegrable_log' (a := c - β) (b := c - α)).comp_sub_left c
    simp only [sub_sub_cancel] at h
    simpa only [Real.log_abs] using h.symm
  have h2 : IntervalIntegrable (fun t => Real.log |c - t| ^ 2 - 2 * Real.log ε * Real.log |c - t| +
      Real.log ε ^ 2) volume α β :=
    ((intervalIntegrable_log_abs_sq c α β).sub (hl.const_mul _)).add intervalIntegrable_const
  refine h2.congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [(volume : Measure ℝ).ae_ne c] with t ht
  have hne : |c - t| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm ht))
  rw [Real.log_div hne hε.ne']
  ring

end logsq

/-! ### The truncation error `K` -/

section trunc

/-- `K(u) = log ε + log⁺(|u|/ε) − log|u| = log max(ε,|u|) − log|u|`. -/
def Kt (ε u : ℝ) : ℝ := Real.log ε + log⁺ (ε⁻¹ * |u|) - Real.log |u|

theorem measurable_Kt (ε : ℝ) : Measurable (Kt ε) := by
  unfold Kt
  have : Measurable fun u : ℝ => log⁺ (ε⁻¹ * |u|) := (continuous_posLog.comp (by
    fun_prop)).measurable
  fun_prop

theorem Kt_nonneg {ε u : ℝ} (hε : 0 < ε) (hu : u ≠ 0) : 0 ≤ Kt ε u := by
  unfold Kt
  have h1 : Real.log (ε⁻¹ * |u|) ≤ log⁺ (ε⁻¹ * |u|) := le_max_right _ _
  rw [Real.log_mul (inv_ne_zero hε.ne') (abs_pos.mpr hu).ne', Real.log_inv] at h1
  linarith

/-- The dominating function of `K²`. -/
def Kb (ε c t : ℝ) : ℝ := (Icc (c - ε) (c + ε)).indicator (fun t => Real.log (|c - t| / ε) ^ 2) t

theorem Kt_sq_le {ε c t : ℝ} (hε : 0 < ε) (ht : t ≠ c) : Kt ε (c - t) ^ 2 ≤ Kb ε c t := by
  have hu : c - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have hu' : 0 < |c - t| := abs_pos.mpr hu
  unfold Kb
  by_cases h : |c - t| ≤ ε
  · have hmem : t ∈ Icc (c - ε) (c + ε) := by
      rcases abs_le.mp h with ⟨h1, h2⟩; constructor <;> linarith
    rw [indicator_of_mem hmem]
    have hp : log⁺ (ε⁻¹ * |c - t|) = 0 := by
      rw [posLog_eq_zero_iff, abs_of_nonneg (by positivity), inv_mul_le_iff₀ hε, mul_one]; exact h
    unfold Kt
    rw [hp, Real.log_div hu'.ne' hε.ne']
    nlinarith
  · push Not at h
    have hK : Kt ε (c - t) = 0 := by
      unfold Kt
      rw [posLog_eq_log (by
        rw [abs_of_nonneg (by positivity), le_inv_mul_iff₀ hε, mul_one]
        exact h.le),
        Real.log_mul (inv_ne_zero hε.ne') hu'.ne', Real.log_inv]
      ring
    rw [hK]
    have := indicator_nonneg (s := Icc (c - ε) (c + ε))
      (f := fun t => Real.log (|c - t| / ε) ^ 2) (fun _ _ => sq_nonneg _) t
    nlinarith

theorem Kb_nonneg (ε c t : ℝ) : 0 ≤ Kb ε c t :=
  indicator_nonneg (fun _ _ => sq_nonneg _) t

theorem integrable_Kb {ε : ℝ} (hε : 0 < ε) (c : ℝ) : Integrable (Kb ε c) := by
  unfold Kb
  rw [integrable_indicator_iff measurableSet_Icc]
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)).mp
    (intervalIntegrable_log_div_sq hε c _ _)

theorem integral_Kb {ε : ℝ} (hε : 0 < ε) (c : ℝ) : ∫ t, Kb ε c t = 4 * ε := by
  unfold Kb
  rw [integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by linarith), integral_log_div_sq hε c]

end trunc

/-! ### Density lemmas for `GoodDensity` -/

section density
variable {ρ : ℝ → ℝ} {a : ℝ}

theorem GoodDensity.intervalIntegrable_log_mul (hρ : GoodDensity ρ a) (x : ℝ) :
    IntervalIntegrable (fun t => Real.log |x - t| * ρ t) volume (-a) a := by
  refine IntervalIntegrable.mono_fun' (((intervalIntegrable_log_abs_sq x (-a) a).add
    hρ.int2).div_const 2)
    ?_ (Filter.Eventually.of_forall fun t => ?_)
  · have := hρ.meas
    have hm : Measurable (fun t => Real.log |x - t| * ρ t) := by fun_prop
    exact hm.aestronglyMeasurable
  · simp only [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (abs (Real.log |x - t|) - abs (ρ t)), sq_abs (Real.log |x - t|), sq_abs
      (ρ t)]

theorem GoodDensity.abs_log_mul_le (ρ : ℝ → ℝ) (x t : ℝ) :
    abs (Real.log |x - t|) * abs (ρ t) ≤ (Real.log |x - t| ^ 2 + ρ t ^ 2) / 2 := by
  nlinarith [sq_nonneg (abs (Real.log |x - t|) - abs (ρ t)), sq_abs (Real.log |x - t|), sq_abs
    (ρ t)]

/-- `∫ ρ K ≤ √ε (N²/2 + 2)`. -/
theorem GoodDensity.cross_error (hρ : GoodDensity ρ a) (c : ℝ) {ε : ℝ} (hε : 0 < ε) :
    IntervalIntegrable (fun t => ρ t * Kt ε (c - t)) volume (-a) a ∧
      ∫ t in (-a)..a, ρ t * Kt ε (c - t) ≤
        √ε * ((∫ t in (-a)..a, ρ t ^ 2) / 2 + 2) := by
  have ha : -a ≤ a := by linarith [hρ.pos]
  have hs : 0 < √ε := Real.sqrt_pos.mpr hε
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have hKb : IntervalIntegrable (Kb ε c) volume (-a) a := (integrable_Kb hε c).intervalIntegrable
  have hdom : IntervalIntegrable (fun t => (√ε / 2) * ρ t ^ 2 + (1 / (2 * √ε)) * Kb ε c t)
    volume (-a) a :=
    (hρ.int2.const_mul _).add (hKb.const_mul _)
  have hpt : ∀ t, t ≠ c → |ρ t * Kt ε (c - t)| ≤ (√ε / 2) * ρ t ^ 2 + (1 / (2 * √ε)) * Kb ε c t
    := by
    intro t ht
    have hK0 := Kt_nonneg hε (sub_ne_zero.mpr (Ne.symm ht))
    have hK2 := Kt_sq_le hε ht
    rw [abs_mul, abs_of_nonneg hK0]
    have hk : (1 / (2 * √ε)) * Kt ε (c - t) ^ 2 ≤ (1 / (2 * √ε)) * Kb ε c t :=
      mul_le_mul_of_nonneg_left hK2 (by positivity)
    have hamgm : |ρ t| * Kt ε (c - t) ≤ (√ε / 2) * ρ t ^ 2 + (1 / (2 * √ε)) * Kt ε (c - t) ^ 2 := by
      have e : (√ε / 2) * ρ t ^ 2 + (1 / (2 * √ε)) * Kt ε (c - t) ^ 2 - |ρ t| * Kt ε (c - t) =
          (√ε * |ρ t| - Kt ε (c - t)) ^ 2 / (2 * √ε) := by
        field_simp
        rw [sub_sq, mul_pow, sq_abs]
        ring
      have : 0 ≤ (√ε * |ρ t| - Kt ε (c - t)) ^ 2 / (2 * √ε) := by positivity
      linarith
    linarith
  have hint : IntervalIntegrable (fun t => ρ t * Kt ε (c - t)) volume (-a) a := by
    refine IntervalIntegrable.mono_fun' hdom ?_ ?_
    · have := hρ.meas
      have hK := measurable_Kt ε
      have hm : Measurable (fun t => ρ t * Kt ε (c - t)) := hρ.meas.mul (hK.comp (by fun_prop))
      exact hm.aestronglyMeasurable
    · filter_upwards [ae_restrict_of_ae ((volume : Measure ℝ).ae_ne c)] with t ht
      rw [Real.norm_eq_abs]; exact hpt t ht
  refine ⟨hint, ?_⟩
  have h1 : ∫ t in (-a)..a, ρ t * Kt ε (c - t) ≤
      ∫ t in (-a)..a, ((√ε / 2) * ρ t ^ 2 + (1 / (2 * √ε)) * Kb ε c t) := by
    refine intervalIntegral.integral_mono_ae ha hint hdom ?_
    filter_upwards [(volume : Measure ℝ).ae_ne c] with t ht
    exact (le_abs_self _).trans (hpt t ht)
  have h2 : ∫ t in (-a)..a, Kb ε c t ≤ 4 * ε := by
    rw [intervalIntegral.integral_of_le ha, ← integral_Kb hε c]
    exact setIntegral_le_integral (integrable_Kb hε c) (Filter.Eventually.of_forall (Kb_nonneg ε c))
  rw [intervalIntegral.integral_add (hρ.int2.const_mul _) (hKb.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at h1
  have h3 : (1 / (2 * √ε)) * ∫ t in (-a)..a, Kb ε c t ≤ (1 / (2 * √ε)) * (4 * ε) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (1 / (2 * √ε)) * (4 * ε) = 2 * √ε := by
    field_simp; nlinarith [hss]
  nlinarith

end density

/-! ### Measures -/

section measures

theorem norm_ofReal_sub (s t : ℝ) : ‖(s : ℂ) - (t : ℂ)‖ = |s - t| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Angular measure on `(0, 2π]` (mass `2π`). -/
def circB : Measure ℝ := volume.restrict (Ioc 0 (2 * π))

instance : IsFiniteMeasure circB := by
  unfold circB; exact isFiniteMeasure_restrict.mpr measure_Ioc_lt_top.ne

theorem integral_circB (g : ℝ → ℝ) : ∫ θ, g θ ∂circB = ∫ θ in (0:ℝ)..2 * π, g θ := by
  unfold circB; rw [intervalIntegral.integral_of_le (by positivity)]

theorem real_circB : circB.real univ = 2 * π := by
  simp [circB, Measure.real, Real.volume_Ioc, Real.pi_pos.le]

variable {ρ : ℝ → ℝ} {a : ℝ}

/-- The comparison measure `ρ(t) dt` on `(-a, a]`. -/
def nuB (ρ : ℝ → ℝ) (a : ℝ) : Measure ℝ :=
  (volume.restrict (Ioc (-a) a)).withDensity (fun t => ENNReal.ofReal (ρ t))

instance (ρ : ℝ → ℝ) (a : ℝ) : SFinite (nuB ρ a) := by unfold nuB; infer_instance

theorem GoodDensity.isFiniteMeasure_nuB (hρ : GoodDensity ρ a) : IsFiniteMeasure (nuB ρ a) := by
  unfold nuB
  have hi := hρ.int
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hρ.pos])] at hi
  exact isFiniteMeasure_withDensity_ofReal hi.hasFiniteIntegral

theorem GoodDensity.integral_nuB (hρ : GoodDensity ρ a) (g : ℝ → ℝ) :
    ∫ t, g t ∂(nuB ρ a) = ∫ t in (-a)..a, ρ t * g t := by
  unfold nuB
  rw [integral_withDensity_eq_integral_toReal_smul (hρ.meas.ennreal_ofReal)
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) g,
    intervalIntegral.integral_of_le (by linarith [hρ.pos])]
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hρ.nonneg] with t ht hnn
  rw [smul_eq_mul, ENNReal.toReal_ofReal (hnn (Ioc_subset_Icc_self ht))]

theorem GoodDensity.integrable_nuB (hρ : GoodDensity ρ a) (g : ℝ → ℝ) :
    Integrable g (nuB ρ a) ↔ IntervalIntegrable (fun t => ρ t * g t) volume (-a) a := by
  unfold nuB
  rw [integrable_withDensity_iff_integrable_smul₀' hρ.meas.ennreal_ofReal.aemeasurable
    (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [hρ.pos])]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hρ.nonneg] with t ht hnn
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal (hnn (Ioc_subset_Icc_self ht))]

theorem GoodDensity.ae_nuB : ∀ᵐ t ∂(nuB ρ a), t ∈ Ioc (-a) a := by
  unfold nuB
  exact (withDensity_absolutelyContinuous _ _).ae_le (ae_restrict_mem measurableSet_Ioc)

theorem GoodDensity.real_nuB (hρ : GoodDensity ρ a) : (nuB ρ a).real univ = 1 := by
  have := hρ.isFiniteMeasure_nuB
  have h := hρ.integral_nuB (fun _ => 1)
  rw [MeasureTheory.integral_const, smul_eq_mul, mul_one] at h
  rw [h]; simp only [mul_one]; exact hρ.mass

theorem nuB_fiber_null (ρ : ℝ → ℝ) (a : ℝ) (w : ℂ) : nuB ρ a {t : ℝ | (t : ℂ) = w} = 0 := by
  unfold nuB
  apply withDensity_absolutelyContinuous
  have hs : {t : ℝ | (t : ℂ) = w} ⊆ {w.re} := by
    intro t ht
    simp only [mem_ofPred_eq] at ht
    simp [← ht]
  exact measure_mono_null hs (nonpos_iff_eq_zero.mp ((Measure.restrict_apply_le _ _).trans
    (measure_singleton _).le))

/-! Pushforwards to `ℂ` -/

theorem integral_prod_map {β₁ β₂ : Measure ℝ} [SFinite β₁] [SFinite β₂] {γ₁ γ₂ : ℝ → ℂ}
    (h₁ : Measurable γ₁) (h₂ : Measurable γ₂) {f : ℂ × ℂ → ℝ} (hf : Measurable f) :
    ∫ p, f p ∂((β₁.map γ₁).prod (β₂.map γ₂)) = ∫ q, f (γ₁ q.1, γ₂ q.2) ∂(β₁.prod β₂) := by
  rw [Measure.map_prod_map _ _ h₁ h₂,
    integral_map (h₁.prodMap h₂).aemeasurable hf.aestronglyMeasurable]
  rfl

theorem integrable_prod_map {β₁ β₂ : Measure ℝ} [SFinite β₁] [SFinite β₂] {γ₁ γ₂ : ℝ → ℂ}
    (h₁ : Measurable γ₁) (h₂ : Measurable γ₂) {f : ℂ × ℂ → ℝ} (hf : Measurable f) :
    Integrable f ((β₁.map γ₁).prod (β₂.map γ₂)) ↔
      Integrable (fun q => f (γ₁ q.1, γ₂ q.2)) (β₁.prod β₂) := by
  rw [Measure.map_prod_map _ _ h₁ h₂,
    integrable_map_measure hf.aestronglyMeasurable (h₁.prodMap h₂).aemeasurable]
  rfl

theorem ae_ne_prod_map {β₁ β₂ : Measure ℝ} [SFinite β₁] [SFinite β₂] {γ₁ γ₂ : ℝ → ℂ}
    (h₁ : Measurable γ₁) (h₂ : Measurable γ₂) :
    (∀ᵐ p ∂((β₁.map γ₁).prod (β₂.map γ₂)), p.1 ≠ p.2) ↔
      ∀ᵐ q ∂(β₁.prod β₂), γ₁ q.1 ≠ γ₂ q.2 := by
  have hmeas : MeasurableSet {y : ℂ × ℂ | y.1 ≠ y.2} :=
    (isClosed_eq continuous_fst continuous_snd).measurableSet.compl
  rw [Measure.map_prod_map _ _ h₁ h₂]
  exact ae_map_iff (h₁.prodMap h₂).aemeasurable (p := fun y : ℂ × ℂ => y.1 ≠ y.2) hmeas

theorem real_map {β : Measure ℝ} {γ : ℝ → ℂ} (h : Measurable γ) : (β.map γ).real univ = β.real
  univ := by
  simp [Measure.real, Measure.map_apply h MeasurableSet.univ]

theorem measurable_logK : Measurable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) :=
  Real.measurable_log.comp (continuous_fst.sub continuous_snd).norm.measurable

/-! Circle–circle -/

theorem integral_cc (c d : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ q, Real.log ‖circleMap c ε q.1 - circleMap d ε q.2‖ ∂(circB.prod circB) =
      ∫ θ in (0:ℝ)..2 * π, ∫ φ in (0:ℝ)..2 * π, Real.log ‖circleMap c ε θ - circleMap d ε φ‖ := by
  have hI : Integrable (fun q : ℝ × ℝ => Real.log ‖circleMap c ε q.1 - circleMap d ε q.2‖)
      (circB.prod circB) := integrable_circle_pair_log c d hε
  rw [integral_prod _ hI, integral_circB]
  apply intervalIntegral.integral_congr
  intro θ _
  exact integral_circB _

theorem ae_cc (c d : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ q ∂(circB.prod circB), circleMap c ε q.1 ≠ circleMap d ε q.2 := by
  have h := pair_collision_null (circleMap c ε) (circleMap d ε) circB circB
    (continuous_circleMap c ε)
    (continuous_circleMap d ε) (fun w => circle_fiber_null d w ε 0 (2 * π) hε.ne')
  exact measure_eq_zero_iff_ae_notMem.mp h

/-! Circle–density -/

theorem measurable_cn (c : ℂ) (ε : ℝ) :
    Measurable (fun q : ℝ × ℝ => Real.log ‖circleMap c ε q.1 - (q.2 : ℂ)‖) := by
  have : Continuous (fun q : ℝ × ℝ => circleMap c ε q.1 - (q.2 : ℂ)) :=
    ((continuous_circleMap c ε).comp continuous_fst).sub (Complex.continuous_ofReal.comp
      continuous_snd)
  exact Real.measurable_log.comp this.norm.measurable

theorem circle_abs_log_le (c : ℂ) {ε : ℝ} (hε : 0 < ε) {a : ℝ} (t : ℝ) (ht : |t| ≤ a) :
    ∫ θ, ‖Real.log ‖circleMap c ε θ - (t : ℂ)‖‖ ∂circB ≤
      4 * π * (‖c‖ + a + ε) - 2 * π * Real.log ε := by
  rw [integral_circB]
  have hpi : 0 ≤ 2 * π := by positivity
  have hP : Continuous fun θ => log⁺ ‖circleMap c ε θ - (t : ℂ)‖ :=
    continuous_posLog.comp ((continuous_circleMap c ε).sub continuous_const).norm
  have hL := circle_log_integrable c (t : ℂ) ε
  have e : (∫ θ in (0:ℝ)..2 * π, ‖Real.log ‖circleMap c ε θ - (t : ℂ)‖‖) =
      2 * (∫ θ in (0:ℝ)..2 * π, log⁺ ‖circleMap c ε θ - (t : ℂ)‖) -
        ∫ θ in (0:ℝ)..2 * π, Real.log ‖circleMap c ε θ - (t : ℂ)‖ := by
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_sub
      ((hP.intervalIntegrable _ _).const_mul _) hL]
    apply intervalIntegral.integral_congr
    intro θ _
    simp only [Real.norm_eq_abs]
    exact circle_abs_log_eq _
  rw [e, circle_log_integral c (t : ℂ) hε.ne']
  have hbound : ∀ θ, log⁺ ‖circleMap c ε θ - (t : ℂ)‖ ≤ ‖c‖ + a + ε := by
    intro θ
    refine (posLog_le_abs _).trans ?_
    rw [abs_of_nonneg (norm_nonneg _)]
    calc ‖circleMap c ε θ - (t : ℂ)‖ ≤ ‖circleMap c ε θ - c‖ + ‖c - (t : ℂ)‖ :=
      norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ ε + (‖c‖ + a) := by
        rw [circleMap_sub_center, norm_circleMap_zero, abs_of_pos hε]
        gcongr
        refine (norm_sub_le _ _).trans ?_
        rw [Complex.norm_real, Real.norm_eq_abs]; linarith
      _ = ‖c‖ + a + ε := by ring
  have hPint : (∫ θ in (0:ℝ)..2 * π, log⁺ ‖circleMap c ε θ - (t : ℂ)‖) ≤ 2 * π * (‖c‖ + a + ε) := by
    have := intervalIntegral.integral_mono_on (μ := volume)
      (f := fun θ => log⁺ ‖circleMap c ε θ - (t : ℂ)‖)
      (g := fun _ => ‖c‖ + a + ε) hpi (hP.intervalIntegrable _ _) intervalIntegrable_const
      (fun θ _ => hbound θ)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at this
    exact this
  have hpos : 0 ≤ log⁺ (ε⁻¹ * ‖c - (t : ℂ)‖) := posLog_nonneg
  nlinarith [Real.pi_pos]

theorem GoodDensity.integrable_cn (hρ : GoodDensity ρ a) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    Integrable (fun q : ℝ × ℝ => Real.log ‖circleMap c ε q.1 - (q.2 : ℂ)‖) (circB.prod (nuB ρ
      a)) := by
  have := hρ.isFiniteMeasure_nuB
  rw [integrable_prod_iff' (measurable_cn c ε).aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun t => ?_, ?_⟩
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp
      (circle_log_integrable c (t : ℂ) ε)
  · refine (integrable_const (4 * π * (‖c‖ + a + ε) - 2 * π * Real.log ε)).mono'
      ((measurable_cn c ε).norm.stronglyMeasurable.integral_prod_left').aestronglyMeasurable ?_
    filter_upwards [GoodDensity.ae_nuB (ρ := ρ) (a := a)] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    exact circle_abs_log_le c hε t (abs_le.mpr ⟨ht.1.le, ht.2⟩)

theorem GoodDensity.integral_cn (hρ : GoodDensity ρ a) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∫ q, Real.log ‖circleMap c ε q.1 - (q.2 : ℂ)‖ ∂(circB.prod (nuB ρ a)) =
      ∫ t in (-a)..a, ρ t * (2 * π * (Real.log ε + log⁺ (ε⁻¹ * ‖c - (t : ℂ)‖))) := by
  have := hρ.isFiniteMeasure_nuB
  rw [integral_prod_symm _ (hρ.integrable_cn c hε)]
  have e : ∀ t : ℝ, ∫ θ, Real.log ‖circleMap c ε θ - (t : ℂ)‖ ∂circB =
      2 * π * (Real.log ε + log⁺ (ε⁻¹ * ‖c - (t : ℂ)‖)) := by
    intro t; rw [integral_circB, circle_log_integral c (t : ℂ) hε.ne']
  simp_rw [e]
  exact hρ.integral_nuB _

theorem ae_cn (ρ : ℝ → ℝ) (a : ℝ) (c : ℂ) {ε : ℝ} :
    ∀ᵐ q ∂(circB.prod (nuB ρ a)), circleMap c ε q.1 ≠ (q.2 : ℂ) := by
  have h := pair_collision_null (circleMap c ε) (fun t : ℝ => (t : ℂ)) circB (nuB ρ a)
    (continuous_circleMap c ε) Complex.continuous_ofReal (nuB_fiber_null ρ a)
  exact measure_eq_zero_iff_ae_notMem.mp h

theorem ae_nc (ρ : ℝ → ℝ) (a : ℝ) (c : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᵐ q ∂((nuB ρ a).prod circB), (q.1 : ℂ) ≠ circleMap c ε q.2 := by
  have h := pair_collision_null (fun t : ℝ => (t : ℂ)) (circleMap c ε) (nuB ρ a) circB
    Complex.continuous_ofReal (continuous_circleMap c ε) (fun w => circle_fiber_null c w ε 0 (2
      * π) hε.ne')
  exact measure_eq_zero_iff_ae_notMem.mp h

/-! Density–density -/

theorem measurable_nn : Measurable (fun q : ℝ × ℝ => Real.log ‖(q.1 : ℂ) - (q.2 : ℂ)‖) := by
  have : Continuous (fun q : ℝ × ℝ => (q.1 : ℂ) - (q.2 : ℂ)) :=
    (Complex.continuous_ofReal.comp continuous_fst).sub (Complex.continuous_ofReal.comp
      continuous_snd)
  exact Real.measurable_log.comp this.norm.measurable

theorem integral_log_sq_shift_le (ha : 0 < a) {s : ℝ} (hs : |s| ≤ a) :
    ∫ t in (-a)..a, Real.log |s - t| ^ 2 ≤ ∫ u in (-(2 * a))..(2 * a), Real.log |u| ^ 2 := by
  have e := intervalIntegral.integral_comp_sub_left (fun u => Real.log |u| ^ 2) (a := -a) (b := a) s
  rw [e]
  rcases abs_le.mp hs with ⟨h1, h2⟩
  refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith) ?_ ?_
  · filter_upwards with u; exact sq_nonneg _
  · simpa only [Real.log_abs] using intervalIntegrable_log_sq _ _

theorem GoodDensity.integrable_nn_slice (hρ : GoodDensity ρ a) (s : ℝ) :
    Integrable (fun t : ℝ => Real.log ‖(s : ℂ) - (t : ℂ)‖) (nuB ρ a) := by
  rw [hρ.integrable_nuB]
  have e : (fun t => ρ t * Real.log ‖(s : ℂ) - (t : ℂ)‖) = fun t => Real.log |s - t| * ρ t := by
    funext t; rw [norm_ofReal_sub, mul_comm]
  rw [e]
  exact hρ.intervalIntegrable_log_mul s

theorem GoodDensity.integrable_nn (hρ : GoodDensity ρ a) :
    Integrable (fun q : ℝ × ℝ => Real.log ‖(q.1 : ℂ) - (q.2 : ℂ)‖) ((nuB ρ a).prod (nuB ρ a)) := by
  have := hρ.isFiniteMeasure_nuB
  have ha : -a ≤ a := by linarith [hρ.pos]
  rw [integrable_prod_iff measurable_nn.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun s => hρ.integrable_nn_slice s, ?_⟩
  set Mc := ∫ u in (-(2 * a))..(2 * a), Real.log |u| ^ 2
  set N := ∫ t in (-a)..a, ρ t ^ 2
  refine (integrable_const ((Mc + N) / 2)).mono'
    (measurable_nn.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable ?_
  filter_upwards [GoodDensity.ae_nuB (ρ := ρ) (a := a)] with s hs
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _), hρ.integral_nuB]
  have hi1 : IntervalIntegrable (fun t => ρ t * ‖Real.log ‖(s : ℂ) - (t : ℂ)‖‖) volume (-a) a :=
    (hρ.integrable_nuB _).mp (hρ.integrable_nn_slice s).norm
  have hi2 : IntervalIntegrable (fun t => (Real.log |s - t| ^ 2 + ρ t ^ 2) / 2) volume (-a) a :=
    ((intervalIntegrable_log_abs_sq s (-a) a).add hρ.int2).div_const 2
  have h1 : ∫ t in (-a)..a, ρ t * ‖Real.log ‖(s : ℂ) - (t : ℂ)‖‖ ≤
      ∫ t in (-a)..a, (Real.log |s - t| ^ 2 + ρ t ^ 2) / 2 := by
    refine intervalIntegral.integral_mono_on ha hi1 hi2 (fun t _ => ?_)
    rw [norm_ofReal_sub, Real.norm_eq_abs]
    have := GoodDensity.abs_log_mul_le ρ s t
    have : ρ t * abs (Real.log |s - t|) ≤ abs (ρ t) * abs (Real.log |s - t|) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) (abs_nonneg _)
    nlinarith
  have h2 : ∫ t in (-a)..a, (Real.log |s - t| ^ 2 + ρ t ^ 2) / 2 =
      ((∫ t in (-a)..a, Real.log |s - t| ^ 2) + N) / 2 := by
    rw [intervalIntegral.integral_div, intervalIntegral.integral_add
      (intervalIntegrable_log_abs_sq s (-a) a)
      hρ.int2]
  have h3 := integral_log_sq_shift_le hρ.pos (abs_le.mpr ⟨hs.1.le, hs.2⟩)
  rw [h2] at h1
  linarith

theorem GoodDensity.integral_nn (hρ : GoodDensity ρ a) :
    ∫ q, Real.log ‖(q.1 : ℂ) - (q.2 : ℂ)‖ ∂((nuB ρ a).prod (nuB ρ a)) = ID ρ a := by
  have := hρ.isFiniteMeasure_nuB
  rw [integral_prod _ hρ.integrable_nn,
    hρ.integral_nuB (fun s => ∫ t, Real.log ‖(s : ℂ) - (t : ℂ)‖ ∂(nuB ρ a))]
  unfold ID potD
  apply intervalIntegral.integral_congr
  intro s _
  simp only
  rw [hρ.integral_nuB, mul_comm]
  congr 1
  apply intervalIntegral.integral_congr
  intro t _
  simp only
  rw [norm_ofReal_sub, mul_comm]

theorem ae_nn (ρ : ℝ → ℝ) (a : ℝ) :
    ∀ᵐ q ∂((nuB ρ a).prod (nuB ρ a)), (q.1 : ℂ) ≠ (q.2 : ℂ) := by
  have h := pair_collision_null (fun t : ℝ => (t : ℂ)) (fun t : ℝ => (t : ℂ)) (nuB ρ a) (nuB ρ a)
    Complex.continuous_ofReal Complex.continuous_ofReal (nuB_fiber_null ρ a)
  exact measure_eq_zero_iff_ae_notMem.mp h

end measures

/-! ### The configuration inequality -/

/-- The atoms: the comparison measure and the `h` circles. -/
def atom (ρ : ℝ → ℝ) (a : ℝ) {h : ℕ} (x : Fin h → ℝ) (ε : ℝ) : Option (Fin h) → Measure ℂ
  | none => (nuB ρ a).map (fun t : ℝ => (t : ℂ))
  | some i => circB.map (circleMap (x i : ℂ) ε)

/-- the proof notes (13′): discretisation by circles of radius `ε`, zero-mass energy inequality. -/
theorem discrete_energy {ρ : ℝ → ℝ} {a : ℝ} (hρ : GoodDensity ρ a) {h : ℕ} (hh : 0 < h)
    (x : Fin h → ℝ) (hx : Function.Injective x) {ε : ℝ} (hε : 0 < ε) :
    2 * ∑ i : Fin h, ∑ j ∈ Finset.Ioi i, Real.log |x j - x i| ≤
      2 * (h : ℝ) * ∑ i : Fin h, potD ρ a (x i) - (h : ℝ)^2 * ID ρ a - (h : ℝ) * Real.log ε +
        2 * (h : ℝ)^2 * (√ε * (32 + (∫ t in (-a)..a, ρ t ^ 2) / 2)) := by
  have := hρ.isFiniteMeasure_nuB
  have hpi : 0 < π := Real.pi_pos
  have hs : 0 < √ε := Real.sqrt_pos.mpr hε
  set N := ∫ t in (-a)..a, ρ t ^ 2 with hNdef
  have hN : 0 ≤ N := intervalIntegral.integral_nonneg (by linarith [hρ.pos]) (fun _ _ =>
    sq_nonneg _)
  set K0 := 32 + N / 2 with hK0
  have hmo : Measurable (fun t : ℝ => (t : ℂ)) := Complex.measurable_ofReal
  have hmc : ∀ i : Fin h, Measurable (circleMap (x i : ℂ) ε) := fun i => (continuous_circleMap _
    _).measurable
  have hfin : ∀ k, IsFiniteMeasure (atom ρ a x ε k) := by
    intro k; cases k <;> (simp only [atom]; infer_instance)
  set E : Option (Fin h) → Option (Fin h) → ℝ := fun k l =>
    ∫ p, Real.log ‖p.1 - p.2‖ ∂((atom ρ a x ε k).prod (atom ρ a x ε l)) with hEdef
  -- integrability and noncollision for every pair
  have hint : ∀ k l, Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      ((atom ρ a x ε k).prod (atom ρ a x ε l)) := by
    intro k l
    cases k with
    | none =>
      cases l with
      | none => exact (integrable_prod_map hmo hmo measurable_logK).mpr hρ.integrable_nn
      | some j =>
        refine (integrable_prod_map hmo (hmc j) measurable_logK).mpr ?_
        refine ((hρ.integrable_cn (x j : ℂ) hε).swap).congr (Filter.Eventually.of_forall fun q
          => ?_)
        simp only [Function.comp_apply, Prod.fst_swap, Prod.snd_swap]
        rw [norm_sub_rev]
    | some i =>
      cases l with
      | none => exact (integrable_prod_map (hmc i) hmo measurable_logK).mpr (hρ.integrable_cn (x
        i : ℂ) hε)
      | some j =>
        exact (integrable_prod_map (hmc i) (hmc j) measurable_logK).mpr
          (integrable_circle_pair_log _ _ hε)
  have hdiag : ∀ k l, ∀ᵐ p ∂((atom ρ a x ε k).prod (atom ρ a x ε l)), p.1 ≠ p.2 := by
    intro k l
    cases k with
    | none =>
      cases l with
      | none => exact (ae_ne_prod_map hmo hmo).mpr (ae_nn ρ a)
      | some j => exact (ae_ne_prod_map hmo (hmc j)).mpr (ae_nc ρ a (x j : ℂ) hε)
    | some i =>
      cases l with
      | none => exact (ae_ne_prod_map (hmc i) hmo).mpr (ae_cn ρ a (x i : ℂ))
      | some j => exact (ae_ne_prod_map (hmc i) (hmc j)).mpr (ae_cc _ _ hε)
  -- symmetry
  have hEsym : ∀ k l, E k l = E l k := by
    intro k l
    simp only [hEdef]
    rw [← integral_prod_swap]
    congr 1; funext z
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [norm_sub_rev]
  -- zero mass
  have hmass : ∑ k : Option (Fin h), (fun k => match k with
      | none => (-1 : ℝ) | some _ => 1 / ((h : ℝ) * (2 * π))) k * (atom ρ a x ε k).real univ = 0
        := by
    rw [Fintype.sum_option]
    simp only [atom]
    rw [real_map hmo, hρ.real_nuB]
    have : ∀ i : Fin h, 1 / ((h : ℝ) * (2 * π)) * (circB.map (circleMap (x i : ℂ) ε)).real univ =
        1 / (h : ℝ) := by
      intro i
      rw [real_map (hmc i), real_circB]
      have : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
      field_simp
    rw [Finset.sum_congr rfl (fun i _ => this i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin,
      nsmul_eq_mul]
    have : (h : ℝ) ≠ 0 := by exact_mod_cast hh.ne'
    field_simp
    ring
  have hzm := zero_mass_energy_nonpos (atom ρ a x ε)
    (fun k => match k with | none => (-1 : ℝ) | some _ => 1 / ((h : ℝ) * (2 * π))) hmass hint hdiag
  -- the four kinds of pair energies
  have h00 : E none none = ID ρ a := by
    simp only [hEdef, atom]
    rw [integral_prod_map hmo hmo measurable_logK]
    exact hρ.integral_nn
  have hself : ∀ i : Fin h, E (some i) (some i) = (2 * π) ^ 2 * Real.log ε := by
    intro i
    simp only [hEdef, atom]
    rw [integral_prod_map (hmc i) (hmc i) measurable_logK]
    dsimp only
    rw [integral_cc _ _ hε]
    exact circle_pair_log_self _ hε
  have hoff : ∀ i j : Fin h, i ≠ j →
      (2 * π) ^ 2 * Real.log ‖(fun i => (x i : ℂ)) j - (fun i => (x i : ℂ)) i‖ ≤ E (some i)
        (some j) := by
    intro i j hij
    simp only [hEdef, atom]
    rw [integral_prod_map (hmc i) (hmc j) measurable_logK]
    dsimp only
    rw [integral_cc _ _ hε]
    have hne : (x i : ℂ) ≠ (x j : ℂ) := fun h' => hij (hx (Complex.ofReal_injective h'))
    have := circle_pair_log_lower (x i : ℂ) (x j : ℂ) hε hne
    rw [norm_sub_rev] at this
    exact this
  have hss : √ε * √ε = ε := Real.mul_self_sqrt hε.le
  have h2M : 2 * (K0 / (2 * √ε)) * ε = √ε * K0 := by
    have e : ε = √ε * √ε := hss.symm
    calc 2 * (K0 / (2 * √ε)) * ε = 2 * (K0 / (2 * √ε)) * (√ε * √ε) := by rw [← e]
      _ = √ε * K0 := by field_simp
  have hcross : ∀ i : Fin h, E (some i) none ≤ (2 * π) * (potD ρ a (x i) + 2 * (K0 / (2 * √ε)) *
    ε) := by
    intro i
    simp only [hEdef, atom]
    rw [integral_prod_map (hmc i) hmo measurable_logK]
    dsimp only
    rw [hρ.integral_cn (x i : ℂ) hε]
    obtain ⟨hKi, hKb⟩ := hρ.cross_error (x i) hε
    have e : ∫ t in (-a)..a, ρ t * (2 * π * (Real.log ε + log⁺ (ε⁻¹ * ‖(x i : ℂ) - (t : ℂ)‖))) =
        ∫ t in (-a)..a, 2 * π * (Real.log |x i - t| * ρ t + ρ t * Kt ε (x i - t)) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp only
      rw [norm_ofReal_sub]
      unfold Kt
      ring
    rw [e, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hρ.intervalIntegrable_log_mul (x i)) hKi, h2M]
    unfold potD
    have : √ε * (N / 2 + 2) ≤ √ε * K0 := by
      apply mul_le_mul_of_nonneg_left _ hs.le
      rw [hK0]; linarith
    nlinarith
  have hmain := complex_signed_energy_log_bound hh (2 * π) ε (K0 / (2 * √ε)) (by positivity)
    (fun i => (x i : ℂ)) (fun i => potD ρ a (x i)) (ID ρ a) E hEsym hzm h00 hcross
    hself hoff
  have e1 : ∀ i j : Fin h, Real.log ‖(fun i => (x i : ℂ)) j - (fun i => (x i : ℂ)) i‖ =
      Real.log |x j - x i| := fun i j => by simp only; rw [norm_ofReal_sub]
  simp only [e1] at hmain
  have e2 : 4 * (K0 / (2 * √ε)) * (h : ℝ) ^ 2 * ε = 2 * (h : ℝ) ^ 2 * (√ε * K0) := by
    rw [← h2M]; ring
  rw [e2] at hmain
  exact hmain

end
end Zeta32.Analytic.EnergyI

end
