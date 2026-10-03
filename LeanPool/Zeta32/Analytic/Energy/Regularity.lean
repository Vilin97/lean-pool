/-
Copyright (c) 2026 Qian Tang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Qian Tang
-/
module
public import LeanPool.Zeta32.Analytic.Energy.Defs
public import LeanPool.Zeta32.Fstar.Rho

/-! Regularity of the comparison density `rhoA a` on `(-a, a)` (the proof notes (8′),
"density near 0"): `rhoA a t = fc a |t| − log|t|/(6π)` with `fc` continuous (Fstar/Rho.lean), hence
`rhoA`, `rhoA²` and `log|x − ·| · rhoA` are integrable (via `log²` integrable, AM–GM). -/

public section

open Real MeasureTheory Set Filter
open scoped Interval

namespace Zeta32.Analytic.EnergyI
noncomputable section

theorem rhoA_neg (a t : ℝ) : rhoA a (-t) = rhoA a t := by
  unfold rhoA Gfun; simp only [neg_sq]

theorem measurable_rhoA (a : ℝ) : Measurable (rhoA a) := by
  unfold rhoA Gfun
  fun_prop

theorem rhoA_abs (a t : ℝ) : rhoA a |t| = rhoA a t := by
  rcases le_or_gt 0 t with h | h
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg h, rhoA_neg]

theorem rhoA_eq_fc_abs {a t : ℝ} (ht : t ≠ 0) (hta : |t| ≤ a) :
    rhoA a t = Fstar.fc a |t| - Real.log |t| / (6 * π) := by
  rw [← rhoA_abs]
  exact Fstar.rhoA_eq_fc (abs_pos.mpr ht) hta

theorem rhoA_nonneg_of_ne {a t : ℝ} (ht : t ≠ 0) (hta : |t| ≤ a) : 0 ≤ rhoA a t := by
  rw [← rhoA_abs]
  exact Fstar.rhoA_nonneg (abs_pos.mpr ht) hta

theorem ae_ne_zero : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := (volume : Measure ℝ).ae_ne 0

/-- `log²` is interval integrable (antiderivative `t log²t − 2t log t + 2t`). -/
theorem intervalIntegrable_log_sq (α β : ℝ) :
    IntervalIntegrable (fun t => Real.log t ^ 2) volume α β := by
  have hpos : ∀ b : ℝ, 0 ≤ b → IntervalIntegrable (fun t => Real.log t ^ 2) volume 0 b := by
    intro b hb
    rw [intervalIntegrable_iff, uIoc_of_le hb]
    let g : ℝ → ℝ := fun t => 4 * (√t * Real.log √t)^2 - 2 * (t * Real.log t) + 2 * t
    have hg : Continuous g := by
      have h1 : Continuous fun t : ℝ => √t * Real.log √t :=
        Real.continuous_mul_log.comp Real.continuous_sqrt
      exact ((continuous_const.mul (h1.pow 2)).sub (continuous_const.mul
        Real.continuous_mul_log)).add
        (continuous_const.mul continuous_id)
    have hderiv : ∀ t ∈ Ioo 0 b, HasDerivAt g (Real.log t ^ 2) t := by
      intro t ht
      have ht0 : 0 < t := ht.1
      have hloc : g =ᶠ[nhds t] fun s => s * Real.log s ^ 2 - 2 * (s * Real.log s) + 2 * s := by
        filter_upwards [lt_mem_nhds ht0] with s hs
        simp only [g]
        rw [Real.log_sqrt hs.le, mul_pow, Real.sq_sqrt hs.le]
        ring
      have h := (((hasDerivAt_id t).mul ((Real.hasDerivAt_log ht0.ne').pow 2)).sub
        (((hasDerivAt_id t).mul (Real.hasDerivAt_log ht0.ne')).const_mul 2)).add
        ((hasDerivAt_id t).const_mul 2)
      refine (h.congr_of_eventuallyEq hloc).congr_deriv ?_
      simp only [id, Pi.pow_apply]
      field_simp
      ring
    exact intervalIntegral.integrableOn_deriv_of_nonneg hg.continuousOn hderiv (fun t _ =>
      sq_nonneg _)
  have hall : ∀ b : ℝ, IntervalIntegrable (fun t => Real.log t ^ 2) volume 0 b := by
    intro b
    rcases le_total 0 b with hb | hb
    · exact hpos b hb
    · have h := (IntervalIntegrable.iff_comp_neg).mp (hpos (-b) (by linarith))
      simpa only [neg_zero, neg_neg, Real.log_neg_eq_log] using h
  exact (hall α).symm.trans (hall β)

theorem intervalIntegrable_log_abs_sq (x α β : ℝ) :
    IntervalIntegrable (fun t => Real.log |x - t| ^ 2) volume α β := by
  have h := (intervalIntegrable_log_sq (x - β) (x - α)).comp_sub_left x
  simp only [sub_sub_cancel] at h
  simpa only [Real.log_abs] using h.symm

variable {a : ℝ}

theorem rhoA_ae_eq (ha : 0 < a) :
    ∀ᵐ t ∂(volume.restrict (Ι (-a) a)), rhoA a t = Fstar.fc a |t| - Real.log |t| / (6 * π) := by
  have h0 : ∀ᵐ t ∂(volume.restrict (Ι (-a) a)), t ≠ 0 := ae_restrict_of_ae ae_ne_zero
  filter_upwards [h0, ae_restrict_mem measurableSet_uIoc] with t ht htI
  rw [uIoc_of_le (by linarith)] at htI
  exact rhoA_eq_fc_abs ht (abs_le.mpr ⟨htI.1.le, htI.2⟩)

theorem intervalIntegrable_rhoA (ha : 0 < a) : IntervalIntegrable (rhoA a) volume (-a) a := by
  have hfc : Continuous fun t => Fstar.fc a |t| := (Fstar.continuous_fc ha).comp continuous_abs
  have h : IntervalIntegrable (fun t => Fstar.fc a |t| - Real.log |t| / (6 * π)) volume (-a) a := by
    refine (hfc.intervalIntegrable _ _).sub ?_
    simpa only [Real.log_abs] using (intervalIntegral.intervalIntegrable_log' (a := -a) (b :=
      a)).div_const
      (6 * π)
  exact h.congr_ae ((rhoA_ae_eq ha).mono fun t h => h.symm)

theorem intervalIntegrable_rhoA_sq (ha : 0 < a) :
    IntervalIntegrable (fun t => rhoA a t ^ 2) volume (-a) a := by
  have hfc : Continuous fun t => Fstar.fc a |t| := (Fstar.continuous_fc ha).comp continuous_abs
  have hl : IntervalIntegrable (fun t => Real.log |t|) volume (-a) a := by
    simpa only [Real.log_abs] using intervalIntegral.intervalIntegrable_log' (a := -a) (b := a)
  have hl2 : IntervalIntegrable (fun t => Real.log |t| ^ 2) volume (-a) a := by
    simpa only [Real.log_abs] using intervalIntegrable_log_sq (-a) a
  have h : IntervalIntegrable (fun t => Fstar.fc a |t| ^ 2 - (2 / (6 * π)) * (Fstar.fc a |t| *
    Real.log |t|)
      + (1 / (6 * π))^2 * Real.log |t| ^ 2) volume (-a) a :=
    (((hfc.pow 2).intervalIntegrable _ _).sub ((hl.continuousOn_mul hfc.continuousOn).const_mul
      _)).add
      (hl2.const_mul _)
  refine h.congr_ae ((rhoA_ae_eq ha).mono fun t h => ?_)
  dsimp only; rw [h]; ring

/-- `t ↦ log|x − t| · rhoA a t` is integrable on `(-a, a)` for every `x`. -/
theorem intervalIntegrable_log_mul_rhoA (ha : 0 < a) (x : ℝ) :
    IntervalIntegrable (fun t => Real.log |x - t| * rhoA a t) volume (-a) a := by
  refine IntervalIntegrable.mono_fun' (((intervalIntegrable_log_abs_sq x (-a) a).add
    (intervalIntegrable_rhoA_sq ha)).div_const 2) ?_ (Filter.Eventually.of_forall fun t => ?_)
  · have := measurable_rhoA a
    have hm : Measurable (fun t => Real.log |x - t| * rhoA a t) := by fun_prop
    exact hm.aestronglyMeasurable
  · simp only [Real.norm_eq_abs, abs_mul]
    nlinarith [sq_nonneg (abs (Real.log |x - t|) - abs (rhoA a t)), sq_abs (Real.log |x - t|),
      sq_abs (rhoA a t)]

theorem intervalIntegrable_abs_log_mul_rhoA (ha : 0 < a) (x : ℝ) :
    IntervalIntegrable (fun t => abs (Real.log |x - t|) * rhoA a t) volume (-a) a := by
  refine IntervalIntegrable.mono_fun' (((intervalIntegrable_log_abs_sq x (-a) a).add
    (intervalIntegrable_rhoA_sq ha)).div_const 2) ?_ (Filter.Eventually.of_forall fun t => ?_)
  · have := measurable_rhoA a
    have hm : Measurable (fun t => abs (Real.log |x - t|) * rhoA a t) := by fun_prop
    exact hm.aestronglyMeasurable
  · simp only [Real.norm_eq_abs, abs_mul, abs_abs]
    nlinarith [sq_nonneg (abs (Real.log |x - t|) - abs (rhoA a t)), sq_abs (Real.log |x - t|),
      sq_abs (rhoA a t)]

end
end Zeta32.Analytic.EnergyI

end
