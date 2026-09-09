/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LpDerivativeMap
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Dominated convergence in genuine L², also for Banach-valued representatives. -/

noncomputable section

namespace EulerLpConvergence

open MeasureTheory Filter
open scoped Topology ENNReal

variable {X V : Type*} [MeasurableSpace X] [NormedAddCommGroup V] (μ : Measure X)

theorem norm_sq_eq_integral (u : Lp V 2 μ) : ‖u‖^2 = ∫ x, ‖u x‖^2 ∂μ := by
  rw [Lp.norm_def, MemLp.eLpNorm_eq_integral_rpow_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞) (Lp.memLp u)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  rw [ENNReal.toReal_ofReal (Real.rpow_nonneg (integral_nonneg (fun _ => sq_nonneg _)) _)]
  rw [inv_eq_one_div, ← Real.sqrt_eq_rpow, Real.sq_sqrt (integral_nonneg (fun _ => sq_nonneg _))]

/-- Domination of literal representatives controls convergence of their actual L² classes. -/
theorem tendsto_of_dominated {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    (U : ι → Lp V 2 μ) (v : Lp V 2 μ) (F : ι → X → V) (g : X → V)
    (hU : ∀ i, U i =ᵐ[μ] F i) (hv : v =ᵐ[μ] g)
    (M : X → ℝ) (hM : MemLp M 2 μ)
    (hbound : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖F i x - g x‖ ≤ M x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun i => F i x) l (𝓝 (g x))) :
    Tendsto U l (𝓝 v) := by
  let q : ι → X → ℝ := fun i x => ‖F i x-g x‖^2
  have hm (i : ι) : AEStronglyMeasurable (q i) μ := by
    exact (((Lp.aestronglyMeasurable (U i)).congr (hU i)).sub
      ((Lp.aestronglyMeasurable v).congr hv)).norm.pow 2
  have hb : ∀ᶠ i in l, ∀ᵐ x ∂μ, ‖q i x‖ ≤ M x ^ 2 := by
    filter_upwards [hbound] with i hi
    filter_upwards [hi] with x hx
    change ‖‖F i x-g x‖^2‖ ≤ _
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) hx 2
  have hi : Integrable (fun x => M x ^ 2) μ := by
    simpa only [Real.norm_eq_abs, sq_abs] using hM.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hl : ∀ᵐ x ∂μ, Tendsto (fun i => q i x) l (𝓝 (0 : ℝ)) := by
    filter_upwards [hlim] with x hx
    simpa only [q, sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      ((hx.sub_const (g x)).norm.pow 2)
  have hI : Tendsto (fun i => ∫ x, q i x ∂μ) l (𝓝 (0 : ℝ)) := by
    simpa only [integral_zero] using tendsto_integral_filter_of_dominated_convergence
      (fun x => M x^2) (Eventually.of_forall hm) hb hi hl
  have he (i : ι) : ‖U i-v‖^2 = ∫ x, q i x ∂μ := by
    rw [norm_sq_eq_integral]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (U i) v, hU i, hv] with x hs hfx hgx
    simp only [Pi.sub_apply] at hs
    rw [hs, hfx, hgx]
  have hsq : Tendsto (fun i => ‖U i-v‖^2) l (𝓝 (0 : ℝ)) :=
    hI.congr' (Eventually.of_forall (fun i => (he i).symm))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hroot

end EulerLpConvergence
