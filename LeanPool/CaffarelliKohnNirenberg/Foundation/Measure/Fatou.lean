/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol, Lean Pool contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol, Lean Pool contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Passing nonnegative integral bounds to an almost-everywhere limit
-/

public section

open MeasureTheory Filter
open scoped ENNReal Topology

namespace CKN

/-- Fatou's lemma transfers convergent upper bounds on nonnegative integrals. -/
theorem integral_le_of_ae_tendsto_nonneg {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} {g : α → ℝ} {bounds : ℕ → ℝ} {bound : ℝ}
    (hf : ∀ n, Integrable (f n) μ) (hfn : ∀ n, 0 ≤ᵐ[μ] f n) (hg : 0 ≤ᵐ[μ] g)
    (hlimit : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    (hbound : 0 ≤ bound) (hboundLimit : Tendsto bounds atTop (𝓝 bound))
    (hupper : ∀ n, ∫ x, f n x ∂μ ≤ bounds n) : ∫ x, g x ∂μ ≤ bound := by
  by_cases hgi : Integrable g μ
  · have hfatou := lintegral_liminf_le' (u := (atTop : Filter ℕ))
      (fun n => (hf n).aestronglyMeasurable.aemeasurable.ennreal_ofReal)
    have hpointwise : (fun x => liminf (fun n => ENNReal.ofReal (f n x)) atTop) =ᵐ[μ]
        fun x => ENNReal.ofReal (g x) := by
      filter_upwards [hlimit] with x hx
      exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq
    rw [lintegral_congr_ae hpointwise,
      ← ofReal_integral_eq_lintegral_ofReal hgi hg] at hfatou
    have hintegral : (fun n => ∫⁻ x, ENNReal.ofReal (f n x) ∂μ) =
        fun n => ENNReal.ofReal (∫ x, f n x ∂μ) := by
      funext n
      exact (ofReal_integral_eq_lintegral_ofReal (hf n) (hfn n)).symm
    rw [hintegral] at hfatou
    have hmono := Filter.liminf_le_liminf (f := (atTop : Filter ℕ))
      (Filter.Eventually.of_forall fun n => ENNReal.ofReal_le_ofReal (hupper n))
    have hlimitBound := (ENNReal.continuous_ofReal.tendsto _).comp hboundLimit
    exact (ENNReal.ofReal_le_ofReal_iff hbound).mp
      (hfatou.trans (hmono.trans_eq hlimitBound.liminf_eq))
  · rw [integral_undef hgi]
    exact hbound

end CKN
