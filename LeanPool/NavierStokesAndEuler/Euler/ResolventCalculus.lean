/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-! Local boundedness, continuity, and differentiation derived from an exact operator resolvent
  identity. -/

noncomputable section

namespace EulerResolventCalculus

open scoped Topology

variable {R : Type*} [NormedRing R]

/-- An exact resolvent identity gives a local inverse bound without assuming a uniform inverse estimate. -/
theorem local_norm_bound (P Q M N : R) (hres : Q - P = Q * ((M - N) * P))
    (hsmall : ‖M - N‖ * ‖P‖ ≤ 1 / 2) : ‖Q‖ ≤ 2 * ‖P‖ := by
  have hresnorm : ‖Q - P‖ ≤ ‖Q‖ * (‖M - N‖ * ‖P‖) := by
    rw [hres]
    exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg Q))
  have hhalf : ‖Q - P‖ ≤ ‖Q‖ / 2 :=
    hresnorm.trans ((mul_le_mul_of_nonneg_left hsmall (norm_nonneg Q)).trans_eq (by ring))
  have htri : ‖Q‖ ≤ ‖Q - P‖ + ‖P‖ := by
    calc
      ‖Q‖ = ‖Q - P + P‖ := by rw [sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  linarith

/-- The exact resolvent identity yields a local Lipschitz estimate using only the reference inverse norm. -/
theorem local_difference_bound (P Q M N : R) (hres : Q - P = Q * ((M - N) * P))
    (hsmall : ‖M - N‖ * ‖P‖ ≤ 1 / 2) :
    ‖Q - P‖ ≤ (2 * ‖P‖ ^ 2) * ‖M - N‖ := by
  have hQ := local_norm_bound P Q M N hres hsmall
  rw [hres]
  calc
    ‖Q * ((M - N) * P)‖ ≤ ‖Q‖ * (‖M - N‖ * ‖P‖) :=
      (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg Q))
    _ ≤ (2 * ‖P‖) * (‖M - N‖ * ‖P‖) :=
      mul_le_mul_of_nonneg_right hQ (mul_nonneg (norm_nonneg _) (norm_nonneg P))
    _ = _ := by ring

/-- Continuity of the coefficient operator implies continuity of actual resolvents, with no separate inverse-continuity assumption. -/
theorem continuousAt_of_resolvent {α : Type*} [TopologicalSpace α] (P M : α → R)
    (hres : ∀ s t, P s - P t = P s * ((M t - M s) * P t)) (t : α)
    (hM : ContinuousAt M t) : ContinuousAt P t := by
  have hdelta : Filter.Tendsto (fun s => ‖M t - M s‖) (𝓝 t) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (hM.const_sub (M t)).norm
  have hsmall : ∀ᶠ s in 𝓝 t, ‖M t - M s‖ * ‖P t‖ ≤ 1 / 2 := by
    have hlim : Filter.Tendsto (fun s => ‖M t - M s‖ * ‖P t‖) (𝓝 t) (𝓝 0) := by
      simpa only [zero_mul] using hdelta.mul_const ‖P t‖
    exact (hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))).mono fun _ h => h.le
  have hbound : ∀ᶠ s in 𝓝 t, ‖P s - P t‖ ≤ (2 * ‖P t‖ ^ 2) * ‖M t - M s‖ :=
    hsmall.mono fun s hs => local_difference_bound (P t) (P s) (M t) (M s) (hres s t) hs
  have hlim : Filter.Tendsto (fun s => (2 * ‖P t‖ ^ 2) * ‖M t - M s‖) (𝓝 t) (𝓝 0) := by
    simpa only [mul_zero] using hdelta.const_mul (2 * ‖P t‖ ^ 2)
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) hbound hlim

variable [NormedAlgebra ℝ R]

/-- Differentiating the actual resolvent identity gives the inverse derivative, after continuity has been proved from the same identity. -/
theorem hasDerivAt_of_resolvent (P M : ℝ → R)
    (hres : ∀ s t, P s - P t = P s * ((M t - M s) * P t))
    (t : ℝ) (M' : R) (hM : HasDerivAt M M' t) :
    HasDerivAt P (-(P t * (M' * P t))) t := by
  have hP := continuousAt_of_resolvent P M hres t hM.continuousAt
  have hshift : Filter.Tendsto (fun r => P (t + r)) (𝓝[≠] 0) (𝓝 (P t)) := by
    have h : Filter.Tendsto (fun r => P (t + r)) (𝓝 (0 : ℝ)) (𝓝 (P t)) := by
      have hadd : Filter.Tendsto (fun r : ℝ => t + r) (𝓝 (0 : ℝ)) (𝓝 t) := by
        simpa only [add_zero, id_eq] using (tendsto_const_nhds.add (Filter.tendsto_id :
          Filter.Tendsto id (𝓝 (0 : ℝ)) (𝓝 0)))
      exact hP.tendsto.comp hadd
    exact h.mono_left nhdsWithin_le_nhds
  have hneg : Filter.Tendsto (fun r : ℝ => r⁻¹ • (M t - M (t + r))) (𝓝[≠] 0) (𝓝 (-M')) := by
    simpa only [← smul_neg, neg_sub] using hM.tendsto_slope_zero.neg
  have hlim : Filter.Tendsto (fun r : ℝ => P (t + r) * ((r⁻¹ • (M t - M (t + r))) * P t))
      (𝓝[≠] 0) (𝓝 (P t * ((-M') * P t))) := hshift.mul (hneg.mul tendsto_const_nhds)
  apply hasDerivAt_iff_tendsto_slope_zero.mpr
  have he : (fun r : ℝ => r⁻¹ • (P (t + r) - P t)) =
      fun r : ℝ => P (t + r) * ((r⁻¹ • (M t - M (t + r))) * P t) := by
    funext r
    rw [hres]
    simp only [smul_mul_assoc, mul_smul_comm]
  rw [he]
  simpa only [neg_mul, mul_neg] using hlim

end EulerResolventCalculus
