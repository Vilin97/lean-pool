/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledRay
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.MeanValue

/-! Tangency is preserved by the actual ray and projected velocity ODEs. -/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit InnerProductSpace ContinuousLinearMap

theorem tangentPairing_hasDerivWithinAt (M : Space →L[ℝ] Space)
    {r w : ℝ → Space} {t : ℝ} {S : Set ℝ}
    (hr : HasDerivWithinAt r (-M.adjoint (r t)) S t)
    (hw : HasDerivWithinAt w (-M (w t) + (2 * ⟪r t, M (w t)⟫_ℝ / ‖r t‖ ^ 2) • r t) S t)
    (hr0 : r t ≠ 0) : HasDerivWithinAt (fun s => ⟪r s,w s⟫_ℝ) 0 S t := by
  apply (hr.inner ℝ hw).congr_deriv
  simp only [inner_add_right, inner_neg_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, inner_neg_left, adjoint_inner_left]
  have hn := pow_ne_zero 2 (norm_ne_zero_iff.mpr hr0)
  field_simp
  ring

theorem rescaled_tangentPairing_zero (M : ℝ → Space →L[ℝ] Space)
    {r w : ℝ → Space} {t₀ a ε T : ℝ} {S : Set ℝ}
    (hmap : MapsTo (physicalTime t₀ a ε) (Icc 0 T) S)
    (hr : ∀ t ∈ S, HasDerivWithinAt r (-(M t).adjoint (r t)) S t)
    (hw : ∀ t ∈ S, HasDerivWithinAt w (-(M t) (w t) +
      (2 * ⟪r t, (M t) (w t)⟫_ℝ / ‖r t‖ ^ 2) • r t) S t)
    (hr0 : ∀ τ ∈ Icc 0 T, r (physicalTime t₀ a ε τ) ≠ 0)
    (h0 : ⟪r t₀, w t₀⟫_ℝ = 0) :
    ∀ τ ∈ Icc 0 T, ⟪r (physicalTime t₀ a ε τ),w (physicalTime t₀ a ε τ)⟫_ℝ = 0 := by
  have hderiv : ∀ τ ∈ Icc 0 T, HasDerivWithinAt
      (fun s => ⟪r (physicalTime t₀ a ε s),w (physicalTime t₀ a ε s)⟫_ℝ) 0 (Icc 0 T) τ := by
    intro τ hτ
    have ht := hmap hτ
    simpa only [zero_mul, Function.comp_def] using
      (tangentPairing_hasDerivWithinAt (M (physicalTime t₀ a ε τ)) (hr _ ht)
        (hw _ ht) (hr0 τ hτ)).comp τ
          (physicalTime_hasDerivAt t₀ a ε τ).hasDerivWithinAt hmap
  have hh := norm_image_sub_le_of_norm_deriv_le_segment' hderiv
    (fun _ _ => (by simp : ‖(0:ℝ)‖ ≤ 0))
  intro τ hτ
  have h := hh τ hτ
  simpa only [physicalTime, mul_zero, add_zero, h0, sub_zero, zero_mul,
    norm_le_zero_iff] using h

end EulerPacketMovingFrame
