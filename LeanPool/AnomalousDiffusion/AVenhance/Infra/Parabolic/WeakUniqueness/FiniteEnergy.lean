/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.ODE.Linear.Energy

/-!
# Energy identity for finite-dimensional integral paths

Once the separated weak tests have identified the Fourier coefficient path as an integral path,
its finite-dimensional energy balance follows from the Hilbert-space chain rule.
-/

@[expose] public section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace AVenhance.Infra.Parabolic.WeakUniqueness

/-- Energy balance for an integral path forced by an integrable vector field. -/
theorem integral_path_energy_identity
    {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    [InnerProductSpace ℝ E]
    {a b : ℝ} {hab : a ≤ b} {u q : ℝ → E} {u₀ : E}
    (hu : AVenhance.Infra.ODE.IsLinearIntegralSolution
      (fun _ : ℝ => (0 : E →L[ℝ] E)) (fun t => -q t) u₀ a b u)
    (hq : IntervalIntegrable q volume a b) :
    ∫ t in a..b, 2 * inner ℝ (u t) (q t) =
      ‖u a‖ ^ 2 - ‖u b‖ ^ 2 := by
  have hrhs : IntervalIntegrable
      (AVenhance.Infra.ODE.linearRhs (fun _ : ℝ => (0 : E →L[ℝ] E))
        (fun t => -q t) u) volume a b := by
    unfold AVenhance.Infra.ODE.linearRhs
    simp only [zero_apply, zero_add]
    exact hq.neg
  have hid := hu.energy_identity hab hrhs
  have hneg :
      (∫ t in a..b, 2 * inner ℝ (u t) (-q t)) =
        -(∫ t in a..b, 2 * inner ℝ (u t) (q t)) := by
    rw [show (fun t => 2 * inner ℝ (u t) (-q t)) =
        fun t => -(2 * inner ℝ (u t) (q t)) by
      funext t
      rw [inner_neg_right]
      ring]
    exact intervalIntegral.integral_neg
  have hid' :
      (∫ t in a..b, 2 * inner ℝ (u t) (-q t)) = ‖u b‖ ^ 2 - ‖u a‖ ^ 2 := by
    simpa [AVenhance.Infra.ODE.linearRhs, zero_apply] using hid
  rw [hneg] at hid'
  linarith

end AVenhance.Infra.Parabolic.WeakUniqueness
