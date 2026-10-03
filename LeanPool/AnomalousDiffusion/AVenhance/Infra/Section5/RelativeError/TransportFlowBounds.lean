/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.GradientDeviation
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Flow.SmoothField

/-! # RelativeError: short-time derivative bounds for the transport flow -/

@[expose] public section

noncomputable section

open Homogenization

namespace AVenhance.Infra.Section5.RelativeError

/-- Grönwall's deviation estimate gives the exponential bound on the full
operator norm of a spatial flow derivative. -/
theorem flow_fderiv_norm_le_exp
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {B : ℝ} (hB : 0 ≤ B)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    (s t : ℝ) (x : Vec 2) :
    ‖fderiv ℝ (fun y => X t y s) x‖ ≤ Real.exp (B * |t - s|) := by
  have hdev := Infra.Flow.flow_fderiv_deviation hb hX hB hDb s t x
  let J := fderiv ℝ (fun y => X t y s) x
  have hdecomp : J = (J - 1) + 1 := by simp [J]
  calc
    ‖J‖ = ‖(J - 1) + 1‖ := congrArg norm hdecomp
    _ ≤ ‖J - 1‖ + ‖(1 : Vec 2 →L[ℝ] Vec 2)‖ := norm_add_le _ _
    _ = ‖J - 1‖ + 1 := by simp
    _ ≤ (Real.exp (B * |t - s|) - 1) + 1 := by
      exact add_le_add hdev le_rfl
    _ = Real.exp (B * |t - s|) := by ring

/-- On a window with `B T ≤ 1`, both the forward and inverse spatial flow
derivatives are bounded by `e`. -/
theorem flow_transport_derivatives_le_exp_one
    {b : ℝ → Vec 2 → Vec 2} (hb : Infra.Flow.SmoothPeriodicField b)
    {X : ℝ → Vec 2 → ℝ → Vec 2} (hX : AVenhance.IsFlow b X)
    {B T : ℝ} (hB : 0 ≤ B) (hBT : B * T ≤ 1)
    (hDb : ∀ r y, ‖Infra.Flow.jointSpatialFDeriv b r y‖ ≤ B)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (x : Vec 2) :
    ‖fderiv ℝ (fun y => X t y 0) x‖ ≤ Real.exp 1 ∧
      ‖fderiv ℝ (fun y => X 0 y t) x‖ ≤ Real.exp 1 := by
  have habs : |t| ≤ T := by
    rw [abs_of_nonneg ht.1]
    exact ht.2
  have hexp : Real.exp (B * |t|) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    exact (mul_le_mul_of_nonneg_left habs hB).trans hBT
  constructor
  · calc
      ‖fderiv ℝ (fun y => X t y 0) x‖ ≤ Real.exp (B * |t - 0|) :=
        flow_fderiv_norm_le_exp hb hX hB hDb 0 t x
      _ = Real.exp (B * |t|) := by rw [sub_zero, abs_of_nonneg ht.1]
      _ ≤ Real.exp 1 := hexp
  · calc
      ‖fderiv ℝ (fun y => X 0 y t) x‖ ≤ Real.exp (B * |0 - t|) :=
        flow_fderiv_norm_le_exp hb hX hB hDb t 0 x
      _ = Real.exp (B * |t|) := by rw [show 0 - t = -t by ring, abs_neg]
      _ ≤ Real.exp 1 := hexp

end AVenhance.Infra.Section5.RelativeError

end
