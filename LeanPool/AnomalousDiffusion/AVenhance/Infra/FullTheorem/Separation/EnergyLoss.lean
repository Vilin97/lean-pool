/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.Gradient

/-! # Energy loss of a classical solution on `[0,t]`

`‖θ₀‖² - ‖θ(t)‖² = 2κ ∫_0^t ‖∇θ‖²` lies in `[2κ t (9/10) G₀, 2κ t (11/10) G₀]`, `G₀ = ‖∇θ₀‖²`. -/

@[expose] public section

open Homogenization MeasureTheory Set
open AVenhance.Infra.Section4

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

open AVenhance

variable {Ψ θ : ℝ → Vec 2 → ℝ} {κ Lu lam t : ℝ} {θ₀ : Vec 2 → ℝ}

theorem energy_identity (hΨ : IsAdmissibleStream Ψ)
    (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) (ht : 0 < t) :
    wEnergy [] θ 0 - wEnergy [] θ t = 2 * κ * ∫ s in (0 : ℝ)..t, gradE θ s := by
  have hcont : ContinuousOn (fun s => -2 * κ * gradE θ s) (Icc 0 t) :=
    continuousOn_const.mul ((gradE_continuousOn hsol).mono fun s hs => hs.1)
  have hderiv : ∀ s ∈ Ioo (0 : ℝ) t, HasDerivAt (wEnergy [] θ) (-2 * κ * gradE θ s) s :=
    fun s hs => hasDerivAt_E hΨ hsol hs.1
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.le
    (wEnergy_continuousOn hsol.1 [] ht.le) hderiv
    (hcont.intervalIntegrable_of_Icc ht.le)
  rw [intervalIntegral.integral_const_mul] at h
  linarith

theorem energy_loss_bounds (hΨ : IsAdmissibleStream Ψ)
    (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) (hκ : 0 < κ) (hLu0 : 0 ≤ Lu)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hLu : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x i k, |spaceGrad (fun y => streamVel Ψ s y k) x i| ≤ Lu)
    (hLt : Lu * t ≤ 1 / 10000) (hkl : κ * t * lam ≤ 1 / 10000)
    (hinit : hessE θ 0 ≤ lam * gradE θ 0) :
    2 * κ * t * ((9 / 10) * gradE θ 0) ≤ wEnergy [] θ 0 - wEnergy [] θ t ∧
      wEnergy [] θ 0 - wEnergy [] θ t ≤ 2 * κ * t * ((11 / 10) * gradE θ 0) := by
  have hb := gradE_two_sided hΨ hsol hκ hLu0 ht ht1 hLu hLt hkl hinit
  have hGc : ContinuousOn (gradE θ) (Icc 0 t) :=
    (gradE_continuousOn hsol).mono fun s hs => hs.1
  have hint : IntervalIntegrable (gradE θ) MeasureTheory.volume 0 t :=
    hGc.intervalIntegrable_of_Icc ht.le
  rw [energy_identity hΨ hsol ht]
  have hlow : ∫ s in (0 : ℝ)..t, (9 / 10) * gradE θ 0 ≤ ∫ s in (0 : ℝ)..t, gradE θ s :=
    intervalIntegral.integral_mono_on ht.le intervalIntegrable_const hint
      (fun s hs => (hb s hs).1)
  have hup : ∫ s in (0 : ℝ)..t, gradE θ s ≤ ∫ s in (0 : ℝ)..t, (11 / 10) * gradE θ 0 :=
    intervalIntegral.integral_mono_on ht.le hint intervalIntegrable_const
      (fun s hs => (hb s hs).2)
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hlow hup
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hlow (by positivity : 0 ≤ 2 * κ)]
  · nlinarith [mul_le_mul_of_nonneg_left hup (by positivity : 0 ≤ 2 * κ)]

end AVenhance.Infra.FullTheorem.Separation
