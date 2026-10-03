/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.Derivs
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.Chain

/-! # Short-time stability of the gradient energy

`(9/10) ‖∇θ₀‖² ≤ ‖∇θ(r)‖² ≤ (11/10) ‖∇θ₀‖²` on `[0,t]`, from the differential inequalities of
`Derivs` and the abstract chain `G_two_sided`. -/

@[expose] public section

open Homogenization MeasureTheory Set
open AVenhance.Infra.Section4

noncomputable section

namespace AVenhance.Infra.FullTheorem.Separation

open AVenhance

variable {Ψ θ : ℝ → Vec 2 → ℝ} {κ Lu lam t : ℝ} {θ₀ : Vec 2 → ℝ}

theorem gradE_continuousOn (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) :
    ContinuousOn (gradE θ) (Ici (0 : ℝ)) :=
  wDiss_continuousOn hsol.1 []

theorem hessE_continuousOn (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ)
    {T : ℝ} (hT : 0 ≤ T) : ContinuousOn (hessE θ) (Icc (0 : ℝ) T) := by
  unfold hessE
  exact continuousOn_finsetSum _ fun j _ => continuousOn_finsetSum _ fun i _ =>
    wEnergy_continuousOn hsol.1 [j, i] hT

theorem gradE_two_sided (hΨ : IsAdmissibleStream Ψ)
    (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ) (hκ : 0 < κ) (hLu0 : 0 ≤ Lu)
    (ht : 0 < t) (ht1 : t ≤ 1)
    (hLu : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x i k, |spaceGrad (fun y => streamVel Ψ s y k) x i| ≤ Lu)
    (hLt : Lu * t ≤ 1 / 10000) (hkl : κ * t * lam ≤ 1 / 10000)
    (hinit : hessE θ 0 ≤ lam * gradE θ 0) :
    ∀ r ∈ Icc (0 : ℝ) t, (9 / 10) * gradE θ 0 ≤ gradE θ r ∧
      gradE θ r ≤ (11 / 10) * gradE θ 0 := by
  have hGc : ContinuousOn (gradE θ) (Icc 0 t) :=
    (gradE_continuousOn hsol).mono fun s hs => hs.1
  have hHc : ContinuousOn (hessE θ) (Icc 0 t) := hessE_continuousOn hsol ht.le
  have hG0 : ∀ r ∈ Icc (0 : ℝ) t, 0 ≤ gradE θ r := fun r hr => gradE_nonneg hsol hr.1
  have hH0 : ∀ r ∈ Icc (0 : ℝ) t, 0 ≤ hessE θ r := fun r _ => hessE_nonneg
  -- derivative information at interior points
  have hGinfo : ∀ s ∈ Ioo (0 : ℝ) t, ∃ C : ℝ, HasDerivAt (gradE θ) (-2 * κ * hessE θ s - 2 * C) s ∧
      |C| ≤ 2 * Lu * gradE θ s := fun s hs =>
    hasDerivAt_G hΨ hsol hs.1 (hLu s ⟨hs.1.le, hs.2.le.trans ht1⟩)
  have hHinfo : ∀ s ∈ Ioo (0 : ℝ) t, ∃ C : ℝ,
      HasDerivAt (hessE θ) (-2 * κ * thirdD θ s - 2 * C) s ∧
      |C| ≤ κ / 2 * thirdD θ s + 4 * (Lu ^ 2 / κ) * gradE θ s + 2 * Lu * hessE θ s :=
    fun s hs => hasDerivAt_H hΨ hsol hs.1 hκ (hLu s ⟨hs.1.le, hs.2.le.trans ht1⟩)
  have hGu : ∀ r ∈ Icc (0 : ℝ) t,
      gradE θ r ≤ gradE θ 0 + ∫ s in (0 : ℝ)..r, 4 * Lu * gradE θ s := by
    intro r hr
    refine le_add_integral_of_deriv_le (f' := deriv (gradE θ)) hr.1
      (hGc.mono (Icc_subset_Icc le_rfl hr.2)) (fun s hs => ?_)
      (continuousOn_const.mul (hGc.mono (Icc_subset_Icc le_rfl hr.2))) (fun s hs => ?_)
    · obtain ⟨C, hC, _⟩ := hGinfo s ⟨hs.1, hs.2.trans_le hr.2⟩
      exact hC.differentiableAt.hasDerivAt
    · obtain ⟨C, hC, hCb⟩ := hGinfo s ⟨hs.1, hs.2.trans_le hr.2⟩
      rw [hC.deriv]
      have h1 := (abs_le.mp hCb).1
      have h2 : 0 ≤ κ * hessE θ s := mul_nonneg hκ.le hessE_nonneg
      nlinarith [h1, h2]
  have hGl : ∀ r ∈ Icc (0 : ℝ) t,
      gradE θ 0 - ∫ s in (0 : ℝ)..r, (2 * κ * hessE θ s + 4 * Lu * gradE θ s) ≤ gradE θ r := by
    intro r hr
    have hGr : ContinuousOn (gradE θ) (Icc 0 r) := hGc.mono (Icc_subset_Icc le_rfl hr.2)
    have hHr : ContinuousOn (hessE θ) (Icc 0 r) := hHc.mono (Icc_subset_Icc le_rfl hr.2)
    have := le_add_integral_of_deriv_le (f := fun s => -gradE θ s)
      (f' := fun s => -deriv (gradE θ) s) (B := fun s => 2 * κ * hessE θ s + 4 * Lu * gradE θ s)
      hr.1 hGr.neg (fun s hs => by
        obtain ⟨C, hC, _⟩ := hGinfo s ⟨hs.1, hs.2.trans_le hr.2⟩
        exact hC.differentiableAt.hasDerivAt.neg)
      ((continuousOn_const.mul hHr).add (continuousOn_const.mul hGr)) (fun s hs => by
        obtain ⟨C, hC, hCb⟩ := hGinfo s ⟨hs.1, hs.2.trans_le hr.2⟩
        rw [hC.deriv]
        have h1 := (abs_le.mp hCb).2
        linarith)
    linarith
  have hHu : ∀ r ∈ Icc (0 : ℝ) t, hessE θ r ≤ hessE θ 0 +
      ∫ s in (0 : ℝ)..r, (12 * Lu * hessE θ s + 8 * (Lu ^ 2 / κ) * gradE θ s) := by
    intro r hr
    have hGr : ContinuousOn (gradE θ) (Icc 0 r) := hGc.mono (Icc_subset_Icc le_rfl hr.2)
    have hHr : ContinuousOn (hessE θ) (Icc 0 r) := hHc.mono (Icc_subset_Icc le_rfl hr.2)
    refine le_add_integral_of_deriv_le (f' := deriv (hessE θ)) hr.1 hHr (fun s hs => ?_)
      ((continuousOn_const.mul hHr).add (continuousOn_const.mul hGr)) (fun s hs => ?_)
    · obtain ⟨C, hC, _⟩ := hHinfo s ⟨hs.1, hs.2.trans_le hr.2⟩
      exact hC.differentiableAt.hasDerivAt
    · obtain ⟨C, hC, hCb⟩ := hHinfo s ⟨hs.1, hs.2.trans_le hr.2⟩
      rw [hC.deriv]
      have h1 := (abs_le.mp hCb).1
      have hD : 0 ≤ thirdD θ s := thirdD_nonneg hsol hs.1.le
      have hHs : 0 ≤ hessE θ s := hessE_nonneg
      have hLH : 0 ≤ Lu * hessE θ s := mul_nonneg hLu0 hHs
      have hκD : 0 ≤ κ * thirdD θ s := mul_nonneg hκ.le hD
      nlinarith [h1, hκD, hLH]
  exact G_two_sided hκ hLu0 ht hLt hkl hGc hHc hG0 hH0 hinit hGu hGl hHu

end AVenhance.Infra.FullTheorem.Separation
