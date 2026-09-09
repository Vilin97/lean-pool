/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationInitial
public import LeanPool.NavierStokesAndEuler.Euler.PacketActivationLipschitz

@[expose] public section

/-! The actual source normal and the same selected terminal coordinate
give the scaled neighboring-label initial errors.  Their constants only
involve coefficient norms, the terminal size, and the stated scaling. -/

noncomputable section

namespace EulerPacketActivationHistory

open Set InnerProductSpace ContinuousLinearMap EulerSmoothLimit
  EulerTransversePacketProvider EulerTransverseActivationSelection
  EulerPacketMovingFrame EulerPacketNormalizedPrimary EulerPacketCrossProduct
  EulerPacketPrimaryFactorization EulerPacketRay

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U] [CompleteSpace U]
  {D : Data U} (τ : ℝ) (hτ : 0 < τ) (hτT : τ < D.T)
  (B : HistoryData (D.initial τ hτ hτT.le))

theorem uncutVelocity_activation_difference (ξ : U) (x y : Space) :
    ‖uncutVelocity τ hτ hτT B ξ τ x-uncutVelocity τ hτ hτT B ξ τ y‖ ≤
      historyLabelDifferenceCost B*‖x-y‖*‖ξ‖ := by
  have hx := uncutVelocity_history τ hτ hτT B ξ ⟨τ,hτ.le,le_rfl⟩ x
  have hy := uncutVelocity_history τ hτ hτT B ξ ⟨τ,hτ.le,le_rfl⟩ y
  change uncutVelocity τ hτ hτT B ξ τ x = _ at hx
  change uncutVelocity τ hτ hτT B ξ τ y = _ at hy
  rw [hx,hy]
  exact labelVelocity_point_difference B x y ξ ⟨τ,hτ.le,le_rfl⟩

theorem actual_scaled_velocity_initial_error
    (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0)
    (ξ : U) (a ε lam : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s 0) τ a ε 0 0 = -lam)
    (hw : scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s 0) τ a ε 0 1 = 1)
    (x : Space) :
    |scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s x) τ a ε 0 1-1|+
      |scaledVelocity m v (fun s => uncutVelocity τ hτ hτT B ξ s x) τ a ε 0 0+lam| ≤
      2*historyLabelDifferenceCost B*‖x‖*‖ξ‖/ε := by
  have hd := uncutVelocity_activation_difference τ hτ hτT B ξ x 0
  rw [sub_zero] at hd
  have he := scaledVelocity_initial_difference_le (m := m) (v := v)
    (x := fun s => uncutVelocity τ hτ hτT B ξ s x)
    (y := fun s => uncutVelocity τ hτ hτT B ξ s 0) (t₀ := τ) (a := a) (ε := ε)
    hm hv hε hε1 hd
  rw [hu,hw,sub_neg_eq_add] at he
  convert! he using 1 <;> ring

omit [CompleteSpace U] in
theorem actual_scaled_ray_initial_error
    (m v : ℝ → Space) (hm : m τ ≠ 0) (hv : v τ ≠ 0) (hmv : ⟪m τ,v τ⟫_ℝ=0)
    (hchoice : D.m₀=activationDirection (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ))))
    (a ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (x : Space) :
    let s₀ := activationRayScale (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
      (cross (unit (m τ)) (unit (v τ)))
    norm3 (scaledRay m v (fun s => D.normal.field (D.clamp s) x) s₀ τ a ε 0 0)
      (scaledRay m v (fun s => D.normal.field (D.clamp s) x) s₀ τ a ε 0 1)
      (scaledRay m v (fun s => D.normal.field (D.clamp s) x) s₀ τ a ε 0 2-1) ≤
      3*‖D.normal.derivative.field‖*‖x‖/(s₀*ε) := by
  dsimp only
  have hs := actual_activation_scaled_ray D m v ⟨τ,hτ.le,hτT.le⟩ a ε hm hv hmv hchoice
  have hn := actual_normal_of_activation_choice D ⟨τ,hτ.le,hτT.le⟩ 0 _ hchoice
  have hd := coefficient_difference D.normal ⟨τ,hτ.le,hτT.le⟩ x 0
  rw [sub_zero,hn] at hd
  have hclamp : D.clamp τ = ⟨τ,hτ.le,hτT.le⟩ := Data.clamp_coe D ⟨τ,hτ.le,hτT.le⟩
  have hd' : ‖D.normal.field (D.clamp τ) x-
      activationRayScale (D.deformationEquiv ⟨τ,hτ.le,hτT.le⟩ 0)
        (cross (unit (m τ)) (unit (v τ))) • cross (unit (m τ)) (unit (v τ))‖ ≤
      ‖D.normal.derivative.field‖*‖x‖ := by rw [hclamp]; exact hd
  convert! scaledRay_initial_error (m := m) (v := v)
    (r := fun s => D.normal.field (D.clamp s) x) (t₀ := τ) (a := a) (ε := ε)
    hs.1 hm hv hmv hε hε1 hd' using 1
  ring

end EulerPacketActivationHistory
