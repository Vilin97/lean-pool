/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.SeparationContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.NoSelection.Scales

/-! # Separation at one level, with the time and scale bookkeeping

`level_sep`: classical solutions `θ₁, θ₂` with the same admissible drift `Ψ`, the same cosine-type
datum, and diffusivities `κ₁ ≤ κ₂ ∈ [3κ₁, 5κ₁]` that are `≍ E^{β+γ}` are separated at the time
`t = c′ E^{2-β}` by `≳ E^δ ‖θ₀‖`. -/

@[expose] public section

open MeasureTheory Homogenization

noncomputable section

namespace AVenhance.Infra.FullTheorem.NoSel

open AVenhance AVenhance.Infra.FullTheorem

/-- The body of `SeparationContract` with the constant `c₀` a parameter. -/
def SepWith (c₀ : ℝ) : Prop :=
    ∀ Ψ : ℝ → Vec 2 → ℝ, IsAdmissibleStream Ψ →
    ∀ Lu : ℝ, 0 ≤ Lu →
      (∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ∀ i j : Fin 2,
        |spaceGrad (fun y => streamVel Ψ t y i) x j| ≤ Lu) →
    ∀ θ₀ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) θ₀ → IsZ2Periodic θ₀ →
    ∀ lam : ℝ, 0 ≤ lam →
      gradNormSq (spaceGrad θ₀) = lam * l2NormSq θ₀ →
      hessNormSq θ₀ ≤ lam * gradNormSq (spaceGrad θ₀) →
    ∀ κ₁ κ₂ : ℝ, 0 < κ₁ → 3 * κ₁ ≤ κ₂ → κ₂ ≤ 5 * κ₁ →
    ∀ t : ℝ, 0 < t → t ≤ 1 → Lu * t ≤ c₀ → κ₂ * t * lam ≤ c₀ →
    ∀ θ₁ θ₂ : ℝ → Vec 2 → ℝ,
      IsClassicalSol (streamVel Ψ) κ₁ (fun _ _ => 0) θ₀ θ₁ →
      IsClassicalSol (streamVel Ψ) κ₂ (fun _ _ => 0) θ₀ θ₂ →
      κ₁ * t * lam * Real.sqrt (l2NormSq θ₀) ≤
        2 * (Real.sqrt (l2NormSq (θ₁ t)) - Real.sqrt (l2NormSq (θ₂ t)))

theorem sepWith_of_contract (h : SeparationContract) : ∃ c₀ : ℝ, 0 < c₀ ∧ SepWith c₀ := h

theorem level_sep {c₀ Cb k0 K0 c' E β γ δ c₁ lam κ₁ κ₂ : ℝ} {Ψ : ℝ → Vec 2 → ℝ}
    (hS : SepWith c₀) (hΨ : IsAdmissibleStream Ψ) (hCb : 0 ≤ Cb)
    (hLu : ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ x, ∀ i j : Fin 2,
      |spaceGrad (fun y => streamVel Ψ t y i) x j| ≤ Cb * E ^ (β - 2))
    {θ₀ : Vec 2 → ℝ} (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) (hper : IsZ2Periodic θ₀)
    (hlam0 : 0 ≤ lam) (hG : gradNormSq (spaceGrad θ₀) = lam * l2NormSq θ₀)
    (hH : hessNormSq θ₀ ≤ lam * gradNormSq (spaceGrad θ₀))
    (hE : 0 < E) (hE1 : E ≤ 1) (hβ2 : β ≤ 2) (hc₁ : 0 < c₁)
    (hc' : 0 < c') (hc'1 : c' ≤ 1) (hCbc : Cb * c' ≤ c₀) (hKc : K0 * c' ≤ c₀)
    (hK0 : 0 ≤ K0) (hk0 : 0 ≤ k0)
    (hκ₁ : k0 * E ^ (β + γ) ≤ κ₁) (hκ₁pos : 0 < κ₁) (hκ₂ : κ₂ ≤ K0 * E ^ (β + γ))
    (h3 : 3 * κ₁ ≤ κ₂) (h5 : κ₂ ≤ 5 * κ₁)
    (hlam1 : lam * E ^ (2 + γ) ≤ 1) (hlam2 : E ^ δ ≤ c₁ ^ 2 * (lam * E ^ (2 + γ)))
    {θ₁ θ₂ : ℝ → Vec 2 → ℝ}
    (hs1 : IsClassicalSol (streamVel Ψ) κ₁ (fun _ _ => 0) θ₀ θ₁)
    (hs2 : IsClassicalSol (streamVel Ψ) κ₂ (fun _ _ => 0) θ₀ θ₂) :
    k0 * c' / 2 * (E ^ δ / c₁ ^ 2) * Real.sqrt (l2NormSq θ₀) ≤
      Real.sqrt (l2NormSq (θ₁ (c' * E ^ (2 - β)))) -
        Real.sqrt (l2NormSq (θ₂ (c' * E ^ (2 - β)))) := by
  set t := c' * E ^ (2 - β) with ht
  have hEp : 0 < E ^ (2 - β) := Real.rpow_pos_of_pos hE _
  have ht0 : 0 < t := mul_pos hc' hEp
  have hEp1 : E ^ (2 - β) ≤ 1 := Real.rpow_le_one hE.le hE1 (by linarith)
  have ht1 : t ≤ 1 := by
    calc t ≤ 1 * 1 := mul_le_mul hc'1 hEp1 hEp.le zero_le_one
      _ = 1 := one_mul 1
  have hEβ : E ^ (β - 2) * E ^ (2 - β) = 1 := by
    rw [← Real.rpow_add hE]; simp
  have hexp : E ^ (β + γ) * E ^ (2 - β) = E ^ (2 + γ) := by
    rw [← Real.rpow_add hE]; congr 1; ring
  have hLt : Cb * E ^ (β - 2) * t ≤ c₀ := by
    calc Cb * E ^ (β - 2) * t = Cb * c' * (E ^ (β - 2) * E ^ (2 - β)) := by rw [ht]; ring
      _ = Cb * c' := by rw [hEβ, mul_one]
      _ ≤ c₀ := hCbc
  have hκ₂0 : 0 ≤ κ₂ := by linarith
  have hEg : 0 ≤ E ^ (β + γ) := Real.rpow_nonneg hE.le _
  have hkl : κ₂ * t * lam ≤ c₀ := by
    have h1 : κ₂ * t * lam ≤ K0 * E ^ (β + γ) * t * lam := by
      gcongr
    have h2 : K0 * E ^ (β + γ) * t * lam = K0 * c' * (lam * E ^ (2 + γ)) := by
      rw [ht, ← hexp]; ring
    have h4 : K0 * c' * (lam * E ^ (2 + γ)) ≤ K0 * c' * 1 :=
      mul_le_mul_of_nonneg_left hlam1 (mul_nonneg hK0 hc'.le)
    calc κ₂ * t * lam ≤ _ := h1
      _ = _ := h2
      _ ≤ K0 * c' * 1 := h4
      _ ≤ c₀ := by rw [mul_one]; exact hKc
  have hsep := hS Ψ hΨ _ (mul_nonneg hCb (Real.rpow_nonneg hE.le _)) hLu θ₀ hθ₀ hper lam hlam0 hG hH
    κ₁ κ₂ hκ₁pos h3 h5 t ht0 ht1 hLt hkl θ₁ θ₂ hs1 hs2
  have hN0 : 0 ≤ Real.sqrt (l2NormSq θ₀) := Real.sqrt_nonneg _
  have hq : E ^ δ / c₁ ^ 2 ≤ lam * E ^ (2 + γ) := by
    rw [div_le_iff₀ (by positivity)]; linarith
  have hlow : k0 * c' * (E ^ δ / c₁ ^ 2) ≤ κ₁ * t * lam := by
    calc k0 * c' * (E ^ δ / c₁ ^ 2) ≤ k0 * c' * (lam * E ^ (2 + γ)) :=
          mul_le_mul_of_nonneg_left hq (mul_nonneg hk0 hc'.le)
      _ = k0 * E ^ (β + γ) * t * lam := by rw [ht, ← hexp]; ring
      _ ≤ κ₁ * t * lam := by gcongr
  have := mul_le_mul_of_nonneg_right hlow hN0
  linarith

end AVenhance.Infra.FullTheorem.NoSel
