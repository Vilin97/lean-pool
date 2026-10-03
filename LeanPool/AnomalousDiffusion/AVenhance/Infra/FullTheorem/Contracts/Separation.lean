/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Integration.SeparationContract
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.EnergyLoss
public import LeanPool.AnomalousDiffusion.AVenhance.Infra.FullTheorem.Separation.SqrtStep

/-! # Proof of the separation statement

`separation_contract : SeparationContract` with `c₀ = 1/10000`.  Assembly of the energy-loss bounds
`Separation.energy_loss_bounds` for the two solutions, the gap `E₁ - E₂ ≥ 3.2 κ₁ t λ E₀`
(using `κ₂ ≥ 3 κ₁`), and `Separation.sqrt_gap`. -/

@[expose] public section

open Homogenization MeasureTheory Set
open AVenhance.Infra.Section4

noncomputable section

namespace AVenhance.Infra.FullTheorem.Contracts

open AVenhance AVenhance.Infra.FullTheorem AVenhance.Infra.FullTheorem.Separation

/-- The initial values of the three energies are the corresponding quantities of `θ₀`. -/
theorem initial_energies {Ψ θ : ℝ → Vec 2 → ℝ} {κ : ℝ} {θ₀ : Vec 2 → ℝ}
    (hsol : IsClassicalSol (streamVel Ψ) κ (fun _ _ => 0) θ₀ θ)
    (hθ₀ : ContDiff ℝ (⊤ : ℕ∞) θ₀) :
    gradE θ 0 = gradNormSq (spaceGrad θ₀) ∧ hessE θ 0 = hessNormSq θ₀ ∧
      wEnergy [] θ 0 = l2NormSq θ₀ := by
  have h0 : θ 0 = θ₀ := funext hsol.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · simp only [gradE, wDiss, gradNormSq, h0]
    rfl
  · have hc : ∀ j i : Fin 2, Continuous
        (fun x => (spaceGrad (fun y => spaceGrad θ₀ y i) x j) ^ 2) :=
      fun j i => (cont_word [j, i] hθ₀).pow 2
    have : hessNormSq θ₀ = ∑ i : Fin 2, ∑ j : Fin 2, ∫ x in unitCube,
        (spaceGrad (fun y => spaceGrad θ₀ y i) x j) ^ 2 := by
      unfold hessNormSq
      exact int_sum_sum (φ := fun i j x => (spaceGrad (fun y => spaceGrad θ₀ y i) x j) ^ 2)
        (fun i j => hc j i)
    rw [this, Finset.sum_comm]
    simp only [hessE, wEnergy, h0]
    rfl
  · simp only [wEnergy, l2NormSq, h0]
    rfl

theorem separation_contract : SeparationContract := by
  refine ⟨1 / 10000, by norm_num, ?_⟩
  intro Ψ hΨ Lu hLu0 hLu θ₀ hθ₀ _hper lam hlam hG hH κ₁ κ₂ hκ₁ h3 h5 t ht ht1 hLt hkl θ₁ θ₂
    hs1 hs2
  have hκ₂ : 0 < κ₂ := by linarith
  have hl1 : κ₁ * t * lam ≤ 1 / 10000 := by
    have : κ₁ * t * lam ≤ κ₂ * t * lam :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) ht.le) hlam
    linarith
  obtain ⟨g1, k1, e1⟩ := initial_energies hs1 hθ₀
  obtain ⟨g2, k2, e2⟩ := initial_energies hs2 hθ₀
  have hLu' : ∀ s ∈ Icc (0 : ℝ) 1, ∀ x i k,
      |spaceGrad (fun y => streamVel Ψ s y k) x i| ≤ Lu := fun s hs x i k => hLu s hs x k i
  have hin1 : hessE θ₁ 0 ≤ lam * gradE θ₁ 0 := by rw [k1, g1]; exact hH
  have hin2 : hessE θ₂ 0 ≤ lam * gradE θ₂ 0 := by rw [k2, g2]; exact hH
  have b1 := energy_loss_bounds hΨ hs1 hκ₁ hLu0 ht ht1 hLu' hLt hl1 hin1
  have b2 := energy_loss_bounds hΨ hs2 hκ₂ hLu0 ht ht1 hLu' hLt hkl hin2
  rw [e1, g1] at b1
  rw [e2, g2] at b2
  set E₀ := l2NormSq θ₀ with hE₀
  set E₁ := wEnergy [] θ₁ t with hE₁
  set E₂ := wEnergy [] θ₂ t with hE₂
  have hE0nn : 0 ≤ E₀ := integral_nonneg fun x => sq_nonneg _
  have hE2nn : 0 ≤ E₂ := integral_nonneg fun x => sq_nonneg _
  have hG0 : gradNormSq (spaceGrad θ₀) = lam * E₀ := hG
  rw [hG0] at b1 b2
  have hP : 0 ≤ t * (lam * E₀) := mul_nonneg ht.le (mul_nonneg hlam hE0nn)
  have hκP : 3 * κ₁ * (t * (lam * E₀)) ≤ κ₂ * (t * (lam * E₀)) :=
    mul_le_mul_of_nonneg_right h3 hP
  have hKE : 0 ≤ κ₁ * t * lam * E₀ := by
    have := mul_nonneg hκ₁.le hP
    nlinarith [this]
  have hgap : (16 / 5) * (κ₁ * t * lam) * E₀ ≤ E₁ - E₂ := by
    nlinarith [b1.2, b2.1, hκP]
  have hE1le : E₁ ≤ E₀ := by
    have : 0 ≤ κ₁ * (t * (lam * E₀)) := mul_nonneg hκ₁.le hP
    nlinarith [b1.1, this]
  have hE21 : E₂ ≤ E₁ := by nlinarith [hgap, hKE]
  exact sqrt_gap hE1le hE2nn hE21 (mul_nonneg (mul_nonneg hκ₁.le ht.le) hlam) hgap

end AVenhance.Infra.FullTheorem.Contracts
