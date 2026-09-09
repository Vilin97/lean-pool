/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-! Uniqueness of the actual scalar comparison equation, including its state. -/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketGrowth EulerPacketExistence

/-- The scalar equation and its initial state determine both state
components on the forward half-line.  This lets independently constructed
neighbor comparisons use one common reference. -/
theorem equation30_state_eq_of_initial
    {σ : ℝ} {Z Z₁ W W₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4)
    (hZ : ∀ t, 0 ≤ t → HasDerivAt Z (Z₁ t) t)
    (hW : ∀ t, 0 ≤ t → HasDerivAt W (W₁ t) t)
    (hfluxZ : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*Z₁ s)
      (2*(1-σ^2*(σ^2*t^2))*Z t) t)
    (hfluxW : ∀ t, 0 ≤ t → HasDerivAt (fun s => (1+(σ^2*s^2)^2)*W₁ s)
      (2*(1-σ^2*(σ^2*t^2))*W t) t)
    (hi : Z 0 = W 0) (hi₁ : Z₁ 0 = W₁ 0) :
    ∀ t, 0 ≤ t → Z t = W t ∧ Z₁ t = W₁ t := by
  have hσ2 : σ^2 ≤ 1 := by nlinarith only [hσ, hσsmall]
  obtain ⟨F, F₁, hF0, hF₁0, hF, hfluxF⟩ := equation30_exists_global (sq_nonneg σ) hσ2 1 0
  intro t ht
  have hdiff : ∀ s ∈ Icc 0 t,
      HasDerivAt (fun x => Z x-W x) (Z₁ s-W₁ s) s := by
    intro s hs
    exact (hZ s hs.1).sub (hW s hs.1)
  have hfluxdiff : ∀ s ∈ Icc 0 t,
      HasDerivAt (fun x => (1+(σ^2*x^2)^2)*(Z₁ x-W₁ x))
        (2*(1-σ^2*(σ^2*s^2))*(Z s-W s)) s := by
    intro s hs
    convert! (hfluxZ s hs.1).sub (hfluxW s hs.1) using 1
    · ext x
      dsimp only [Pi.sub_apply]
      ring
    · ring
  have hb := equation30_relative_propagator hσ hσsmall (le_max_left 1 t)
    (by norm_num : (0:ℝ) ≤ 0) ht (le_max_right 1 t)
    (fun s _ => hF s) (fun s _ => hfluxF s) hF0 hF₁0 hdiff hfluxdiff
  simp only [hi, hi₁, sub_self, abs_zero, add_zero, mul_zero] at hb
  have hz : |Z t-W t| = 0 := by linarith only [hb, abs_nonneg (Z t-W t), abs_nonneg (Z₁ t-W₁ t)]
  have hz₁ : |Z₁ t-W₁ t| = 0 := by linarith only [hb, abs_nonneg (Z t-W t), abs_nonneg (Z₁ t-W₁ t)]
  exact ⟨sub_eq_zero.mp (abs_eq_zero.mp hz), sub_eq_zero.mp (abs_eq_zero.mp hz₁)⟩

end EulerPacketMovingFrame
