/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-! Relative growth of the primary scalar reference dominates zero slope. -/

noncomputable section


namespace EulerPacketMovingFrame

open Set EulerPacketGrowth

theorem equation30_slope_ratio_dominates
    {σ lam s t : ℝ} {F F₁ Z Z₁ : ℝ → ℝ}
    (hσ : 0 < σ) (hσsmall : σ ≤ 1/4) (hlam : 0 ≤ lam)
    (hF : ∀ x, 0 ≤ x → HasDerivAt F (F₁ x) x)
    (hZ : ∀ x, 0 ≤ x → HasDerivAt Z (Z₁ x) x)
    (hfluxF : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1+(σ^2*u^2)^2)*F₁ u)
      (2*(1-σ^2*(σ^2*x^2))*F x) x)
    (hfluxZ : ∀ x, 0 ≤ x → HasDerivAt (fun u => (1+(σ^2*u^2)^2)*Z₁ u)
      (2*(1-σ^2*(σ^2*x^2))*Z x) x)
    (hF0 : F 0 = 1) (hF₁0 : F₁ 0 = 0) (hZ0 : Z 0 = 1) (hZ₁0 : Z₁ 0 = lam)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    F t/F s ≤ Z t/Z s := by
  have hFp := equation30_global_positive hσ hσsmall hF hfluxF hF0 (by rw [hF₁0])
  have hZp := equation30_global_positive hσ hσsmall hZ hfluxZ hZ0 (by rw [hZ₁0]; exact hlam)
  have ht : 0 ≤ t := hs.trans hst
  let D : ℝ → ℝ := fun x => 1+(σ^2*x^2)^2
  have hquotient : ∀ x ∈ Icc 0 t,
      HasDerivAt (fun u => Z u/F u) (lam/(D x*(F x)^2)) x := by
    have hh := quotient_derivative_of_flux
      (D := D) (c := fun x => 2*(1-σ^2*(σ^2*x^2)))
      (fun x (hx : x ∈ Icc 0 t) => hF x hx.1)
      (fun x hx => hZ x hx.1) (fun x hx => hfluxF x hx.1) (fun x hx => hfluxZ x hx.1)
      (fun _ _ => by dsimp [D]; positivity)
      (fun x hx => ne_of_gt (hFp x hx.1))
    intro x hx
    simpa only [hF0, hF₁0, hZ₁0, D, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul,
      add_zero, one_mul, sub_zero] using hh x hx
  have hmono : MonotoneOn (fun x => Z x/F x) (Icc 0 t) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc (0:ℝ) t)
      (fun x hx => (hquotient x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hquotient x (interior_subset hx)).hasDerivWithinAt)
    intro x _
    exact div_nonneg hlam (by dsimp [D]; positivity)
  have hr := hmono ⟨hs, hst⟩ ⟨ht, le_rfl⟩ hst
  have hp := (div_le_div_iff₀ (hFp s hs) (hFp t ht)).mp hr
  apply (div_le_div_iff₀ (hFp s hs) (hZp s hs)).mpr
  nlinarith only [hp]

end EulerPacketMovingFrame
