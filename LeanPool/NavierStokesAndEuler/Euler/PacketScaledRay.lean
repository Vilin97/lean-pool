/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketMovingRay
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-! The actual ray in the source time and coordinate scaling. -/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay InnerProductSpace

/-- Physical time, given by `t₀ + (ε/a)*τ`. -/
def physicalTime (t₀ a ε τ : ℝ) : ℝ := t₀ + (ε/a)*τ

theorem physicalTime_hasDerivAt (t₀ a ε τ : ℝ) :
    HasDerivAt (physicalTime t₀ a ε) (ε/a) τ := by
  convert! ((hasDerivAt_id τ).const_mul (ε/a)).const_add t₀ using 1
  simp

theorem rayScale_ne_zero {ε : ℝ} (hε : ε ≠ 0) (i : Fin 3) : rayScale ε i ≠ 0 := by
  unfold rayScale
  split_ifs
  · exact hε
  · exact one_ne_zero

theorem scaledRayRate_algebra {a ε s₀ : ℝ} (ha : a ≠ 0) (hε : ε ≠ 0) (hs₀ : s₀ ≠ 0)
    (M S : Fin 3 → Fin 3 → ℝ) (R : Fin 3 → ℝ) (i : Fin 3) :
    ((-(∑ j : Fin 3, (M j i-S j i)*R j))*(ε/a))/(s₀*rayScale ε i) =
      ∑ j : Fin 3, scaledRayEntry a ε M S i j*(R j/(s₀*rayScale ε j)) := by
  rw [← Finset.sum_neg_distrib, Finset.sum_mul, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  unfold scaledRayEntry
  field_simp [ha, hs₀, rayScale_ne_zero hε i, rayScale_ne_zero hε j]

/-- Scaled ray, given by `movingRay m v r (physicalTime t₀ a ε τ) i / (s₀*rayScale ε i)`. -/
def scaledRay (m v r : ℝ → Space) (s₀ t₀ a ε τ : ℝ) (i : Fin 3) : ℝ :=
  movingRay m v r (physicalTime t₀ a ε τ) i / (s₀*rayScale ε i)

/-- The physical ODE supplies exactly the scaled coefficient matrix whose
entrywise errors are controlled in the existing propagation proof. -/
theorem scaledRay_hasDerivAt (B M : Space →L[ℝ] Space)
    {m v r : ℝ → Space} {s₀ t₀ a ε τ : ℝ}
    (ha : a ≠ 0) (hε : ε ≠ 0) (hs₀ : s₀ ≠ 0)
    (hm : HasDerivAt m (-B.adjoint (m (physicalTime t₀ a ε τ))) (physicalTime t₀ a ε τ))
    (hv : HasDerivAt v (-B (v (physicalTime t₀ a ε τ)) +
      (2 * ⟪m (physicalTime t₀ a ε τ), B (v (physicalTime t₀ a ε τ))⟫_ℝ /
        ‖m (physicalTime t₀ a ε τ)‖ ^ 2) • m (physicalTime t₀ a ε τ)) (physicalTime t₀ a ε τ))
    (hr : HasDerivAt r (-M.adjoint (r (physicalTime t₀ a ε τ))) (physicalTime t₀ a ε τ))
    (hm0 : m (physicalTime t₀ a ε τ) ≠ 0) (hv0 : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0) (i : Fin 3) :
    HasDerivAt (fun σ => scaledRay m v r s₀ t₀ a ε σ i)
      (∑ j : Fin 3, scaledRayEntry a ε
        (frameMatrix M (unit (m (physicalTime t₀ a ε τ))) (unit (v (physicalTime t₀ a ε τ))))
        (frameSkew (frameMatrix B (unit (m (physicalTime t₀ a ε τ))) (unit (v (physicalTime t₀ a ε
            τ)))))
        i j * scaledRay m v r s₀ t₀ a ε τ j) τ := by
  have h := ((movingRay_hasDerivAt B M hm hv hr hm0 hv0 hmv i).comp τ
    (physicalTime_hasDerivAt t₀ a ε τ)).div_const (s₀*rayScale ε i)
  rw [scaledRayRate_algebra ha hε hs₀] at h
  simpa only [scaledRay, Function.comp_def] using h

/-- The same rescaling for actual one-sided time derivatives. -/
theorem scaledRay_hasDerivWithinAt (B M : Space →L[ℝ] Space)
    {m v r : ℝ → Space} {s₀ t₀ a ε τ : ℝ} {S U : Set ℝ}
    (ha : a ≠ 0) (hε : ε ≠ 0) (hs₀ : s₀ ≠ 0)
    (hmap : MapsTo (physicalTime t₀ a ε) U S)
    (hm : HasDerivWithinAt m (-B.adjoint (m (physicalTime t₀ a ε τ))) S (physicalTime t₀ a ε τ))
    (hv : HasDerivWithinAt v (-B (v (physicalTime t₀ a ε τ)) +
      (2 * ⟪m (physicalTime t₀ a ε τ), B (v (physicalTime t₀ a ε τ))⟫_ℝ /
        ‖m (physicalTime t₀ a ε τ)‖ ^ 2) • m (physicalTime t₀ a ε τ)) S (physicalTime t₀ a ε τ))
    (hr : HasDerivWithinAt r (-M.adjoint (r (physicalTime t₀ a ε τ))) S (physicalTime t₀ a ε τ))
    (hm0 : m (physicalTime t₀ a ε τ) ≠ 0) (hv0 : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0) (i : Fin 3) :
    HasDerivWithinAt (fun σ => scaledRay m v r s₀ t₀ a ε σ i)
      (∑ j : Fin 3, scaledRayEntry a ε
        (frameMatrix M (unit (m (physicalTime t₀ a ε τ))) (unit (v (physicalTime t₀ a ε τ))))
        (frameSkew (frameMatrix B (unit (m (physicalTime t₀ a ε τ))) (unit (v (physicalTime t₀ a ε
            τ)))))
        i j * scaledRay m v r s₀ t₀ a ε τ j) U τ := by
  have h := ((movingRay_hasDerivWithinAt B M hm hv hr hm0 hv0 hmv i).comp τ
    (physicalTime_hasDerivAt t₀ a ε τ).hasDerivWithinAt hmap).div_const (s₀*rayScale ε i)
  rw [scaledRayRate_algebra ha hε hs₀] at h
  simpa only [scaledRay, Function.comp_def] using h

end EulerPacketMovingFrame
