/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketScaledVelocity
public import LeanPool.NavierStokesAndEuler.Euler.Foundations.PacketBridge
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
The actual scaled velocity supplies the first two equations and the scalar
flux equation used in amplification.  Only the first two transport rows are
relevant; the auxiliary third row in the scalar estimate is filled explicitly.
-/

@[expose] public section


noncomputable section


namespace EulerPacketMovingFrame

open Set EulerSmoothLimit EulerPacketNormalizedPrimary EulerPacketRay
  EulerPacketBridge InnerProductSpace

/-- A harmless third-row extension of a two-row transport matrix. -/
def firstTwoRows (C : Fin 3 → Fin 3 → ℝ) (i j : Fin 3) : ℝ :=
  if i = 0 then C 0 j else C 1 j

theorem velocityFirstRhs_firstTwoRows (A C : Fin 3 → Fin 3 → ℝ)
    (ε P Q N U V : ℝ) :
    velocityFirstRhs A (firstTwoRows C) ε P Q N U V =
      velocityFirstRhs A C ε P Q N U V := by
  simp [velocityFirstRhs, firstTwoRows]

theorem velocitySecondRhs_firstTwoRows (A C : Fin 3 → Fin 3 → ℝ)
    (ε P Q N U V : ℝ) :
    velocitySecondRhs A (firstTwoRows C) ε P Q N U V =
      velocitySecondRhs A C ε P Q N U V := by
  simp [velocitySecondRhs, firstTwoRows]

/-- The scalar error estimate needs no assumption on the physical third
transport row. -/
theorem velocity_rhs_error_firstTwo
    {A C : Fin 3 → Fin 3 → ℝ} {Θ e ε β P Q N P₀ Q₀ U V : ℝ}
    (hΘ : 1 ≤ Θ) (he : 0 ≤ e) (hε : 0 ≤ ε) (hεe : ε ≤ e)
    (hsmall : 10000 * e * Θ ^ 5 ≤ 1) (hβ : |β| ≤ 1)
    (hA : ∀ i j, |A i j - idealVelocityEntry β i j| ≤ 3 * e)
    (hC : ∀ j, |C 0 j - idealUnprojectedEntry 0 j| ≤ 5 * e ∧
      |C 1 j - idealUnprojectedEntry 1 j| ≤ 5 * e)
    (hP₀ : |P₀| ≤ Θ ^ 2) (hQ₀ : |Q₀| ≤ 2 * Θ ^ 2)
    (hP : |P - P₀| ≤ 800 * e * Θ ^ 5)
    (hQ : |Q - Q₀| ≤ 800 * e * Θ ^ 5)
    (hN : |N - 1| ≤ 800 * e * Θ ^ 5) :
    |velocityFirstRhs A C ε P Q N U V -
        (-2 * V + 2 * P₀ * ((P₀ + β) * V + Q₀ * U) / (1 + P₀ ^ 2))| +
      |velocitySecondRhs A C ε P Q N U V + U| ≤
        200000 * e * Θ ^ 12 * (|U| + |V|) := by
  have hC' : ∀ i j, |firstTwoRows C i j - idealUnprojectedEntry i j| ≤ 5 * e := by
    intro i j
    fin_cases i
    · simpa [firstTwoRows] using (hC j).1
    · simpa [firstTwoRows] using (hC j).2
    · simpa [firstTwoRows, idealUnprojectedEntry] using (hC j).2
  simpa only [velocityFirstRhs_firstTwoRows, velocitySecondRhs_firstTwoRows] using
    velocity_rhs_error hΘ he hε hεe hsmall hβ hA hC' hP₀ hQ₀ hP hQ hN

/-- The actual tangency constraint removes the third scaled coordinate. -/
theorem scaledVelocity_firstTwo_hasDerivWithinAt (B M : Space →L[ℝ] Space)
    {m v r w : ℝ → Space} {s₀ t₀ a ε τ : ℝ} {S U : Set ℝ}
    (ha : a ≠ 0) (hε : ε ≠ 0) (hs₀ : s₀ ≠ 0)
    (hmap : MapsTo (physicalTime t₀ a ε) U S)
    (hm : HasDerivWithinAt m (-B.adjoint (m (physicalTime t₀ a ε τ))) S (physicalTime t₀ a ε τ))
    (hv : HasDerivWithinAt v (-B (v (physicalTime t₀ a ε τ)) +
      (2 * ⟪m (physicalTime t₀ a ε τ), B (v (physicalTime t₀ a ε τ))⟫_ℝ /
        ‖m (physicalTime t₀ a ε τ)‖ ^ 2) • m (physicalTime t₀ a ε τ)) S (physicalTime t₀ a ε τ))
    (hw : HasDerivWithinAt w (-M (w (physicalTime t₀ a ε τ)) +
      (2 * ⟪r (physicalTime t₀ a ε τ), M (w (physicalTime t₀ a ε τ))⟫_ℝ /
        ‖r (physicalTime t₀ a ε τ)‖ ^ 2) • r (physicalTime t₀ a ε τ)) S (physicalTime t₀ a ε τ))
    (hm0 : m (physicalTime t₀ a ε τ) ≠ 0) (hv0 : v (physicalTime t₀ a ε τ) ≠ 0)
    (hmv : ⟪m (physicalTime t₀ a ε τ), v (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hr0 : r (physicalTime t₀ a ε τ) ≠ 0)
    (hrw : ⟪r (physicalTime t₀ a ε τ), w (physicalTime t₀ a ε τ)⟫_ℝ = 0)
    (hN : scaledRay m v r s₀ t₀ a ε τ 2 ≠ 0) :
    let R := scaledRay m v r s₀ t₀ a ε τ
    let V := scaledVelocity m v w t₀ a ε τ
    let A := scaledAction M m v a ε (physicalTime t₀ a ε τ)
    let C := scaledTransport B M m v a ε (physicalTime t₀ a ε τ)
    HasDerivWithinAt (fun σ => scaledVelocity m v w t₀ a ε σ 0)
      (velocityFirstRhs A C ε (R 0) (R 1) (R 2) (V 0) (V 1)) U τ ∧
    HasDerivWithinAt (fun σ => scaledVelocity m v w t₀ a ε σ 1)
      (velocitySecondRhs A C ε (R 0) (R 1) (R 2) (V 0) (V 1)) U τ := by
  have hthird := thirdVelocity_of_pairing _ _ hN
    (scaled_pairing_zero m v r w hs₀ hε hm0 hv0 hmv hrw)
  constructor
  · have h := scaledVelocity_hasDerivWithinAt B M ha hε hs₀ hmap hm hv hw hm0 hv0 hmv hr0 0
    rw [scaledVelocityRhs_first _ _ _ _ _ hthird] at h
    exact h
  · have h := scaledVelocity_hasDerivWithinAt B M ha hε hs₀ hmap hm hv hw hm0 hv0 hmv hr0 1
    rw [scaledVelocityRhs_second _ _ _ _ _ hthird] at h
    exact h

/-- The flux identity is valid with the actual one-sided endpoint derivatives
of packet paths, as well as in the interior. -/
theorem velocity_scalar_flux_within
    {β t u₁ v₁ : ℝ} {U V : ℝ → ℝ} {S : Set ℝ}
    (hU : HasDerivWithinAt U u₁ S t) (hV : HasDerivWithinAt V v₁ S t) :
    HasDerivWithinAt V (-U t + (v₁ + U t)) S t ∧
    HasDerivWithinAt (fun s => (1 + (β * s ^ 2) ^ 2) * (-U s))
      (2 * (1 - β * (β * t ^ 2)) * V t + (1 + (β * t ^ 2) ^ 2) *
        (-u₁ + idealVelocityFirst β t (U t) (V t))) S t := by
  refine ⟨hV.congr_deriv (by ring), ?_⟩
  have hD : HasDerivAt (fun s : ℝ => 1 + (β * s ^ 2) ^ 2) (4 * β ^ 2 * t ^ 3) t := by
    convert! ((((hasDerivAt_id t).pow 2).const_mul β).pow 2).const_add 1 using 1
    simp only [Pi.pow_apply, id_eq]
    ring
  apply (hD.hasDerivWithinAt.mul hU.neg).congr_deriv
  have hden : 1 + (β * t ^ 2) ^ 2 ≠ 0 := by positivity
  dsimp [idealVelocityFirst]
  field_simp
  ring

end EulerPacketMovingFrame
