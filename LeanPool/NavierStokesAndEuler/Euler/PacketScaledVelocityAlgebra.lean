/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.EulerProof

@[expose] public section

/-! Exact finite-dimensional algebra of the source ray/velocity scaling. -/

noncomputable section


namespace EulerPacketMovingFrame

open EulerPacketRay

def velocityScale (ε : ℝ) (i : Fin 3) : ℝ := if i = 1 then 1 else ε

theorem velocityScale_ne_zero {ε : ℝ} (hε : ε ≠ 0) (i : Fin 3) : velocityScale ε i ≠ 0 := by
  unfold velocityScale
  split_ifs
  · exact one_ne_zero
  · exact hε

theorem scaling_denominator (s₀ ε : ℝ) (R : Fin 3 → ℝ) :
    (∑ j : Fin 3, (s₀*rayScale ε j*R j)^2) =
      s₀^2 * rayDenominator ε (R 0) (R 1) (R 2) := by
  norm_num [Fin.sum_univ_three, rayScale, rayDenominator, Fin.ext_iff]
  ring

theorem scaling_flux {a : ℝ} (ha : a ≠ 0) (s₀ ε : ℝ)
    (M : Fin 3 → Fin 3 → ℝ) (R V : Fin 3 → ℝ) :
    (∑ i : Fin 3, (s₀*rayScale ε i*R i) *
      (∑ j : Fin 3, M i j*(velocityScale ε j*V j))) =
      s₀*a*velocityNumerator (scaledVelocityEntry a ε M)
        (R 0) (R 1) (R 2) (V 0) (V 1) (V 2) := by
  norm_num [Fin.sum_univ_three, rayScale, velocityScale, scaledVelocityEntry,
    velocityNumerator, Fin.ext_iff]
  field_simp

theorem scaling_pairing (s₀ ε : ℝ) (R V : Fin 3 → ℝ) :
    (∑ i : Fin 3, (s₀*rayScale ε i*R i)*(velocityScale ε i*V i)) =
      s₀*ε*(R 0*V 0+R 1*V 1+R 2*V 2) := by
  norm_num [Fin.sum_univ_three, rayScale, velocityScale, Fin.ext_iff]
  ring

theorem scaling_velocity_rate {a ε s₀ D : ℝ}
    (ha : a ≠ 0) (hε : ε ≠ 0) (hs₀ : s₀ ≠ 0) (hD : D ≠ 0)
    (M S : Fin 3 → Fin 3 → ℝ) (R V : Fin 3 → ℝ) (J : ℝ) (i : Fin 3) :
    ((-(∑ j : Fin 3, (M i j+S i j)*(velocityScale ε j*V j)) +
      (2*(s₀*a*J)/(s₀^2*D))*(s₀*rayScale ε i*R i))*(ε/a))/velocityScale ε i =
      -(∑ j : Fin 3, scaledVelocityEntry a ε (fun i j => M i j+S i j) i j * V j) +
        2*(rayScale ε i)^2*R i*J/D := by
  fin_cases i <;>
    norm_num [Fin.sum_univ_three, velocityScale, rayScale, scaledVelocityEntry, Fin.ext_iff] <;>
    field_simp

def scaledVelocityRhs (A C : Fin 3 → Fin 3 → ℝ) (ε : ℝ) (R V : Fin 3 → ℝ) (i : Fin 3) : ℝ :=
  -(∑ j : Fin 3, C i j*V j) + 2*(rayScale ε i)^2*R i *
    velocityNumerator A (R 0) (R 1) (R 2) (V 0) (V 1) (V 2) /
      rayDenominator ε (R 0) (R 1) (R 2)

theorem thirdVelocity_of_pairing (R V : Fin 3 → ℝ) (hN : R 2 ≠ 0)
    (hRV : R 0*V 0+R 1*V 1+R 2*V 2 = 0) :
    V 2 = velocityThird (R 0) (R 1) (R 2) (V 0) (V 1) := by
  unfold velocityThird
  apply (eq_div_iff hN).2
  linarith only [hRV]

theorem scaledVelocityRhs_first (A C : Fin 3 → Fin 3 → ℝ) (ε : ℝ) (R V : Fin 3 → ℝ)
    (hV : V 2 = velocityThird (R 0) (R 1) (R 2) (V 0) (V 1)) :
    scaledVelocityRhs A C ε R V 0 = velocityFirstRhs A C ε (R 0) (R 1) (R 2) (V 0) (V 1) := by
  norm_num [scaledVelocityRhs, velocityFirstRhs, rayScale, Fin.sum_univ_three, Fin.ext_iff, hV]

theorem scaledVelocityRhs_second (A C : Fin 3 → Fin 3 → ℝ) (ε : ℝ) (R V : Fin 3 → ℝ)
    (hV : V 2 = velocityThird (R 0) (R 1) (R 2) (V 0) (V 1)) :
    scaledVelocityRhs A C ε R V 1 = velocitySecondRhs A C ε (R 0) (R 1) (R 2) (V 0) (V 1) := by
  norm_num [scaledVelocityRhs, velocitySecondRhs, rayScale, Fin.sum_univ_three, Fin.ext_iff, hV]

end EulerPacketMovingFrame
