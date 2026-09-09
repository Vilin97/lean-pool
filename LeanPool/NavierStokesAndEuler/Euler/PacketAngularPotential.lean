/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.PacketCrossProduct
public import LeanPool.NavierStokesAndEuler.Euler.AnglePrimitiveBounds

@[expose] public section

/-! The vector potential Q of a tangent, mean-zero, periodic high coefficient. -/

noncomputable section

namespace EulerPacketAngularPotential

open EulerSmoothLimit EulerPacketCrossProduct EulerAngleMeanZeroPrimitive
  MeasureTheory Set InnerProductSpace

def potential (P : ℝ) (m : Space) (A : ℝ → Space) : ℝ → Space :=
  primitive P (fun θ => potentialMultiplier m (A θ))

theorem potential_hasDerivAt (P : ℝ) (m : Space) (A : ℝ → Space)
    (hA : Continuous A) (θ : ℝ) :
    HasDerivAt (potential P m A) (potentialMultiplier m (A θ)) θ :=
  primitive_hasDerivAt P _ ((potentialMultiplier m).continuous.comp hA) θ

/-- The actual angular derivative recovers A after crossing with m. -/
theorem cross_deriv_potential (P : ℝ) (m : Space) (hm : m ≠ 0) (A : ℝ → Space)
    (hA : Continuous A) (htan : ∀ θ, ⟪m,A θ⟫_ℝ=0) (θ : ℝ) :
    cross m (deriv (potential P m A) θ)=A θ := by
  rw [(potential_hasDerivAt P m A hA θ).deriv]
  exact cross_potentialMultiplier m (A θ) hm (htan θ)

theorem potential_periodic (P : ℝ) (m : Space) (A : ℝ → Space)
    (hA : Continuous A) (hper : Function.Periodic A P)
    (hmean : ∫ θ in 0..P, A θ=0) : Function.Periodic (potential P m A) P := by
  apply primitive_periodic P _ ((potentialMultiplier m).continuous.comp hA)
  · intro θ
    exact congrArg (potentialMultiplier m) (hper θ)
  · simp only [Function.comp_def]
    rw [(potentialMultiplier m).intervalIntegral_comp_comm (hA.intervalIntegrable 0 P),
      hmean, map_zero]

theorem potential_mean_zero (P : ℝ) (hP : P ≠ 0) (m : Space) (A : ℝ → Space)
    (hA : Continuous A) : (∫ θ in 0..P, potential P m A θ)=0 :=
  primitive_mean_zero P hP _ ((potentialMultiplier m).continuous.comp hA)

theorem potential_zero (P : ℝ) (m : Space) :
    potential P m (fun _ => 0)=fun _ => 0 := by
  funext θ
  simp [potential, primitive, rawPrimitive]

/-- The angular construction creates no values at labels where the whole input vanishes. -/
theorem potential_vanishes (P : ℝ) (m : Space) (A : ℝ → Space) (hA : ∀ θ, A θ=0) :
    ∀ θ, potential P m A θ=0 := by
  have h : A=fun _ => 0 := funext hA
  rw [h, potential_zero]
  exact fun _ => rfl

theorem potential_bound (P M : ℝ) (hP : 0 < P) (hM : 0 ≤ M) (m : Space)
    (A : ℝ → Space) (hA : ∀ θ ∈ Icc 0 P, ‖A θ‖ ≤ M) (θ : ℝ) (hθ : θ ∈ Icc 0 P) :
    ‖potential P m A θ‖ ≤ 2*P*(‖potentialMultiplier m‖*M) := by
  apply primitive_bound P (‖potentialMultiplier m‖*M) hP
    (mul_nonneg (norm_nonneg _) hM) _ _ θ hθ
  intro s hs
  exact ((potentialMultiplier m).le_opNorm (A s)).trans
    (mul_le_mul_of_nonneg_left (hA s hs) (norm_nonneg _))

end EulerPacketAngularPotential
