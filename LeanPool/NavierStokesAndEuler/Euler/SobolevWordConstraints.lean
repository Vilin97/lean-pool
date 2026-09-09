/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevWordBlocks
public import LeanPool.NavierStokesAndEuler.Euler.DivergenceFreeHeat

@[expose] public section

/-! The actual lifted gradient and divergence constraints persist under every available strong
  derivative word. -/

noncomputable section

namespace EulerSobolevWordConstraints

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerSobolevWordBlocks
  EulerDivergenceFreeHeat

variable (period : ℝ) [Fact (0 < period)]

/-- The genuine orthogonal lifted gradient projection acting on the complete Sobolev scale. -/
def sobolevGradientProjection (q : ℕ) (κ : ℝ) (m : Vector3) :
    SobolevSpace period q →L[ℝ] SobolevSpace period q :=
  liftOperator period q (gradientProjection period κ m)
    (fun a f => (gradientProjection_translation period κ m a f).symm)

/-- Its zeroth coordinate is exactly the original L² orthogonal projection. -/
theorem sobolevGradientProjection_value {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q) :
    value period (sobolevGradientProjection period q κ m u) = gradientProjection period κ m (value
      period u) := rfl

/-- The actual Sobolev gradient projection acts on each genuine derivative coordinate. -/
theorem sobolevGradientProjection_word {q n : ℕ} (hn : n ≤ q) (κ : ℝ) (m : Vector3)
    (u : SobolevSpace period q) (w : Fin n → Fin 4) :
    word period (sobolevGradientProjection period q κ m u) hn w =
      gradientProjection period κ m (word period u hn w) := rfl

/-- A divergence-free Sobolev field has zero Sobolev gradient projection, including all derivatives. -/
theorem sobolevGradientProjection_zero {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q)
    (hu : value period u ∈ divergenceFreeSpace period κ m) :
    sobolevGradientProjection period q κ m u = 0 := by
  apply value_injective period
  rw [sobolevGradientProjection_value]
  exact (gradientEvaluation_zero_iff period κ m u).mpr hu

/-- Every actual derivative word of a divergence-free field remains divergence-free. -/
theorem word_divergenceFree {q n : ℕ} (hn : n ≤ q) (κ : ℝ) (m : Vector3)
    (u : SobolevSpace period q) (hu : value period u ∈ divergenceFreeSpace period κ m)
    (w : Fin n → Fin 4) : word period u hn w ∈ divergenceFreeSpace period κ m := by
  apply (gradientSpace period κ m).orthogonalProjectionOnto_eq_zero_iff.mp
  apply Subtype.ext
  change gradientProjection period κ m (word period u hn w) = 0
  rw [← sobolevGradientProjection_word period hn κ m u w,
    sobolevGradientProjection_zero period κ m u hu]
  rfl

/-- A genuine gradient field is fixed by the Sobolev gradient projection. -/
theorem sobolevGradientProjection_self {q : ℕ} (κ : ℝ) (m : Vector3) (u : SobolevSpace period q)
    (hu : value period u ∈ gradientSpace period κ m) :
    sobolevGradientProjection period q κ m u = u := by
  apply value_injective period
  rw [sobolevGradientProjection_value]
  exact (gradientSpace period κ m).starProjection_eq_self_iff.mpr hu

/-- Every actual derivative word of a lifted pressure gradient remains in the lifted gradient space. -/
theorem word_gradient {q n : ℕ} (hn : n ≤ q) (κ : ℝ) (m : Vector3)
    (u : SobolevSpace period q) (hu : value period u ∈ gradientSpace period κ m)
    (w : Fin n → Fin 4) : word period u hn w ∈ gradientSpace period κ m := by
  apply (gradientSpace period κ m).starProjection_eq_self_iff.mp
  change gradientProjection period κ m (word period u hn w) = word period u hn w
  rw [← sobolevGradientProjection_word period hn κ m u w,
    sobolevGradientProjection_self period κ m u hu]

end EulerSobolevWordConstraints
