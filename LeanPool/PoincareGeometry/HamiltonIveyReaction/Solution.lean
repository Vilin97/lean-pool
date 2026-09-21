/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.HamiltonIveyReaction.Reaction

/-! # Solution -/

@[expose] public noncomputable section

namespace HamiltonIveyChallenge

/-- Closed Mathlib-facing statement, repeated on the Solution side for Comparator. -/
def completeStatement : Prop :=
  let scalar := fun lambda mu nu : ℝ ↦ lambda + mu + nu
  let defect := fun K t lambda mu nu : ℝ ↦
    scalar lambda mu nu / (-nu) - Real.log (-nu) + 3 +
      Real.log (K / (1 + K * t))
  ∀ (K T : ℝ) (lambda mu nu : ℝ → ℝ),
    0 < K → 0 ≤ T →
    (∀ t ∈ Set.Icc 0 T,
      HasDerivAt lambda (lambda t ^ 2 + mu t * nu t) t) →
    (∀ t ∈ Set.Icc 0 T,
      HasDerivAt mu (mu t ^ 2 + lambda t * nu t) t) →
    (∀ t ∈ Set.Icc 0 T,
      HasDerivAt nu (nu t ^ 2 + lambda t * mu t) t) →
    (∀ t ∈ Set.Icc 0 T, mu t ≤ lambda t) →
    (∀ t ∈ Set.Icc 0 T, nu t ≤ mu t) →
    (∀ t ∈ Set.Icc 0 T, nu t < 0) →
    -K ≤ nu 0 →
    ∀ t ∈ Set.Icc 0 T, 0 ≤ defect K t (lambda t) (mu t) (nu t)

theorem hamiltonIveyODEPinching : completeStatement := by
  dsimp only [completeStatement]
  intro K T lambda mu nu hK hT hlambda hmu hnuODE hlm hmn hnuNeg hnuLower
  exact HamiltonIveyReaction.hamiltonIvey_ode_pinching hK hlambda hmu hnuODE
    hlm hmn hnuNeg hT hnuLower

end HamiltonIveyChallenge
