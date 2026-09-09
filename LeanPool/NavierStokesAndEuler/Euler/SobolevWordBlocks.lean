/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.SobolevRestriction
public import LeanPool.NavierStokesAndEuler.Euler.SobolevHeat

@[expose] public section

/-! Bounded actual derivative-word blocks on the complete Sobolev scale. -/

noncomputable section

namespace EulerSobolevWordBlocks

open EulerLiftedGradientSpace EulerCylinderSobolevSpace EulerCylinderSobolev
  EulerSobolevHeat EulerGaussianCylinderHeat EulerPressureSpatialRegularity
open scoped Topology NNReal

variable (period : ℝ) [Fact (0 < period)]

/-- A derivative word as an actual bounded map H^(q+n)→Hq, with its literal differentiation order. -/
def wordBlock (q : ℕ) : (n : ℕ) → (Fin n → Fin 4) →
    SobolevSpace period (q + n) →L[ℝ] SobolevSpace period q
  | 0, _ => ContinuousLinearMap.id ℝ (SobolevSpace period q)
  | n + 1, w => (wordBlock q n (Fin.init w)).comp (derivativeOperator period (q + n) (w (Fin.last
    n)))

/-- Actual word differentiation is contractive between the corresponding array norms. -/
theorem wordBlock_bound (q n : ℕ) (w : Fin n → Fin 4) (u : SobolevSpace period (q + n)) :
    ‖wordBlock period q n w u‖ ≤ ‖u‖ := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    exact (ih (Fin.init w) (derivativeOperator period (q + n) (w (Fin.last n)) u)).trans
      (derivativeOperator_bound period (w (Fin.last n)) u)

/-- The field underlying a derivative block is exactly its genuine derivative-word coordinate. -/
theorem wordBlock_value (q n : ℕ) (w : Fin n → Fin 4) (u : SobolevSpace period (q + n)) :
    value period (wordBlock period q n w u) = word period u (by omega : n ≤ q + n) w := by
  induction n with
  | zero =>
    have hw : w = Fin.elim0 := Subsingleton.elim _ _
    subst w
    rfl
  | succ n ih =>
    change value period (wordBlock period q n (Fin.init w)
      (derivativeOperator period (q+n) (w (Fin.last n)) u)) = _
    rw [ih]
    change u.val ⟨⟨n+1, _⟩, Fin.snoc (Fin.init w) (w (Fin.last n))⟩ = _
    rw [Fin.snoc_init_self]
    rfl

/-- Every derivative block commutes with actual cylinder translation. -/
theorem wordBlock_translation (q n : ℕ) (w : Fin n → Fin 4)
    (a : LiftDomain period) (u : SobolevSpace period (q+n)) :
    wordBlock period q n w (sobolevTranslation period (q+n) a u) =
      sobolevTranslation period q a (wordBlock period q n w u) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change wordBlock period q n (Fin.init w)
      (derivativeOperator period (q+n) (w (Fin.last n)) (sobolevTranslation period (q+n+1) a u)) = _
    rw [derivativeOperator_translation, ih]
    rfl

/-- Every actual derivative block commutes with the Gaussian heat semigroup. -/
theorem wordBlock_heat (q n : ℕ) (w : Fin n → Fin 4)
    (v : ℝ≥0) (u : SobolevSpace period (q+n)) :
    wordBlock period q n w (heatOperator period (q+n) v u) =
      heatOperator period q v (wordBlock period q n w u) := by
  apply value_injective period
  rw [wordBlock_value, heatOperator_value, wordBlock_value]
  rfl

/-- Truncating a derivative block agrees with taking the same word after truncating its input. -/
theorem truncate_wordBlock (q n : ℕ) (w : Fin n → Fin 4)
    (u : SobolevSpace period (q+1+n)) :
    truncateOperator period q (wordBlock period (q+1) n w u) =
      wordBlock period q n w (restrictOperator period (by omega : q+n ≤ q+1+n) u) := by
  apply value_injective period
  rw [value_truncateOperator, wordBlock_value, wordBlock_value]
  rfl

end EulerSobolevWordBlocks
