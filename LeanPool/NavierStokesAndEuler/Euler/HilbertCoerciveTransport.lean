/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Positivity.Finset
import Mathlib.Tactic.Measurability.Init

/-!
# Coercive operator transport between Hilbert models

This elementary operator lemma applies equally to mean and transverse
displacement spaces, including forms with nonlocal initial-trace terms.
-/

@[expose] public section


noncomputable section

namespace EulerHilbertCoerciveTransport

open InnerProductSpace ContinuousLinearMap

variable {V W : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [CompleteSpace W]

/-- Pull a genuine bounded operator back along a bounded linear coordinate map. -/
def transportedOperator (D : V →L[ℝ] W) (A : W →L[ℝ] W) : V →L[ℝ] V :=
  D.adjoint.comp (A.comp D)

/-- The transported bilinear form is exactly the original form on the image. -/
theorem transportedOperator_inner (D : V →L[ℝ] W) (A : W →L[ℝ] W) (u v : V) :
    ⟪transportedOperator D A u, v⟫_ℝ = ⟪A (D u), D v⟫_ℝ := by
  exact adjoint_inner_left D v (A (D u))

/-- Coercivity transports using only a proved lower bound for the coordinate map. -/
theorem transportedOperator_coercive (D : V →L[ℝ] W) (A : W →L[ℝ] W)
    (a d : ℝ) (ha : 0 ≤ a)
    (hA : ∀ w, a * ‖w‖ ^ 2 ≤ ⟪A w, w⟫_ℝ)
    (hD : ∀ v, d * ‖v‖ ^ 2 ≤ ‖D v‖ ^ 2) (v : V) :
    (a*d) * ‖v‖^2 ≤ ⟪transportedOperator D A v, v⟫_ℝ := by
  rw [transportedOperator_inner]
  calc
    (a*d) * ‖v‖^2 = a * (d * ‖v‖^2) := by ring
    _ ≤ a * ‖D v‖^2 := mul_le_mul_of_nonneg_left (hD v) ha
    _ ≤ ⟪A (D v), D v⟫_ℝ := hA (D v)

/-- The transported forcing is the actual adjoint pullback. -/
theorem transported_forcing_inner (D : V →L[ℝ] W) (f : W) (v : V) :
    ⟪D.adjoint f, v⟫_ℝ = ⟪f, D v⟫_ℝ := adjoint_inner_left D v f

end EulerHilbertCoerciveTransport
