/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# Torsion-free Koszul formula for the Levi-Civita correction

This file records the exact metric-defect formula for the difference between
an arbitrary torsion-free background connection and its Levi-Civita
correction.  The argument order follows `CovariantDerivative.difference`:
the first vector is differentiated and the second is the direction.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Bundle Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I 2 M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "⟪" x ", " y "⟫" => inner ℝ x y

/-- For a torsion-free background connection, the Levi-Civita correction is
the Koszul polarization of its metric defect.  In the conventional notation
`A(u, v) = ∇ᵍ_u v - ∇bar_u v`, the left side is `2 g(A(u,v), w)`.

Here `leviCivitaCorrection x v u` uses the repository's order `(v, u)`, where
`v` is the differentiated vector and `u` is the direction. -/
theorem leviCivitaCorrection_inner_of_isTorsionFree
    (cov : CovariantDerivative I E TM) (hTorsionFree : cov.IsTorsionFree)
    (x : M) (v u w : TM x) :
    2 * ⟪cov.leviCivitaCorrection x v u, w⟫ =
      cov.metricDefect x v w u + cov.metricDefect x u w v - cov.metricDefect x u v w := by
  have h := cov.leviCivitaCorrection_inner x v u w
  rw [hTorsionFree] at h
  simpa using h

/-- The difference from a background connection to the connection constructed
by `leviCivitaConnection` is exactly the explicit correction. -/
theorem leviCivitaConnection_difference_apply_eq_leviCivitaCorrection
    (cov : CovariantDerivative I E TM) (x : M) (v u : TM x) :
    (CovariantDerivative.difference cov.leviCivitaConnection cov x v) u =
      cov.leviCivitaCorrection x v u := by
  rw [difference_apply_eq_extend_tm cov.leviCivitaConnection cov v]
  simp [leviCivitaConnection, CovariantDerivative.addOneForm]

/-- The exact background-metric-defect formula for
`∇ᵍ - ∇bar`, when the background connection is torsion-free. -/
theorem leviCivitaConnection_difference_inner_of_isTorsionFree
    (cov : CovariantDerivative I E TM) (hTorsionFree : cov.IsTorsionFree)
    (x : M) (v u w : TM x) :
    2 * ⟪(CovariantDerivative.difference cov.leviCivitaConnection cov x v) u, w⟫ =
      cov.metricDefect x v w u + cov.metricDefect x u w v - cov.metricDefect x u v w := by
  rw [leviCivitaConnection_difference_apply_eq_leviCivitaCorrection]
  exact cov.leviCivitaCorrection_inner_of_isTorsionFree hTorsionFree x v u w

end CovariantDerivative
