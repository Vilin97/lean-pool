/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Hom

/-! # Covariant differentiation along actual tangent sections

Regularity is derived from mathlib's connection regularity class by evaluating
the resulting hom-bundle section. No curvature identities are assumed.
-/

@[expose] public noncomputable section
open Bundle FiberBundle
open scoped Manifold ContDiff

namespace AlmostSchur

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The actual covariant derivative of `Z` in the direction `X`. -/
def covariantAlong (cov : CovariantDerivative I E TM) (X Z : Π x, TM x) :
    Π x, TM x := fun x ↦ cov Z x (X x)

/-- A Cᵏ connection applied along a Cᵏ field to a Cᵏ⁺¹ field gives a Cᵏ field. -/
theorem contMDiff_covariantAlong (k : ℕ∞ω)
    [ContMDiffVectorBundle k E TM I]
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative k]
    {X Z : Π x, TM x}
    (hX : ContMDiff I (I.prod 𝓘(ℝ, E)) k (T% X))
    (hZ : ContMDiff I (I.prod 𝓘(ℝ, E)) (k + 1) (T% Z)) :
    ContMDiff I (I.prod 𝓘(ℝ, E)) k (T% (covariantAlong cov X Z)) := by
  have hc := (CovariantDerivative.ContMDiffCovariantDerivative.contMDiff
    (cov := cov)).contMDiff hZ.contMDiffOn
  exact contMDiffOn_univ.mp (hc.clm_bundle_apply hX.contMDiffOn)

end AlmostSchur
