/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.BonnetMyers.Curvature

/-!
# The constructed connection and curvature data

This module discharges the differential-geometric part of the conclusion of
`completeStatement`.  The remaining comparison argument is deliberately not
packaged here: it must use the actual metric distance, geodesics, and index
form rather than an assumed diameter lemma.
-/

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry

universe u v w

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [I.Boundaryless]
  {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [SigmaCompactSpace M] [IsManifold I ∞ M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- The supplied smooth metric determines the connection and the actual
curvature tensor used by the comparison argument. -/
noncomputable def constructedCurvature
    (g : ContMDiffRiemannianMetric I ∞ E TM)
    (cov : CovariantDerivative I E TM) [cov.ContMDiffCovariantDerivative 1]
    (x : M) :
    TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x :=
  curvature (cov := cov) x

theorem constructed_connection_data
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    ∃ cov : CovariantDerivative I E TM,
      cov.torsion = 0 ∧
      (∀ (Y Z : Π x : M, TM x) (x : M),
        MDiffAt (T% Y) x → MDiffAt (T% Z) x → ∀ a : TM x,
        mfderiv I 𝓘(ℝ) (fun y ↦ g.inner y (Y y) (Z y)) x a =
          g.inner x (cov Y x a) (Z x) + g.inner x (Y x) (cov Z x a)) ∧
      ∃ R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x,
      (∀ (X Y Z : Π x : M, TM x),
          ContMDiff I I.tangent ∞ (T% X) →
          ContMDiff I I.tangent ∞ (T% Y) →
          ContMDiff I I.tangent ∞ (T% Z) → ∀ x,
          R x (X x) (Y x) (Z x) =
            cov (fun y => cov Z y (Y y)) x (X x) -
            cov (fun y => cov Z y (X y)) x (Y x) -
            cov Z x (VectorField.mlieBracket I X Y x)) := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  let cov : CovariantDerivative I E TM := leviCivita (I := I) (M := M) g
  letI : cov.ContMDiffCovariantDerivative 1 := by
    simpa [cov] using (leviCivitaSmooth (I := I) (M := M) g)
  have hcov : CovariantDerivative.IsLeviCivita cov := by
    simpa [cov] using (leviCivita_isLeviCivita (I := I) (M := M) g)
  let R : Π x : M, TM x →L[ℝ] TM x →L[ℝ] TM x →L[ℝ] TM x :=
    fun x ↦ constructedCurvature (g := g) (cov := cov) x
  refine ⟨cov, hcov.1, ?_, R, ?_⟩
  · intro Y Z x hY hZ a
    exact hcov.2 hY hZ a
  · intro X Y Z hX hY hZ x
    exact curvature_apply_smooth (cov := cov) X Y Z hX hY hZ x

end BonnetMyersEntry
