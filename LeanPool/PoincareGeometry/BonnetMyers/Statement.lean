/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Torsion
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Topology.EMetricSpace.Diam
import Mathlib.LinearAlgebra.Trace

/-!+# Bonnet--Myers: independent geometric statement

The connection and curvature are constructed in the conclusion. Curvature is
characterized on all smooth vector fields by the covariant-derivative
commutator, and Ricci is the ordinary linear trace of Z ↦ R(Z,v)v.
The distance and completeness use the supplied smooth metric. No geodesic,
second-variation, compactness, or diameter assertion is an input hypothesis.
The constant is the classical sharp bound; sphere attainment is not selected.
-/

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff ENNReal Topology

namespace BonnetMyersEntry
universe u v w

/-- Complete connected smooth boundaryless finite-dimensional real Riemannian
manifolds with Ricci ≥ (n-1)K g, K > 0 and n ≥ 2 are compact and have induced
extended diameter at most π/√K. The explicit Hausdorff and sigma-compact
assumptions specify the manifold conventions. Every geometric notion used
below is a Mathlib construction or an explicit formula in this definition. -/
def completeStatement : Prop :=
  ∀ {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type v} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [I.Boundaryless] {M : Type w} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
    [SigmaCompactSpace M] [ConnectedSpace M]
    (g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _)),
  letI : IsManifold I 1 M := IsManifold.of_le (I := I) (M := M)
    (n := (∞ : WithTop ℕ∞)) (by decide : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞))
  letI : TopologicalSpace.MetrizableSpace M := Manifold.metrizableSpace I M
  letI : T3Space M := inferInstance
  letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  letI : IsContinuousRiemannianBundle E (TangentSpace I : M → Type _) :=
    ⟨⟨g.inner, g.contMDiff.continuous, by intro x a b; rfl⟩⟩
  letI : EMetricSpace M := EMetricSpace.ofRiemannianMetric I M
  ∃ cov : CovariantDerivative I E (TangentSpace I : M → Type _),
    cov.torsion = 0 ∧
    (∀ (Y Z : Π x : M, TangentSpace I x) (x : M),
      MDiffAt (T% Y) x → MDiffAt (T% Z) x → ∀ a : TangentSpace I x,
      mfderiv I 𝓘(ℝ) (fun y => g.inner y (Y y) (Z y)) x a =
        g.inner x (cov Y x a) (Z x) + g.inner x (Y x) (cov Z x a)) ∧
    ∃ R : Π x : M, TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ]
        TangentSpace I x →L[ℝ] TangentSpace I x,
      (∀ (X Y Z : Π x : M, TangentSpace I x),
        ContMDiff I I.tangent ∞ (T% X) →
        ContMDiff I I.tangent ∞ (T% Y) →
        ContMDiff I I.tangent ∞ (T% Z) → ∀ x,
        R x (X x) (Y x) (Z x) =
          cov (fun y => cov Z y (Y y)) x (X x) -
          cov (fun y => cov Z y (X y)) x (Y x) -
          cov Z x (VectorField.mlieBracket I X Y x)) ∧
      ∀ (K : ℝ), 0 < K → 2 ≤ Module.finrank ℝ E → CompleteSpace M →
        (∀ (x : M) (a : TangentSpace I x),
          (((Module.finrank ℝ E : ℝ) - 1) * K) * g.inner x a a ≤
            LinearMap.trace ℝ (TangentSpace I x)
              { toFun := fun z => R x z a a
                map_add' := by intro z z'; simp
                map_smul' := by intro c z; simp }) →
        CompactSpace M ∧ Metric.ediam (Set.univ : Set M) ≤
          ENNReal.ofReal (Real.pi / Real.sqrt K)

end BonnetMyersEntry
