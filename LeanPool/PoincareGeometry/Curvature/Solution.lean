/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.GaugeTransport

/-! # Solution -/

@[expose] public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace RicciFlow

end RicciFlow

local notation "palomarRegularityTwo" =>
  @OfNat.ofNat (WithTop ENat) (nat_lit 2)
    (@instOfNatAtLeastTwo (WithTop ENat) (nat_lit 2) (@WithTop.natCast ENat ENat.instNatCast)
      RicciFlow.connectionDifferenceTraceOneForm._proof_1)

namespace PoincareCurvature.Palomar

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M]
  [ContMDiffVectorBundle palomarRegularityTwo E (TangentSpace I : M → Type _) I]

theorem curvatureAux_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y σ : Π x : M, TangentSpace I x}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    (φ.pullbackCovariantDerivative cov).curvatureAux X Y σ =
      φ.pullbackVectorField
        (cov.curvatureAux
          (φ.pushforwardVectorField X)
          (φ.pushforwardVectorField Y)
          (φ.pushforwardVectorField σ)) := by
  exact RicciFlow.SmoothSelfDiffeomorph2.curvatureAux_pullbackCovariantDerivative
    φ cov hX hY

theorem curvatureAux_pullbackCovariantDerivative_apply
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y σ : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiff (T% X)) (hY : MDiff (T% Y)) :
    (φ.pullbackCovariantDerivative cov).curvatureAux X Y σ x =
      φ.pullbackTangent x
        (cov.curvatureAux
          (φ.pushforwardVectorField X)
          (φ.pushforwardVectorField Y)
          (φ.pushforwardVectorField σ) (φ x)) := by
  exact RicciFlow.SmoothSelfDiffeomorph2.curvatureAux_pullbackCovariantDerivative_apply
    φ cov hX hY

theorem torsion_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    {X Y : Π x : M, TangentSpace I x} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    ((φ.pullbackCovariantDerivative cov).torsion x) (X x) (Y x) =
      φ.pullbackTangent x
        ((cov.torsion (φ x)) (φ.pushforwardTangent x (X x))
          (φ.pushforwardTangent x (Y x))) := by
  exact RicciFlow.SmoothSelfDiffeomorph2.torsion_pullbackCovariantDerivative
    φ cov hX hY

theorem isTorsionFree_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    [RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : cov.IsTorsionFree) :
    (φ.pullbackCovariantDerivative cov).IsTorsionFree := by
  exact RicciFlow.SmoothSelfDiffeomorph2.isTorsionFree_pullbackCovariantDerivative
    φ cov hcov

theorem isMetricCompatibleTangent_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    {g g' : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)}
    (hinner : ∀ x : M, ∀ u v : TangentSpace I x,
      g'.inner x u v =
        g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩; cov.IsMetricCompatibleTangent) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsMetricCompatibleTangent := by
  exact RicciFlow.SmoothSelfDiffeomorph2.isMetricCompatibleTangent_pullbackCovariantDerivative
    φ hinner cov hcov

theorem isLeviCivita_pullbackCovariantDerivative
    (φ : RicciFlow.SmoothSelfDiffeomorph2 (I := I) (M := M))
    {g g' : Bundle.ContMDiffRiemannianMetric I 2 E (TangentSpace I : M → Type _)}
    (hinner : ∀ x : M, ∀ u v : TangentSpace I x,
      g'.inner x u v =
        g.inner (φ x) (φ.pushforwardTangent x u) (φ.pushforwardTangent x v))
    (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
    (hcov : letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g.toRiemannianMetric⟩; cov.IsLeviCivita) :
    letI : Bundle.RiemannianBundle (TangentSpace I : M → Type _) :=
      ⟨g'.toRiemannianMetric⟩;
    (φ.pullbackCovariantDerivative cov).IsLeviCivita := by
  exact RicciFlow.SmoothSelfDiffeomorph2.isLeviCivita_pullbackCovariantDerivative
    φ hinner cov hcov

end PoincareCurvature.Palomar
