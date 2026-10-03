/-
Copyright (c) 2026 Arthur Freitas Ramos and coauthors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module


/-
Original copyright notice:
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights
reserved.
-/

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Contractions
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.LeviCivita

/-!
# The local connection layer

This module is the first Bonnet--Myers-specific bridge.  It consumes only the
audited same-repository connection construction and exposes the concrete
Levi--Civita data needed by the later geodesic and index-form modules.
-/

@[expose] public section

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

/-- A concrete locally constructed Levi--Civita connection for the supplied
Riemannian metric. -/
noncomputable def leviCivita
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    CovariantDerivative I E TM :=
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  CovariantDerivative.someContMDiffLeviCivitaConnection (I := I) (E := E) (M := M)

instance leviCivitaSmooth
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    CovariantDerivative.ContMDiffCovariantDerivative
      (leviCivita (I := I) (M := M) g) 1 := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  dsimp [leviCivita]
  exact CovariantDerivative.someContMDiffLeviCivitaConnection_contMDiff
    (I := I) (E := E) (M := M)

theorem leviCivita_isLeviCivita
    (g : ContMDiffRiemannianMetric I ∞ E TM) :
    letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
    CovariantDerivative.IsLeviCivita (leviCivita (I := I) (M := M) g) := by
  letI : RiemannianBundle TM := ⟨g.toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  dsimp [leviCivita]
  exact CovariantDerivative.someContMDiffLeviCivitaConnection_isLeviCivita
    (I := I) (E := E) (M := M)

end BonnetMyersEntry
