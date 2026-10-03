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

module

public import LeanPool.PoincareGeometry.AlmostSchur.CurvatureVendor.Along
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-! # Metric Predicate -/

/- Minimal metric predicate extracted from Arthur Freitas Ramos's committed
contracted-bianchi LeviCivita.lean, commit 12cebb809524d0cd185c6cd7bcb5b73d3562bce1,
blob 31a79f8cc30b8dbed94396a2575274effbd83f54. No existence or uniqueness declarations imported. -/

@[expose] public noncomputable section
open Bundle
open scoped Manifold ContDiff
namespace CovariantDerivative
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  [RiemannianBundle (TangentSpace I : M → Type _)]
local notation "TM" => (TangentSpace I : M → Type _)

/-- Metric Leibniz rule, without any regularity or uniqueness conclusion. -/
def IsMetricCompatibleTangentAlmostSchur (cov : CovariantDerivative I E TM) : Prop :=
  ∀ {x : M} {σ τ : Π x : M, TangentSpace I x},
    MDiffAt (T% σ) x → MDiffAt (T% τ) x →
      ∀ u : TangentSpace I x,
        mvfderiv (I := I) (fun y ↦ inner ℝ (σ y) (τ y)) x u =
          inner ℝ (cov σ x u) (τ x) + inner ℝ (σ x) (cov τ x u)

end CovariantDerivative
