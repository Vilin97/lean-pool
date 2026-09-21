/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

module

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckJointRegularity

/-!
# Torsion symmetry of the explicit Levi-Civita correction

The explicit correction of a background affine connection has precisely the
antisymmetric part needed to cancel the background torsion.  In particular,
it is symmetric in its two tangent inputs when the background is torsion-free.
This is a pointwise algebraic fact; it makes no curvature, cancellation, or
regularity assertion.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]

local notation "TM" => (TangentSpace I : M → Type _)
/-- The antisymmetric part of the explicit correction is the negative of the
background torsion, in the correction's `(differentiated vector, direction)`
argument order. -/
theorem explicitLeviCivitaCorrection_sub_eq_neg_torsion
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    explicitLeviCivitaCorrection (I := I) (M := M) g background t x v u -
        explicitLeviCivitaCorrection (I := I) (M := M) g background t x u v =
      - (background t).torsion x u v := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  simpa [explicitLeviCivitaCorrection] using
    (CovariantDerivative.leviCivitaCorrection_sub_eq_neg_torsion
      (I := I) (E := E) (cov := background t) x u v)
/-- Over a torsion-free background, the explicit correction is symmetric in
its two tangent inputs. -/
theorem explicitLeviCivitaCorrection_symm_of_isTorsionFree
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (hbackground : (background t).IsTorsionFree)
    (x : M) (u v : TM x) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    explicitLeviCivitaCorrection (I := I) (M := M) g background t x v u =
      explicitLeviCivitaCorrection (I := I) (M := M) g background t x u v := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM :=
    g.slice_isContMDiffRiemannianBundle t
  have ht : (background t).torsion x u v = 0 := by
    change (background t).torsion = 0 at hbackground
    simpa using congrArg (fun torsion => torsion x u v) hbackground
  have hsub := explicitLeviCivitaCorrection_sub_eq_neg_torsion
    (I := I) (M := M) g background t x u v
  rw [ht] at hsub
  have hzero :
      explicitLeviCivitaCorrection (I := I) (M := M) g background t x v u -
          explicitLeviCivitaCorrection (I := I) (M := M) g background t x u v = 0 := by
    simpa using hsub
  exact sub_eq_zero.mp hzero

end RicciFlow
