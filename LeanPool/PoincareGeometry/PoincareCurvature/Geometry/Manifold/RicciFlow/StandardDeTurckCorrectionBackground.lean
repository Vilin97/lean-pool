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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckEquation
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckRegularity
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.DeTurckJointRegularity

/-!
# Background-connection formula for the standard DeTurck correction

The standard DeTurck correction is defined with the evolving metric's
Levi-Civita connection.  This file rewrites that derivative through an
arbitrary background connection and its explicit Levi-Civita correction:

`∇ᵍ W = ∇bar W + (∇ᵍ - ∇bar)(W)`.

The final term is represented by `explicitLeviCivitaCorrection`, so the
formula exposes the quadratic-in-first-derivatives contribution that has to
be accounted for when deriving a background-covariant Ricci--DeTurck
operator.
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
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- At a point where the standard DeTurck field is differentiable, its
evolving Levi-Civita derivative is its background derivative plus the
explicit Levi-Civita correction applied to that field. -/
theorem chosenLeviCivita_standardDeTurckVectorField_eq_background_add_explicitLeviCivitaCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M)
    (hW : MDiffAt (T% (standardDeTurckVectorField
      (I := I) (M := M) g background t)) x) :
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (standardDeTurckVectorField (I := I) (M := M) g background t) x =
      (background t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x +
        explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (standardDeTurckVectorField (I := I) (M := M) g background t x) := by
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  ext u
  have hdiff := CovariantDerivative.difference_apply_tm
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t) (background t)
    (x := x)
    (σ := standardDeTurckVectorField (I := I) (M := M) g background t) hW
  have hdiffu := congrArg (fun A : TM x →L[ℝ] TM x => A u) hdiff
  rw [intrinsicDeTurck_difference_apply_eq_leviCivitaCorrection
    (I := I) (M := M) g background t x
    (standardDeTurckVectorField (I := I) (M := M) g background t x) u] at hdiffu
  change
    explicitLeviCivitaCorrection (I := I) (M := M) g background t x
        (standardDeTurckVectorField (I := I) (M := M) g background t x) u =
      ((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (standardDeTurckVectorField (I := I) (M := M) g background t) x u -
        (background t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x u at hdiffu
  calc
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (standardDeTurckVectorField (I := I) (M := M) g background t) x u =
        (((chosenLeviCivitaFamily (I := I) (M := M) g) t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x u -
          (background t)
            (standardDeTurckVectorField (I := I) (M := M) g background t) x u) +
          (background t)
            (standardDeTurckVectorField (I := I) (M := M) g background t) x u := by
              abel
    _ = explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (standardDeTurckVectorField (I := I) (M := M) g background t x) u +
          (background t)
            (standardDeTurckVectorField (I := I) (M := M) g background t) x u := by
              rw [← hdiffu]
    _ = (background t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x u +
        explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (standardDeTurckVectorField (I := I) (M := M) g background t x) u := by
            abel

/-- Pointwise form of
`chosenLeviCivita_standardDeTurckVectorField_eq_background_add_explicitLeviCivitaCorrection`. -/
theorem chosenLeviCivita_standardDeTurckVectorField_apply_eq_background_add_explicitLeviCivitaCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M)
    (hW : MDiffAt (T% (standardDeTurckVectorField
      (I := I) (M := M) g background t)) x)
    (u : TM x) :
    ((chosenLeviCivitaFamily (I := I) (M := M) g) t)
        (standardDeTurckVectorField (I := I) (M := M) g background t) x u =
      (background t)
          (standardDeTurckVectorField (I := I) (M := M) g background t) x u +
        explicitLeviCivitaCorrection (I := I) (M := M) g background t x
          (standardDeTurckVectorField (I := I) (M := M) g background t x) u := by
  exact congrArg (fun A : TM x →L[ℝ] TM x => A u)
    (chosenLeviCivita_standardDeTurckVectorField_eq_background_add_explicitLeviCivitaCorrection
      (I := I) (M := M) g background t x hW)

/-- With a spatially `C¹` background connection, the standard DeTurck
correction can be written entirely using the background derivative of `W`
and the explicit Levi-Civita correction of that background connection. -/
theorem standardDeTurckCorrection_apply_eq_background_add_explicitLeviCivitaCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (t : ℝ) (x : M) (u v : TM x)
    (hbackground : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1) :
    standardDeTurckCorrection (I := I) (M := M) g background t x u v =
      (g t).inner x
          ((background t)
            (standardDeTurckVectorField (I := I) (M := M) g background t) x u +
            explicitLeviCivitaCorrection (I := I) (M := M) g background t x
              (standardDeTurckVectorField (I := I) (M := M) g background t x) u) v +
        (g t).inner x u
          ((background t)
            (standardDeTurckVectorField (I := I) (M := M) g background t) x v +
            explicitLeviCivitaCorrection (I := I) (M := M) g background t x
              (standardDeTurckVectorField (I := I) (M := M) g background t x) v) := by
  have hW : MDiffAt (T% (standardDeTurckVectorField
      (I := I) (M := M) g background t)) x := by
    simpa using
      (standardDeTurckVectorField_contMDiffAt_of_contMDiffCovariantDerivative_background
        (I := I) (M := M) g background t hbackground x).mdifferentiableAt (by norm_num)
  rw [standardDeTurckCorrection_apply]
  rw [chosenLeviCivita_standardDeTurckVectorField_apply_eq_background_add_explicitLeviCivitaCorrection
    (I := I) (M := M) g background t x hW u]
  rw [chosenLeviCivita_standardDeTurckVectorField_apply_eq_background_add_explicitLeviCivitaCorrection
    (I := I) (M := M) g background t x hW v]

end RicciFlow
