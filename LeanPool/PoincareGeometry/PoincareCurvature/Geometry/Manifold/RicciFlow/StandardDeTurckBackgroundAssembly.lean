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

public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.StandardDeTurckCorrectionBackground
public import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.RicciConnectionChange

/-!
# Pre-cancellation background assembly for the standard Ricci--DeTurck operator

This file combines the two exact background expansions that precede the
principal-part cancellation.  It does **not** assert parabolicity or hide a
remainder in a new definition.  The curvature contribution is the explicit
orthonormal-frame Ricci connection-change sum, and the gauge contribution is
the background derivative of the standard DeTurck vector plus the explicit
Levi-Civita correction.

The convention for `explicitLeviCivitaCorrection x z X` is inherited from
`CovariantDerivative.difference`: `z` is the differentiated vector and `X`
is the connection direction.  The derivative arguments of
`covariantDerivativeOneForm` are `(derivative direction, differentiated
vector, one-form direction)`.
-/

@[expose] public noncomputable section

open Bundle FiberBundle
open scoped Manifold ContDiff Topology BigOperators

namespace RicciFlow

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E] [IsManifold I ∞ M]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)
local notation "TCorr" =>
  (fun x : M ↦ TM x →L[ℝ] TM x →L[ℝ] TM x)

/-- The standard Ricci--DeTurck right-hand side, assembled before its
second-derivative terms are cancelled.

For a torsion-free spatially `C¹` background, this is `-2` times the
background Ricci curvature, followed by `-2` times the explicit Ricci
connection-change trace, and the explicit background form of the standard
DeTurck correction.  In particular, every use of the evolving metric
connection is displayed through `explicitLeviCivitaCorrection`; no
connection-change remainder is suppressed. -/
theorem standardRicciDeTurckRHS_apply_eq_background_ricci_add_explicit_connectionChange_add_backgroundCorrection
    (g : MetricFamily (I := I) (M := M))
    (background : ConnectionFamily (I := I) (M := M))
    (hbackground : ∀ t : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative (background t) 1)
    (hbackgroundTorsionFree : ∀ t : ℝ, (background t).torsion = 0)
    (t : ℝ) (x : M) :
    letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
    ∀ {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ (TM x)) (u v : TM x),
      standardRicciDeTurckRHS (I := I) (M := M) g background t x u v =
        (-2 : ℝ) * CovariantDerivative.ricciCurvature (cov := background t) x u v +
          (-2 : ℝ) * ∑ i, inner ℝ (b i)
            (CovariantDerivative.covariantDerivativeOneForm (background t)
                (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x
                (b i) v u -
              CovariantDerivative.covariantDerivativeOneForm (background t)
                (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x
                u v (b i) +
              explicitLeviCivitaCorrection (I := I) (M := M) g background t x
                (explicitLeviCivitaCorrection (I := I) (M := M) g background t x v u)
                (b i) -
              explicitLeviCivitaCorrection (I := I) (M := M) g background t x
                (explicitLeviCivitaCorrection (I := I) (M := M) g background t x v (b i))
                u) +
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
  letI : Bundle.RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  intro ι inst b u v
  letI : IsContMDiffRiemannianBundle I 2 E TM := by infer_instance
  letI : CovariantDerivative.ContMDiffCovariantDerivative (background t) 1 :=
    hbackground t
  have hCorrection : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] (E →L[ℝ] E))) 1
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] (E →L[ℝ] E)) (E := TCorr) y
        ((background t).leviCivitaCorrection y)) :=
    CovariantDerivative.contMDiff_leviCivitaCorrection_section
      (I := I) (E := E) (M := M) (cov := background t)
  have hLeviRegular : ∀ s : ℝ,
      CovariantDerivative.ContMDiffCovariantDerivative
        ((g.leviCivitaConnection background) s) 1 :=
    g.contMDiffCovariantDerivative_leviCivitaConnection background hbackground
  letI : CovariantDerivative.ContMDiffCovariantDerivative
      ((g.leviCivitaConnection background) t) 1 := hLeviRegular t
  have hIntrinsic :
      intrinsicRicciFlowRHS (I := I) (M := M) g =
        ricciFlowRHS (I := I) (M := M) g
          (g.leviCivitaConnection background) hLeviRegular :=
    intrinsicRicciFlowRHS_eq_ricciFlowRHS_of_isLeviCivita
      (I := I) (M := M) g hLeviRegular
      (g.leviCivitaConnection_isLeviCivita background)
  have hRicci :
      CovariantDerivative.ricciCurvature
          (cov := (g.leviCivitaConnection background) t) x u v =
        CovariantDerivative.ricciCurvature (cov := background t) x u v +
          ∑ i, inner ℝ (b i)
            (CovariantDerivative.covariantDerivativeOneForm (background t)
                (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x
                (b i) v u -
              CovariantDerivative.covariantDerivativeOneForm (background t)
                (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x
                u v (b i) +
              explicitLeviCivitaCorrection (I := I) (M := M) g background t x
                (explicitLeviCivitaCorrection (I := I) (M := M) g background t x v u)
                (b i) -
              explicitLeviCivitaCorrection (I := I) (M := M) g background t x
                (explicitLeviCivitaCorrection (I := I) (M := M) g background t x v (b i))
                u) := by
    have hExplicitCorrection :
        explicitLeviCivitaCorrection (I := I) (M := M) g background t =
          (background t).leviCivitaCorrection := by
      rfl
    rw [hExplicitCorrection]
    simpa [CovariantDerivative.TimeDependentRiemannianMetric.leviCivitaConnection,
      CovariantDerivative.leviCivitaConnection] using
      (CovariantDerivative.ricciCurvature_addOneForm_eq_sum_orthonormalBasis
        (I := I) (E := E) (M := M) (background t)
        ((background t).leviCivitaCorrection)
        (hbackgroundTorsionFree t) hCorrection x b u v)
  have hCorrectionFormula :=
    standardDeTurckCorrection_apply_eq_background_add_explicitLeviCivitaCorrection
      (I := I) (M := M) g background t x u v (hbackground t)
  calc
    standardRicciDeTurckRHS (I := I) (M := M) g background t x u v =
        intrinsicRicciFlowRHS (I := I) (M := M) g t x u v +
          standardDeTurckCorrection (I := I) (M := M) g background t x u v := rfl
    _ = ricciFlowRHS (I := I) (M := M) g
          (g.leviCivitaConnection background) hLeviRegular t x u v +
          standardDeTurckCorrection (I := I) (M := M) g background t x u v := by
      rw [congrArg (fun F ↦ F t x u v) hIntrinsic]
    _ = (-2 : ℝ) * CovariantDerivative.ricciCurvature
          (cov := (g.leviCivitaConnection background) t) x u v +
          standardDeTurckCorrection (I := I) (M := M) g background t x u v := by
      rfl
    _ = (-2 : ℝ) * CovariantDerivative.ricciCurvature (cov := background t) x u v +
        (-2 : ℝ) * ∑ i, inner ℝ (b i)
          (CovariantDerivative.covariantDerivativeOneForm (background t)
              (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x
              (b i) v u -
            CovariantDerivative.covariantDerivativeOneForm (background t)
              (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x
              u v (b i) +
            explicitLeviCivitaCorrection (I := I) (M := M) g background t x
              (explicitLeviCivitaCorrection (I := I) (M := M) g background t x v u)
              (b i) -
            explicitLeviCivitaCorrection (I := I) (M := M) g background t x
              (explicitLeviCivitaCorrection (I := I) (M := M) g background t x v (b i))
              u) +
          standardDeTurckCorrection (I := I) (M := M) g background t x u v := by
      rw [hRicci]
      ring
    _ = (-2 : ℝ) * CovariantDerivative.ricciCurvature (cov := background t) x u v +
        (-2 : ℝ) * ∑ i, inner ℝ (b i)
          (CovariantDerivative.covariantDerivativeOneForm (background t)
              (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x
              (b i) v u -
            CovariantDerivative.covariantDerivativeOneForm (background t)
              (explicitLeviCivitaCorrection (I := I) (M := M) g background t) x
              u v (b i) +
            explicitLeviCivitaCorrection (I := I) (M := M) g background t x
              (explicitLeviCivitaCorrection (I := I) (M := M) g background t x v u)
              (b i) -
            explicitLeviCivitaCorrection (I := I) (M := M) g background t x
              (explicitLeviCivitaCorrection (I := I) (M := M) g background t x v (b i))
              u) +
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
      rw [hCorrectionFormula]
      ring

end RicciFlow
