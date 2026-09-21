/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyScalarC2Regularity

/-!
# Assemble derived Hamilton--Ivey slice regularity

This constructor packages the actual Ricci, trace, and scalar C² results into the slice record used
by the geometric evolution certificate.  It keeps the all-time C² connection hypothesis required
by the contracted-Bianchi argument, while only requiring C³ connection regularity on the selected
slice.
-/

noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [RiemannianBundle (TangentSpace I : M → Type _)]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 4 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 2) M]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]
  [SigmaCompactSpace M] [CompactSpace M] [Nonempty M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Assemble the intrinsic slice regularity record from all-time C² connection regularity and the
actual C² Ricci tensor derived from C³ regularity on the selected slice. -/
theorem HamiltonIveyIntrinsicSliceRegularity.of_connectionC3At
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hLevi : g.IsLeviCivita cov) (t : ℝ)
    (hcov₂ : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 2)
    (hcov₃t : ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 3)
    (hmetric₂ :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 2 E TM) :
    HamiltonIveyIntrinsicSliceRegularity g cov hcov hLevi t := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  letI : IsContMDiffRiemannianBundle I 2 E TM := hmetric₂
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov t) 2 := hcov₂ t
  letI : ContMDiffCovariantDerivative (cov t) 3 := hcov₃t
  have hRicciSection : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TM z →L[ℝ] TM z →L[ℝ] ℝ) y
        (RicciFlow.ricciBilinearFormSection (I := I) (M := M) (cov t) y)) :=
    CovariantDerivative.ricciBilinearFormSection_contMDiff_two
      (I := I) (M := M) (cov t) (Module.finBasis ℝ E)
  have hRicci₂ : ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
      (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun z : M ↦ TM z →L[ℝ] TM z →L[ℝ] ℝ) y
        (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) := by
    have hfun :
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] TM z →L[ℝ] ℝ) y
          (RicciFlow.ricciBilinearFormSection (I := I) (M := M) (cov t) y)) =
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] TM z →L[ℝ] ℝ) y
          (CovariantDerivative.ricciCovariantTwoTensor (cov t) y)) := by
      funext y
      apply congrArg (TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ) y)
      ext u v
      rfl
    simpa only [hfun] using hRicciSection
  have htrace := intrinsicRicciTraceRegularity_of_ricciC2
    g cov hcov hLevi t hmetric₂ hRicci₂
  have hscalar := CovariantDerivative.scalarCurvature_contMDiff_two_of_ricciC2
    (I := I) (M := M) (cov t) hRicci₂
  exact {
    connectionC2 := hcov₂
    metricC2 := hmetric₂
    trace := htrace
    scalarC2 := hscalar
    ricciC2 := hRicci₂
  }

end CovariantDerivative.TimeDependentRiemannianMetric

end
