/-
Copyright (c) 2026 Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyIntrinsicSliceRegularityBridge
import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyRicciC2Regularity

/-!
# Deriving Hamilton--Ivey trace regularity from a C³ connection

The intrinsic slice trace regularity is derived from the actual C² Ricci tensor established by the
local-frame curvature argument.  C² and C³ connection regularity remain explicit inputs; neither is
silently inferred from the current time-dependent metric type.
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

/-- A C³ connection slice and C² metric tensor supply the actual C² Ricci section needed by
`intrinsicRicciTraceRegularity_of_ricciC2`. Consequently the full pointwise intrinsic trace
regularity record follows without a separate Ricci regularity hypothesis. -/
theorem intrinsicRicciTraceRegularity_of_connectionC3
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 1)
    (hcov₂ : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 2)
    (hcov₃ : ∀ τ : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov τ) 3)
    (hLevi : g.IsLeviCivita cov) (t : ℝ)
    (hmetric₂ :
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      IsContMDiffRiemannianBundle I 2 E TM) :
    ∀ x : M, intrinsicRicciTraceRegularity g cov hcov hLevi t x := by
  letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
  letI : IsContMDiffRiemannianBundle I 1 E TM := g.slice_isContMDiffRiemannianBundle t
  letI : IsContMDiffRiemannianBundle I 2 E TM := hmetric₂
  letI : ContMDiffCovariantDerivative (cov t) 1 := hcov t
  letI : ContMDiffCovariantDerivative (cov t) 2 := hcov₂ t
  letI : ContMDiffCovariantDerivative (cov t) 3 := hcov₃ t
  have hRicciSection :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
        (fun y ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
          (E := fun z : M ↦ TM z →L[ℝ] TM z →L[ℝ] ℝ) y
          (RicciFlow.ricciBilinearFormSection (I := I) (M := M) (cov t) y)) :=
    CovariantDerivative.ricciBilinearFormSection_contMDiff_two
      (I := I) (M := M) (cov t) (Module.finBasis ℝ E)
  have hRicci₂ :
      ContMDiff I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) 2
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
  exact intrinsicRicciTraceRegularity_of_ricciC2 g cov hcov hLevi t hmetric₂ hRicci₂

end CovariantDerivative.TimeDependentRiemannianMetric

end
