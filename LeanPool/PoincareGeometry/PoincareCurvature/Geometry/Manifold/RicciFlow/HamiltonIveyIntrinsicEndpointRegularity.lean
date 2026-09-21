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

import LeanPool.PoincareGeometry.PoincareCurvature.Geometry.Manifold.RicciFlow.HamiltonIveyOperatorC2Regularity

/-!
# Hamilton--Ivey endpoint with operator regularity derived from slice data

This endpoint takes the selected-slice regularity package and derives the
regularity of the actual lowered curvature operator from it.  Callers no
longer need to provide that same operator package separately.
-/

noncomputable section

open Bundle
open Filter Set Topology
open scoped BigOperators Manifold ContDiff

namespace CovariantDerivative.TimeDependentRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [T2Space M] [FiniteDimensional ℝ E] [CompleteSpace E]
  [IsManifold I ∞ M] [I.Boundaryless]
  [ContMDiffVectorBundle 2 E (TangentSpace I : M → Type _) I]
  [ContMDiffVectorBundle 3 E (TangentSpace I : M → Type _) I]
  [IsManifold I (minSmoothness ℝ 3) M]
  [IsManifold I ((2 : ℕ∞) + 1) M]
  [IsManifold I ((3 : ℕ∞) + 1) M]
  [CompactSpace M] [Nonempty M] [SigmaCompactSpace M]

local notation "TM" => (TangentSpace I : M → Type _)

/-- Hamilton--Ivey pinching from intrinsic Ricci flow data and slice
regularity.  The operator regularity needed by the evolution proof is derived
from `sliceRegularity` at each time and point. -/
theorem hamiltonIveyPinching_of_intrinsicRicciFlow_and_jointGeometricEvolution_contactData_on_negative_spectrum_of_sliceRegularity
    (g : TimeDependentRiemannianMetric (I := I) (M := M))
    (cov : TimeDependentCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM))
    (hcov : ∀ t : ℝ, ContMDiffCovariantDerivative
      (𝕜 := ℝ) (I := I) (M := M) (F := E) (V := TM) (cov t) 1)
    (hLevi : g.IsLeviCivita cov)
    (hdim : ∀ x : M, Module.finrank ℝ (TM x) = 3)
    (gdot : RicciFlow.MetricTensorFamily (I := I) (M := M))
    {K T : ℝ} (hK : 0 < K) (hT : 0 ≤ T)
    (hflow : RicciFlow.IsRicciFlowOn
      (I := I) (M := M) g cov hcov gdot (Icc 0 T))
    (hregularity : ∀ {t : ℝ}, t ∈ Icc 0 T →
      HamiltonIveyIntrinsicCurvatureVariationRegularity
        g cov hcov hLevi t)
    (sliceRegularity : ∀ {t : ℝ}, t ∈ Icc 0 T →
      HamiltonIveyIntrinsicSliceRegularity g cov hcov hLevi t)
    (hnuLower : ∀ x : M,
      -K ≤ g.curvatureNu cov hcov hLevi hdim 0 x)
    (hScalarCont : ContinuousOn
      (fun p : ℝ × M => g.scalarCurvature cov hcov p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hNuCont : ContinuousOn
      (fun p : ℝ × M =>
        g.curvatureNu cov hcov hLevi hdim p.1 p.2)
      (Icc 0 T ×ˢ (Set.univ : Set M)))
    (hcontact : ∀ {t : ℝ} {x : M}, t ∈ Icc 0 T →
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
      g.hamiltonIveyDefect cov hcov hLevi hdim K t x < 0 →
      HamiltonIveySupportContactRegularityData g cov hcov hLevi hdim t x) :
    ∀ t ∈ Icc 0 T, ∀ x : M,
      g.curvatureNu cov hcov hLevi hdim t x < 0 →
        0 ≤ g.hamiltonIveyDefect cov hcov hLevi hdim K t x := by
  apply hamiltonIveyPinching_of_intrinsicRicciFlow_and_jointGeometricEvolution_contactData_on_negative_spectrum
    g cov hcov hLevi hdim gdot hK hT hflow hregularity
    (fun t ht x => by
      letI : RiemannianBundle TM := ⟨(g t).toRiemannianMetric⟩
      exact HamiltonIveyCurvatureOperatorRegularity.of_sliceRegularity
        g cov hcov hLevi hdim (sliceRegularity (t := t) ht) x)
    sliceRegularity hnuLower hScalarCont hNuCont hcontact

end CovariantDerivative.TimeDependentRiemannianMetric

end
