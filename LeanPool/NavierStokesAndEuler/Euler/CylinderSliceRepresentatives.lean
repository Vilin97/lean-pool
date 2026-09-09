/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.CylinderScalarTime

@[expose] public section

/-! Equality of actual cylinder L² slices identifies their continuous representatives everywhere. -/

noncomputable section

namespace EulerCylinderSmoothOrbit

open MeasureTheory EulerSmoothLimit EulerLiftedGradientSpace EulerLpCylinderTranslation
  EulerMetricTransport EulerCylinderScalarPrimitive
open scoped ContDiff

variable (P : ℝ) [Fact (0 < P)]
  {K L : Type*} [TopologicalSpace K] [CompactSpace K]
  [TopologicalSpace L] [CompactSpace L]

theorem pointField_eq_of_slice_eq (p : C(K,LiftL2 P)) (q : C(L,LiftL2 P))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p))
    (hq : ContDiff ℝ ∞ (fun a => pathTranslate P a q))
    (t : K) (s : L) (he : p t = q s) : pointField P p hp t = pointField P q hq s := by
  have h := pointField_ae P p hp t
  rw [he] at h
  exact Measure.eq_of_ae_eq (h.symm.trans (pointField_ae P q hq s))
    (smoothField_continuous P _ (pointField_smooth P p hp t))
    (smoothField_continuous P _ (pointField_smooth P q hq s))

theorem scalarPointField_eq_of_slice_eq (p : C(K,CylinderL2 P ℝ)) (q : C(L,CylinderL2 P ℝ))
    (hp : ContDiff ℝ ∞ (fun a => pathTranslate P a p))
    (hq : ContDiff ℝ ∞ (fun a => pathTranslate P a q))
    (t : K) (s : L) (he : p t = q s) : scalarPointField P p hp t = scalarPointField P q hq s := by
  have h := scalarPointField_ae P p hp t
  rw [he] at h
  exact Measure.eq_of_ae_eq (h.symm.trans (scalarPointField_ae P q hq s))
    (scalarPointField_continuous P p hp t) (scalarPointField_continuous P q hq s)

end EulerCylinderSmoothOrbit
