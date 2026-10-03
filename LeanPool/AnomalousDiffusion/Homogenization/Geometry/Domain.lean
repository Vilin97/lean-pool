/-
Copyright (c) 2026 Scott Armstrong and Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Tuomo Kuusi
-/
-- From CoarseGraining (https://github.com/scottnarmstrong/CoarseGraining), commit c7ddd76.

module

public import LeanPool.AnomalousDiffusion.Homogenization.Ambient.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Domain

Support for the Armstrong–Vicol anomalous-diffusion formalization. -/

@[expose] public section

namespace Homogenization

/-- Coordinatewise boundedness of a spatial domain within a positive-radius box. -/
def IsBoundedDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∀ x ∈ U, ∀ i, |x i| ≤ R

/--
Working domain-regularity predicate for the current Sobolev layer.

At this stage of the development, the reusable geometric input needed by the
mean-zero and affine-average arguments is exactly measurability together with
the repository's bounded-domain predicate.
-/
def IsSobolevRegularDomain {d : ℕ} (U : Set (Vec d)) : Prop :=
  MeasurableSet U ∧ IsBoundedDomain U

namespace IsSobolevRegularDomain

theorem measurableSet {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    MeasurableSet U :=
  hU.1

theorem isBoundedDomain {d : ℕ} {U : Set (Vec d)} (hU : IsSobolevRegularDomain U) :
    IsBoundedDomain U :=
  hU.2

end IsSobolevRegularDomain

end Homogenization
