/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Ambient.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Domain -/

namespace Homogenization

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
