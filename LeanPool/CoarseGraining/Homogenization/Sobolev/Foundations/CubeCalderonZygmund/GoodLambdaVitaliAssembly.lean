/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambda
import LeanPool.CoarseGraining.Homogenization.Sobolev.Foundations.CubeCalderonZygmund.GoodLambdaVitaliSum

/-! # Good Lambda Vitali Assembly -/

namespace Homogenization

open scoped ENNReal BigOperators

noncomputable section

namespace CubeCalderonZygmund

open MeasureTheory

/-!
# Global measure bound from a stopping-ball family

This is the one-level assembly bridge for a good-`λ` argument.  A stopping
radius is supplied at every point of the target set; Vitali selection and the
measure summation are internal to the theorem.
-/

/-- A uniformly bounded positive stopping-ball family with a local estimate
gives the corresponding global measure estimate.  No countability or
disjointness data are supplied by the caller: they are produced internally by
Vitali selection. -/
theorem measure_le_mul_measure_of_vitali_stopping_family
    {d : ℕ} (ν κ : Measure (Vec d)) (target ambient : Set (Vec d))
    (radius : Vec d → ℝ) (R τ : ℝ) (K : ℝ≥0∞)
    (hradius : ∀ x ∈ target, radius x ≤ R)
    (hpositive : ∀ x ∈ target, 0 < radius x) (hτ : 3 < τ)
    (hlocal : ∀ x ∈ target,
      ν (target ∩ Metric.closedBall x (τ * radius x)) ≤
        K * κ (Metric.closedBall x (radius x)))
    (hambient : (⋃ x ∈ target, Metric.closedBall x (radius x)) ⊆ ambient) :
    ν target ≤ K * κ ambient := by
  obtain ⟨u, hu, hdisjoint, hcover⟩ :=
    exists_disjoint_closedBall_subfamily_covering_union target (fun x => x)
      radius R hradius τ hτ
  have htarget_original : target ⊆ ⋃ x ∈ target, Metric.closedBall x (radius x) := by
    intro x hx
    exact Set.mem_iUnion₂.mpr ⟨x, hx,
      Metric.mem_closedBall_self (le_of_lt (hpositive x hx))⟩
  have htarget : target ⊆ ⋃ x ∈ u, Metric.closedBall x (τ * radius x) :=
    htarget_original.trans hcover
  have huambient : (⋃ x ∈ u, Metric.closedBall x (radius x)) ⊆ ambient := by
    apply (show (⋃ x ∈ u, Metric.closedBall x (radius x)) ⊆
      ⋃ x ∈ target, Metric.closedBall x (radius x) by
      intro y hy
      rcases Set.mem_iUnion₂.mp hy with ⟨x, hx, hyx⟩
      exact Set.mem_iUnion₂.mpr ⟨x, hu hx, hyx⟩).trans hambient
  exact measure_le_mul_measure_of_vitali_closedBall_cover ν κ target ambient u
    (fun x => x) radius τ K
    (fun x hx => hpositive x (hu hx)) hdisjoint htarget
    (fun x hx => hlocal x (hu hx)) huambient

end CubeCalderonZygmund

end

end Homogenization
