/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import LeanPool.AnomalousDiffusion.AVenhance.Infra.Section4.IteratesWordEquation

/-! Exact spatial energy identities before expansion of drift commutators. -/

@[expose] public section

noncomputable section
open Homogenization MeasureTheory
open scoped Matrix.Norms.Elementwise
namespace AVenhance.Infra.Section4
open IterateCalculus
open AVenhance

/-- Every ordered spatial word of a smooth periodic scalar is periodic. -/
theorem iterateSpatialWord_periodic {f : Vec 2 → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : IsZ2Periodic f) (w : List (Fin 2)) :
    IsZ2Periodic (iterateSpatialWord w f) := by
  induction w with
  | nil => exact hp
  | cons i w ih =>
    have hg := iterate_gradient_periodic ((iterateSpatialWord_smooth hf w).of_le (by simp)) ih
    intro k x
    exact congrFun (hg k x) i

end AVenhance.Infra.Section4
