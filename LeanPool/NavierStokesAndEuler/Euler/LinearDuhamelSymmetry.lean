/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.LinearDuhamelWeighted

@[expose] public section

/-!
# Independence and symmetries of the actual forward solve

The forced solution is independent of the selected homogeneous fundamental
representation. Consequently coefficient symmetries pass to the solution
without assuming any corresponding symmetry of that representation.
-/

noncomputable section

namespace EulerLinearDuhamel

open Set ContinuousLinearMap EulerContinuousTimeIntegral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable {T : ℝ} {hT : 0 ≤ T} {B : C(Icc (0 : ℝ) T,E →L[ℝ] E)}

namespace Evolution

/-- The true forced path is independent of the fundamental evolution chosen to represent it. -/
theorem solution_independent (U V : Evolution T hT B) (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) :
    U.solution f a₀ = V.solution f a₀ := by
  ext t
  exact V.solution_unique f a₀ (U.solutionReal f a₀) (U.solution_derivative f a₀)
    (U.solution_initial f a₀) t

/-- Sign reversal of both data reverses the actual solution. -/
theorem solution_neg (U : Evolution T hT B) (f : C(Icc (0 : ℝ) T,E)) (a₀ : E) :
    U.solution (-f) (-a₀) = -U.solution f a₀ := by
  rw [U.solution_eq_operators, U.solution_eq_operators, map_neg, map_neg, neg_add]

/-- Zero data vanish identically. -/
@[simp] theorem solution_zero (U : Evolution T hT B) :
    U.solution (0 : C(Icc (0 : ℝ) T,E)) 0 = 0 := by
  rw [U.solution_eq_operators, map_zero, map_zero, add_zero]

end Evolution

variable {P : Type*} (T : ℝ) (hT : 0 ≤ T)
  (B : P → C(Icc (0 : ℝ) T,E →L[ℝ] E)) (U : ∀ x, Evolution T hT (B x))

/-- Reflection or any other parameter symmetry is inherited from coefficients
and data; no regularity or symmetry of the chosen propagators is required. -/
theorem solution_odd_under (σ : P → P) (hB : ∀ x, B (σ x) = B x)
    (f : P → C(Icc (0 : ℝ) T,E)) (a₀ : P → E)
    (hf : ∀ x, f (σ x) = -f x) (ha₀ : ∀ x, a₀ (σ x) = -a₀ x) (x : P) :
    (U (σ x)).solution (f (σ x)) (a₀ (σ x)) = -(U x).solution (f x) (a₀ x) := by
  have he := (U x).frozen_solution (U (σ x)) (f (σ x)) (a₀ (σ x))
  have hm : multiplier (0 : C(Icc (0 : ℝ) T,E →L[ℝ] E)) = 0 := by
    ext p t
    rfl
  have hcoeff : B (σ x)-B x = 0 := by rw [hB x, sub_self]
  rw [hcoeff, hm, zero_apply, add_zero] at he
  calc
    (U (σ x)).solution (f (σ x)) (a₀ (σ x)) =
        (U x).initialOperator (a₀ (σ x)) + (U x).forcingOperator (f (σ x)) := he
    _ = -((U x).initialOperator (a₀ x) + (U x).forcingOperator (f x)) := by
      rw [hf x, ha₀ x, map_neg, map_neg, neg_add]
    _ = -(U x).solution (f x) (a₀ x) := by rw [(U x).solution_eq_operators]

/-- The actual forward solution stays in the union of the supports of its data. -/
theorem solution_support_subset (f : P → C(Icc (0 : ℝ) T,E)) (a₀ : P → E) :
    Function.support (fun x => (U x).solution (f x) (a₀ x)) ⊆
      Function.support f ∪ Function.support a₀ := by
  intro x hx
  by_cases hf : f x = 0
  · by_cases ha : a₀ x = 0
    · have hz : (U x).solution (f x) (a₀ x) = 0 := by rw [hf, ha, Evolution.solution_zero]
      exact (hx hz).elim
    · exact Or.inr ha
  · exact Or.inl hf

end EulerLinearDuhamel
