/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeAlgebra
import LeanPool.NavierStokesAndEuler.Euler.FiniteGradeDiagonal
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic.Continuity.Init
import Mathlib.Tactic.Measurability.Init
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.NormNum.Pow
import Mathlib.Tactic.Positivity.Finset

/-! Which unknown coefficients can enter the slow and fast quadratic terms. -/

@[expose] public section


noncomputable section

namespace EulerFiniteGrades

open Finset

variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- With zero constant coefficient, the slow grade p depends only on grades below p. -/
theorem convolution_strict_congr (M p : ℕ) (hp : 0 < p) (hMp : p ≤ M)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u u' : ℕ → V) (hu0 : u 0 = 0)
    (hu : ∀ i < p, u' i = u i) :
    convolution M B u' u' p = convolution M B u u p := by
  rw [convolution_eq_range M p hMp, convolution_eq_range M p hMp]
  apply sum_congr rfl
  intro i hi
  have hi' : i ≤ p := by have h := mem_range.mp hi; omega
  by_cases hi0 : i=0
  · simp only [hi0, hu 0 hp, hu0, map_zero, LinearMap.zero_apply]
  by_cases hip : i=p
  · simp only [hip, Nat.sub_self, hu 0 hp, hu0, map_zero]
  rw [hu i (by omega), hu (p-i) (by omega)]

/-- The fast grade p has exactly two possible dependencies on the new grade p. -/
theorem convolution_next_delta (M p : ℕ) (hp : 2 ≤ p) (hMp : p + 1 ≤ M)
    (B : V →ₗ[ℝ] V →ₗ[ℝ] W) (u u' : ℕ → V) (δ : V) (hu0 : u 0 = 0)
    (hu : ∀ i < p, u' i = u i) (hδ : u' p = u p + δ) :
    convolution M B u' u' (p+1) = convolution M B u u (p+1) +
      B δ (u 1) + B (u 1) δ := by
  rw [convolution_eq_range M (p+1) hMp, convolution_eq_range M (p+1) hMp]
  have hterm : ∀ i ∈ range (p+2),
      B (u' i) (u' (p+1-i)) = B (u i) (u (p+1-i)) +
        (if i=p then B δ (u 1) else 0) + (if i=1 then B (u 1) δ else 0) := by
    intro i hi
    have hi' : i ≤ p+1 := by have h := mem_range.mp hi; omega
    by_cases hi0 : i=0
    · simp [hi0, hu 0 (by omega), hu0, show (0 : ℕ) ≠ p by omega]
    by_cases hiend : i=p+1
    · simp [hiend, hu 0 (by omega), hu0, show p ≠ 0 by omega]
    by_cases hip : i=p
    · simp [hip, hδ, hu 1 (by omega), show p ≠ 1 by omega, map_add,
        LinearMap.add_apply]
    by_cases hi1 : i=1
    · simp [hi1, hδ, hu 1 (by omega), show 1 ≠ p by omega, map_add]
    rw [hu i (by omega), hu (p+1-i) (by omega)]
    simp [hip, hi1]
  calc
    _ = ∑ i ∈ range (p+2),
        (B (u i) (u (p+1-i)) + (if i=p then B δ (u 1) else 0) +
          (if i=1 then B (u 1) δ else 0)) := sum_congr rfl hterm
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib]
      simp only [sum_ite_eq', mem_range, show p < p+2 by omega,
        show 1 < p+2 by omega, ite_true]

end EulerFiniteGrades
