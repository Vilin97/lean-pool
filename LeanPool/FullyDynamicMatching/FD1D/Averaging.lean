/-
Copyright (c) 2026 Yash Kanoria. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yash Kanoria
-/
module


public import LeanPool.FullyDynamicMatching.FD1D.Expectations

/-! # Averaging -/

@[expose] public section

namespace FD1D

noncomputable section

open scoped BigOperators

namespace FiniteLaw

variable {α : Type*} [Fintype α]

/--
Choose a time uniformly from `Fin T`, then sample from the law assigned to
that time.
-/
def timeAverage {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) : FiniteLaw (Fin T × α) where
  mass z := (1 / (T : ℝ)) * (μ z.1).mass z.2
  mass_nonneg z :=
    mul_nonneg (by positivity) ((μ z.1).mass_nonneg z.2)
  sum_mass := by
    rw [Fintype.sum_prod_type]
    calc
      (∑ t : Fin T, ∑ x : α,
          (1 / (T : ℝ)) * (μ t).mass x) =
          ∑ _t : Fin T, (1 / (T : ℝ)) := by
            apply Finset.sum_congr rfl
            intro t _
            rw [← Finset.mul_sum, (μ t).sum_mass, mul_one]
      _ = 1 := by
        simp [hT.ne']

@[simp]
theorem timeAverage_mass {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) (t : Fin T) (x : α) :
    (timeAverage hT μ).mass (t, x) =
      (1 / (T : ℝ)) * (μ t).mass x :=
  rfl

/-- Expectation under the time/state mixture is the average expectation. -/
theorem expect_timeAverage {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) (f : Fin T × α → ℝ) :
    (timeAverage hT μ).expect f =
      (∑ t : Fin T, (μ t).expect (fun x => f (t, x))) / (T : ℝ) := by
  rw [expect, Fintype.sum_prod_type]
  simp only [expect]
  calc
    (∑ t : Fin T, ∑ x : α,
        (1 / (T : ℝ)) * (μ t).mass x * f (t, x)) =
        (1 / (T : ℝ)) *
          ∑ t : Fin T, ∑ x : α, (μ t).mass x * f (t, x) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro t _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            ring
    _ = (∑ t : Fin T, ∑ x : α, (μ t).mass x * f (t, x)) /
          (T : ℝ) := by ring

/-- Range-indexed form of `expect_timeAverage`. -/
theorem expect_timeAverage_eq_sum_range {T : ℕ} (hT : 0 < T)
    (μ : ℕ → FiniteLaw α) (f : ℕ → α → ℝ) :
    (timeAverage hT (fun t : Fin T => μ t)).expect
        (fun z => f z.1 z.2) =
      (∑ t ∈ Finset.range T, (μ t).expect (f t)) / (T : ℝ) := by
  rw [expect_timeAverage]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun t => (μ t).expect (f t)) T

/-- A state-only observable averages in the same way. -/
theorem expect_timeAverage_state {T : ℕ} (hT : 0 < T)
    (μ : ℕ → FiniteLaw α) (f : α → ℝ) :
    (timeAverage hT (fun t : Fin T => μ t)).expect
        (fun z => f z.2) =
      (∑ t ∈ Finset.range T, (μ t).expect f) / (T : ℝ) := by
  simpa using expect_timeAverage_eq_sum_range hT μ (fun _ => f)

/-- Lift a state permutation without changing the sampled time. -/
def timeLiftPerm {T : ℕ} (e : Equiv.Perm α) :
    Equiv.Perm (Fin T × α) :=
  (Equiv.refl (Fin T)).prodCongr e

omit [Fintype α] in
@[simp]
theorem timeLiftPerm_apply {T : ℕ} (e : Equiv.Perm α)
    (t : Fin T) (x : α) :
    timeLiftPerm e (t, x) = (t, e x) :=
  rfl

/-- Pointwise state-law invariance passes to the uniform time mixture. -/
theorem timeAverage_lawInvariant {T : ℕ} (hT : 0 < T)
    (μ : Fin T → FiniteLaw α) (e : Equiv.Perm α)
    (hinv : ∀ t, FiniteKernel.LawInvariant (μ t) e) :
    FiniteKernel.LawInvariant (timeAverage hT μ) (timeLiftPerm e) := by
  intro z
  rcases z with ⟨t, x⟩
  simp only [timeLiftPerm_apply, timeAverage_mass]
  rw [hinv t x]

end FiniteLaw

end

end FD1D
