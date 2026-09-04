/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.ChainInsertion
import LeanPool.Feige.ChainMeasure

/-!
# Finite expectations in the two-point calibration argument

This file defines the independent product expectation and the rejection
payoff used by the ordered insertion proof.
-/

open scoped BigOperators

namespace Feige

/-- Expectation under the independent product law on high sets. -/
noncomputable def productHighSetExpectation {m : ℕ}
    (p : Fin m → ℝ) (g : Finset (Fin m) → ℝ) : ℝ :=
  ∑ S ∈ Finset.univ.powerset, highSetMass p S * g S

@[simp]
theorem productHighSetExpectation_one {m : ℕ} (p : Fin m → ℝ) :
    productHighSetExpectation p (fun _ ↦ 1) = 1 := by
  unfold productHighSetExpectation
  simp only [mul_one]
  exact sum_highSetMass p

/-- Rejection is an increasing payoff because `K` is antitone on the
Boolean lattice. -/
theorem monotone_booleanRejectionPayoff {m : ℕ}
    (γ β : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    (α : ℝ) :
    Monotone (booleanRejectionPayoff γ β α) := by
  intro A B hAB
  unfold booleanRejectionPayoff
  by_cases hA : twoPointKFinset γ β A ≤ α
  · have hK := twoPointKFinset_antitone hγ hβ hAB
    simp [hA, hK.trans hA]
  · simp only [hA, ite_false]
    split_ifs <;> norm_num

theorem productExpectation_rejection_eq {m : ℕ}
    (γ β : Fin m → ℝ) (α : ℝ) :
    productHighSetExpectation (twoPointHighProbability γ β)
        (booleanRejectionPayoff γ β α) =
      twoPointRejectionMass γ β α := by
  classical
  unfold productHighSetExpectation booleanRejectionPayoff
    twoPointRejectionMass
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : twoPointKFinset γ β S ≤ α <;> simp [hS]

end Feige
