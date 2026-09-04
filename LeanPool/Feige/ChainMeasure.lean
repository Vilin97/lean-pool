/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.ChainFromBoolean

/-!
# Probability measures carried by maximal chains

The auxiliary chain distribution mentioned in the proof outline is a finite
probability mass function on the levels of a maximal chain.  This file
packages its expectation and relates the indicator of a threshold rejection
event to `rejectedMass`.
-/

open scoped BigOperators

namespace Feige

namespace CalibratedChain

variable {m : ℕ} (C : CalibratedChain m)

/-- Expectation of a payoff on the `m + 1` genuine levels of a calibrated
chain. -/
noncomputable def expectation (g : ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), chainMass C.K j * g j

theorem expectation_one : C.expectation (fun _ ↦ 1) = 1 := by
  simp only [expectation, mul_one]
  exact C.total_mass

theorem expectation_nonneg {g : ℕ → ℝ} (hg : ∀ j < m + 1, 0 ≤ g j) :
    0 ≤ C.expectation g := by
  unfold expectation
  exact Finset.sum_nonneg fun j hj ↦
    mul_nonneg (C.mass_nonneg j) (hg j (Finset.mem_range.mp hj))

/-- The rejection indicator used for exact chain calibration. -/
noncomputable def rejectionIndicator (α : ℝ) (j : ℕ) : ℝ :=
  if C.K j ≤ α then 1 else 0

/-- Expectation of the rejection indicator is exactly the previously
defined rejection mass. -/
theorem expectation_rejectionIndicator (α : ℝ) :
    C.expectation (C.rejectionIndicator α) = C.rejectedMass α := by
  classical
  simp only [expectation, rejectionIndicator, rejectedMass]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : C.K j ≤ α <;> simp [hj]

/-- Exact calibration in expectation form. -/
theorem expectation_rejection_le {α : ℝ} (hα : 0 ≤ α) :
    C.expectation (C.rejectionIndicator α) ≤ α := by
  rw [C.expectation_rejectionIndicator]
  exact C.exact_chain_calibration' hα

end CalibratedChain

section BooleanChain

/-- Expectation `E_{ν_C} g` for the auxiliary maximal-chain law. -/
noncomputable def booleanChainExpectation {m : ℕ}
    (γ β : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    (g : Finset (Fin m) → ℝ) : ℝ :=
  (booleanCalibratedChain γ β σ hγ hβ).expectation
    (fun j ↦
      if hj : j < m + 1 then g (chainState σ ⟨j, hj⟩) else 0)

/-- Increasing rejection payoff on the Boolean lattice. -/
noncomputable def booleanRejectionPayoff {m : ℕ}
    (γ β : Fin m → ℝ) (α : ℝ) (S : Finset (Fin m)) : ℝ :=
  if twoPointKFinset γ β S ≤ α then 1 else 0

theorem booleanChainExpectation_one {m : ℕ}
    (γ β : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i) :
    booleanChainExpectation γ β σ hγ hβ (fun _ ↦ 1) = 1 := by
  unfold booleanChainExpectation CalibratedChain.expectation
  rw [show (∑ j ∈ Finset.range (m + 1),
      chainMass (booleanCalibratedChain γ β σ hγ hβ).K j *
        (if hj : j < m + 1 then (1 : ℝ) else 0)) =
      ∑ j ∈ Finset.range (m + 1),
        chainMass (booleanCalibratedChain γ β σ hγ hβ).K j by
      apply Finset.sum_congr rfl
      intro j hj
      simp [Finset.mem_range.mp hj]]
  exact (booleanCalibratedChain γ β σ hγ hβ).total_mass

/-- Exact calibration stated directly for the statistic evaluated on the
states of a maximal Boolean chain. -/
theorem booleanChain_rejection_le {m : ℕ}
    (γ β : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    {α : ℝ} (hα : 0 ≤ α) :
    booleanChainExpectation γ β σ hγ hβ
      (booleanRejectionPayoff γ β α) ≤ α := by
  let C := booleanCalibratedChain γ β σ hγ hβ
  have heq :
      booleanChainExpectation γ β σ hγ hβ
          (booleanRejectionPayoff γ β α) =
        C.expectation (C.rejectionIndicator α) := by
    unfold booleanChainExpectation CalibratedChain.expectation
    apply Finset.sum_congr rfl
    intro j hj
    have hjlt := Finset.mem_range.mp hj
    simp only [booleanRejectionPayoff, CalibratedChain.rejectionIndicator]
    rw [dite_eq_left hjlt]
    dsimp [C, booleanCalibratedChain]
    simp only [booleanChainK_of_lt γ β σ hjlt]
  rw [heq]
  exact C.expectation_rejection_le hα

end BooleanChain

end Feige
