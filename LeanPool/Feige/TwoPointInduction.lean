/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.ChainInsertion
import LeanPool.Feige.ChainMeasure

/-!
# The finite induction in the two-point calibration argument

The local insertion result is the analytic input: at each stage one can
choose an insertion position that does not decrease the expectation of an
increasing payoff.  This file treats that statement as an explicit `Prop`
parameter and proves the remaining finite induction.  Thus no convolution or log-concavity claim
is hidden in the result below.
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

/-- A numerical tail-hybrid expectation.  Index `0` is the original product
expectation, and the last index is the expectation on the fully constructed
maximal chain. -/
def tailHybridExpectation {m : ℕ} (H : Fin (m + 1) → ℝ)
    (k : Fin (m + 1)) : ℝ :=
  H k

/-- The precise finite part of the local insertion hypothesis.  The witness
`σ` is the final maximal chain, while `H` records the successive hybrid
expectations obtained by the insertion choices. -/
def HasNondecreasingInsertionHybrid {m : ℕ}
    (γ β p : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    (g : Finset (Fin m) → ℝ) : Prop :=
  ∃ (σ : Equiv.Perm (Fin m)) (H : Fin (m + 1) → ℝ),
    H 0 = productHighSetExpectation p g ∧
    H (Fin.last m) = booleanChainExpectation γ β σ hγ hβ g ∧
    ∀ k : Fin m, H k.castSucc ≤ H k.succ

/-- Abstract local-insertion property sufficient for finite two-point
calibration: every increasing payoff admits nondecreasing insertion choices
at all levels. -/
def LocalInsertionDominance {m : ℕ}
    (γ β p : Fin m → ℝ) (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i) : Prop :=
  ∀ g : Finset (Fin m) → ℝ,
    Monotone g → HasNondecreasingInsertionHybrid γ β p hγ hβ g

/-- Pure finite induction: adjacent insertion dominance compares the initial
product expectation to the final chain expectation. -/
theorem productExpectation_le_chainExpectation_of_hybrid {m : ℕ}
    {γ β p : Fin m → ℝ} {hγ : ∀ i, 0 ≤ γ i} {hβ : ∀ i, 0 ≤ β i}
    {g : Finset (Fin m) → ℝ}
    (h : HasNondecreasingInsertionHybrid γ β p hγ hβ g) :
    ∃ σ : Equiv.Perm (Fin m),
      productHighSetExpectation p g ≤
        booleanChainExpectation γ β σ hγ hβ g := by
  obtain ⟨σ, H, hzero, hlast, hstep⟩ := h
  refine ⟨σ, ?_⟩
  rw [← hzero, ← hlast]
  exact (Fin.monotone_iff_le_succ.mpr hstep) (Fin.zero_le _)

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

/-- Finite two-point calibration with local insertion exposed as the explicit
hypothesis `hinsert`: the product rejection probability is at most `α`. -/
theorem twoPoint_product_rejection_le {m : ℕ}
    (γ β : Fin m → ℝ)
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    (p : Fin m → ℝ)
    (hinsert : LocalInsertionDominance γ β p hγ hβ)
    {α : ℝ} (hα : 0 ≤ α) :
    productHighSetExpectation p (booleanRejectionPayoff γ β α) ≤ α := by
  obtain ⟨σ, hσ⟩ :=
    productExpectation_le_chainExpectation_of_hybrid
      (hinsert _ (monotone_booleanRejectionPayoff γ β hγ hβ α))
  exact hσ.trans (booleanChain_rejection_le γ β σ hγ hβ hα)

/-- The finite two-point calibration result in named product-mass notation. -/
theorem twoPoint_rejection_le_of_localInsertion {m : ℕ}
    (γ β : Fin m → ℝ)
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 < β i)
    (hinsert : LocalInsertionDominance γ β
      (twoPointHighProbability γ β) hγ (fun i ↦ (hβ i).le))
    {α : ℝ} (hα : 0 ≤ α) :
    twoPointRejectionMass γ β α ≤ α := by
  rw [← productExpectation_rejection_eq]
  exact twoPoint_product_rejection_le γ β hγ (fun i ↦ (hβ i).le)
    (twoPointHighProbability γ β) hinsert hα

end Feige
