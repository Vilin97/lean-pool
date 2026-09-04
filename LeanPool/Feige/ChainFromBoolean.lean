/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.BooleanChain
import LeanPool.Feige.ChainCalibration

/-!
# Calibrated statistic sequences along maximal Boolean chains

This file evaluates `twoPointKFinset` on the states of a maximal chain and
extends the resulting finite sequence by zero.  The extension is a
`CalibratedChain`, so the exact telescoping calibration lemma applies
immediately.
-/

namespace Feige

/-- The two-point statistic along the maximal chain encoded by `σ`, extended
by zero from the sentinel index `m + 1` onwards. -/
noncomputable def booleanChainK {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) (j : ℕ) : ℝ :=
  if hj : j < m + 1 then
    twoPointKFinset γ β (chainState σ ⟨j, hj⟩)
  else
    0

@[simp]
theorem booleanChainK_of_lt {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) {j : ℕ} (hj : j < m + 1) :
    booleanChainK γ β σ j =
      twoPointKFinset γ β (chainState σ ⟨j, hj⟩) := by
  simp [booleanChainK, hj]

@[simp]
theorem booleanChainK_of_not_lt {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) {j : ℕ} (hj : ¬j < m + 1) :
    booleanChainK γ β σ j = 0 := by
  simp [booleanChainK, hj]

theorem booleanChainK_sentinel {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) :
    booleanChainK γ β σ (m + 1) = 0 := by
  exact booleanChainK_of_not_lt γ β σ (Nat.not_lt.mpr le_rfl)

theorem twoPointKFinset_nonneg {ι : Type*} [Fintype ι]
    (γ β : ι → ℝ) (S : Finset ι) :
    0 ≤ twoPointKFinset γ β S := by
  exact dirichletK_nonneg _

theorem booleanChainK_antitone {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 ≤ β i) :
    Antitone (booleanChainK γ β σ) := by
  intro j k hjk
  by_cases hk : k < m + 1
  · have hj : j < m + 1 := lt_of_le_of_lt hjk hk
    rw [booleanChainK_of_lt γ β σ hj, booleanChainK_of_lt γ β σ hk]
    apply twoPointKFinset_antitone hγ hβ
    exact chainState_mono σ hjk
  · rw [booleanChainK_of_not_lt γ β σ hk]
    by_cases hj : j < m + 1
    · rw [booleanChainK_of_lt γ β σ hj]
      exact twoPointKFinset_nonneg γ β _
    · rw [booleanChainK_of_not_lt γ β σ hj]

theorem booleanChainK_initial {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) (hγ : ∀ i, 0 ≤ γ i) :
    booleanChainK γ β σ 0 = 1 := by
  have hzero : 0 < m + 1 := Nat.zero_lt_succ m
  rw [booleanChainK_of_lt γ β σ hzero]
  have hs : chainState σ ⟨0, hzero⟩ = ∅ := by
    ext i
    simp
  rw [hs]
  simp only [twoPointKFinset, Finset.coe_empty]
  exact twoPointK_empty γ β hγ

/-- The calibrated sequence carried by a maximal Boolean-lattice chain. -/
noncomputable def booleanCalibratedChain {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 ≤ β i) : CalibratedChain m where
  K := booleanChainK γ β σ
  antitone := booleanChainK_antitone γ β σ hγ hβ
  initial := booleanChainK_initial γ β σ hγ
  sentinel := booleanChainK_sentinel γ β σ

/-- Exact calibration for the statistic values along any maximal
Boolean-lattice chain. -/
theorem booleanChain_exact_calibration {m : ℕ} (γ β : Fin m → ℝ)
    (σ : Equiv.Perm (Fin m)) (hγ : ∀ i, 0 ≤ γ i)
    (hβ : ∀ i, 0 ≤ β i) {α : ℝ} (hα : 0 ≤ α) :
    (booleanCalibratedChain γ β σ hγ hβ).rejectedMass α ≤ α :=
  (booleanCalibratedChain γ β σ hγ hβ).exact_chain_calibration' hα

end Feige
