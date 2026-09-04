/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.InsertionK
import LeanPool.Feige.ChainMeasure

/-!
# Expectations on inserted maximal chains

This file rewrites the chain expectation in terms of the direct inserted
states.  Together with `InsertionK` and `InsertionAlgebra`, it is the bridge
from concrete Boolean chains to the pairwise mass-transport calculation in
the proof of Theorem 2.1.
-/

open scoped BigOperators

namespace Feige

/-- Expand a Boolean-chain expectation as its finite level sum. -/
theorem booleanChainExpectation_eq_levelSum {m : ℕ}
    (γ β : Fin m → ℝ) (σ : Equiv.Perm (Fin m))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    (g : Finset (Fin m) → ℝ) :
    booleanChainExpectation γ β σ hγ hβ g =
      ∑ r : Fin (m + 1),
        chainMass (booleanChainK γ β σ) r.val *
          g (chainState σ r) := by
  unfold booleanChainExpectation CalibratedChain.expectation
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro r hr
  change
    chainMass (booleanChainK γ β σ) r.val *
        (if hj : r.val < m + 1 then
          g (chainState σ ⟨r.val, hj⟩) else 0) =
      chainMass (booleanChainK γ β σ) r.val * g (chainState σ r)
  rw [dite_eq_left r.isLt]

/-- For an inserted permutation, the same expectation is carried by the
direct states `C₀,...,C_J,H_J,...,Hₙ`. -/
theorem booleanChainExpectation_insertChainPerm_eq_levelSum {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    (g : Finset (Fin (n + 1)) → ℝ) :
    booleanChainExpectation γ β (insertChainPerm σ J) hγ hβ g =
      ∑ r : Fin (n + 2),
        chainMass (booleanChainK γ β (insertChainPerm σ J)) r.val *
          g (insertedChainState σ J r) := by
  rw [booleanChainExpectation_eq_levelSum]
  apply Finset.sum_congr rfl
  intro r hr
  congr 2
  exact chainState_insertChainPerm_eq_insertedChainState σ J r

/-- Payoff at a lifted lower state `Cᵣ`, with a harmless zero extension. -/
noncomputable def insertionLowerPayoff {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (g : Finset (Fin (n + 1)) → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r < n + 1 then
    g (liftChainState (chainState σ ⟨r, hr⟩))
  else 0

/-- Payoff at a lifted upper state `Hᵣ`, with a harmless zero extension. -/
noncomputable def insertionUpperPayoff {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (g : Finset (Fin (n + 1)) → ℝ)
    (r : ℕ) : ℝ :=
  if hr : r < n + 1 then
    g (insert (Fin.last n) (liftChainState (chainState σ ⟨r, hr⟩)))
  else 0

/-- Payoff after independently revealing the new last coordinate with
probability `p`. -/
noncomputable def revealedLastPayoff {n : ℕ}
    (p : ℝ) (g : Finset (Fin (n + 1)) → ℝ)
    (S : Finset (Fin n)) : ℝ :=
  (1 - p) * g (liftChainState S) +
    p * g (insert (Fin.last n) (liftChainState S))

/-- In expectation form, the old chain followed by an independent Bernoulli
reveal expands into the independent lower and upper pair masses. -/
theorem booleanChainExpectation_revealedLast_eq_pairSum {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    (p : ℝ) (g : Finset (Fin (n + 1)) → ℝ) :
    booleanChainExpectation
        (fun i ↦ γ i.castSucc) (fun i ↦ β i.castSucc) σ
        (fun i ↦ hγ i.castSucc) (fun i ↦ hβ i.castSucc)
        (revealedLastPayoff p g) =
      ∑ j ∈ Finset.range (n + 1),
        (independentLowerMass (insertionOldK γ β σ) p j *
            insertionLowerPayoff σ g j +
          independentUpperMass (insertionOldK γ β σ) p j *
            insertionUpperPayoff σ g j) := by
  rw [booleanChainExpectation_eq_levelSum]
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro j hj
  have hjlt := j.isLt
  unfold revealedLastPayoff insertionLowerPayoff insertionUpperPayoff
    independentLowerMass independentUpperMass insertionOldK chainMass
  rw [dite_eq_left hjlt, dite_eq_left hjlt]
  ring

/-- An increasing Boolean-lattice payoff is increasing on every insertion
pair `Cᵣ ⊆ Hᵣ`. -/
theorem insertionLowerPayoff_le_upperPayoff {n : ℕ}
    (σ : Equiv.Perm (Fin n)) {g : Finset (Fin (n + 1)) → ℝ}
    (hg : Monotone g) (r : ℕ) :
    insertionLowerPayoff σ g r ≤ insertionUpperPayoff σ g r := by
  by_cases hr : r < n + 1
  · rw [insertionLowerPayoff, dite_eq_left hr,
      insertionUpperPayoff, dite_eq_left hr]
    exact hg (Finset.subset_insert _ _)
  · simp [insertionLowerPayoff, insertionUpperPayoff, hr]

/-- Each level term in the abstract insertion score is the corresponding
term of the concrete inserted Boolean-chain expectation. -/
theorem insertionLevelScore_eq_booleanChainTerm {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1)) (g : Finset (Fin (n + 1)) → ℝ)
    (r : Fin (n + 2)) :
    insertionLevelScore
        (insertionUpperK γ β σ) (insertionLowerK γ β σ)
        (fun q ↦ insertionLowerK γ β σ q - insertionUpperK γ β σ q)
        (insertionLowerPayoff σ g) (insertionUpperPayoff σ g)
        J.val r.val =
      chainMass (booleanChainK γ β (insertChainPerm σ J)) r.val *
        g (insertedChainState σ J r) := by
  by_cases h : r.val ≤ J.val
  · let j : Fin (n + 1) := ⟨r.val, lt_of_le_of_lt h J.isLt⟩
    have hjJ : j ≤ J := h
    unfold insertionLevelScore insertionLowerPayoff
    rw [ite_eq_left h, dite_eq_left j.isLt]
    rw [← chainMass_booleanChainK_insert_lower γ β σ J j hjJ]
    unfold insertedChainState
    rw [dite_eq_left h]
  · have hJr : J.val < r.val := Nat.lt_of_not_ge h
    have hrpos : 0 < r.val := lt_of_le_of_lt (Nat.zero_le _) hJr
    let j : Fin (n + 1) := ⟨r.val - 1, by omega⟩
    have hJj : J ≤ j := by
      change J.val ≤ j.val
      simp only [j]
      omega
    unfold insertionLevelScore insertionUpperPayoff
    rw [ite_eq_right h, dite_eq_left j.isLt]
    rw [← chainMass_booleanChainK_insert_upper γ β σ J j hJj]
    unfold insertedChainState
    rw [dite_eq_right h]
    congr 3
    all_goals simp only [j]
    all_goals omega

/-- The canonical pairwise score is exactly the concrete expectation of
the corresponding inserted maximal chain. -/
theorem insertionPairScore_eq_booleanChainExpectation {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (J : Fin (n + 1))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    (g : Finset (Fin (n + 1)) → ℝ) :
    insertionPairScore
        (insertionUpperK γ β σ) (insertionLowerK γ β σ)
        (fun q ↦ insertionLowerK γ β σ q - insertionUpperK γ β σ q)
        (insertionLowerPayoff σ g) (insertionUpperPayoff σ g)
        (n + 1) J.val =
      booleanChainExpectation γ β (insertChainPerm σ J) hγ hβ g := by
  rw [insertionPairScore_eq_levelScore J.isLt]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [booleanChainExpectation_insertChainPerm_eq_levelSum]
  apply Finset.sum_congr rfl
  intro r hr
  exact insertionLevelScore_eq_booleanChainTerm γ β σ J g r

/-- Concrete finite conclusion of the chain-insertion step.

All combinatorial and averaging steps have been discharged: the remaining
hypotheses are exactly the analytic sequence identities and signs supplied
by the exponential-transfer argument. -/
theorem exists_insertChainPerm_expectation_ge_of_transfer {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    {g : Finset (Fin (n + 1)) → ℝ} (hg : Monotone g)
    (F θ a : ℕ → ℝ) (p c d old : ℝ)
    (hF : ∀ r,
      F r = insertionUpperK γ β σ r +
        θ r * (insertionLowerK γ β σ r - insertionUpperK γ β σ r))
    (hθ : Antitone θ)
    (hθ0 : θ 0 = 1) (hθlast : θ (n + 1) = 0)
    (hac : ∀ j < n + 1, c ≤ a j)
    (hcd : 0 < c + d)
    (hw : ∀ j < n + 1,
      0 ≤ insertionLowerK γ β σ j - insertionUpperK γ β σ j)
    (htransfer : ∀ j < n + 1,
      insertionTransfer (insertionUpperK γ β σ) F θ p j =
        ((a j - c) / (c + d)) *
          (insertionLowerK γ β σ j - insertionUpperK γ β σ j) *
            (θ j - θ (j + 1)))
    (hold : old =
      ∑ j ∈ Finset.range (n + 1),
        (independentLowerMass F p j * insertionLowerPayoff σ g j +
          independentUpperMass F p j * insertionUpperPayoff σ g j)) :
    ∃ J : Fin (n + 1),
      old ≤ booleanChainExpectation γ β (insertChainPerm σ J) hγ hβ g := by
  let A := insertionUpperK γ β σ
  let B := insertionLowerK γ β σ
  let w := fun r ↦ B r - A r
  let gLower := insertionLowerPayoff σ g
  let gUpper := insertionUpperPayoff σ g
  have hB : ∀ r, B r = A r + w r := by
    intro r
    dsimp [w]
    ring
  have hgpair : ∀ j < n + 1, gLower j ≤ gUpper j := by
    intro j hj
    exact insertionLowerPayoff_le_upperPayoff σ hg j
  obtain ⟨j, hj, hscore⟩ :=
    exists_insertionPairScore_of_transfer (Nat.zero_lt_succ n)
      hB hF hθ hθ0 hθlast hac hcd hw htransfer hgpair hold
  let J : Fin (n + 1) := ⟨j, hj⟩
  refine ⟨J, ?_⟩
  rw [← insertionPairScore_eq_booleanChainExpectation γ β σ J hγ hβ g]
  exact hscore

/-- The chain-insertion conclusion specialized to the actual `F,A,B,w,θ`
sequences of an old Boolean chain.  Only strict band positivity,
monotonicity of `θ`, the edgewise transfer identity, and the
old-expectation expansion remain as analytic inputs. -/
theorem exists_insertChainPerm_expectation_ge {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    {g : Finset (Fin (n + 1)) → ℝ} (hg : Monotone g)
    (a : ℕ → ℝ) (p c d old : ℝ)
    (hwidth : ∀ r < n + 1, 0 < insertionWidth γ β σ r)
    (hθ : Antitone (insertionTheta γ β σ))
    (hac : ∀ j < n + 1, c ≤ a j)
    (hcd : 0 < c + d)
    (htransfer : ∀ j < n + 1,
      insertionTransfer (insertionUpperK γ β σ)
          (insertionOldK γ β σ) (insertionTheta γ β σ) p j =
        ((a j - c) / (c + d)) * insertionWidth γ β σ j *
          (insertionTheta γ β σ j - insertionTheta γ β σ (j + 1)))
    (hold : old =
      ∑ j ∈ Finset.range (n + 1),
        (independentLowerMass (insertionOldK γ β σ) p j *
            insertionLowerPayoff σ g j +
          independentUpperMass (insertionOldK γ β σ) p j *
            insertionUpperPayoff σ g j)) :
    ∃ J : Fin (n + 1),
      old ≤ booleanChainExpectation γ β (insertChainPerm σ J) hγ hβ g := by
  apply exists_insertChainPerm_expectation_ge_of_transfer γ β σ hγ hβ hg
      (insertionOldK γ β σ) (insertionTheta γ β σ) a p c d old
  · exact insertionOldK_eq_upper_add_theta_mul_width_all γ β σ
      (fun r hr ↦ (hwidth r hr).ne')
  · exact hθ
  · exact insertionTheta_zero γ β σ hγ (hwidth 0 (Nat.zero_lt_succ n)).ne'
  · exact insertionTheta_sentinel γ β σ
  · exact hac
  · exact hcd
  · intro j hj
    simpa [insertionWidth] using insertionWidth_nonneg γ β σ hγ hβ j
  · simpa [insertionWidth] using htransfer
  · exact hold

/-- In chain-expectation form, independently revealing the new coordinate
is dominated by one concrete insertion of that coordinate into the old
maximal chain. -/
theorem exists_insertChainPerm_dominates_reveal {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    (hγ : ∀ i, 0 ≤ γ i) (hβ : ∀ i, 0 ≤ β i)
    {g : Finset (Fin (n + 1)) → ℝ} (hg : Monotone g)
    (a : ℕ → ℝ) (p c d : ℝ)
    (hwidth : ∀ r < n + 1, 0 < insertionWidth γ β σ r)
    (hθ : Antitone (insertionTheta γ β σ))
    (hac : ∀ j < n + 1, c ≤ a j)
    (hcd : 0 < c + d)
    (htransfer : ∀ j < n + 1,
      insertionTransfer (insertionUpperK γ β σ)
          (insertionOldK γ β σ) (insertionTheta γ β σ) p j =
        ((a j - c) / (c + d)) * insertionWidth γ β σ j *
          (insertionTheta γ β σ j - insertionTheta γ β σ (j + 1))) :
    ∃ J : Fin (n + 1),
      booleanChainExpectation
          (fun i ↦ γ i.castSucc) (fun i ↦ β i.castSucc) σ
          (fun i ↦ hγ i.castSucc) (fun i ↦ hβ i.castSucc)
          (revealedLastPayoff p g) ≤
        booleanChainExpectation γ β (insertChainPerm σ J) hγ hβ g := by
  apply exists_insertChainPerm_expectation_ge γ β σ hγ hβ hg
    a p c d
    (booleanChainExpectation
      (fun i ↦ γ i.castSucc) (fun i ↦ β i.castSucc) σ
      (fun i ↦ hγ i.castSucc) (fun i ↦ hβ i.castSucc)
      (revealedLastPayoff p g))
    hwidth hθ hac hcd htransfer
  exact booleanChainExpectation_revealedLast_eq_pairSum γ β σ hγ hβ p g

end Feige
