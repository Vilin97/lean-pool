/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
import LeanPool.Feige.InsertionExpectation
import LeanPool.Feige.Lemma43Insertion

/-!
# Assembly of the analytic insertion edges

This file performs the last finite bookkeeping step in the chain-insertion
argument for Theorem 2.1.  Once each genuine edge of the old chain is
represented by the two signed-exponential endpoint laws from the local
transfer step, and the terminal edge is
represented by its one-sided common law, all positivity, monotonicity, and
transfer hypotheses required by `exists_insertChainPerm_dominates_reveal`
follow automatically.
-/

open MeasureTheory

namespace Feige

noncomputable section

/-- The low-side scale of the old coordinate changed at edge `j`; it equals
`1` at the terminal edge, which changes the distinguished exponential. -/
def insertionEdgeScale {n : ℕ}
    (γ : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n)) (j : ℕ) : ℝ :=
  if hj : j < n then γ (σ ⟨j, hj⟩).castSucc else 1

/-- The zero-extended interpolation sequence is identically zero from its
sentinel onward. -/
theorem insertionTheta_eq_zero_of_ge {n : ℕ}
    (γ β : Fin (n + 1) → ℝ) (σ : Equiv.Perm (Fin n))
    {r : ℕ} (hr : n + 1 ≤ r) :
    insertionTheta γ β σ r = 0 := by
  have hnot : ¬r < n + 1 := Nat.not_lt.mpr hr
  unfold insertionTheta insertionWidth insertionOldK
  rw [booleanChainK_of_not_lt _ _ _ hnot]
  simp [insertionLowerK, insertionUpperK, hnot]

/-- The chain-insertion conclusion after all measure-theoretic endpoint
identifications have been exposed as `RealizesInsertionEdge` hypotheses.

There is one genuine signed-exponential edge for every old coordinate.
The final edge changes the distinguished `E₀` from positive to negative;
its common law need only be supported on the nonpositive half-line. -/
theorem exists_insertChainPerm_dominates_reveal_of_realizedEdges
    {n : ℕ}
    (γ β : Fin (n + 1) → ℝ)
    (hγpos : ∀ i, 0 < γ i) (hγle : ∀ i, γ i ≤ 1)
    (hβpos : ∀ i, 0 < β i) (hγord : Antitone γ)
    (σ : Equiv.Perm (Fin n))
    {g : Finset (Fin (n + 1)) → ℝ} (hg : Monotone g)
    (Fs : Fin n → List LikelihoodRatio.SignedExpFactor)
    (hrealInterior : ∀ j : Fin n,
      Lemma43.RealizesInsertionEdge
        (insertionUpperK γ β σ) (insertionOldK γ β σ)
        (insertionWidth γ β σ) (insertionTheta γ β σ) j.val
        (TransferStein.zPlusLaw
          (volume.withDensity
            (LikelihoodRatio.finiteSignedExpSumDensity (Fs j)))
          (γ (σ j).castSucc))
        (TransferStein.zMinusLaw
          (volume.withDensity
            (LikelihoodRatio.finiteSignedExpSumDensity (Fs j)))
          (β (σ j).castSucc))
        (γ (Fin.last n)) (β (Fin.last n)))
    (μterminal : Measure ℝ) [IsProbabilityMeasure μterminal]
    (hterminalSupport : μterminal (Set.Ioi 0) = 0)
    (hrealTerminal :
      Lemma43.RealizesInsertionEdge
        (insertionUpperK γ β σ) (insertionOldK γ β σ)
        (insertionWidth γ β σ) (insertionTheta γ β σ) n
        (TransferStein.zPlusLaw μterminal 1)
        (TransferStein.zMinusLaw μterminal 1)
        (γ (Fin.last n)) (β (Fin.last n))) :
    ∃ J : Fin (n + 1),
      booleanChainExpectation
          (fun i ↦ γ i.castSucc) (fun i ↦ β i.castSucc) σ
          (fun i ↦ (hγpos i.castSucc).le)
          (fun i ↦ (hβpos i.castSucc).le)
          (revealedLastPayoff
            (twoPointHighProbability γ β (Fin.last n)) g) ≤
        booleanChainExpectation γ β (insertChainPerm σ J)
          (fun i ↦ (hγpos i).le) (fun i ↦ (hβpos i).le) g := by
  let c : ℝ := γ (Fin.last n)
  let d : ℝ := β (Fin.last n)
  have hc : 0 < c := hγpos (Fin.last n)
  have hd : 0 < d := hβpos (Fin.last n)
  have hinterior : ∀ j : Fin n,
      insertionTransfer (insertionUpperK γ β σ)
          (insertionOldK γ β σ) (insertionTheta γ β σ)
          (c / (c + d)) j.val =
        ((γ (σ j).castSucc - c) / (c + d)) *
            insertionWidth γ β σ j.val *
          (insertionTheta γ β σ j.val -
            insertionTheta γ β σ (j.val + 1)) ∧
      insertionTheta γ β σ (j.val + 1) ≤
          insertionTheta γ β σ j.val ∧
      0 < insertionWidth γ β σ j.val := by
    intro j
    exact Lemma43.finiteSignedExp_insertion_conclusions
      (Fs j) (hγpos (σ j).castSucc) (hβpos (σ j).castSucc)
      hc hd (hrealInterior j)
  have hterminal :
      insertionTransfer (insertionUpperK γ β σ)
          (insertionOldK γ β σ) (insertionTheta γ β σ)
          (c / (c + d)) n =
        ((1 - c) / (c + d)) * insertionWidth γ β σ n *
          (insertionTheta γ β σ n -
            insertionTheta γ β σ (n + 1)) ∧
      insertionTheta γ β σ (n + 1) ≤
          insertionTheta γ β σ n ∧
      0 < insertionWidth γ β σ n := by
    exact Lemma43.terminal_insertion_conclusions μterminal
      hterminalSupport hc hd hrealTerminal
  have hwidth : ∀ r < n + 1, 0 < insertionWidth γ β σ r := by
    intro r hr
    by_cases hrn : r < n
    · exact (hinterior ⟨r, hrn⟩).2.2
    · have hre : r = n := by omega
      simpa [hre] using hterminal.2.2
  have htheta : Antitone (insertionTheta γ β σ) := by
    apply antitone_nat_of_succ_le
    intro r
    by_cases hrn : r < n
    · exact (hinterior ⟨r, hrn⟩).2.1
    · by_cases hre : r = n
      · simpa [hre] using hterminal.2.1
      · have hrge : n + 1 ≤ r := by omega
        rw [insertionTheta_eq_zero_of_ge γ β σ hrge,
          insertionTheta_eq_zero_of_ge γ β σ (by omega)]
  have hac : ∀ j < n + 1, c ≤ insertionEdgeScale γ σ j := by
    intro j hj
    by_cases hjn : j < n
    · rw [insertionEdgeScale, dite_eq_left hjn]
      exact hγord (Fin.le_last ((σ ⟨j, hjn⟩).castSucc))
    · have hje : j = n := by omega
      rw [insertionEdgeScale, dite_eq_right hjn]
      exact hγle (Fin.last n)
  have htransfer : ∀ j < n + 1,
      insertionTransfer (insertionUpperK γ β σ)
          (insertionOldK γ β σ) (insertionTheta γ β σ)
          (c / (c + d)) j =
        ((insertionEdgeScale γ σ j - c) / (c + d)) *
            insertionWidth γ β σ j *
          (insertionTheta γ β σ j -
            insertionTheta γ β σ (j + 1)) := by
    intro j hj
    by_cases hjn : j < n
    · simpa [insertionEdgeScale, hjn] using (hinterior ⟨j, hjn⟩).1
    · have hje : j = n := by omega
      simpa [insertionEdgeScale, hjn, hje] using hterminal.1
  have hdom :=
    exists_insertChainPerm_dominates_reveal γ β σ
      (fun i ↦ (hγpos i).le) (fun i ↦ (hβpos i).le) hg
      (insertionEdgeScale γ σ) (c / (c + d)) c d
      hwidth htheta hac (add_pos hc hd) htransfer
  simpa [c, d, twoPointHighProbability, highProbability] using hdom

end

end Feige
